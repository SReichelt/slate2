//! The buffers implemented in this file form a flexible custom implementation of text ropes, with
//! two distinguishing features:
//!
//! * There is no concept of lines and columns; clients can freely decide how to split strings. In
//!   particular, this facilitates adhering to the line ending rules of the language server protocol
//!   (LSP) without having to encode these rules in the text rope implementation.
//!   (In contrast, it seems that existing text rope crates are currently not LSP-compatible.)
//!
//! * Chunks can be nested, so a client can decide to add further chunking to lines and/or columns,
//!   resulting in markers with more than two fields. This can help keep markers stable when lines
//!   are inserted or removed.
//!
//! We currently don't optimize for extreme performance. In fact, operations that insert or remove
//! chunks have a linear runtime (unless operations are guaranteed to happen at or near the end).
//! Clients are expected to mitigate this using nested chunks.

use std::{borrow::Cow, marker::PhantomData, mem::take, ops::Range};

use smallvec::SmallVec;

use crate::{char::*, char_slice::*, event::*, event_sequence::*, event_source::*};

pub trait CharEventBuffer<'a>: Default + EventSequence<'a, Ev = char> {
    type Input<'b>;

    fn from_input(input: Self::Input<'_>) -> Result<Self, Message> {
        let (buffer, _) = Self::from_input_with_range(input)?;
        Ok(buffer)
    }

    fn from_input_with_range(
        input: Self::Input<'_>,
    ) -> Result<(Self, Range<Self::Marker>), Message> {
        let mut buffer = Self::default();
        let range = buffer.insert(&Self::start_marker(), input)?;
        Ok((buffer, range))
    }

    fn to_input(&self, range: Range<Option<&Self::Marker>>) -> Self::Input<'_>;

    fn replace(
        &mut self,
        range: Range<Option<&Self::Marker>>,
        input: Self::Input<'_>,
    ) -> Result<Range<Self::Marker>, Message>;

    fn insert(
        &mut self,
        pos: &Self::Marker,
        input: Self::Input<'_>,
    ) -> Result<Range<Self::Marker>, Message> {
        self.replace(Some(pos)..Some(pos), input)
    }

    fn delete(&mut self, range: Range<Option<&Self::Marker>>) -> Result<Self::Marker, Message> {
        self.replace(range, Self::empty_input())
            .map(|range| range.start)
    }

    fn empty_input<'b>() -> Self::Input<'b>;

    fn append_input_to_string(input: Self::Input<'_>, s: &mut String);

    fn append_to_string(&self, range: Range<Option<&Self::Marker>>, s: &mut String) {
        Self::append_input_to_string(self.to_input(range), s)
    }
}

pub struct CharBuffer {
    s: String,
}

impl CharBuffer {
    fn new() -> Self {
        CharBuffer { s: String::new() }
    }

    fn get_range(&self, range: Range<Option<&Marker>>) -> Range<usize> {
        let start = range.start.map(unpack_marker).unwrap_or(0);
        let end = range.end.map(unpack_marker).unwrap_or_else(|| self.s.len());
        start..end
    }
}

impl Default for CharBuffer {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> EventSequence<'a> for CharBuffer {
    type Ev = char;
    type Marker = Marker;

    fn for_each(&self, mut f: impl FnMut(Self::Ev, Range<&Self::Marker>)) -> Self::Marker {
        let mut chars = self.s.char_indices();
        while let Some((idx, c)) = chars.next() {
            let start_marker = pack_marker(idx);
            let end_marker = pack_marker(chars.offset());
            f(c, &start_marker..&end_marker);
        }
        pack_marker(chars.offset())
    }

    fn special_ops(&'a self) -> <Self::Ev as Event>::SpecialOps<'a, Self::Marker> {
        self
    }

    fn start_marker() -> Self::Marker {
        pack_marker(0)
    }
}

impl<'a> CharEventOps<'a, Marker> for CharBuffer {
    fn slice(&'a self, range: Range<&Marker>) -> Cow<'a, str> {
        Cow::Borrowed(&self.s[unpack_marker_range(range)])
    }
}

impl<'a> CharEventBuffer<'a> for CharBuffer {
    type Input<'b> = &'b str;

    fn to_input(&self, range: Range<Option<&Self::Marker>>) -> Self::Input<'_> {
        &self.s[self.get_range(range)]
    }

    fn replace(
        &mut self,
        range: Range<Option<&Self::Marker>>,
        s: Self::Input<'_>,
    ) -> Result<Range<Self::Marker>, Message> {
        let range = self.get_range(range);
        if self.s.len() - (range.end - range.start) + s.len() > MAX_LEN {
            return Err(format!("input larger than {MAX_LEN} bytes not supported"));
        }
        let start = range.start;
        self.s.replace_range(range, s);
        Ok(pack_marker(start)..pack_marker(start + s.len()))
    }

    fn empty_input<'b>() -> Self::Input<'b> {
        ""
    }

    fn append_input_to_string(input: Self::Input<'_>, s: &mut String) {
        *s += input;
    }
}

pub trait LimitedIndex: Clone + PartialEq {
    fn max() -> usize;

    fn from_usize(idx: usize) -> Self;
    fn to_usize(&self) -> usize;
}

macro_rules! limited_index {
    ($ty: tt) => {
        impl LimitedIndex for $ty {
            fn max() -> usize {
                $ty::MAX as usize
            }

            fn from_usize(idx: usize) -> Self {
                idx as $ty
            }

            fn to_usize(&self) -> usize {
                *self as usize
            }
        }
    };
}

limited_index!(u8);
limited_index!(u16);
limited_index!(u32);
limited_index!(usize);

type ChunkVec<T> = SmallVec<[T; 1]>;

pub struct ChunkedEventBuffer<ChunkIdx, Chunk> {
    chunks: ChunkVec<Chunk>,
    _phantom_idx: PhantomData<ChunkIdx>,
}

impl<'a, ChunkIdx: LimitedIndex, Chunk: CharEventBuffer<'a>> ChunkedEventBuffer<ChunkIdx, Chunk> {
    fn new() -> Self {
        ChunkedEventBuffer {
            chunks: ChunkVec::new(),
            _phantom_idx: PhantomData,
        }
    }

    fn max_chunk_idx(&self) -> usize {
        if self.chunks.is_empty() {
            0
        } else {
            self.chunks.len() - 1
        }
    }

    fn inserted_chunks(input: &[Chunk::Input<'_>]) -> usize {
        if input.is_empty() {
            0
        } else {
            input.len() - 1
        }
    }

    fn get_range<'b>(
        &self,
        range: Range<Option<&'b (ChunkIdx, Chunk::Marker)>>,
    ) -> Range<(usize, Option<&'b Chunk::Marker>)> {
        let start = if let Some(start) = range.start {
            (start.0.to_usize(), Some(&start.1))
        } else {
            (0, None)
        };
        let end = if let Some(end) = range.end {
            (end.0.to_usize(), Some(&end.1))
        } else {
            (self.max_chunk_idx(), None)
        };
        start..end
    }

    fn remove_chunks(&mut self, start_idx: usize, count: usize) {
        if count > 0 {
            let new_len = self.chunks.len() - count;
            for idx in start_idx..new_len {
                self.chunks.swap(idx, idx + count);
            }
            self.chunks.truncate(new_len);
        }
    }

    fn replace_chunks(&mut self, start_idx: usize, count: usize, chunks: ChunkVec<Chunk>) {
        let mut idx = start_idx;
        let mut remaining_count = count;
        for chunk in chunks {
            if remaining_count > 0 {
                self.chunks[idx] = chunk;
                remaining_count -= 1;
            } else {
                self.chunks.insert(idx, chunk);
            }
            idx += 1;
        }
        self.remove_chunks(idx, remaining_count);
    }
}

impl<'a, ChunkIdx: LimitedIndex, Chunk: CharEventBuffer<'a>> Default
    for ChunkedEventBuffer<ChunkIdx, Chunk>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, ChunkIdx: LimitedIndex, Chunk: CharEventBuffer<'a>> EventSequence<'a>
    for ChunkedEventBuffer<ChunkIdx, Chunk>
{
    type Ev = Chunk::Ev;
    type Marker = (ChunkIdx, Chunk::Marker);

    fn for_each(&self, mut f: impl FnMut(Self::Ev, Range<&Self::Marker>)) -> Self::Marker {
        let mut chunk_idx = None;
        let mut chunk_end_marker = Chunk::start_marker();
        for chunk in &self.chunks {
            let new_chunk_idx = if let Some(chunk_idx) = chunk_idx {
                chunk_idx + 1
            } else {
                0
            };
            chunk_idx = Some(new_chunk_idx);
            let new_chunk_idx = ChunkIdx::from_usize(new_chunk_idx);
            chunk_end_marker = chunk.for_each(|event, range| {
                f(
                    event,
                    &(new_chunk_idx.clone(), range.start.clone())
                        ..&(new_chunk_idx.clone(), range.end.clone()),
                )
            });
        }
        (
            ChunkIdx::from_usize(chunk_idx.unwrap_or(0)),
            chunk_end_marker,
        )
    }

    fn special_ops(&'a self) -> <Self::Ev as Event>::SpecialOps<'a, Self::Marker> {
        self
    }

    fn start_marker() -> Self::Marker {
        (ChunkIdx::from_usize(0), Chunk::start_marker())
    }
}

impl<'a, ChunkIdx: LimitedIndex, Chunk: CharEventBuffer<'a>>
    CharEventOps<'a, (ChunkIdx, Chunk::Marker)> for ChunkedEventBuffer<ChunkIdx, Chunk>
{
    fn slice(&'a self, range: Range<&(ChunkIdx, Chunk::Marker)>) -> Cow<'a, str> {
        if range.start.0 == range.end.0 && (range.start.0.to_usize()) < self.chunks.len() {
            self.chunks[range.start.0.to_usize()]
                .special_ops()
                .slice(&range.start.1..&range.end.1)
        } else {
            let mut s = String::new();
            self.append_to_string(Some(range.start)..Some(range.end), &mut s);
            Cow::Owned(s)
        }
    }
}

impl<'a, ChunkIdx: LimitedIndex, Chunk: CharEventBuffer<'a>> CharEventBuffer<'a>
    for ChunkedEventBuffer<ChunkIdx, Chunk>
{
    type Input<'b> = ChunkVec<Chunk::Input<'b>>;

    fn to_input(&self, range: Range<Option<&Self::Marker>>) -> Self::Input<'_> {
        if self.chunks.is_empty() {
            Self::empty_input()
        } else {
            let range = self.get_range(range);
            let mut result = ChunkVec::with_capacity(range.end.0 - range.start.0 + 1);
            let mut cur_start_col = range.start.1;
            for cur_row in range.start.0..range.end.0 {
                result.push(self.chunks[cur_row].to_input(cur_start_col..None));
                cur_start_col = None;
            }
            result.push(self.chunks[range.end.0].to_input(cur_start_col..range.end.1));
            result
        }
    }

    fn replace(
        &mut self,
        range: Range<Option<&Self::Marker>>,
        mut input: Self::Input<'_>,
    ) -> Result<Range<Self::Marker>, Message> {
        let range = self.get_range(range);
        let removed_chunks = range.end.0 - range.start.0;
        let inserted_chunks = Self::inserted_chunks(&input);
        let max_chunk_idx = self.max_chunk_idx() - removed_chunks + inserted_chunks;
        let max_chunks = ChunkIdx::max();
        if max_chunk_idx >= max_chunks {
            return Err(format!("number of chunks cannot exceed {max_chunks}"));
        }

        let mut result_range: Range<Self::Marker>;

        if self.chunks.is_empty() {
            result_range = Self::start_marker()..Self::start_marker();
            let mut chunks = ChunkVec::with_capacity(input.len());
            for chunk_input in input {
                let (chunk, chunk_range) = Chunk::from_input_with_range(chunk_input)?;
                result_range.end = (ChunkIdx::from_usize(chunks.len()), chunk_range.end);
                chunks.push(chunk);
            }
            self.chunks = chunks;
        } else if inserted_chunks == 0 {
            let result_chunk_idx = ChunkIdx::from_usize(range.start.0);
            let chunk_input = input.pop().unwrap_or_else(Chunk::empty_input);
            let input_range: Range<Chunk::Marker>;
            if removed_chunks > 0 && range.end.1.is_some() {
                input_range = self.chunks[range.start.0]
                    .insert(range.start.1.unwrap_or(&Chunk::start_marker()), chunk_input)?;
                let last_removed_chunk = take(&mut self.chunks[range.end.0]);
                let to_append = last_removed_chunk.to_input(range.end.1..None);
                if let Err(err) =
                    self.chunks[range.start.0].replace(Some(&input_range.end)..None, to_append)
                {
                    self.chunks[range.start.0]
                        .delete(Some(&input_range.start)..Some(&input_range.end))
                        .unwrap();
                    self.chunks[range.end.0] = last_removed_chunk;
                    return Err(err);
                }
            } else {
                input_range =
                    self.chunks[range.start.0].replace(range.start.1..range.end.1, chunk_input)?;
            }
            self.remove_chunks(range.start.0 + 1, removed_chunks);
            result_range =
                (result_chunk_idx.clone(), input_range.start)..(result_chunk_idx, input_range.end);
        } else {
            let last_chunk_input = input.pop().unwrap();
            debug_assert_eq!(input.len(), inserted_chunks);
            let mut chunks_to_insert = ChunkVec::with_capacity(inserted_chunks);
            for chunk_input in input {
                chunks_to_insert.push(Chunk::from_input(chunk_input)?);
            }
            let first_chunk_start: Chunk::Marker;
            if range.start.1.is_some() {
                let insert_range = chunks_to_insert.first_mut().unwrap().insert(
                    &Chunk::start_marker(),
                    self.chunks[range.start.0].to_input(None..range.start.1),
                )?;
                first_chunk_start = insert_range.end;
            } else {
                first_chunk_start = Chunk::start_marker();
            }
            let last_chunk_range =
                self.chunks[range.end.0].replace(None..range.end.1, last_chunk_input)?;
            if inserted_chunks > removed_chunks {
                self.chunks.reserve(inserted_chunks - removed_chunks);
            }
            self.replace_chunks(range.start.0, removed_chunks, chunks_to_insert);
            let result_start_chunk_idx = ChunkIdx::from_usize(range.start.0);
            let result_end_chunk_idx = ChunkIdx::from_usize(range.start.0 + inserted_chunks);
            result_range = (result_start_chunk_idx, first_chunk_start)
                ..(result_end_chunk_idx, last_chunk_range.end);
        }

        debug_assert_eq!(self.max_chunk_idx(), max_chunk_idx);

        Ok(result_range)
    }

    fn empty_input<'b>() -> Self::Input<'b> {
        ChunkVec::new()
    }

    fn append_input_to_string(input: Self::Input<'_>, s: &mut String) {
        for input_chunk in input {
            Chunk::append_input_to_string(input_chunk, s);
        }
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;

    use super::*;

    #[test]
    fn from_empty_input() -> Result<(), Message> {
        let mut buffer = ChunkedEventBuffer::<u8, CharBuffer>::from_input(SmallVec::new())?;
        assert_contents(&buffer, "");
        let pos = buffer.delete(None..None)?;
        assert_eq!(pos, (0, pack_marker(0)));
        assert_contents(&buffer, "");
        Ok(())
    }

    #[test]
    fn from_single_chunk() -> Result<(), Message> {
        let mut buffer = ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["abc"])?;
        assert_contents(&buffer, "abc");
        let pos = buffer.delete(None..None)?;
        assert_eq!(pos, (0, pack_marker(0)));
        assert_contents(&buffer, "");
        Ok(())
    }

    #[test]
    fn from_multiple_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "b", "c"])?;
        assert_contents(&buffer, "abc");
        let pos = buffer.delete(None..None)?;
        assert_eq!(pos, (0, pack_marker(0)));
        assert_contents(&buffer, "");
        Ok(())
    }

    #[test]
    fn delete_nothing() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "d"])?;
        let pos = buffer.delete(Some(&(1, pack_marker(1)))..Some(&(1, pack_marker(1))))?;
        assert_eq!(pos, (1, pack_marker(1)));
        assert_contents(&buffer, "abcd");
        Ok(())
    }

    #[test]
    fn delete_within_chunk() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bcd", "e"])?;
        let pos = buffer.delete(Some(&(1, pack_marker(1)))..Some(&(1, pack_marker(2))))?;
        assert_eq!(pos, (1, pack_marker(1)));
        assert_contents(&buffer, "abde");
        Ok(())
    }

    #[test]
    fn delete_across_two_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "de", "f"])?;
        let pos = buffer.delete(Some(&(1, pack_marker(1)))..Some(&(2, pack_marker(1))))?;
        assert_eq!(pos, (1, pack_marker(1)));
        assert_contents(&buffer, "abef");
        Ok(())
    }

    #[test]
    fn delete_across_three_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["ab", "c", "de", "f"])?;
        let pos = buffer.delete(Some(&(0, pack_marker(1)))..Some(&(2, pack_marker(1))))?;
        assert_eq!(pos, (0, pack_marker(1)));
        assert_contents(&buffer, "aef");
        Ok(())
    }

    #[test]
    fn insert_empty_input() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "d"])?;
        let range = buffer.insert(&(1, pack_marker(1)), SmallVec::new())?;
        assert_eq!(range, (1, pack_marker(1))..(1, pack_marker(1)));
        assert_contents(&buffer, "abcd");
        Ok(())
    }

    #[test]
    fn insert_single_chunk() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "be", "f"])?;
        let range = buffer.insert(&(1, pack_marker(1)), smallvec!["cd"])?;
        assert_eq!(range, (1, pack_marker(1))..(1, pack_marker(3)));
        assert_contents(&buffer, "abcdef");
        Ok(())
    }

    #[test]
    fn insert_multiple_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bg", "h"])?;
        let range = buffer.insert(&(1, pack_marker(1)), smallvec!["c", "d", "ef"])?;
        assert_eq!(range, (1, pack_marker(1))..(3, pack_marker(2)));
        assert_contents(&buffer, "abcdefgh");
        Ok(())
    }

    #[test]
    fn replace_within_chunk() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bcd", "e"])?;
        let range = buffer.replace(
            Some(&(1, pack_marker(1)))..Some(&(1, pack_marker(2))),
            smallvec!["xyz"],
        )?;
        assert_eq!(range, (1, pack_marker(1))..(1, pack_marker(4)));
        assert_contents(&buffer, "abxyzde");
        Ok(())
    }

    #[test]
    fn replace_additional_chunks_within_chunk() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bcd", "e"])?;
        let range = buffer.replace(
            Some(&(1, pack_marker(1)))..Some(&(1, pack_marker(2))),
            smallvec!["x", "y", "z"],
        )?;
        assert_eq!(range, (1, pack_marker(1))..(3, pack_marker(1)));
        assert_contents(&buffer, "abxyzde");
        Ok(())
    }

    #[test]
    fn replace_with_single_chunk() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "d", "ef", "g"])?;
        let range = buffer.replace(
            Some(&(1, pack_marker(1)))..Some(&(3, pack_marker(1))),
            smallvec!["xx"],
        )?;
        assert_eq!(range, (1, pack_marker(1))..(1, pack_marker(3)));
        assert_contents(&buffer, "abxxfg");
        Ok(())
    }

    #[test]
    fn replace_with_fewer_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "d", "ef", "g"])?;
        let range = buffer.replace(
            Some(&(1, pack_marker(1)))..Some(&(3, pack_marker(1))),
            smallvec!["xx", "yy"],
        )?;
        assert_eq!(range, (1, pack_marker(1))..(2, pack_marker(2)));
        assert_contents(&buffer, "abxxyyfg");
        Ok(())
    }

    #[test]
    fn replace_with_equal_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "d", "ef", "g"])?;
        let range = buffer.replace(
            Some(&(1, pack_marker(1)))..Some(&(3, pack_marker(1))),
            smallvec!["xx", "yy", "zz"],
        )?;
        assert_eq!(range, (1, pack_marker(1))..(3, pack_marker(2)));
        assert_contents(&buffer, "abxxyyzzfg");
        Ok(())
    }

    #[test]
    fn replace_with_more_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, CharBuffer>::from_input(smallvec!["a", "bc", "de", "f"])?;
        let range = buffer.replace(
            Some(&(1, pack_marker(1)))..Some(&(2, pack_marker(1))),
            smallvec!["xx", "yy", "zz"],
        )?;
        assert_eq!(range, (1, pack_marker(1))..(3, pack_marker(2)));
        assert_contents(&buffer, "abxxyyzzef");
        Ok(())
    }

    #[test]
    fn replace_in_nested_chunks() -> Result<(), Message> {
        let mut buffer =
            ChunkedEventBuffer::<u8, ChunkedEventBuffer<u8, CharBuffer>>::from_input(smallvec![
                smallvec!["a", "bc"],
                smallvec!["d"],
                smallvec!["ef", "g"]
            ])?;
        let range = buffer.replace(
            Some(&(0, (1, pack_marker(1))))..Some(&(2, (0, pack_marker(1)))),
            smallvec![smallvec!["xx", "yy"], smallvec!["zz"]],
        )?;
        assert_eq!(range, (0, (1, pack_marker(1)))..(1, (0, pack_marker(2))));
        assert_contents(&buffer, "abxxyyzzfg");
        Ok(())
    }

    fn assert_contents<'a>(buffer: &impl CharEventBuffer<'a>, contents: &str) {
        let mut iter = contents.chars();
        buffer.for_each(|c, _| assert_eq!(Some(c), iter.next()));
        assert_eq!(None, iter.next());
    }
}
