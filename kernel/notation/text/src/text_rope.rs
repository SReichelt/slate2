//! This file provides the `TextRope` type implementing a configurable text rope, with three
//! distinguishing features:
//!
//! * There is no concept of lines and columns; clients can freely decide how to split strings. In
//!   particular, this facilitates adhering to the line ending rules of the language server protocol
//!   (LSP) without having to encode these rules in the text rope implementation.
//!   (In contrast, it seems that other text rope crates are currently not fully LSP-compatible.)
//!
//! * Chunks can be nested, so a client can decide to add further chunking to lines and/or columns,
//!   resulting in positions with more than two fields. This can help keep encoded positions stable
//!   when lines are inserted or removed.
//!
//! * The client can specify an arbitrary number of typed "overlays" consisting of items that are
//!   located at a "managed" position in the text.
//!
//! We currently don't optimize for extreme performance. In fact, operations that insert or remove
//! chunks have a linear runtime (unless operations are guaranteed to happen at or near the end).
//! Clients are expected to mitigate this using nested chunks (keeping the number of chunks bounded
//! at each level).
//!
//! However, limitations on the number of chunks (and, in theory, on the text length within a single
//! chunk) can cause operations to fail (including removal, if at least one chunk boundary is
//! involved). Handling such errors, e.g. by re-balancing the text rope, is the responsibility of
//! the client, as every solution necessarily affects encoded positions.

use std::{
    fmt::Debug,
    iter::empty,
    ops::{Add, AddAssign, Range, Sub, SubAssign},
    slice::Iter,
    str::CharIndices,
};

use nonminmax::NonMaxU32;
use smallvec::SmallVec;
use thiserror::Error;

use crate::{text_rope::storage::*, tree_shape::*, type_list::*, type_list_trait};

pub trait TextRopeShape: TreeShape {
    type Storage<Overlays: TextRopeOverlays>: TextRopeStorage<Self>;
    type Position: Copy + PartialOrd + Default;
    type Input<'a>: TextRopeInput<'a, Self>;
}

impl TextRopeShape for type_list![] {
    type Storage<Overlays: TextRopeOverlays> =
        Overlays::MatchTextRopeOverlayStorage<OverlayStorageConstructor>;
    type Position = LeafPosition;
    type Input<'a> = &'a str;
}

impl<ChunkIdx: LimitedIndex, Chunk: TextRopeShape> TextRopeShape for type_list![ChunkIdx, ..Chunk] {
    type Storage<Overlays: TextRopeOverlays> = ChunkedStorage<Chunk, Overlays>;
    type Position = (ChunkIdx, Chunk::Position);
    type Input<'a> = ChunkVec<Chunk::Input<'a>>;
}

type_list_trait!((TextRopeOverlays: SizedTypeList + 'static) (: TextRopeOverlayItem) [
    (MatchTextRopeOverlayStorage: TextRopeStorage<type_list![]>),
]);

#[derive(Debug)]
pub struct TextRope<Shape: TextRopeShape, Overlays: TextRopeOverlays>(Shape::Storage<Overlays>);

impl<Shape: TextRopeShape, Overlays: TextRopeOverlays> TextRope<Shape, Overlays> {
    pub fn new() -> Self {
        TextRope(Shape::Storage::default())
    }

    pub fn from_input(input: Shape::Input<'_>) -> Result<Self, TextRopeInputError> {
        let storage = Shape::Storage::from_input(input)?;
        Ok(TextRope(storage))
    }

    pub fn replace(
        &mut self,
        range: Range<Option<Shape::Position>>,
        input: Shape::Input<'_>,
    ) -> Result<Range<Shape::Position>, TextRopeInputError> {
        self.0.replace(range, input)
    }

    pub fn insert(
        &mut self,
        pos: Shape::Position,
        input: Shape::Input<'_>,
    ) -> Result<Range<Shape::Position>, TextRopeInputError> {
        self.0.insert(pos, input)
    }

    pub fn remove(
        &mut self,
        range: Range<Option<Shape::Position>>,
    ) -> Result<Shape::Position, TextRopeInputError> {
        self.0.remove(range)
    }

    pub fn range_iter(
        &self,
        range: Range<Option<Shape::Position>>,
    ) -> <Shape::Storage<Overlays> as TextRopeStorage<Shape>>::Iter<'_> {
        self.0.range_iter(range)
    }

    pub fn total_chunk_count(&self) -> usize {
        self.0.total_chunk_count()
    }

    pub fn chunk_str(&self, total_chunk_idx: usize) -> TupleWith<Shape, &str> {
        self.0.chunk_str(total_chunk_idx)
    }
}

impl<Shape: TextRopeShape, Overlays: TextRopeOverlays> Default for TextRope<Shape, Overlays> {
    fn default() -> Self {
        Self(Shape::Storage::default())
    }
}

#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
pub struct LeafPosition(NonMaxU32);

impl LeafPosition {
    pub fn from_usize(idx: usize) -> Self {
        LeafPosition(NonMaxU32::new(idx.try_into().unwrap()).unwrap())
    }

    pub fn to_usize(position: Self) -> usize {
        position.0.get() as usize
    }

    fn max_idx() -> Self {
        LeafPosition(NonMaxU32::new(u32::MAX - 1).unwrap())
    }
}

impl Add for LeafPosition {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        // (Note that this is guaranteed to panic on overflow.)
        Self::from_usize(Self::to_usize(self) + Self::to_usize(rhs))
    }
}

impl AddAssign for LeafPosition {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for LeafPosition {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        // (Note that this is guaranteed to panic on overflow, though not always at the same place.)
        Self::from_usize(Self::to_usize(self) - Self::to_usize(rhs))
    }
}

impl SubAssign for LeafPosition {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Default for LeafPosition {
    fn default() -> Self {
        LeafPosition(NonMaxU32::new(0).unwrap())
    }
}

pub trait TextRopeInput<'a, Shape: TextRopeShape>: Sized + Default {
    fn balanced(chunks: &[&'a str]) -> Self;
}

impl<'a> TextRopeInput<'a, type_list![]> for &'a str {
    fn balanced(chunks: &[&'a str]) -> Self {
        if let &[text] = chunks {
            text
        } else {
            panic!("exactly one chunk expected")
        }
    }
}

impl<'a, ChunkIdx: LimitedIndex, Chunk: TextRopeShape>
    TextRopeInput<'a, type_list![ChunkIdx, ..Chunk]> for ChunkVec<Chunk::Input<'a>>
{
    fn balanced(chunks: &[&'a str]) -> Self {
        let total_chunk_count = chunks.len();
        if total_chunk_count == 0 {
            ChunkVec::new()
        } else {
            let chunk_count =
                (total_chunk_count - 1).min(<ChunkIdx as LimitedIndex>::max_idx()) + 1;
            let chunk_size = (total_chunk_count - 1) / chunk_count + 1;
            chunks
                .chunks(chunk_size)
                .map(Chunk::Input::balanced)
                .collect()
        }
    }
}

pub trait TextRopeIterator<'a, Shape: TextRopeShape>:
    Default + Iterator<Item = (Shape::Position, char)>
{
    fn next_slice(&mut self) -> Option<(Shape::Position, &'a str)>;

    fn next_position(&self) -> Shape::Position;
}

pub type ChunkVec<T> = SmallVec<[T; 1]>;

#[macro_export]
macro_rules! chunk_vec {
    [$($items:tt)*] => {
        smallvec::smallvec![$($items)*]
    };
}

pub trait TextRopeOverlayItem: Debug + 'static {
    fn overwrite(&mut self) -> OverlayItemOverwriteAction;
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum OverlayItemOverwriteAction {
    MoveToStart,
    MoveToEnd,
    Delete,
}

#[derive(Clone, Copy, PartialEq, Debug, Error)]
pub enum TextRopeInputError {
    #[error("input length of {len} exceeds than maximum of {max_len}")]
    InputTooLong { len: usize, max_len: usize },

    #[error("input chunk count of {chunk_count} exceeds maximum of {max_chunks}")]
    TooManyChunks {
        chunk_count: usize,
        max_chunks: usize,
    },
}

mod storage {
    use super::*;

    pub trait TextRopeStorage<Shape: TextRopeShape>: Default + Debug {
        type Iter<'a>: TextRopeIterator<'a, Shape>
        where
            Self: 'a;

        type ExtractedOverlays: Default;

        fn from_input(input: Shape::Input<'_>) -> Result<Self, TextRopeInputError> {
            let (text_rope, _) = Self::from_input_with_range(input)?;
            Ok(text_rope)
        }

        fn from_input_with_range(
            input: Shape::Input<'_>,
        ) -> Result<(Self, Range<Shape::Position>), TextRopeInputError> {
            let mut text_rope = Self::default();
            let range = text_rope.insert(Shape::Position::default(), input)?;
            Ok((text_rope, range))
        }

        fn to_input(&self, range: Range<Option<Shape::Position>>) -> Shape::Input<'_>;

        fn replace(
            &mut self,
            range: Range<Option<Shape::Position>>,
            input: Shape::Input<'_>,
        ) -> Result<Range<Shape::Position>, TextRopeInputError>;

        fn insert(
            &mut self,
            pos: Shape::Position,
            input: Shape::Input<'_>,
        ) -> Result<Range<Shape::Position>, TextRopeInputError> {
            self.replace(Some(pos)..Some(pos), input)
        }

        fn remove(
            &mut self,
            range: Range<Option<Shape::Position>>,
        ) -> Result<Shape::Position, TextRopeInputError> {
            self.replace(range, Shape::Input::default())
                .map(|range| range.start)
        }

        fn range_iter(&self, range: Range<Option<Shape::Position>>) -> Self::Iter<'_>;

        fn total_chunk_count(&self) -> usize;

        fn chunk_str(&self, total_chunk_idx: usize) -> TupleWith<Shape, &str>;

        fn extract_overlays(
            &mut self,
            range: Range<Option<Shape::Position>>,
            include_boundary: bool,
        ) -> Self::ExtractedOverlays;

        fn insert_extracted_overlays(
            &mut self,
            pos: Shape::Position,
            overlays: Self::ExtractedOverlays,
        );

        fn overwrite_extracted_overlays(
            overlays: Self::ExtractedOverlays,
            start_overlays: &mut Self::ExtractedOverlays,
            end_overlays: &mut Self::ExtractedOverlays,
        );
    }

    pub struct OverlayStorageConstructor;

    impl MatchTextRopeOverlayStorage for OverlayStorageConstructor {
        type MatchEmpty = LeafStorage;
        type MatchNonEmpty<Head: TextRopeOverlayItem, Tail: TextRopeStorage<type_list![]>> =
            WithOverlay<Tail, Head>;
    }

    #[derive(Default, Debug)]
    pub struct LeafStorage(String);

    impl LeafStorage {
        fn get_range(&self, range: Range<Option<LeafPosition>>) -> Range<usize> {
            let start = range.start.map(LeafPosition::to_usize).unwrap_or(0);
            let end = range
                .end
                .map(LeafPosition::to_usize)
                .unwrap_or_else(|| self.0.len());
            start..end
        }
    }

    impl TextRopeStorage<type_list![]> for LeafStorage {
        type Iter<'a> = LeafIter<'a>;

        type ExtractedOverlays = ();

        fn to_input(&self, range: Range<Option<LeafPosition>>) -> &str {
            &self.0[self.get_range(range)]
        }

        fn replace(
            &mut self,
            range: Range<Option<LeafPosition>>,
            input: &str,
        ) -> Result<Range<LeafPosition>, TextRopeInputError> {
            let range = self.get_range(range);
            let len = self.0.len() - (range.end - range.start) + input.len();
            let max_len = LeafPosition::to_usize(LeafPosition::max_idx());
            if len > max_len {
                return Err(TextRopeInputError::InputTooLong { len, max_len });
            }
            let start = range.start;
            self.0.replace_range(range, input);
            Ok(LeafPosition::from_usize(start)..LeafPosition::from_usize(start + input.len()))
        }

        fn range_iter(&self, range: Range<Option<LeafPosition>>) -> LeafIter {
            let range = self.get_range(range);
            let start = range.start;
            LeafIter {
                iter: self.0[range].char_indices(),
                start,
            }
        }

        fn total_chunk_count(&self) -> usize {
            1
        }

        fn chunk_str(&self, total_chunk_idx: usize) -> &str {
            assert_eq!(total_chunk_idx, 0);
            &self.0
        }

        fn extract_overlays(
            &mut self,
            _range: Range<Option<LeafPosition>>,
            _include_boundary: bool,
        ) -> Self::ExtractedOverlays {
            ()
        }

        fn insert_extracted_overlays(
            &mut self,
            _pos: LeafPosition,
            _overlays: Self::ExtractedOverlays,
        ) {
        }

        fn overwrite_extracted_overlays(
            _overlays: Self::ExtractedOverlays,
            _start_overlays: &mut Self::ExtractedOverlays,
            _end_overlays: &mut Self::ExtractedOverlays,
        ) {
        }
    }

    pub struct LeafIter<'a> {
        iter: CharIndices<'a>,
        start: usize,
    }

    impl<'a> Default for LeafIter<'a> {
        fn default() -> Self {
            Self {
                iter: "".char_indices(),
                start: 0,
            }
        }
    }

    impl<'a> Iterator for LeafIter<'a> {
        type Item = (LeafPosition, char);

        fn next(&mut self) -> Option<Self::Item> {
            let (idx, c) = self.iter.next()?;
            Some((LeafPosition::from_usize(idx), c))
        }
    }

    impl<'a> TextRopeIterator<'a, type_list![]> for LeafIter<'a> {
        fn next_slice(&mut self) -> Option<(LeafPosition, &'a str)> {
            let chunk = self.iter.as_str();
            if chunk.is_empty() {
                return None;
            }
            let position = self.next_position();
            self.iter = "".char_indices();
            self.start += chunk.len();
            Some((position, chunk))
        }

        fn next_position(&self) -> LeafPosition {
            LeafPosition::from_usize(self.start + self.iter.offset())
        }
    }

    #[derive(Clone, Debug)]
    pub struct ChunkedStorage<Chunk: TextRopeShape, Overlays: TextRopeOverlays> {
        chunks: ChunkVec<Chunk::Storage<Overlays>>,
        total_chunk_count: usize,
    }

    impl<Chunk: TextRopeShape, Overlays: TextRopeOverlays> ChunkedStorage<Chunk, Overlays> {
        pub fn new() -> Self {
            ChunkedStorage {
                chunks: ChunkVec::new(),
                total_chunk_count: 0,
            }
        }

        pub fn chunk_count(&self) -> usize {
            self.chunks.len()
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

        fn get_range<ChunkIdx: LimitedIndex>(
            &self,
            range: Range<Option<(ChunkIdx, Chunk::Position)>>,
        ) -> Range<(usize, Option<Chunk::Position>)> {
            let start = if let Some(start) = range.start {
                (LimitedIndex::to_usize(start.0), Some(start.1))
            } else {
                (0, None)
            };
            let end = if let Some(end) = range.end {
                (LimitedIndex::to_usize(end.0), Some(end.1))
            } else {
                (self.max_chunk_idx(), None)
            };
            start..end
        }

        fn remove_chunks(
            &mut self,
            start_idx: usize,
            count: usize,
            start_overlays: &mut <Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::ExtractedOverlays,
            end_overlays: &mut <Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::ExtractedOverlays,
        ) {
            if count > 0 {
                for chunk in &mut self.chunks[start_idx..(start_idx + count)] {
                    self.total_chunk_count -= chunk.total_chunk_count();
                    let extracted_overlays = chunk.extract_overlays(None..None, true);
                    Chunk::Storage::overwrite_extracted_overlays(
                        extracted_overlays,
                        start_overlays,
                        end_overlays,
                    );
                }
                let new_len = self.chunks.len() - count;
                for idx in start_idx..new_len {
                    self.chunks.swap(idx, idx + count);
                }
                self.chunks.truncate(new_len);
            }
        }

        fn replace_chunks(
            &mut self,
            start_idx: usize,
            count: usize,
            chunks: ChunkVec<Chunk::Storage<Overlays>>,
            start_overlays: &mut <Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::ExtractedOverlays,
            end_overlays: &mut <Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::ExtractedOverlays,
        ) {
            let mut idx = start_idx;
            let mut remaining_count = count;
            for chunk in chunks {
                self.total_chunk_count += chunk.total_chunk_count();
                if remaining_count > 0 {
                    let chunk_to_replace = &mut self.chunks[idx];
                    self.total_chunk_count -= chunk_to_replace.total_chunk_count();
                    let extracted_overlays = chunk_to_replace.extract_overlays(None..None, true);
                    Chunk::Storage::overwrite_extracted_overlays(
                        extracted_overlays,
                        start_overlays,
                        end_overlays,
                    );
                    *chunk_to_replace = chunk;
                    remaining_count -= 1;
                } else {
                    self.chunks.insert(idx, chunk);
                }
                idx += 1;
            }
            self.remove_chunks(idx, remaining_count, start_overlays, end_overlays);
        }
    }

    impl<Chunk: TextRopeShape, Overlays: TextRopeOverlays> Default for ChunkedStorage<Chunk, Overlays> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<ChunkIdx: LimitedIndex, Chunk: TextRopeShape, Overlays: TextRopeOverlays>
        TextRopeStorage<type_list![ChunkIdx, ..Chunk]> for ChunkedStorage<Chunk, Overlays>
    {
        type Iter<'a> = ChunkedIter<'a, ChunkIdx, Chunk, Overlays>
        where
            Self: 'a;

        type ExtractedOverlays =
            ChunkVec<<Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::ExtractedOverlays>;

        fn to_input(
            &self,
            range: Range<Option<(ChunkIdx, Chunk::Position)>>,
        ) -> ChunkVec<Chunk::Input<'_>> {
            if self.chunks.is_empty() {
                ChunkVec::new()
            } else {
                let range = self.get_range(range);
                let mut result = ChunkVec::with_capacity(range.end.0 - range.start.0 + 1);
                let mut cur_start_pos = range.start.1;
                for chunk_idx in range.start.0..range.end.0 {
                    result.push(self.chunks[chunk_idx].to_input(cur_start_pos..None));
                    cur_start_pos = None;
                }
                result.push(self.chunks[range.end.0].to_input(cur_start_pos..range.end.1));
                result
            }
        }

        fn replace(
            &mut self,
            range: Range<Option<(ChunkIdx, Chunk::Position)>>,
            mut input: ChunkVec<Chunk::Input<'_>>,
        ) -> Result<Range<(ChunkIdx, Chunk::Position)>, TextRopeInputError> {
            let range = self.get_range(range);
            let removed_chunks = range.end.0 - range.start.0;
            let inserted_chunks = Self::inserted_chunks(&input);
            let max_chunk_idx = self.max_chunk_idx() - removed_chunks + inserted_chunks;
            let max_chunks = ChunkIdx::max_idx();
            if max_chunk_idx >= max_chunks {
                return Err(TextRopeInputError::TooManyChunks {
                    chunk_count: max_chunk_idx + 1,
                    max_chunks,
                });
            }

            let mut result_range: Range<(ChunkIdx, Chunk::Position)>;

            if self.chunks.is_empty() {
                result_range = Default::default()..Default::default();
                let mut chunks = ChunkVec::with_capacity(input.len());
                let mut total_chunk_count = 0;
                for chunk_input in input {
                    let (chunk, chunk_range) = Chunk::Storage::from_input_with_range(chunk_input)?;
                    total_chunk_count += chunk.total_chunk_count();
                    result_range.end = (ChunkIdx::from_usize(chunks.len()), chunk_range.end);
                    chunks.push(chunk);
                }
                self.chunks = chunks;
                self.total_chunk_count = total_chunk_count;
            } else if inserted_chunks == 0 {
                // `input` has one chunk, which we need to insert "inline" (or none, which is treated as
                // an empty chunk).
                let result_chunk_idx = ChunkIdx::from_usize(range.start.0);
                let chunk_input = input.pop().unwrap_or_default();
                let start_chunk_orig_chunks = self.chunks[range.start.0].total_chunk_count();
                let input_range: Range<Chunk::Position>;
                if removed_chunks > 0 {
                    let mut start_overlays = Default::default();
                    let mut end_overlays = Default::default();
                    let start_chunk_overwritten_overlays:
                    <Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::ExtractedOverlays;
                    if range.end.1.is_some() {
                        // Removal spans a chunk boundary. Potentially insert single-chunk content at
                        // `range.start`, and move rest of chunk after `range.end` to the end of the
                        // inserted content.
                        let (chunks_before_end, chunks_after_end) =
                            self.chunks.as_mut_slice().split_at_mut(range.end.0);
                        let start_chunk = &mut chunks_before_end[range.start.0];
                        let end_chunk = &mut chunks_after_end[0];
                        input_range =
                            start_chunk.insert(range.start.1.unwrap_or_default(), chunk_input)?;
                        start_chunk_overwritten_overlays =
                            start_chunk.extract_overlays(Some(input_range.end)..None, false);
                        let to_append = end_chunk.to_input(range.end.1..None);
                        if let Err(err) =
                            start_chunk.replace(Some(input_range.end)..None, to_append)
                        {
                            start_chunk.insert_extracted_overlays(
                                input_range.end,
                                start_chunk_overwritten_overlays,
                            );
                            start_chunk
                                .remove(Some(input_range.start)..Some(input_range.end))
                                .unwrap();
                            return Err(err);
                        }
                        let overlays_after_end =
                            end_chunk.extract_overlays(range.end.1..None, true);
                        let start_chunk = &mut self.chunks[range.start.0];
                        start_chunk.insert_extracted_overlays(input_range.end, overlays_after_end);
                    } else {
                        // The removal extends to the end of a chunk, so we don't need to deal with the
                        // rest of that chunk.
                        let start_chunk = &mut self.chunks[range.start.0];
                        start_chunk_overwritten_overlays =
                            start_chunk.extract_overlays(range.start.1..None, false);
                        input_range = match start_chunk.replace(range.start.1..None, chunk_input) {
                            Ok(range) => range,
                            Err(err) => {
                                start_chunk.insert_extracted_overlays(
                                    range.start.1.unwrap_or_default(),
                                    start_chunk_overwritten_overlays,
                                );
                                return Err(err);
                            }
                        };
                    }
                    Chunk::Storage::overwrite_extracted_overlays(
                        start_chunk_overwritten_overlays,
                        &mut start_overlays,
                        &mut end_overlays,
                    );
                    self.remove_chunks(
                        range.start.0 + 1,
                        removed_chunks,
                        &mut start_overlays,
                        &mut end_overlays,
                    );
                    self.chunks[range.start.0]
                        .insert_extracted_overlays(input_range.start, start_overlays);
                    self.chunks[range.start.0]
                        .insert_extracted_overlays(input_range.end, end_overlays);
                } else {
                    // We neither insert nor remove chunks, so we can just forward the operation to a
                    // single chunk.
                    let chunk = &mut self.chunks[range.start.0];
                    input_range = chunk.replace(range.start.1..range.end.1, chunk_input)?;
                }
                self.total_chunk_count -= start_chunk_orig_chunks;
                self.total_chunk_count += self.chunks[range.start.0].total_chunk_count();
                result_range = (result_chunk_idx.clone(), input_range.start)
                    ..(result_chunk_idx, input_range.end);
            } else {
                // `input` has more than one chunk, so insertion is not "inline".
                // We need to replace part of the chunk at `range.start.0`, and then potentially entire
                // chunks from `range.start.0 + 1` to `range.end.0` (inclusive). To preserve the rest of
                // the chunk after `range.end.1`, we move it to the last inserted chunk.
                let (mut last_chunk_to_insert, last_chunk_range) =
                    Chunk::Storage::from_input_with_range(input.pop().unwrap())?;
                debug_assert_eq!(input.len(), inserted_chunks);
                let mut chunks_to_insert = ChunkVec::with_capacity(inserted_chunks);
                let mut input_iter = input.into_iter();
                let first_chunk_input = input_iter.next().unwrap();
                for chunk_input in input_iter {
                    chunks_to_insert.push(Chunk::Storage::from_input(chunk_input)?);
                }
                let mut overlays_after_end = None;
                if range.end.1.is_some() {
                    let to_append = self.chunks[range.end.0].to_input(range.end.1..None);
                    last_chunk_to_insert.insert(last_chunk_range.end, to_append)?;
                    overlays_after_end =
                        Some(self.chunks[range.end.0].extract_overlays(range.end.1..None, true));
                }
                let start_chunk = &mut self.chunks[range.start.0];
                let start_chunk_orig_chunks = start_chunk.total_chunk_count();
                let start_chunk_overwritten_overlays =
                    start_chunk.extract_overlays(range.start.1..None, false);
                let first_chunk_input_range =
                    match start_chunk.replace(range.start.1..None, first_chunk_input) {
                        Ok(range) => range,
                        Err(err) => {
                            start_chunk.insert_extracted_overlays(
                                range.start.1.unwrap_or_default(),
                                start_chunk_overwritten_overlays,
                            );
                            if let Some(overlays_after_end) = overlays_after_end {
                                self.chunks[range.end.0].insert_extracted_overlays(
                                    range.end.1.unwrap(),
                                    overlays_after_end,
                                );
                            }
                            return Err(err);
                        }
                    };
                self.total_chunk_count -= start_chunk_orig_chunks;
                self.total_chunk_count += start_chunk.total_chunk_count();
                let mut start_overlays = Default::default();
                let mut end_overlays = Default::default();
                Chunk::Storage::overwrite_extracted_overlays(
                    start_chunk_overwritten_overlays,
                    &mut start_overlays,
                    &mut end_overlays,
                );
                if let Some(overlays_after_end) = overlays_after_end {
                    last_chunk_to_insert
                        .insert_extracted_overlays(last_chunk_range.end, overlays_after_end);
                }
                chunks_to_insert.push(last_chunk_to_insert);
                if inserted_chunks > removed_chunks {
                    self.chunks.reserve(inserted_chunks - removed_chunks);
                }
                self.replace_chunks(
                    range.start.0 + 1,
                    removed_chunks,
                    chunks_to_insert,
                    &mut start_overlays,
                    &mut end_overlays,
                );
                self.chunks[range.start.0]
                    .insert_extracted_overlays(first_chunk_input_range.start, start_overlays);
                self.chunks[range.start.0 + inserted_chunks]
                    .insert_extracted_overlays(last_chunk_range.end, end_overlays);
                let result_start_chunk_idx = ChunkIdx::from_usize(range.start.0);
                let result_end_chunk_idx = ChunkIdx::from_usize(range.start.0 + inserted_chunks);
                result_range = (result_start_chunk_idx, first_chunk_input_range.start)
                    ..(result_end_chunk_idx, last_chunk_range.end);
            }

            debug_assert_eq!(self.max_chunk_idx(), max_chunk_idx);

            Ok(result_range)
        }

        fn range_iter(
            &self,
            range: Range<Option<(ChunkIdx, Chunk::Position)>>,
        ) -> ChunkedIter<ChunkIdx, Chunk, Overlays> {
            let range = self.get_range(range);
            let chunk_range_end = range.end.0 + 1;
            let mut chunk_iter = if chunk_range_end < self.chunks.len() {
                self.chunks[range.start.0..chunk_range_end].iter()
            } else {
                self.chunks[range.start.0..].iter()
            };
            let chunk = chunk_iter.next();
            let inner_iter = if let Some(chunk) = chunk {
                let inner_range_end = if range.start.0 == range.end.0 {
                    range.end.1
                } else {
                    None
                };
                chunk.range_iter(range.start.1..inner_range_end)
            } else {
                Default::default()
            };
            ChunkedIter {
                chunk_iter,
                chunk_idx: ChunkIdx::from_usize(range.start.0),
                end_chunk_idx: ChunkIdx::from_usize(range.end.0),
                inner_iter,
                end_pos: range.end.1,
            }
        }

        fn total_chunk_count(&self) -> usize {
            self.total_chunk_count
        }

        fn chunk_str(&self, mut total_chunk_idx: usize) -> (ChunkIdx, TupleWith<Chunk, &str>) {
            for (chunk_idx, chunk) in self.chunks.iter().enumerate() {
                let chunk_count = chunk.total_chunk_count();
                if total_chunk_idx < chunk_count {
                    return (
                        ChunkIdx::from_usize(chunk_idx),
                        chunk.chunk_str(total_chunk_idx),
                    );
                }
                total_chunk_idx -= chunk_count;
            }
            panic!("invalid chunk index");
        }

        fn extract_overlays(
            &mut self,
            range: Range<Option<(ChunkIdx, Chunk::Position)>>,
            include_boundary: bool,
        ) -> Self::ExtractedOverlays {
            if self.chunks.is_empty() {
                ChunkVec::new()
            } else {
                let range = self.get_range(range);
                let mut result = ChunkVec::with_capacity(range.end.0 - range.start.0 + 1);
                let mut cur_start_pos = range.start.1;
                for chunk_idx in range.start.0..range.end.0 {
                    result.push(
                        self.chunks[chunk_idx]
                            .extract_overlays(cur_start_pos..None, include_boundary),
                    );
                    cur_start_pos = None;
                }
                result.push(
                    self.chunks[range.end.0]
                        .extract_overlays(cur_start_pos..range.end.1, include_boundary),
                );
                result
            }
        }

        fn insert_extracted_overlays(
            &mut self,
            pos: (ChunkIdx, Chunk::Position),
            overlays: Self::ExtractedOverlays,
        ) {
            if self.chunks.is_empty() {
                self.chunks.push(Default::default());
            }

            let mut chunk_idx = LimitedIndex::to_usize(pos.0);
            let mut cur_start_pos = pos.1;
            for chunk_overlays in overlays {
                self.chunks[chunk_idx].insert_extracted_overlays(cur_start_pos, chunk_overlays);
                chunk_idx += 1;
                cur_start_pos = Default::default();
            }
        }

        fn overwrite_extracted_overlays(
            overlays: Self::ExtractedOverlays,
            start_overlays: &mut Self::ExtractedOverlays,
            end_overlays: &mut Self::ExtractedOverlays,
        ) {
            if overlays.is_empty() {
                return;
            }
            if start_overlays.is_empty() {
                start_overlays.push(Default::default());
            }
            let start_overlays = start_overlays.first_mut().unwrap();
            if end_overlays.is_empty() {
                end_overlays.push(Default::default());
            }
            let end_overlays = end_overlays.first_mut().unwrap();
            for chunk_overlays in overlays {
                Chunk::Storage::overwrite_extracted_overlays(
                    chunk_overlays,
                    start_overlays,
                    end_overlays,
                );
            }
        }
    }

    pub struct ChunkedIter<
        'a,
        ChunkIdx: LimitedIndex,
        Chunk: TextRopeShape,
        Overlays: TextRopeOverlays,
    > {
        chunk_iter: Iter<'a, Chunk::Storage<Overlays>>,
        chunk_idx: ChunkIdx,
        end_chunk_idx: ChunkIdx,
        inner_iter: <Chunk::Storage<Overlays> as TextRopeStorage<Chunk>>::Iter<'a>,
        end_pos: Option<Chunk::Position>,
    }

    impl<'a, ChunkIdx: LimitedIndex, Chunk: TextRopeShape, Overlays: TextRopeOverlays>
        ChunkedIter<'a, ChunkIdx, Chunk, Overlays>
    {
        fn advance_chunk_iter(&mut self) -> Option<()> {
            let next_chunk = self.chunk_iter.next()?;
            self.chunk_idx += ChunkIdx::from_usize(1);
            let inner_range_end = if self.chunk_idx == self.end_chunk_idx {
                self.end_pos
            } else {
                None
            };
            self.inner_iter = next_chunk.range_iter(None..inner_range_end);
            Some(())
        }
    }

    impl<'a, ChunkIdx: LimitedIndex, Chunk: TextRopeShape, Overlays: TextRopeOverlays> Default
        for ChunkedIter<'a, ChunkIdx, Chunk, Overlays>
    {
        fn default() -> Self {
            Self {
                chunk_iter: Default::default(),
                chunk_idx: Default::default(),
                end_chunk_idx: Default::default(),
                inner_iter: Default::default(),
                end_pos: None,
            }
        }
    }

    impl<'a, ChunkIdx: LimitedIndex, Chunk: TextRopeShape, Overlays: TextRopeOverlays> Iterator
        for ChunkedIter<'a, ChunkIdx, Chunk, Overlays>
    {
        type Item = ((ChunkIdx, Chunk::Position), char);

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some((pos, c)) = self.inner_iter.next() {
                    return Some(((self.chunk_idx, pos), c));
                }
                self.advance_chunk_iter()?;
            }
        }
    }

    impl<'a, ChunkIdx: LimitedIndex, Chunk: TextRopeShape, Overlays: TextRopeOverlays>
        TextRopeIterator<'a, type_list![ChunkIdx, ..Chunk]>
        for ChunkedIter<'a, ChunkIdx, Chunk, Overlays>
    {
        fn next_slice(&mut self) -> Option<((ChunkIdx, Chunk::Position), &'a str)> {
            loop {
                if let Some((pos, s)) = self.inner_iter.next_slice() {
                    return Some(((self.chunk_idx, pos), s));
                }
                self.advance_chunk_iter()?;
            }
        }

        fn next_position(&self) -> (ChunkIdx, Chunk::Position) {
            (self.chunk_idx, self.inner_iter.next_position())
        }
    }

    #[derive(Debug)]
    pub struct WithOverlay<Inner, Item: TextRopeOverlayItem> {
        inner: Inner,
        overlay_items: Vec<(LeafPosition, Item)>,
    }

    impl<Inner, Item: TextRopeOverlayItem> WithOverlay<Inner, Item> {
        fn next_item_idx(&self, pos: LeafPosition, include_pos: bool) -> usize {
            self.overlay_items.partition_point(|entry| {
                if include_pos {
                    entry.0 < pos
                } else {
                    entry.0 <= pos
                }
            })
        }

        fn item_idx_range(
            &self,
            range: Range<Option<LeafPosition>>,
            include_boundary: bool,
        ) -> Range<usize> {
            let start_idx = if let Some(start_pos) = range.start {
                self.next_item_idx(start_pos, include_boundary)
            } else {
                0
            };
            let end_idx = if let Some(end_pos) = range.end {
                self.next_item_idx(end_pos, !include_boundary)
            } else {
                self.overlay_items.len()
            };
            start_idx..end_idx
        }

        fn adjust_overlays(
            &mut self,
            overwritten_range: Range<Option<LeafPosition>>,
            input_len: usize,
        ) {
            let start_pos = overwritten_range.start.unwrap_or_default();
            let new_end_pos = start_pos + LeafPosition::from_usize(input_len);

            for item_idx in (0..self.overlay_items.len()).rev() {
                let (pos, item) = &mut self.overlay_items[item_idx];
                if let Some(old_end_pos) = overwritten_range.end {
                    if *pos >= old_end_pos {
                        *pos -= old_end_pos;
                        *pos += new_end_pos;
                        continue;
                    }
                }

                if *pos <= start_pos {
                    break;
                }

                match item.overwrite() {
                    OverlayItemOverwriteAction::MoveToStart => {
                        *pos = start_pos;
                    }
                    OverlayItemOverwriteAction::MoveToEnd => {
                        *pos = new_end_pos;
                    }
                    OverlayItemOverwriteAction::Delete => {
                        self.overlay_items.remove(item_idx);
                    }
                }
            }
        }
    }

    impl<Inner: Default, Item: TextRopeOverlayItem> Default for WithOverlay<Inner, Item> {
        fn default() -> Self {
            Self {
                inner: Default::default(),
                overlay_items: Default::default(),
            }
        }
    }

    impl<Inner: TextRopeStorage<type_list![]>, Item: TextRopeOverlayItem>
        TextRopeStorage<type_list![]> for WithOverlay<Inner, Item>
    {
        type Iter<'a> = Inner::Iter<'a>
        where
            Self: 'a;

        type ExtractedOverlays = WithOverlay<Inner::ExtractedOverlays, Item>;

        fn to_input(&self, range: Range<Option<LeafPosition>>) -> &str {
            self.inner.to_input(range)
        }

        fn replace(
            &mut self,
            range: Range<Option<LeafPosition>>,
            input: &str,
        ) -> Result<Range<LeafPosition>, TextRopeInputError> {
            let result = self.inner.replace(range.clone(), input)?;
            self.adjust_overlays(range, input.len());
            Ok(result)
        }

        fn range_iter(&self, range: Range<Option<LeafPosition>>) -> Self::Iter<'_> {
            self.inner.range_iter(range)
        }

        fn total_chunk_count(&self) -> usize {
            self.inner.total_chunk_count()
        }

        fn chunk_str(&self, total_chunk_idx: usize) -> &str {
            self.inner.chunk_str(total_chunk_idx)
        }

        fn extract_overlays(
            &mut self,
            range: Range<Option<LeafPosition>>,
            include_boundary: bool,
        ) -> Self::ExtractedOverlays {
            let item_range = self.item_idx_range(range.clone(), include_boundary);
            let mut extracted_items: Vec<(LeafPosition, Item)> =
                self.overlay_items.splice(item_range, empty()).collect();
            if let Some(pos) = range.start {
                for item in &mut extracted_items {
                    item.0 -= pos;
                }
            }
            WithOverlay {
                inner: self.inner.extract_overlays(range, include_boundary),
                overlay_items: extracted_items,
            }
        }

        fn insert_extracted_overlays(
            &mut self,
            pos: LeafPosition,
            mut overlays: Self::ExtractedOverlays,
        ) {
            for item in &mut overlays.overlay_items {
                item.0 += pos;
            }
            let item_idx = self.next_item_idx(pos, false);
            self.overlay_items
                .splice(item_idx..item_idx, overlays.overlay_items)
                .last();
            self.inner.insert_extracted_overlays(pos, overlays.inner);
        }

        fn overwrite_extracted_overlays(
            overlays: Self::ExtractedOverlays,
            start_overlays: &mut Self::ExtractedOverlays,
            end_overlays: &mut Self::ExtractedOverlays,
        ) {
            for (_, mut item) in overlays.overlay_items {
                match item.overwrite() {
                    OverlayItemOverwriteAction::MoveToStart => {
                        start_overlays
                            .overlay_items
                            .push((LeafPosition::default(), item));
                    }
                    OverlayItemOverwriteAction::MoveToEnd => {
                        end_overlays
                            .overlay_items
                            .push((LeafPosition::default(), item));
                    }
                    OverlayItemOverwriteAction::Delete => {}
                }
            }
            Inner::overwrite_extracted_overlays(
                overlays.inner,
                &mut start_overlays.inner,
                &mut end_overlays.inner,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct TestOverlayItem(OverlayItemOverwriteAction);

    impl TextRopeOverlayItem for TestOverlayItem {
        fn overwrite(&mut self) -> OverlayItemOverwriteAction {
            self.0
        }
    }

    type TextRope1 = TextRope<type_list![u8], type_list![TestOverlayItem, TestOverlayItem]>;
    type TextRope2 = TextRope<type_list![u8, u8], type_list![TestOverlayItem, TestOverlayItem]>;

    #[test]
    fn from_empty_input() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(ChunkVec::new())?;
        assert_contents(&text_rope, "");
        let pos = text_rope.remove(None..None)?;
        assert_eq!(pos, (0, LeafPosition::from_usize(0)));
        assert_contents(&text_rope, "");
        Ok(())
    }

    #[test]
    fn from_single_chunk() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["abc"])?;
        assert_contents(&text_rope, "abc");
        let pos = text_rope.remove(None..None)?;
        assert_eq!(pos, (0, LeafPosition::from_usize(0)));
        assert_contents(&text_rope, "");
        Ok(())
    }

    #[test]
    fn from_multiple_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "b", "c"])?;
        assert_contents(&text_rope, "abc");
        let pos = text_rope.remove(None..None)?;
        assert_eq!(pos, (0, LeafPosition::from_usize(0)));
        assert_contents(&text_rope, "");
        Ok(())
    }

    #[test]
    fn remove_nothing() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "d"])?;
        let pos = text_rope.remove(
            Some((1, LeafPosition::from_usize(1)))..Some((1, LeafPosition::from_usize(1))),
        )?;
        assert_eq!(pos, (1, LeafPosition::from_usize(1)));
        assert_contents(&text_rope, "abcd");
        Ok(())
    }

    #[test]
    fn remove_within_chunk() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bcd", "e"])?;
        let pos = text_rope.remove(
            Some((1, LeafPosition::from_usize(1)))..Some((1, LeafPosition::from_usize(2))),
        )?;
        assert_eq!(pos, (1, LeafPosition::from_usize(1)));
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abde");
        Ok(())
    }

    #[test]
    fn remove_across_two_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "de", "f"])?;
        let pos = text_rope.remove(
            Some((1, LeafPosition::from_usize(1)))..Some((2, LeafPosition::from_usize(1))),
        )?;
        assert_eq!(pos, (1, LeafPosition::from_usize(1)));
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abef");
        Ok(())
    }

    #[test]
    fn remove_across_three_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["ab", "c", "de", "f"])?;
        let pos = text_rope.remove(
            Some((0, LeafPosition::from_usize(1)))..Some((2, LeafPosition::from_usize(1))),
        )?;
        assert_eq!(pos, (0, LeafPosition::from_usize(1)));
        assert_eq!(text_rope.total_chunk_count(), 2);
        assert_contents(&text_rope, "aef");
        Ok(())
    }

    #[test]
    fn insert_empty_input() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "d"])?;
        let range = text_rope.insert((1, LeafPosition::from_usize(1)), ChunkVec::new())?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(1, LeafPosition::from_usize(1))
        );
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abcd");
        Ok(())
    }

    #[test]
    fn insert_single_chunk() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "be", "f"])?;
        let range = text_rope.insert((1, LeafPosition::from_usize(1)), chunk_vec!["cd"])?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(1, LeafPosition::from_usize(3))
        );
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abcdef");
        Ok(())
    }

    #[test]
    fn insert_multiple_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bg", "h"])?;
        let range =
            text_rope.insert((1, LeafPosition::from_usize(1)), chunk_vec!["c", "d", "ef"])?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(3, LeafPosition::from_usize(2))
        );
        assert_eq!(text_rope.total_chunk_count(), 5);
        assert_contents(&text_rope, "abcdefgh");
        Ok(())
    }

    #[test]
    fn replace_within_chunk() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bcd", "e"])?;
        let range = text_rope.replace(
            Some((1, LeafPosition::from_usize(1)))..Some((1, LeafPosition::from_usize(2))),
            chunk_vec!["xyz"],
        )?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(1, LeafPosition::from_usize(4))
        );
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abxyzde");
        Ok(())
    }

    #[test]
    fn replace_additional_chunks_within_chunk() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bcd", "e"])?;
        let range = text_rope.replace(
            Some((1, LeafPosition::from_usize(1)))..Some((1, LeafPosition::from_usize(2))),
            chunk_vec!["x", "y", "z"],
        )?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(3, LeafPosition::from_usize(1))
        );
        assert_eq!(text_rope.total_chunk_count(), 5);
        assert_contents(&text_rope, "abxyzde");
        Ok(())
    }

    #[test]
    fn replace_with_single_chunk() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "d", "ef", "g"])?;
        let range = text_rope.replace(
            Some((1, LeafPosition::from_usize(1)))..Some((3, LeafPosition::from_usize(1))),
            chunk_vec!["xx"],
        )?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(1, LeafPosition::from_usize(3))
        );
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abxxfg");
        Ok(())
    }

    #[test]
    fn replace_with_fewer_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "d", "ef", "g"])?;
        let range = text_rope.replace(
            Some((1, LeafPosition::from_usize(1)))..Some((3, LeafPosition::from_usize(1))),
            chunk_vec!["xx", "yy"],
        )?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(2, LeafPosition::from_usize(2))
        );
        assert_eq!(text_rope.total_chunk_count(), 4);
        assert_contents(&text_rope, "abxxyyfg");
        Ok(())
    }

    #[test]
    fn replace_with_equal_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "d", "ef", "g"])?;
        let range = text_rope.replace(
            Some((1, LeafPosition::from_usize(1)))..Some((3, LeafPosition::from_usize(1))),
            chunk_vec!["xx", "yy", "zz"],
        )?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(3, LeafPosition::from_usize(2))
        );
        assert_eq!(text_rope.total_chunk_count(), 5);
        assert_contents(&text_rope, "abxxyyzzfg");
        Ok(())
    }

    #[test]
    fn replace_with_more_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope1::from_input(chunk_vec!["a", "bc", "de", "f"])?;
        let range = text_rope.replace(
            Some((1, LeafPosition::from_usize(1)))..Some((2, LeafPosition::from_usize(1))),
            chunk_vec!["xx", "yy", "zz"],
        )?;
        assert_eq!(
            range,
            (1, LeafPosition::from_usize(1))..(3, LeafPosition::from_usize(2))
        );
        assert_eq!(text_rope.total_chunk_count(), 5);
        assert_contents(&text_rope, "abxxyyzzef");
        Ok(())
    }

    #[test]
    fn remove_in_nested_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope2::from_input(chunk_vec![
            chunk_vec!["a", "bc"],
            chunk_vec!["d"],
            chunk_vec!["ef", "g"]
        ])?;
        assert_eq!(text_rope.total_chunk_count(), 5);
        assert_contents(&text_rope, "abcdefg");
        let pos = text_rope.remove(
            Some((0, (1, LeafPosition::from_usize(1))))
                ..Some((2, (0, LeafPosition::from_usize(1)))),
        )?;
        assert_eq!(pos, (0, (1, LeafPosition::from_usize(1))));
        assert_eq!(text_rope.total_chunk_count(), 3);
        assert_contents(&text_rope, "abfg");
        Ok(())
    }

    #[test]
    fn insert_in_nested_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope2::from_input(chunk_vec![
            chunk_vec!["a", "bc"],
            chunk_vec!["d"],
            chunk_vec!["ef", "g"]
        ])?;
        assert_eq!(text_rope.total_chunk_count(), 5);
        let range = text_rope.insert(
            (0, (1, LeafPosition::from_usize(1))),
            chunk_vec![chunk_vec!["xx", "yy"], chunk_vec!["z", "zz", "zzz"]],
        )?;
        assert_eq!(
            range,
            (0, (1, LeafPosition::from_usize(1)))..(1, (2, LeafPosition::from_usize(3)))
        );
        assert_eq!(text_rope.total_chunk_count(), 9);
        assert_contents(&text_rope, "abxxyyzzzzzzcdefg");
        Ok(())
    }

    #[test]
    fn replace_in_nested_chunks() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope2::from_input(chunk_vec![
            chunk_vec!["a", "bc"],
            chunk_vec!["d"],
            chunk_vec!["ef", "g"]
        ])?;
        assert_eq!(text_rope.total_chunk_count(), 5);
        let range = text_rope.replace(
            Some((0, (1, LeafPosition::from_usize(1))))
                ..Some((2, (0, LeafPosition::from_usize(1)))),
            chunk_vec![chunk_vec!["xx", "yy"], chunk_vec!["z", "zz", "zzz"]],
        )?;
        assert_eq!(
            range,
            (0, (1, LeafPosition::from_usize(1)))..(1, (2, LeafPosition::from_usize(3)))
        );
        assert_eq!(text_rope.total_chunk_count(), 7);
        assert_contents(&text_rope, "abxxyyzzzzzzfg");
        Ok(())
    }

    #[test]
    fn removal_not_possible() -> Result<(), TextRopeInputError> {
        let mut text_rope = TextRope2::from_input(chunk_vec![
            chunk_vec!["a"; 200],
            chunk_vec!["b"],
            chunk_vec!["c"; 200]
        ])?;
        assert_eq!(text_rope.total_chunk_count(), 401);
        assert_content_length(&text_rope, 401);

        let result = text_rope.remove(
            Some((0, (199, LeafPosition::from_usize(1))))
                ..Some((2, (1, LeafPosition::from_usize(0)))),
        );
        assert_eq!(
            result,
            Err(TextRopeInputError::TooManyChunks {
                chunk_count: 398,
                max_chunks: 255
            })
        );
        assert_eq!(text_rope.total_chunk_count(), 401);
        assert_content_length(&text_rope, 401);

        let result = text_rope.replace(
            Some((0, (199, LeafPosition::from_usize(1))))
                ..Some((2, (1, LeafPosition::from_usize(0)))),
            chunk_vec![chunk_vec!["d", "e"]],
        );
        assert_eq!(
            result,
            Err(TextRopeInputError::TooManyChunks {
                chunk_count: 399,
                max_chunks: 255
            })
        );
        assert_eq!(text_rope.total_chunk_count(), 401);
        assert_content_length(&text_rope, 401);

        text_rope.replace(
            Some((0, (199, LeafPosition::from_usize(1))))
                ..Some((2, (1, LeafPosition::from_usize(0)))),
            chunk_vec![chunk_vec!["d", "e"], chunk_vec!["f", "g", "h"]],
        )?;
        assert_eq!(text_rope.total_chunk_count(), 402);
        assert_content_length(&text_rope, 404);

        Ok(())
    }

    fn assert_contents<Shape: TextRopeShape, Overlays: TextRopeOverlays>(
        text_rope: &TextRope<Shape, Overlays>,
        mut contents: &str,
    ) {
        let mut text_rope_iter = text_rope.range_iter(None..None);
        while let Some((_, s)) = text_rope_iter.next_slice() {
            let Some(rest) = contents.strip_prefix(s) else {
                panic!("expected {contents}, found {s}[...]")
            };
            contents = rest;
        }
        assert!(contents.is_empty(), "expected {contents}, found end");
    }

    fn assert_content_length<Shape: TextRopeShape, Overlays: TextRopeOverlays>(
        text_rope: &TextRope<Shape, Overlays>,
        mut len: usize,
    ) {
        let mut text_rope_iter = text_rope.range_iter(None..None);
        while let Some((_, s)) = text_rope_iter.next_slice() {
            assert!(
                len >= s.len(),
                "expected remaining length {len}, found {s}[...]"
            );
            len -= s.len();
        }
        assert!(len == 0, "expected remaining length {len}, found end");
    }

    #[test]
    fn small_balanced_input() {
        let input =
            <ChunkVec<ChunkVec<&str>> as TextRopeInput<type_list![u8, u8]>>::balanced(&["a"; 5]);
        assert_eq!(input.len(), 5);
        for chunk in input {
            assert_eq!(chunk.len(), 1);
        }
    }

    #[test]
    fn large_balanced_input() {
        let input =
            <ChunkVec<ChunkVec<&str>> as TextRopeInput<type_list![u8, u8]>>::balanced(&["a"; 1000]);
        assert_eq!(input.len(), 250);
        for chunk in input {
            assert_eq!(chunk.len(), 4);
        }
    }

    #[test]
    fn exact_balanced_input() {
        let input =
            <ChunkVec<ChunkVec<&str>> as TextRopeInput<type_list![u8, u8]>>::balanced(&["a"; 1024]);
        assert_eq!(input.len(), 256);
        for chunk in input {
            assert_eq!(chunk.len(), 4);
        }
    }

    #[test]
    fn almost_exact_balanced_input() {
        let input =
            <ChunkVec<ChunkVec<&str>> as TextRopeInput<type_list![u8, u8]>>::balanced(&["a"; 1025]);
        assert_eq!(input.len(), 205);
        for chunk in input {
            assert_eq!(chunk.len(), 5);
        }
    }
}
