use std::{
    collections::{vec_deque, VecDeque},
    iter::Take,
    mem::swap,
};

pub struct QueueSlice<'a, T> {
    recorded_tokens: &'a mut VecDeque<T>,
    len: usize,
}

impl<'a, T> QueueSlice<'a, T> {
    pub fn new(recorded_tokens: &'a mut VecDeque<T>) -> Self {
        let len = recorded_tokens.len();
        QueueSlice {
            recorded_tokens,
            len,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn with_subslice<R>(&mut self, len: usize, f: impl FnOnce(&mut Self) -> R) -> R {
        assert!(len <= self.len);
        let remaining = self.len - len;
        self.len = len;
        let result = f(self);
        self.len += remaining;
        result
    }

    pub fn front(&self) -> Option<&T> {
        if self.len > 0 {
            self.recorded_tokens.front()
        } else {
            None
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        if self.len > 0 {
            self.len -= 1;
            self.recorded_tokens.pop_front()
        } else {
            None
        }
    }

    pub fn push_front(&mut self, value: T) {
        self.recorded_tokens.push_front(value);
        self.len += 1;
    }

    pub fn iter(&self) -> Take<vec_deque::Iter<T>> {
        self.recorded_tokens.iter().take(self.len)
    }

    pub fn into_queue(&mut self) -> VecDeque<T> {
        let mut result = self.recorded_tokens.split_off(self.len);
        swap(&mut result, self.recorded_tokens);
        self.len = 0;
        result
    }
}
