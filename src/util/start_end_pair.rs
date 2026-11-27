//! `util.StartEndPair`: the first and last bytecode offset covered by a statement.

use std::fmt;

use super::jhash::JavaHash;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StartEndPair {
    pub start: i32,
    pub end: i32,
}

impl StartEndPair {
    pub fn new(start: i32, end: i32) -> Self {
        Self { start, end }
    }
}

/// `StartEndPair.join`: the range spanning every pair that is present. Without
/// any pair the result runs from `i32::MAX` to `i32::MIN`.
pub fn join(pairs: impl IntoIterator<Item = Option<StartEndPair>>) -> StartEndPair {
    pairs
        .into_iter()
        .flatten()
        .fold(StartEndPair::new(i32::MAX, i32::MIN), |joined, pair| {
            StartEndPair::new(joined.start.min(pair.start), joined.end.max(pair.end))
        })
}

impl JavaHash for StartEndPair {
    fn java_hash(&self) -> i32 {
        self.start.wrapping_mul(31).wrapping_add(self.end)
    }
}

impl fmt::Display for StartEndPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}->{}", self.start, self.end)
    }
}
