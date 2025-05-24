/// Represents a list of values and a cursor that is used to iterate forward or backward through
/// them.
pub struct Stream<T> {
    tokens: Vec<T>,
    cursor: usize,
}

impl<T> Stream<T> {
    /// Creates a new stream.
    pub fn new(tokens: Vec<T>) -> Self {
        Stream { tokens, cursor: 0 }
    }

    /// Returns the current position of the cursor in the stream.
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// Sets the cursor position in the stream.
    pub fn set_cursor(&mut self, pos: usize) {
        self.cursor = pos
    }

    /// Returns the next value in the stream and increments the cursor position by 1.
    pub fn next(&mut self) -> Option<&T> {
        let tok = self.tokens.get(self.cursor);
        self.cursor += 1;
        tok
    }

    /// Returns the previous value in the stream without moving the cursor.
    pub fn prev(&self) -> Option<&T> {
        self.tokens.get(self.cursor - 1)
    }

    /// Moves the cursor position back by 1.
    pub fn rewind(&mut self, n: usize) {
        self.cursor -= n;
    }

    /// Returns the next value in the stream without moving the cursor.
    pub fn peek_next(&self) -> Option<&T> {
        self.tokens.get(self.cursor)
    }

    /// Returns the value n positions ahead of the current cursor position without moving the
    /// cursor.
    pub fn peek_ahead(&self, n: usize) -> Option<&T> {
        self.tokens.get(self.cursor + n)
    }

    /// Returns true only if there is at least one more value left in the stream beyond the current
    /// cursor position.
    pub fn has_next(&self) -> bool {
        self.peek_next().is_some()
    }
}
