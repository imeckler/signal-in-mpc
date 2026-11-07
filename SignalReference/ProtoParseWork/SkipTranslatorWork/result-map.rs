    pub const fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: [const] FnOnce(T) -> U + [const] Destruct,
    {
        match self {
            Ok(t) => Ok(op(t)),
            Err(e) => Err(e),
        }
    }
