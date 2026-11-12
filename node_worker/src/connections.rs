//! The connection table (operation 90; one TLS connection per Tor circuit), socket half.
//!
//! One connection is active; every server operation acts on it, so a controller that never
//! selects uses connection 0 exactly as before. Each entry holds the leader's [`Server`] (the
//! follower only records that the leader holds one). The per-connection TLS and WebSocket state
//! is the engines' (`ea_legacy_select` / `ea_legacy_reset`); the engines, circuits, masks,
//! buffers, contacts and the account are shared by all connections.
use crate::server::Server;

pub enum Endpoint {
    /// The leader's socket to the server.
    Leader(Server),
    /// The follower's mark that the leader holds an open socket for this connection.
    Follower,
}

pub struct Connections {
    slots: Vec<Option<Endpoint>>,
    active: usize,
    /// Unset before the first connect; then whether it went through a proxy, the same for every connection.
    proxied: Option<bool>,
}

impl Default for Connections {
    fn default() -> Self {
        Connections { slots: vec![None], active: 0, proxied: None }
    }
}

impl Connections {
    pub fn active(&mut self) -> &mut Option<Endpoint> {
        &mut self.slots[self.active]
    }
    pub fn connected(&self) -> bool {
        self.slots[self.active].is_some()
    }
    pub fn active_index(&self) -> usize {
        self.active
    }
    pub fn count(&self) -> usize {
        self.slots.len()
    }
    /// An existing index, or the next unused one (a new, fresh connection); at most 64.
    pub fn check_select(&self, to: u8) -> Result<(), String> {
        if (to as usize) < 64 && (to as usize) <= self.slots.len() { Ok(()) } else { Err("connection index".into()) }
    }
    pub fn select(&mut self, to: u8) {
        if to as usize == self.slots.len() {
            self.slots.push(None);
        }
        self.active = to as usize;
    }
    /// Every connection of a worker goes the same way: all direct or all through the proxy.
    pub fn note_route(&mut self, proxy: bool) -> Result<(), String> {
        match self.proxied {
            Some(p) if p != proxy => Err("every connection of a worker goes the same way".into()),
            _ => {
                self.proxied = Some(proxy);
                Ok(())
            }
        }
    }
    /// Abort: every socket is closed; the table keeps its shape.
    pub fn drop_all(&mut self) {
        for slot in &mut self.slots {
            *slot = None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn select_grows_by_one_and_stops_at_64() {
        let mut c = Connections::default();
        assert!(c.check_select(0).is_ok());
        assert!(c.check_select(1).is_ok());
        assert!(c.check_select(2).is_err());
        c.select(1);
        assert_eq!((c.count(), c.active_index()), (2, 1));
        for i in 2..64u8 {
            c.check_select(i).unwrap();
            c.select(i);
        }
        assert!(c.check_select(64).is_err());
    }

    #[test]
    fn route_is_fixed_by_the_first_connect() {
        let mut c = Connections::default();
        c.note_route(true).unwrap();
        c.note_route(true).unwrap();
        assert!(c.note_route(false).is_err());
    }
}
