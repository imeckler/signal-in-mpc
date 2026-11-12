//! The daemon of one computation node: node-daemon CONFIG.json. See ../../README.md.
//!
//! It handles public values only (the application's requests, ids, results, session names) and
//! this node's own database client key file, by path. It never sees a share, never parses
//! Signal traffic, and returns nothing the controller did not report as an agreed public value.
//!
//! This file is only the wiring: every input and output is in `node_daemon::channels`, the state
//! machine in `node_daemon::scheduler`.

use node_daemon::channels::disk::Disk;
use node_daemon::channels::host::{announce_listening, arguments, catch_stop_signals, fail, log};
use node_daemon::channels::{Listener, application, peer};
use node_daemon::config::Config;
use node_daemon::hmac;
use node_daemon::scheduler::Daemon;
use std::time::Duration;

fn main() {
    let arguments = arguments();
    if arguments.len() != 2 {
        fail("usage: node-daemon CONFIG.json");
    }
    let config = Config::load(&arguments[1]).unwrap_or_else(|why| fail(&format!("node-daemon: {why}")));
    catch_stop_signals();
    let disk = Disk::new(config.state.clone());
    if let Err(why) = disk.create() {
        fail(&format!("node-daemon: {why}"));
    }
    // Signups reported before a restart are still reported after it.
    let events = disk.load_events();
    // Journals of notifies that can no longer be resumed (their request has long expired).
    disk.prune_journals(Duration::from_secs(86400));
    // Two listeners: the application's (`listen`) and the other daemon's (`peer_listen`). Each
    // takes only its own messages, so neither can reach the other's operations.
    let bind = |address: &str| Listener::bind(address).unwrap_or_else(|why| fail(&format!("node-daemon: {why}")));
    let (listener, peer_listener) = (bind(&config.listen), bind(&config.peer_listen));
    // A fixed check of the link's MAC, so that a wrong build is noticed at start.
    assert_eq!(hex::encode(hmac(b"Jefe", b"what do ya want for nothing?")), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
    let daemon = Daemon::new(config, disk, events);
    let c = &daemon.config;
    log(&format!("party {} listening on {} (application{}) and {} (the other daemon)", c.party, c.listen,
        if c.bearer.is_some() { ", bearer token required" } else { "" }, c.peer_listen));
    announce_listening(&c.listen, &c.peer_listen);
    let handler = daemon.clone();
    application::serve(listener, c.bearer.clone(), move |request| handler.application(request));
    let handler = daemon.clone();
    peer::serve(peer_listener, c.peer_key.clone(), c.party, move |message| handler.peer(message));
    daemon.run();
}
