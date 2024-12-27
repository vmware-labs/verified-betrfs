// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
extern crate git2;

use chrono::TimeZone;
use git2::{Cred, FetchOptions, RemoteCallbacks, Repository, Revwalk};
use std::{cmp::Reverse, path::Path};

fn main() {
    let url = "git@github.com:verus-lang/z-recorded-histories.git";
    let mut args = std::env::args();
    let _ = args.next().expect("binary name");
    let private_key_path = args
        .next()
        .expect("missing private key path; usage: ./check_recordings private_key public_key");
    let public_key_path = args
        .next()
        .expect("missing private key path; usage: ./check_recordings private_key public_key");

    // Remote callbacks to authenticate via SSH.
    let mut callbacks = RemoteCallbacks::new();
    callbacks.credentials(|_url, username_from_url, _allowed_types| {
        Cred::ssh_key(
            username_from_url.expect("username is required"),
            Some(Path::new(&public_key_path)),
            Path::new(&private_key_path),
            None,
        )
    });

    let mut fetch_options = FetchOptions::new();
    fetch_options.remote_callbacks(callbacks);

    let repo = Repository::init_bare("z-recorded-histories")
        .expect("failed to initialize repository in memory");

    let mut remote = repo
        .find_remote("origin")
        .ok()
        .or_else(|| repo.remote("origin", url).ok())
        .expect("failed to create anonymous remote");
    remote
        .download(&["HEAD"], Some(&mut fetch_options))
        .expect("failed to fetch");
    let heads: Vec<String> = remote
        .list()
        .expect("cannot obtain remote heads")
        .iter()
        .map(|h| h.name().to_owned())
        .filter(|h| h.as_str() != "HEAD" && h.as_str() != "refs/heads/default")
        .collect();
    remote
        .fetch(&heads[..], Some(&mut fetch_options), None)
        .expect("failed to fetch");
    let mut all_branches = Vec::new();
    for r in repo.references().expect("failed to get references") {
        let r = r.expect("reference");
        let r = r.name().expect("reference name");
        let mut revwalk: Revwalk = repo.revwalk().expect("Failed to create revwalk");
        revwalk.push_ref(&r).expect("failed to push ref in revwalk");
        let commit_count = revwalk.count();
        if commit_count > 0 {
            let mut revwalk: Revwalk = repo.revwalk().expect("Failed to create revwalk");
            revwalk.push_ref(&r).expect("failed to push ref in revwalk");
            let last_rev = revwalk.next().expect("no revision").expect("no revision");
            let last_commit = repo.find_commit(last_rev).expect("commit");
            let time = last_commit.time();
            #[allow(deprecated)]
            let datetime = chrono::Utc.timestamp(time.seconds(), 0);
            all_branches.push((r.to_owned(), commit_count, datetime));
        }
    }
    all_branches.sort_by_key(|k| Reverse(k.2));
    for (r, count, datetime) in all_branches.iter() {
        println!("{}", format!("{datetime}: {r} ({count} commits)"));
    }
}
