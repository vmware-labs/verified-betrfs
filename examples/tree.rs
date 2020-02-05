#[allow(dead_code)]

extern crate prusti_contracts;
use prusti_contracts::*;

pub struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
    value: u64,
}

#[pure]
pub fn search_tree(node: &Node, from: u64, to: u64) -> bool {
    (from <= node.value && node.value < to) &&
    (match &node.left {
        Some(ref left) => search_tree(left, from, node.value),
        None => true,
    }) &&
    (match &node.right {
        Some(ref right) => search_tree(right, node.value, to),
        None => true,
    })
}

#[requires="search_tree(tree, ghost_from, ghost_to)"]
#[requires="0 <= value && value < 1024"]
#[requires="ghost_from <= value && value < ghost_to"]
#[ensures="search_tree(tree, ghost_from, ghost_to)"]
pub fn insert(tree: &mut Node, value: u64, ghost_from: u64, ghost_to: u64) {
    if value < tree.value {
        match &mut tree.left {
            Some(ref mut left) => {
                insert(left, value, ghost_from, tree.value);
            },
            None => {
                tree.left = Some(Box::new(Node { left: None, right: None, value: value }));
            },
        }
    } else {
        match &mut tree.right {
            Some(ref mut right) => {
                insert(right, value, tree.value, ghost_to);
            },
            None => {
                tree.right = Some(Box::new(Node { left: None, right: None, value: value }));
            },
        }
    }
}

#[requires="search_tree(tree, 0, 1024)"]
#[requires="0 <= value && value < 1024"]
#[ensures="search_tree(tree, 0, 1024)"]
pub fn do_insert(tree: &mut Node, value: u64) {
    insert(tree, value, 0, 1024);
}

#[requires="search_tree(tree1, 0, 1024)"]
#[requires="search_tree(tree2, 0, 1024)"]
#[ensures="search_tree(tree1, 0, 1024)"]
#[ensures="search_tree(tree2, 0, 1024)"]
pub fn dont_interfere(tree1: &mut Node, tree2: &mut Node) {
    do_insert(tree1, 82);
}