struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
    value: u64,
}

fn bad(mut tree: Node) -> Option<()> {
    tree.left.as_mut()?.right = tree.right.as_mut()?.left;
    Some(())
}

fn main() {
    let tree: Node = Node {
        left: Some(Box::new(Node { left: Some(Box::new(Node { left: None, right: None, value: 3 })), right: None, value: 2})),
        right: Some(Box::new(Node { left: None, right: Some(Box::new(Node { left: None, right: None, value: 6 })), value: 5})),
        value: 4,
    };
}
