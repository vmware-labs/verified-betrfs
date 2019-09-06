fn bar(x: &mut Box<u64>, v: u64) {
    **x = v;
}

fn foo(x: &mut Box<u64>, y: &Box<u64>)
// requires **y == 20
{
    bar(x, **y);
    // assert **y == 20
}

fn main() {
    let mut x = Box::new(10);
    foo(&mut x, &x);
}

