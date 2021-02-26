module A {
    predicate x() { true }
}

module B {
    import A1 = A
    import A2 = A
}

module C {
    import B
    predicate x() { B.A1.x() }
}
