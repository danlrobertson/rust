// run-pass
#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash

#[derive(Debug)]
enum Test {
    Foo,
    Bar,
    Baz,
    Qux
}

#[derive(Debug)]
enum Wrapper {
    Filled(Test),
    Empty,
}

fn test_wrapper(x: Wrapper) -> bool {
    match x {
        // most simple case
        Wrapper::Filled(Test::Bar | Test::Qux) => true,
        // wild case
        Wrapper::Filled(_) => false,
        // empty case
        Wrapper::Empty => false,
    }
}

fn main() {
    assert!(!test_wrapper(Wrapper::Filled(Test::Foo)));
    assert!(test_wrapper(Wrapper::Filled(Test::Bar)));
    assert!(!test_wrapper(Wrapper::Filled(Test::Baz)));
    assert!(test_wrapper(Wrapper::Filled(Test::Qux)));
    assert!(!test_wrapper(Wrapper::Empty))
}
