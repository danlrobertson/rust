// run-pass
#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash

#[derive(Debug)]
enum Other {
    One,
    Two,
    Three,
    Four
}

#[derive(Debug)]
enum Test {
    Foo,
    Bar(Other),
    Baz(usize),
    Qux(usize, Option<usize>),
    Unused
}

fn test(x: Option<Test>) -> bool {
    match x {
        // nested (single subpattern)
        Some(Test::Bar(Other::Two | Other::Four) | Test::Foo) => true,
        Some(Test::Baz(255 | 42) | Test::Qux(42, None)) => true,
        // nested (multiple subpatterns)
        Some(_) => false,
        // option is none
        None => false,
    }
}

fn main() {
    assert!(test(Some(Test::Bar(Other::Four))));
    assert!(!test(Some(Test::Bar(Other::Three))));
    assert!(test(Some(Test::Qux(42, None))));
    assert!(!test(Some(Test::Qux(43, None))));
    assert!(test(Some(Test::Baz(42))));
    assert!(!test(Some(Test::Baz(43))));
    assert!(!test(None));
}
