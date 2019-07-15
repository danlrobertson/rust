// run-pass
#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash

enum Other {
    One,
    Two,
    Three
}

enum Test {
    Foo {
        first: usize,
        second: Other,
    },
    Bar {
        value: bool
    }
}

fn test(pat: Option<Test>) -> bool {
    match pat {
        Some(
            Test::Foo { first: (42 | 255), second: (Other::One | Other::Two) } |
            Test::Bar { value: true }
        ) => true,
        Some(
            Test::Foo { first: _, second: _ } |
            Test::Bar { value: false }
        ) => false,
        None => false,
    }
}

fn main() {
    assert!(test(Some(Test::Foo { first: 42, second: Other::Two })));
    assert!(test(Some(Test::Foo { first: 255, second: Other::One })));
    assert!(test(Some(Test::Bar { value: true })));
    assert!(!test(Some(Test::Bar { value: false })));
    assert!(!test(Some(Test::Foo { first: 255, second: Other::Three })));
    assert!(!test(Some(Test::Foo { first: 0, second: Other::Two })));
}
