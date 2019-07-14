// run-pass
#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash

#[derive(Debug)]
pub enum Test {
    Foo(usize, Option<usize>),
    Bar,
    Baz
}

pub fn test(x: Option<Test>) -> bool {
    match x {
        Some(Test::Bar | Test::Foo(_, Some(_))) => true,
        Some(_) => false,
        _ => false,
    }
}

fn main() {
    assert!(test(Some(Test::Foo(42, Some(1)))));
    assert!(test(Some(Test::Foo(255, Some(255)))));
    assert!(test(Some(Test::Bar)));
    assert!(!test(Some(Test::Baz)));
    assert!(!test(None));
}
