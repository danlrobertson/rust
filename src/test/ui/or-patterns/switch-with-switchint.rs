// run-pass
#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash

#[derive(Debug)]
enum Foo {
    Bar(usize),
    Baz(usize, usize),
}

fn test(x: Option<Foo>) -> bool {
    match x {
        Some(Foo::Bar(1024) | Foo::Baz(2048, 4096)) => true,
        Some(_) => false,
        None => false,
    }
}

fn main() {
    assert!(test(Some(Foo::Bar(1024))));
    assert!(!test(Some(Foo::Bar(1025))));
    assert!(test(Some(Foo::Baz(2048, 4096))));
    assert!(!test(Some(Foo::Baz(2048, 4097))));
    assert!(!test(Some(Foo::Baz(2049, 4096))));
}
