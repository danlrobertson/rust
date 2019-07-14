// run-pass
#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash

pub fn test(x: Option<usize>) -> usize {
    match x {
        Some(0 | _) => 0,
        _ => 1
    }
}

fn main() {
    assert_eq!(test(Some(42)), 0);
}
