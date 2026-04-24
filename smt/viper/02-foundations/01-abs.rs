extern crate prusti_contracts;
use prusti_contracts::*;


fn abs(x:i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}