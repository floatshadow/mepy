use prusti_contracts::*;

#[ensures(0 <= result && result <= a.len())]
fn search(a: &[i32], key: i32) -> usize {
    let mut i = 0;

    while i < a.len() {
        body_invariant!(0 <= i && i < a.len());

        if(a[i] == key) {
            return i; // key found
        }
        i = i + 1;
    }

    return a.len(); // key not found
}
