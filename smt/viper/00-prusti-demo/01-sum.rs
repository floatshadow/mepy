fn sum(n: i32) -> i32 
{
    let mut res = 0;
    let mut i = 0;
    while i <= n {
        res = res + i;
        i = i + 1;
    }
    res
}


fn client() {
    let r = sum(5);
    assert!(r == 15);
}