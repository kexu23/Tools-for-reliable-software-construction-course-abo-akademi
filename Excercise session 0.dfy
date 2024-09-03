
method Triple (x: int) returns (r: int) 
    ensures r == 3*x
{
    if x == 0 {
        r := 0;
    }
    else {
        var y := 2*x;
        assert y == 2*x;
        r := x + y;
    }
    assert r == 3*x;
}

method TripleCase(x: int) returns (r: int) {
    if {
        case x < 18 =>
            var a, b := 2*x, 4*x;
            r := (a + b) / 2;
        case 0 <= x =>
            var y := 2*x;
            r := x + y;
    }
    assert r == 3*x;
}

method TriplePre(x: int) returns (r: int)   // now with prerequisites :)
    requires x % 2 == 0
    ensures r == 3*x
{
    var y := x / 2;
    r := 6*y;
}

method Index(n: int) returns (i: int)
    requires 1 <= n
    ensures 0 <= i < n
{
    i := n/2;
}

function Average (a: int, b: int): int {
    (a + b / 2)
}

method Triple'(x: int) returns (r: int)
    ensures Average(r,3*x) == 3*x

predicate IsEven(x: int) {
    x % 2 == 0
}

function IsEvenfunc(x: int): bool {
    x % 2 == 0
}

method Test(i: int) {
    var x := Index(50);
    var y := Index(50);

}

method Abs (x: int) returns (y: int) {
    if x < 0 {
        return -x;
    }
    else {
        return x;
    }
}

method MultipleReturns (x: int, y: int) returns (more: int, less: int) {
    more := x + y;
    less := x-y;
    //comments not necessary :)
}

method Caller() {
    var t := Triple(18);
    assert t < 100;
}

