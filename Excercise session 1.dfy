
// Exercise 1.6
method Min(x: int, y: int) returns (m: int)     
    ensures m <= x && m <= y
    ensures m == x || m == y
{
    if x < y {
        m := x;
    }
    else {
        m := y;
    }
}

// Exercise 1.7
method MaxSum(x: int, y: int) returns (s: int, m: int)
    ensures s == x + y
    ensures m == x || m == y
{
    s := x + y;
    if x <= y {
        m := x;
    }
    else {
        m := y;
    }
    return s, m;
}

method MaxSumCall(i: int) {
    var x, y := MaxSum(1928, 1);
}

//Exercise 1.9

method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    var y := 2*x;
    r := x + y;
}

function Average(a: int, b: int): int {
    (a + b) / 2
}

method Triple'(x: int) returns (r: int)
    requires x % 2 == 0
    ensures Average(r, 3*x) == 3*x
{
    r := 3 * x + 1;
}

method TripleSpecStrengthened(x: int) returns (r: int)
    ensures Average(r, 3*x) == 3*x 
    ensures r % 3 == 0

//Exercise 1.11
function F(): int {
    29
}

method M() returns (r: int)
    ensures r == 29
{
    r := 29;
}

method Caller() {
    var a := F();
    var b := M();
    assert a == 29;
    assert b == 29;     // parser gives error on assertion on the method because the assertion cannot know what is inside the method body
                        // Can be fixed by adding postconditions
}

//Exercise 1.8
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    ensures s == x + y
    ensures x <= m && y <= m
    ensures m == x || m == y
    requires s <= 2*m
    {
        x := m;
        y := s - m;
    }


method TestMaxSum(x: int, y: int)
 {
    var s, m := MaxSum(x, y);
    var xx, yy := ReconstructFromMaxSum(s, m);
    assert (xx == x && yy == y) || (xx == y && yy == x);
}
