
// Exercise 2.4
    // a) If x == y or if y is less than 1
    // b) y != 4 since there is no precondition for y
    // c) Doesn't hold because of post-condition false
    // d) Triple holds?

// Exercise 2.22

method Exercise222(x: int) returns (y: int)
    requires x >= 10
    ensures y % 2 == 0
{   
    // Here we know y % 2 == 0 && (x <= 10 || x > 10)
    if x < 10 {
        // Here we know x < 10
        if x < 20 {y := 1; } // Here we know y % 2 == 1 and x < 10 
        else {y := 2;} // Here we know x >= 20 and y % 2 == 0
    } else {
        // Here we know x >= 10 and y % 2 == 0
        y := 4;
    }
}

method Exercise222Better(x: int) returns (y: int) // For y % 2 == 0, x needs to be more than or equal 10
    requires x >= 10
    ensures y % 2 == 0
{
    // Here we know x < 10 or x >= 10
    if x < 10 {
        // Here we know x < 10
        y := 1;
    }
    else {
        // Here we know x >= 10
        y := 4;
    }
}


// Exercise 2.26

method Exercise226a(x: int, y: int)
    requires x + 1 + y <= 100
    ensures x + y <= 100
{
    // Here we want x + 1 + y <= 100
    var x := x + 1;
    // Here we want x + y <= 100
    var y := x + y;
    // Here we want y <= 100
}

method Exercise226b(x: int, y: int)
    requires x + y <= 100
    ensures x + y <= 100
{
    // Here we want x + y <= 100
    var y := x + y;
    // Here we want y <= 100
    var x := x + 1;
    // Here we want y <= 100
}

method Exercise226c(x: int, y: int)
    requires x + 1 + y <= 100
    ensures x + y <= 100
{
    // Here we want x + 1 + y <= 100
    var x, y := x + 1, x + y;
    // Here we want y = <= 100
}

// Exercise 3.3

function I(x: nat, y: nat): int
    decreases x, y
{
    if x == 0 || y == 0 then 
        12
    else if x % 2 == y % 2 then
        I(x - 1, y)
    else
        I(x, y - 1)
}

// Exercise 3.5

function K(x: nat, y: nat, z: nat): int 
    decreases x, y, z
{
    if x < 10 || y < 5 then
        x + y
    else if z == 0 then
        K(x - 1, y, 5)
    else
        K(x, y - 1, z - 1)
}

// Exercise 3.9

function N(x: int, y: int, b: bool): int 
    decreases x, b
{
    if x <= 0 || y <= 0 then
        x + y 
    else if b then
        N(x, y + 3, !b)
    else
        N(x - 1, y, true)
}

// Exercise 3.12

method Study(n: nat, h: nat)
    decreases n, h
{
    if h != 0 {
        // first study for an hour, and then:
        Study(n, h - 1);
    }
    else if n == 0 {
        // You just finished course 0 - woot woot, graduation time!
    }
    else {
        // Find out how much studying is needed for the next course
        var hours := RequiredStudyTime(n - 1);
        // Get started with course n - 1
        Study(n - 1, hours);
    }
}

method StudyNoTuple(n: nat, h: nat)
    decreases n, h
{
    if h != 0 {
        // first study for an hour, and then:
        StudyNoTuple(n, h - 1);
    }
    else if n == 0 {
        // You just finished course 0 - woot woot, graduation time!
    }
    else {
        // Find out how much studying is needed for the next course
        var hours := RequiredStudyTime(n - 1);
        // Get started with course n - 1
        StudyNoTuple(n - 1, hours);
    }
}

method RequiredStudyTime(c: nat) returns (hours: nat)
    ensures hours <= 200




// Optional Exercise 9 a

method OuterA(a: nat)
    decreases a
{
    if a != 0 {
        var b := RequiredStudyTime(a - 1);
        InnerA(a, b);
    }
}

method InnerA(a: nat, b: nat)
    requires 1 <= a
    decreases a, b
{
    if b == 0 {
        OuterA(a - 1);
    }
    else {
        InnerA(a, b - 1);
    }
}

// Optional Exercise 9 b

method OuterB(a: nat) 
    decreases a
{
    if a != 0{
        var b := RequiredStudyTime(a - 1);
        InnerB(a - 1, b);
    }
}

method InnerB(a: nat, b: nat)
    decreases a + 1, b
{
    if b == 0 {
        OuterB(a);
    }
    else {
        InnerB(a, b - 1);
    }
}

method Q2a () returns (x: int)
    requires true
    ensures x == 400
{
    x := 400;
}

method Q2b (x: int) returns (xx: int)
    requires x % 2 == 1
    ensures xx % 2 == 0
{
    xx := x + 3;
}



method Q2c (y: int) returns (x: int)
    requires y <= 65
    ensures y <= x
{
    x := 65;
}

method Q2e (x: int, y: int) returns (xx: int, yy: int)
    requires (0<=x<=50)&& (y <=x)
    ensures 0 <= xx <= 100 && yy <= xx
{
    xx, yy := 2 * x, x + y;
}

method Q2f (x: int, y: int) returns (xx: int, yy: int)
    requires false
    ensures 10 <= x <= y
{
    xx := 2 * y;
}

method Q2d (y: int, x: int) returns (b: bool)
    requires y < 10 ==> x < y
    ensures b ==> x < y
{
    b := y < 10;
}

method Q3b (x: int, y: int) returns (xx: int, yy: int)
    requires x == 4
    ensures yy-xx == 3
{
    xx, yy := x +1, 2 * x;
}

method Q3c (x: int, y: int) returns (xx: int, yy: int)
    requires x == 2
    ensures yy-xx == 3
{
    xx := x + 1;
    yy := 2 * xx;
}
