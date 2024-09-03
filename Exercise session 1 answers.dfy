//Ex 1.6

method MinPage16(x: int, y: int) returns (m: int)
  ensures m <= x && m <= y
  
//Write an implementation for Min that satisﬁes the postcondition above but is not always the minimum of x and y. 

method Min(x: int, y: int) returns (m: int)
  ensures m <= x && m <= y
{
    m := if x <= y then x - 1 else y - 1;
}


//-------------------------------





//Ex 1.7

//Here is the type signature of a method to compute s to be the sum of x and y and m to be the maximum of x and y: 

method MaxSumEx1Point7(x: int, y: int) returns (s: int, m: int) 

/*
(a) Specify the intended postcondition of this method. 
(b) Write a method that calls MaxSum with the input arguments 1928 and 1. Follow the call with an assertion about what you 
expect the two out-parameters to be. If the veriﬁer complains that the assertion may be violated, go back to (a) to improve 
the speciﬁcation. This is a useful way to “test the speciﬁcation”. Note, you’re testing the speciﬁcation by using the veriﬁer,
not by running the program. 
(c) Write an implementation for MaxSum. 
*/

//(a)
method MaxSumSpec(x: int, y: int) returns (s: int, m: int) 
    ensures s == x + y 
    ensures x <= m && y <= m
    ensures x == m || y == m

//-------------------------------

//(b)

method Test(){
    var a, b := MaxSumSpec(1928, 1);
    assert a == 1929 && b == 1928;
}
//-------------------------------

//(c)
method MaxSum(x: int, y: int) returns (s: int, m: int) 
    ensures s == x + y 
    ensures x <= m && y <= m
    ensures x == m || y == m
{
    s := x + y;
    m := if x <= y then y else x;
}
//------------------------------




// Ex 1.8

/*
Consider a method that attempts to reconstruct the arguments x and y from the return values of MaxSum in Exercise 1.7. In 
other words, consider a method with the following type signature and postcondition: 
*/

method ReconstructFromMaxSumSpec(s: int, m: int) returns (x: int, y: int)
ensures s == x + y
ensures x <= m && y <= m 
ensures m == x || m == y

/*
(a) Try to write the body for this method. You will ﬁnd you cannot. Write an appropriate precondition for the method that allows 
you to implement the method.
*/

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
ensures s == x + y
ensures x <= m && y <= m 
ensures m == x || m == y
requires s <= 2*m
{
    x := m;
    y := s-m;
}
//------------------------------


//(b) Write the following test harness to test the method’s speciﬁcation: 

method TestMaxSum(x: int , y: int ){ 
    var s, m := MaxSum(x, y); 
    var xx, yy := ReconstructFromMaxSum(s, m); 
    assert (xx == x && yy == y) || (xx == y && yy == x); 
} 

/*How can you change the speciﬁcation of ReconstructFromMaxSum to allow the assertion in the test harness to succeed?
*/

//--------------------------------




//Ex 1.9

/*
The speciﬁcation of Triple’ is not the same as that of Triple . 
(a) Write a correct body for Triple’ that does not meet the speciﬁcation of Triple . 
(b) How can you strengthen the speciﬁcation of Triple’ with minimal changes to make it equivalent to the speciﬁcation 
of Triple ? 
(c) How can you use Dafny to prove that the speciﬁcations in (b) are indeed equivalent?
*/


method Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
    var y := 2*x;
    r := x + y;
}

function Average(a: int, b: int): int
{
  (a + b) / 2
}

method Triple'Spec(x: int) returns (r: int)
  ensures Average(r, 3*x) == 3 * x

//(a)
method Triple'(x: int) returns (r: int)
  ensures Average(r, 3*x) == 3 * x
{
    r := 3*x + 1;
}
//----------------

//(b)
method Triple'SpecStrengthened(x: int) returns (r: int)
  ensures Average(r, 3*x) == 3 * x
  ensures r % 3 == 0
//------------------

//(c)
method TestEx1Point9(x :int){
    var triple1 := Triple(x);
    var triple2 := Triple'SpecStrengthened(x);
    assert triple1 == triple2;
}
//----------------



// Ex 1.11

// (a) What does the veriﬁer have to say about the two assertions in this program?

function F(): int { 
    29 
} 

method M() returns (r: int ){ 
    r := 29; 
} 

method Caller() { 
    var a := F(); 
    var b := M'(); 
    assert a == 29; 
    assert b == 29; 
}

// It says "Assertion might not hold."

// (b) Explain why. 

// Methods opaque, implementation hidden. Dafny can not know what the method's body does to "r".

//(c) How can you change the program to make both assertions verify?

method M'() returns (r: int) 
ensures r == 29
{
    r := 29; 
}

