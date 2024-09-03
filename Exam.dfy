method Question3(x: int) returns (y: int)
    requires x == 20 || x == 19
    ensures x + y == 22
{
    if x < 20 {
        // Here we want x + 3 == 22 <==> x == 19
        y := 3;
    } 
    else {
        // Here we want x + 2 == 22 <==> x == 20
        y := 2;
    } 
    // Here we want x + y == 22
}

method RequiredStudyTime(c: nat) returns (hours: nat)
ensures hours <= 128


method Study(n: nat, h: nat)
// simulates time until graduation from the study perspective
decreases 129*n + h
{
 if h != 0 {
 // first study for an hour, and then:
 Study(n, h - 1);
 }
 else // finished with course n (h == 0 for course n)
 {
  if n == 0 {// you just finished course 0, great, graduation time!
  }
  else {//find out how much studying is needed for the next course
    var hours := RequiredStudyTime(n - 1); // n-1 is the next course
    //get started with course n-1:
    Study(n-1, hours);
  }
 }
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Count(xs: List<int>, p: int): nat {
match xs
case Nil => 0
case Cons(x, tail) => (if x == p then 1 else 0) + Count(tail, p)
}

function Project(xs: List<int>, p: int): List<int> {
match xs
case Nil => Nil
case Cons(x, tail) => if x == p then Cons(p, Project(tail, p)) else Project(tail, p)
}


/*
lemma StabilityImpliesOccurrence(xs: List<int>, ys: List<int>, p: int)
requires Project(xs, p) == Project(ys, p)
ensures Count(xs, p) == Count(ys, p)
{
    calc {

        Count(xs, p);
        == {Project(xs, p);}
        Cons(xs, p);
        == // Using the precondition
        Cons(ys, p);
        == {Project(ys, p);}
        Count(ys, p);


        
    }
}
 
lemma OccurenceImpliesStability(xs: List<int>, ys: List<int>, p: int)
requires Count(xs, p) == Count(ys, p)
ensures Project(xs, p) == Project(ys, p)
{
    calc {

        Project(xs, p);
        == {Count(xs, p);}
        Cons(xs, p);
        == // Using the precondition
        Cons(ys, p);
        == {Count(ys, p);}
        Project(ys, p);


        
    }
}
*/

method Question8() returns (a: int)
{

    a := 98;
    while a < 2500
        invariant a <= 2506
        invariant (a - 98) % 7 == 0
    { 
        a := a + 7;
        var x := a;
    }
    assert a == 2506;
}

method Quadruple(n : nat) returns (q: nat)
ensures q == n * n * n * n
{
    var m, k, v, w := 0, 1, 8, 24;
    q := 0;
    while m < n
        invariant 0 <= m <= n
        invariant q == m * m * m * m
        invariant k == 4*m*m*m + 6*m*m + 4*m + 1
        invariant v == 12*m*m + 24*m + 8
        invariant w == 24*m + 24
    {
        m, q, k, v, w := m + 1, q + k, k + v, v + w, w + 24;
    }
}

/*

q == m^4 [M := m +1]
==
q == (m+1)^4
==
q == m^4 + 4*m^3 + 6*m^2 + 4*m + 1
== {k == 4*m^3 + 6*m^2 + 4*m + 1}
q == q + k

k == 4*m^3 + 6*m^2 + 4*m + 1
==
k == 4*(m+1)^3 + 6*(m+1)^2 + 4*(m+1) + 1
==
k == 4*m^3 + 12*m^2 + 12*m + 4 + 6*m^2 + 12*m + 6 + 4*m + 4 + 1
== {v == 12*m^2 + 24*m + 8}
k == k + v

v == 12*m^2 + 24*m + 8 [m := m + 1]
==
v == 12*(m + 1)^2 + 24*(m + 1) + 8
==
v == 12*m^2 + 24*m + 12 + 24*m + 24 + 8
== {w == 24*m + 36}
v == v + w

w == 24*m + 36 [m := m + 1]
==
w == 24*(m + 1) + 36
==
w == 24*m + 24 + 36
==
w == w + 24

*/

method QuadrupleAgain(n : nat) returns (q: nat)
ensures q == n * n * n * n
{
    var m, k, v, w := 0, 1, 8, 24;
    q := 0;
    while m < n
        invariant 0 <= m <= n
        invariant q == m * m * m * m
        invariant k == 4*m*m*m + 6*m*m + 4*m + 1
        invariant v == 18*m*m + 14
        invariant w == 36*m + 32
    {
        m, q, k, v, w := m + 1, q + k, k + v, v + w, w + 24;
    }
}

/*
// calculating again

q == m^4 [M := m +1]
==
q == (m+1)^4
==
q == m^4 + 4*m^3 + 6*m^2 + 4*m + 1
== {k == 4*m^3 + 6*m^2 + 4*m + 1}
q == q + k

k == 4*m^3 + 6*m^2 + 4*m + 1
==
k == 4*(m+1)^3 + 6*(m+1)^2 + 4*(m+1) + 1
==
k == 4*m^3 + 12*m^2 + 12*m + 4 + 6*m^2 + 12*m + 6 + 4*m + 4 + 1
== {v == 18*m^2 + 14}
k == k + v

v == 18*m^2 + 14 [m := m + 1]
==
v == 18*(m + 1)^2 + 14
==
v == 18*m^2 + 36*m + 32
== {w == 36*m + 32}
v == v + w

w == 36*m + 32 [m := m + 1]
==
w == 36*(m + 1) + 32
==
w == 36*m + 36 + 32
==
w == w + 36