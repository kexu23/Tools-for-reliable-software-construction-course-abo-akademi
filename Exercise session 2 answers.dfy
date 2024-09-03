// 2.4 * ////////////////////////////////

/*
x == ? y == ? so that triples do not hold

{{ true }} x := 2 * y {{ y <= x }} ---> x: int, y == -2 (in general y < 0)
{{ x == 3 }} x := x+1 {{ y == 4 }} ---> x == 3, y = 5 (in general y != 4)
{ true }} x := 100 {{ false }} ---> x: int, y: int
{{ 0 <= x }} x:=x-1 {{ 0 <= x }} ---> x == 0, y: int

*/

// 2.7, 2.8 ////////

/*
Predicate instead of ❓ so that triples hold. Weakest preconditions.

a) {{ ❓ }} x := 400 {{ x == 400 }} ---> true

b) {{ ❓ }} x := x + 3 {{ x is even }} ---> x is odd

c) {{ ❓ }} x := 65 {{ y <= x }} ---> y <= 65

d) {{ ❓ }} b := y < 10 {{ b ==> x < y }} ---> y < 10 ==> x < y 
  (also !(y < 10) || x < y, or 10 <= y || x < y)

e) {{ ❓ }} x, y := 2 * x, x + y {{ 0 <= x <= 100 && y <= x }} ---> 0 <= x <= 50 && y <= x

f) {{ ❓ }} x := 2 * y {{ 10 <= x <= y } ---> false (y <= 0 && y >= 5)

*/

// 2.11 ////////

/*
Predicate instead of ❓ so that triples hold. Weakest preconditions.

a) {{ ❓ }} x, y := 6, 7 {{ x < 10 && y <= z }} ---> z >= 7

b) {{ ❓ }} x, y := x + 1, 2 * x {{ y - x == 3 }} ---> x == 4

c) {{ ❓ }} x := x + 1; y := 2 * x {{ y - x == 3 }} ---> x == 2

*/

// 2.22 * ////////////////////////////

/*
Compute the weakest precondition for the following statement

if x < 10 {
  if x < 20 { y := 1; } else { y := 2; }
} else {
  y := 4;
}

with respect to

y % 2 == 0

(that is, “y is even”). Simplify the condition.

Answer --> 10 <= x

Notations: a = x < 10, b = x < 20, c = y := 1, d = y := 2, e = y := 4, f = y % 2 == 0
We need to compute g = WP[if a then (if b then c else d) else e, f]

g 
= // WP definition for "if then else" 
(a ==> WP[if b then c else d, f]) && (!a ==> WP[e, f])
= // expanding e, f
(a ==> WP[if b then c else d, y % 2 == 0]) && (!a ==> WP[y := 4, y % 2 == 0])
= // WP definition for :=
(a ==> WP[if b then c else d, y % 2 == 0]) && (!a ==> 4 % 2 == 0)
= //logic
(a ==> WP[if b then c else d, y % 2 == 0]) && (!a ==> true)
= //logic
(a ==> WP[if b then c else d, y % 2 == 0]) && (a || true)
= //logic
(a ==> WP[if b then c else d, y % 2 == 0]) && true
= //logic
a ==> WP[if b then c else d, y % 2 == 0]
= // WP definition for "if then else"
a ==> ((b ==> WP[c, y % 2 == 0]) && (!b ==> WP[d, y % 2 == 0]))
= //expanding c, d
a ==> ((b ==> WP[y := 1, y % 2 == 0]) && (!b ==> WP[y := 2, y % 2 == 0]))
= //WP definition for :=
a ==> ((b ==> 1 % 2 == 0) && (!b ==> 2 % 2 == 0))
= //logic
a ==> ((b ==> false) && (!b ==> true))
= //logic
a ==> ((!b || false) && (b || true))
= //logic
a ==> (!b && true)
= //logic
a ==> !b
= //logic
!a || !b
= // logic
!(a && b)
= // expanding a and b 
!(x < 10 && x < 20)
= // logic
!(x < 10)
= // logic
10 <= x
*/

// 2.25  ////////

/*
Which of the following Hoare-triple combinations are valid?
a.{{ 0 <= x }} x:=x+1 {{ -2 <= x }} y := 0 {{ -10 <= x }} 
---> valid, we strengthen conditions

b.{{ x < 2 }} y := x + 5; x := 2 * x {{ x < y }} 
---> valid, strengthening from x < 5 to x < 2

c.{ 0 <= x }} x := 3 * x; x:=x+1 {{ 3 <= x }} 
--->
not valid if x a real number, weakening: 
WP[x := 3*x; x := x + 1, 3 <= x] 
== 
2 <= 3*x 
== 
2/3 <= x
==> 
0 <= x 
If x an integer, then ok

d.{{ 0 <= x }} x:=x+1 {{ true }} x:=x+1 {{ 2 <= x }} 
--->
not valid, condition in the middle is not SP[x := x + 1, 0 <= x], nor WP[x := x + 1, 2 <= x].
However, {{0 <= x}} x := x + 1; x := x + 1 {{2 <= x}} holds, as shown in c) below.

e.{{ 0 <= x }} x:=x+1; x:=x+1 {{ 2 <= x }}
---> yes

*/

// 2.26 * ///////////////////////////

/*
Practice working backward over several assignment statements. Compute WP with respect to

x + y <= 100

for the following programs:

a) x := x + 1; y := x + y

b) y := x + y; x := x + 1;

c) x, y := x + 1, x + y

a) ---> 2 * x + y <= 98
b) ---> 2 * x + y <= 99
c) ---> 2 * x + y <= 99

*/

// 3.3 * ///////////////////////
function I(x: nat, y: nat): int 
decreases x + y
{
 if x == 0 || y == 0 then
  12
 else if x % 2 == y % 2 then 
        I(x - 1, y)
      else
        I(x, y - 1)
} 

// 3.5 * ///////////////////
function K(x: nat, y: nat, z: nat): int {
 if x < 10 || y < 5 then
  x+y
 else if z == 0 then
        K(x - 1, y, 5)
      else
        K(x, y - 1, z - 1)
}

// 3.9 * //////////////////
function N(x: int, y: int, b: bool): int 
decreases x, b
{ if x <= 0 || y <= 0 then
  x+y
 else if b then
        N(x, y + 3, !b)
      else
        N(x - 1, y, true)
}

// 3.12 * //////////////////
/* 
Suppose the university cracks down on professors to limit the required study time for a course to 200. We can then write a 
postcondition for method RequiredStudyTime:

method RequiredStudyTime(c: nat) returns (hours: nat)
ensures hours <= 200

Knowing such a bound, you can still use the termination metric n,h for Study, but it is also possible to write a termination 
metric without using a lexicographic tuple. Do so.
*/

method RequiredStudyTime(c: nat) returns (hours: nat)
ensures hours < 200

method Study(n: nat, h: nat)
decreases 200*n + h
{ 
  if h != 0 {
  // first study for an hour, and then:
  Study(n, h - 1);
  }
  else if n == 0 {
       // you just finished course 0, great, graduation time!
       } else {
    var hours := RequiredStudyTime(n - 1); //find out how much studying is needed for the next course
    //get started with course n-1:
    Study(n-1, hours);
         }
}
// Some explanation
// We need to compute what exactly decreases in the Study(n, h) method. This is 200*n + h (max 
// 200 hours per each course still to study (course 0, course 1, ... course n - 1) plus h hours
// remained to study for the current course, course n). However, this gives an error when calling
// Study(n-1, hours), because we need to prove 
// 200*n + h (= 200*(n-1) + 200 + h) > 200*(n-1) + hours
// As hours <= 200, from the above formula we are left with having to prove h > 0 when h is nat. 
// (on that branch actually h == 0)
// So of course the verifier cannot prove this, but with 201*n + h it has no problem to prove
// 201*n + h = 201*(n-1) + 201 + h > 201*(n-1) + hours, as hours < 201.
// Alternatively, if the postcondition was ensures hours < 200, then the termination metric
// 200*n + h works nicely.

// 3.13 //////////
//Add decreases clauses to prove termination of the following variation of the outer/ inner StudyPlan program from above.
method RequiredStudyTime1(c: nat) returns (hours: nat)
//a)

method Outer(a: nat)
decreases a
{
 if a != 0 {
  var b := RequiredStudyTime1(a - 1);
  Inner(a, b);
 }
}

method Inner(a: nat, b: nat)
 requires 1 <= a
 decreases a, b
{ 
 if b == 0 {
  Outer(a - 1);
 } else {
    Inner(a, b - 1);
   }
} 

//b)

method Outer1(a: nat)
decreases a
{
 if a!=0{
  var b := RequiredStudyTime1(a - 1);
  Inner1(a - 1, b);
 }
}

method Inner1(a: nat, b: nat)
decreases a + 1, b
{
 if b == 0{
  Outer1(a);
 } else {
    Inner1(a, b - 1);
   }
} 

// 4.1 and 4.3 ///////////////
/*
a) Write a function ReverseColors that takes a blue-white tree and returns a tree just like it, except with blue nodes 
turned into white nodes and white nodes turned into blue nodes.

b) Write a function Oceanize that takes a blue-white tree and returns a tree just like it, except with all leaf nodes 
turned into blue leaf nodes. 
*/

datatype BWTree = BlueLeaf | WhiteLeaf | Node(BWTree, BWTree)

// a)

function ReverseColors(t: BWTree) : BWTree {
  match t
    case BlueLeaf => WhiteLeaf
    case WhiteLeaf => BlueLeaf
    case Node(left, right) => Node(ReverseColors(left), ReverseColors(right))
}

method TestReverseColors() { 
  var a := Node(BlueLeaf, Node(BlueLeaf, WhiteLeaf)); 
  var b := Node(WhiteLeaf, Node(WhiteLeaf, BlueLeaf)); 
  assert ReverseColors(a) == b; 
  assert ReverseColors(b) == a; 
}

// b)

function Oceanize(t: BWTree) : BWTree {
  match t
    case BlueLeaf => BlueLeaf
    case WhiteLeaf => BlueLeaf
    case Node(left, right) => Node(Oceanize(left), Oceanize(right))
}