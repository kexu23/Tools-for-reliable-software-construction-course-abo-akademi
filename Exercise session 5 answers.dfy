// Ex 9.5
/*
How come we didn’t need (==) already when we compared q’ == IQ.Empty() in method Client() in Section 9.3.3? 
 */

module QueueClient{
  import 
    IQ = ImmutableQueue
  
  method Client() {
   IQ.EmptyCorrect<int>(); var q := IQ.Empty();
   IQ.EnqueueCorrect(q, 20); q := IQ.Enqueue(q, 20);
   IQ.DequeueCorrect(q);  var (a, q') := IQ.Dequeue(q);
  
   assert a == 20;
   assert IQ.Elements(q') == IQ.LL.Nil;
   IQ.EmptyUnique(q');
  
   assert q' == IQ.Empty();
  }
}

//Answer

// In Client() , we wrote that equality in an assert, which is a ghost statement. 
// In ghost contexts, Dafny supports equality for all types

///////////////////////////
// Queues

module ImmutableQueue {
  import LL = ListLibrary

  export   
    provides Queue, Empty, Enqueue, Dequeue, IsEmpty
    provides LL, Elements
    provides EmptyCorrect, EnqueueCorrect, DequeueCorrect, EmptyUnique

  datatype Queue<A> = FQ(front: LL.List<A>, rear: LL.List<A>)
 // type Queue(==)<A(==)> = Queue'<A>
 //datatype Queue'<A> = FQ(front: LL.List, rear: LL.List)


  function Empty<A>(): Queue {
	 FQ(LL.Nil, LL.Nil)
  }

  predicate IsEmpty(q: Queue) 
   ensures IsEmpty(q) <==> q == Empty()
  {
   q == FQ(LL.Nil, LL.Nil)
  }

  function Enqueue<A>(q: Queue, a: A): Queue{
	FQ(q.front, LL.Cons(a, q.rear))
    }

  function Dequeue<A>(q: Queue): (A, Queue)
	  requires q != Empty()
  {
  match q.front
  case Cons(x, front') => (x, FQ(front', q.rear))
  case Nil => //assert q.rear != LL.Nil;
              LL.ReverseCorrect(q.rear);
              var f := LL.Reverse(q.rear);
              (f.head, FQ(f.tail, LL.Nil))
  }

  ghost function Elements(q: Queue): LL.List {
  LL.Append(q.front, LL.Reverse(q.rear))
    }


  lemma EmptyCorrect<A> ()
    ensures Elements(Empty<A>()) == LL.Nil
  {}

  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Elements(Enqueue(q, x)) == LL.Snoc(Elements(q), x)


  lemma DequeueCorrect(q: Queue)
    requires q != Empty()
    ensures var (a, q') := Dequeue(q);
            LL.Cons(a, Elements(q')) == Elements(q)


  lemma EmptyUnique(q: Queue)
    ensures Elements(q) == LL.Nil ==> q == Empty() 

}

///////////////////////
// Extra Exercise
// a)

/*
Write a module PowersOf2 with a type P (from power) and three functions with the following signatures:

function One() : P
function Next(p: P) : P
function Prev(p: P): P

The idea is that

One() == 2^^0
Next(2^^n) == 2^^(n+1) == 2*(2^^n)
Prev(2^^n) == 2^^(n-1) == (2^^n)*(1/2), for n != 0
(where "^^" means "to the power of")

Include an export declaration in your module.
*/

module Powersof2a{

  export
    provides P, One, Next, Prev
  
  type P

  function One(): P

  function Next(p:P): P 

  function Prev(p: P): P 

}

// b) Design an abstraction function and lemmas that make this a usable module. 
// Write a simple client to test that these behave as you'd expect.

module Powersof2b{

  export
    provides P, One, Next, Prev
    provides Value, OneCorrect, NextCorrect, PrevCorrect, Even
  
  type P

  function One(): P

  function Next(p:P): P 

  function Prev(p: P): P 

  ghost function Value(p: P): nat

  lemma OneCorrect()
  ensures Value(One()) == 1

  lemma NextCorrect(p:P)
  ensures Value(Next(p)) == 2 * Value(p)

  lemma PrevCorrect(p:P)
  requires p != One()
  ensures Value(Prev(p)) == Value(p) / 2

  lemma Even(p:P)
  requires p != One()
  ensures Value(p) % 2 == 0

}

module PowersClient {
  import P2 = Powersof2c

  method Test(a: P2.P){
    var b := P2.One(); P2.OneCorrect(); 
    assert P2.Value(b) == 1;

    P2.NextCorrect(a); 
    assert P2.Value(P2.Next(a)) % 2 == 0;
   
    assert if a != P2.One() 
           then 
                P2.PrevCorrect(a);  P2.NextCorrect(P2.Prev(a)); P2.Even(a); P2.Value(a) == P2.Value(P2.Next(P2.Prev(a)))
           else P2.Value(a) == 1;
  }
}


// c) Implement the module

module Powersof2c{

  export
    reveals P
    provides One, Next, Prev
    provides Value, OneCorrect, NextCorrect, PrevCorrect, Even
  
  datatype P = Two(exp: nat)

  function One(): P{
    Two(0)
  }

  function Next(p:P): P {
    Two(p.exp + 1)
  }

  function Prev(p: P): P 
  requires p != One()
  {
    Two(p.exp - 1)
  }

  ghost function Value(p: P): nat
  decreases p.exp
  {
    if p.exp == 0 then 1 else 2*Value(Prev(p))
  }

  lemma OneCorrect()
  ensures Value(One()) == 1
  {}

  lemma NextCorrect(p:P)
  ensures Value(Next(p)) == 2 * Value(p)
  {
    assert p.exp + 1 != 0;
  }


  lemma PrevCorrect(p:P)
  requires p != One()
  ensures Value(Prev(p)) == Value(p) / 2
  {}

  lemma Even(p:P)
  requires p != One()
  ensures Value(p) % 2 == 0
  {}

}

module Powersof2 {
  
  export 
    provides P, One, Next, Prev, Exponent
    provides Value, OneCorrect, NextCorrect, PrevCorrect
  
  datatype P = Two(exp: nat)

  function One(): P {
    Two(0)
  }

  function Next(p: P): P{
    Two(p.exp + 1)
  } 
  function Prev(p: P): P
    requires p != One()
  {
    Two(p.exp - 1)
  }

 function Exponent(p: P): nat
 {p.exp}

  function Value(p: P): nat
  decreases Exponent(p)
  {
    if p.exp == 0 then 1 else 2*Value(Prev(p))
  }

  lemma OneCorrect()
  ensures Value(One()) == 1
  {}

  lemma NextCorrect(p: P)
  ensures assert Prev(Next(p)) == p; Value(Next(p)) == 2 * Value(p)
  {}

  lemma PrevCorrect(p: P)
  requires p != One()
  ensures 2*Value(Prev(p)) == Value(p)
  {}

  

}


// Ex. 10.3
/*
The very ﬁrst case of DeleteMin handles the situation when one or both subtrees are empty. In the if condition, 
I wrote the test as a disjunction (an “or”): 

pq.left == Leaf || pq.right == Leaf 

If the tree is balanced, then the condition pq.left == Leaf implies pq.right == Leaf, so the disjunction is equivalent 
to the simpler test 

pq.right == Leaf 

Why didn’t I write it that way? What happens if you change the condition to the simpler one?
 */



/* 
Verifier says: "destructor 'x' can only be applied to datatype values constructed by 'Node' "
The test on the next line cannot be held, because we are on the "else" branch of the first if, meaning pq.right is not a Leaf,
but pq.left might be a Leaf (or at least Dafny thinks so).

*/

// Ex 11.0
/*
For each of the following uses of loop speciﬁcations, indicate whether or not the loop-use proof obligation is met and 
whether or not the assertion following the loop can be proved to hold.
 */

// a) true, true

method Test110a(){
var x := 0;
while x != 100
  invariant true
assert x == 100;
}

// b) true, false

method Test110b(){
var x := 20;
while 10 < x
  invariant x % 2 == 0
assert x == 10;
}

// c) true, false

method Test110c(){
var x := 20;
while x < 20
  invariant x % 2 == 0
assert x == 20;
}

// d) false, true

method Test110d(){
var x := 3;
while x < 2
  invariant x % 2 == 0
assert x % 2 == 0;
}

// e) false, false

method Test110e(x: int){
if 50 < x < 100 {
while x < 85
  invariant x % 2 == 0
assert x < 85 && x % 2 == 1;
}
}

// f) false, false

method Test110f(x: int){
if 0 <= x {
while x % 2 == 0
  invariant x < 100
assert 0 <= x;
}
}

// g) true, true

method Test110g(){
var x := 0;
while x < 100
  invariant 0 <= x < 100
assert x == 25;
}

// Ex. 11.1
/*
For each program, give a possible value of i of type int after the loop that shows that the assertion is not provable.
 */

// a) 101

method Test111a(){
var i := 0;
while i < 100
  invariant 0 <= i
assert i == 100;
}

// b) -1

method Test111b(){
var i := 100;
while 0 < i
  invariant true
assert i == 0;
}

// c) 97 or 98

method Test111c(){
var i := 0;
while i < 97
  invariant 0 <= i <= 99
assert i == 99;
}

// d) 60

method Test111d(){
var i := 22;
while i % 5 != 0
  invariant 10 <= i <= 100
assert i == 55;
}

// Ex. 11.2
/*
For each program in Exercise 11.1, strengthen the invariant so that the invariant both holds on entry to the loop and 
suﬃces to prove the assertion.
 */

// a) invariant 0 <= i --> invariant 0 <= i <= 100

method Test112a(){
var i := 0;
while i < 100
  invariant 0 <= i <= 100
assert i == 100;
}

// b) invariant true --> invariant 0 <= i

method Test112b(){
var i := 100;
while 0 < i
  invariant 0 <= i
assert i == 0;
}

// c) invariant 0 <= i <= 99 --> invariant 0 <= i <= 99 && i % 3 == 0

method Test112c(){
var i := 0;
while i < 97
  invariant 0 <= i <= 99 && i % 3 == 0
assert i == 99;
}

// d) invariant 10 <= i <= 100 --> invariant 10 <= i <= 100 && i % 11 == 0

method Test112d(){
var i := 22;
while i % 5 != 0
  invariant 10 <= i <= 100 && i % 11 == 0
assert i == 55;
}

// Ex. 11.5
// Write an initializing assignment and a loop implementation for the following loop speciﬁcations: 

//a)
method Ex115a(){
  var x := 298;
  while x < 300
    invariant x % 2 == 0
    {x := x + 2;}
}

//b)
method Ex115b(){
  var x := 35;
  assert x >= 0;
  while x % 2 == 1
    invariant 0 <= x <= 100
    decreases x
    {if x >= 3 {x := x - 3;}
    else { x := 0;}
    }
}

// Ex. 11.6
// For the loop below, write a loop invariant that holds initially, is maintained by the loop body, and allows 
// you to prove the assertion after the loop. 

method Ex116(){
  var x := 0;
  while x < 100
  invariant x % 3 == 0 && 0 <= x <= 104
  {
    x := x + 3;
  }
  assert x == 102;
}

// Ex 11.7
// For each of the following methods, write a loop invariant and an (explicit) decreases clause that allow you to prove the method. 

method UpWhileLess(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i < N 
  invariant 0 <= i <= N
  decreases N - i
  {
    i := i + 1;
  }
}

method UpWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i != N 
  invariant 0 <= i <= N
  decreases N - i
  {
    i := i + 1;
  }
}

method DownWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == 0
{
  i := N;
  while i != 0
  invariant 0 <= i <= N
  //decreases i
  {
    i := i - 1;
  }
}

method DownWhileGreater(N: int) returns (i: int)
  requires 0 <= N
  ensures i == 0
{
  i := N;
  while 0 < i
  invariant 0 <= i <= N
  //decreases i
  {
    i := i - 1;
  }
}

// Ex. 11.8
/*
Using datatype List and function Length from Chapter 6, write a loop that constructs a List with a given value d repeated n times. Prove as a 
postcondition of the method that the returned list has length n.
*/

method ListLoop<T>(d: T, n: nat) returns (l: ListLibrary.List)
ensures ListLibrary.Length(l) == n
{
  var i := 0;
  l := ListLibrary.Nil;
  while i < n 
  invariant 0 <= i <= n 
  invariant ListLibrary.Length(l) == i
  {
    l := ListLibrary.Cons(d, l);
    i := i + 1;
  }
}

// Ex. 11.9
/*
Write a method Duplicate that takes a List (see Chapter 6) and returns a list twice as long. The elements of the new list can be anything you’d 
like—this exercise is concerned only with the length of the list. Prove the postcondition that the returned list is indeed twice as long as the 
original.
 */

method Duplicate<T>(l: ListLibrary.List) returns (d: ListLibrary.List)
ensures ListLibrary.Length(d) == 2 * ListLibrary.Length(l)
{
  d := l;
  match l 
  case Nil => 
  case Cons(head, tail) => 
    {
        var i, n := 0, ListLibrary.Length(l); 
        while i < n 
        invariant 0 <= i <= n 
        invariant n <= ListLibrary.Length(d) 
        invariant ListLibrary.Length(d) == i + n
        {
          d := ListLibrary.Cons(head, d);
          i := i + 1;
        }
    }
}

// Ex. 12.2
// Implement method Cube with a loop that iterates n times and only does addition (no multiplication).

// method Cube(n : nat) returns (c: nat)
// ensures c == n * n * n

method Cube(n : nat) returns (c: nat)
ensures c == n * n * n
{
    var m, k, v := 0, 1, 6;
    c := 0;
    while m < n
        invariant 0 <= m <= n 
        invariant c == m * m * m
        invariant k == 3*m*m + 3*m + 1
        invariant v == 6*m + 6
        {
            m, c, k, v := m + 1, c + k, k + v, v + 6;
        }
}

// Why?
/*
It's clear that we start by updating m to m + 1 and then we want the first 2 invariants. Also, note that in the invariants we can have 
multiplication, it's just in the implementation that we are not allowed to.

c == m^3 [m := m+1]
==
c == (m+1)^3
==
c == m^3 + 3*m^2 + 3*m + 1
== {k == 3*m^2 + 3*m + 1} //this is a wish!
c == c + k

We got the third invariant and c's update. We continue:

k == 3*m^2 + 3*m + 1 [m := m+1]
==
k == 3*(m+1)^2 + 3*(m+1) + 1
==
k == 3*m^2 + 6*m + 3 + 3*m + 3 + 1
== {v == 6*m + 6} // another wish!
k == k + v

We got the last invariant and k's update. How about updating v?

v == 6*m + 6 [m := m+1]
==
v == 6*(m+1) + 6
==
v == 6*m + 6 + 6
==
v == v + 6

And Bob's your uncle, as they say 💪
*/

///////
// Lists

module ListLibrary {
 
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Append<T>(xs: List<T>, ys: List<T>): List<T> 
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma LengthSnoc<T>(xs: List<T>, x: T)
  ensures Length(Snoc(xs, x)) == Length(xs) + 1
{
}

ghost function SlowReverse<T>(xs: List<T>): List<T>{
  match xs
  case Nil => Nil
  case Cons(x, tail) => Snoc(SlowReverse(tail), x)
}

lemma LengthSlowReverse<T>(xs: List<T>)
   ensures Length(SlowReverse(xs)) == Length(xs)
{
    match xs
    case Nil =>
    case Cons(x, tail) => 
        calc{
            Length(SlowReverse(xs));
            == // def of SlowReverse
            Length(Snoc(SlowReverse(tail), x));
            == {LengthSnoc(SlowReverse(tail), x);}
            Length(SlowReverse(tail)) + 1;
            == {LengthSlowReverse(tail);}
            Length(tail) + 1;
        }
}

function ReverseAux<T>(xs: List<T>, acc: List<T>): List<T>{
  match xs
  case Nil => acc
  case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
}

lemma SnocAppend<T>(xs: List<T>, y: T)
ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))

lemma AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))


lemma ReverseAuxSlowCorrect<T>(xs: List<T>, acc: List<T>)
  ensures ReverseAux(xs, acc) == Append(SlowReverse(xs), acc)
{
    match xs
    case Nil =>
    case Cons(x, tail) => 
        calc{
            Append(SlowReverse(xs), acc);
            == // Def SlowReverse
            Append(Snoc(SlowReverse(tail), x), acc);
            == {SnocAppend(SlowReverse(tail), x);}
            Append(Append(SlowReverse(tail),  Cons(x, Nil)), acc);
            == {AppendAssociative(SlowReverse(tail),  Cons(x, Nil), acc);}
            Append(SlowReverse(tail), Append(Cons(x, Nil), acc));
            == {assert Append(Cons(x, Nil), acc) == Cons(x, acc);}
            Append(SlowReverse(tail), Cons(x, acc));
            == {ReverseAuxSlowCorrect(tail, Cons(x, acc));}
            ReverseAux(tail, Cons(x, acc));
            == {}
            ReverseAux(xs, acc);
        }
} 

function Reverse<T>(xs: List<T>): List<T> {
   ReverseAux(xs, Nil)
}

lemma AppendNil(xs: List)
ensures Append(xs, Nil) == xs
{
    
}

lemma ReverseCorrect<T>(xs: List<T>)
  ensures Reverse(xs) == SlowReverse(xs)
{
    calc{
        Reverse(xs);
        == {}
        ReverseAux(xs, Nil);
        == {ReverseAuxSlowCorrect(xs, Nil);}
        Append(SlowReverse(xs), Nil);
        == {AppendNil(SlowReverse(xs));}
        SlowReverse(xs);
    }
}

lemma ReverseAuxCorrect'<T>(xs: List<T>, acc: List<T>)
ensures ReverseAux(xs, acc) == Append(Reverse(xs), acc)
{
    ReverseCorrect(xs);
    ReverseAuxSlowCorrect(xs, acc);
}

lemma LengthReverse'<T>(xs: List<T>)
ensures Length(Reverse(xs)) == Length(xs)
{
    ReverseCorrect(xs);
    LengthSlowReverse(xs);
}

lemma ReverseAuxAppend<T>(xs: List<T>, ys: List<T>, acc: List<T>)
ensures ReverseAux(Append(xs, ys), acc) == Append(Reverse(ys), ReverseAux(xs, acc))

lemma ReverseAppend<T>(xs: List<T>, ys: List<T>)
ensures Reverse(Append(xs, ys)) == Append(Reverse(ys), Reverse(xs))

function ReverseAux'<T>(xs: List<T>, acc: List<T>): List<T>
ensures ReverseAux'(xs, acc) == Append(SlowReverse(xs), acc)
{
    match xs
    case Nil => acc
    case Cons(x, tail) => 
        calc{
            Append(SlowReverse(xs), acc);
            == // Def SlowReverse
            Append(Snoc(SlowReverse(tail), x), acc);
            == {SnocAppend(SlowReverse(tail), x);}
            Append(Append(SlowReverse(tail),  Cons(x, Nil)), acc);
            == {AppendAssociative(SlowReverse(tail),  Cons(x, Nil), acc);}
            Append(SlowReverse(tail), Append(Cons(x, Nil), acc));
            == {assert Append(Cons(x, Nil), acc) == Cons(x, acc);}
            Append(SlowReverse(tail), Cons(x, acc));
            == //this lemma's postcondition
            ReverseAux'(tail, Cons(x, acc));
        }
    ReverseAux'(tail, Cons(x, acc))
}


}



// Priority Queues

module PriorityQueue {

export 
    provides PQueue, Empty, IsEmpty, Insert, RemoveMin
    provides Elements
    provides EmptyCorrect, IsEmptyCorrect, InsertCorrect, RemoveMinCorrect
    reveals IsMin
    provides Valid

type PQueue = BraunTree
  datatype BraunTree =
    | Leaf
    | Node(x: int, left: BraunTree, right: BraunTree)

ghost function Elements(pq:PQueue): multiset<int>{
  match pq
  case Leaf => multiset{}
  case Node(x, left, right) => multiset{x} + Elements(left) + Elements(right)
} 

ghost predicate IsMin(y: int, s: multiset<int>) {
    y in s && forall x:: x in s ==> y <= x
}
  
ghost predicate Valid(pq: PQueue){
  IsBinaryHeap(pq) && IsBalanced(pq)
}

ghost predicate IsBinaryHeap(pq: PQueue) {
match pq
case Leaf => true
case Node(x, left, right) =>
  IsBinaryHeap(left) &&    
  IsBinaryHeap(right) &&
  (left == Leaf || x <= left.x) &&
  (right == Leaf || x <= right.x)
}

ghost predicate IsBalanced(pq: PQueue) {
match pq    
case Leaf => true    
case Node(x, left, right) =>             
  IsBalanced(left) && IsBalanced(right) &&          
  var L, R := |Elements(left)|, 
              |Elements(right)|;        
  L == R || L == R + 1
}

function Empty(): PQueue{
    Leaf
}
  
predicate IsEmpty(pq: PQueue){
    pq == Leaf
}

function Insert(pq:PQueue, y: int): PQueue{
    match pq 
    case Leaf => Node(y, Leaf, Leaf)
    case Node(x, left, right) =>
    if y < x then Node(y, Insert(right, x), left)
             else Node(x, Insert(right, y), left)
    }

function RemoveMin(pq: PQueue): (int, PQueue)
  requires !IsEmpty(pq) 
{
  (pq.x, DeleteMin(pq))
}

function DeleteMin(pq: PQueue): PQueue
  requires !IsEmpty(pq) 
{
  if  pq.left == Leaf || pq.right == Leaf then pq.left
  else if pq.left.x <= pq.right.x then Node(pq.left.x, pq.right, DeleteMin(pq.left))
       else Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
}

function ReplaceRoot(pq: PQueue, y: int): PQueue
  requires !IsEmpty(pq)
{
  if pq.left == Leaf || (y <= pq.left.x && (pq.right == Leaf || y <= pq.right.x))
  then Node(y, pq.left, pq.right)
  else if pq.right == Leaf 
	     then assert y > pq.left.x; Node(pq.left.x, Node(y, Leaf, Leaf), Leaf)
       else if pq.left.x < pq.right.x 
	       then assert y > pq.left.x; Node(pq.left.x, ReplaceRoot(pq.left, y), pq.right)
         else assert y > pq.right.x; Node(pq.right.x, pq.left, ReplaceRoot(pq.right, y))
}

lemma EmptyCorrect()
  ensures Elements(Empty()) == multiset{}
  ensures Valid(Empty())
  {}

lemma IsEmptyCorrect(pq: PQueue)
  requires Valid(pq)
  ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
  {}

lemma InsertCorrect(pq:PQueue, y: int)
  requires Valid(pq)
  ensures Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
	 && Valid(Insert(pq, y))
{}


lemma RemoveMinCorrect(pq: PQueue)
  requires !IsEmpty(pq)
  requires Valid(pq)
  ensures var (y, pq') := RemoveMin(pq);
              IsMin(y, Elements(pq)) && Valid(pq') &&
              Elements(pq') + multiset{y} == Elements(pq)           
{
  DeleteMinCorrect(pq);
}

lemma ReplaceRootCorrect(pq: PQueue, y: int)
  requires Valid(pq) && !IsEmpty(pq)
  ensures var pq' := ReplaceRoot(pq, y);
	 Valid(pq') && Elements(pq) + multiset{y} ==  Elements(pq') + multiset{pq.x} &&
	 |Elements(pq')| == |Elements(pq)|


lemma DeleteMinCorrect(pq: PQueue)
  requires Valid(pq) && pq != Leaf
  ensures var pq' := DeleteMin(pq);
          Valid(pq') && 
          Elements(pq') + multiset{pq.x} == Elements(pq) &&
          |Elements(pq')| == |Elements(pq)| - 1


}