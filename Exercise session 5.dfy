
/*module ImmutableQueue {
import LL = ListLibrary
type Queue<A>
function Empty(): Queue
function Enqueue<A>(q: Queue, a: A): Queue
function Dequeue<A>(q: Queue): (A, Queue)
requires q != Empty()
ghost function Elements(q: Queue): LL.List
lemma EmptyCorrect<A> ()
ensures Elements(Empty<A>()) == LL.Nil
lemma EnqueueCorrect<A>(q: Queue, x: A)
ensures Elements(Enqueue(q, x)) ==
LL.Snoc(Elements(q), x)
lemma DequeueCorrect(q: Queue)
requires q != Empty()
ensures var (a, q') := Dequeue(q);
LL.Cons(a, Elements(q')) == Elements(q)

export
            provides Queue, Empty, Enqueue, Dequeue
            provides LL, Elements
            provides EmptyCorrect, EnqueueCorrect, DequeueCorrect
}

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
    lemma AppendNil<T>(xs: List<T>)
    ensures Append(xs, Nil) == xs
    {}
    lemma AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
    ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
    {}
    function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
}
}



module QueueClient{
import IQ = ImmutableQueue
method Test() {
    IQ.EmptyCorrect<int>(); var q := IQ.Empty();
    IQ.EnqueueCorrect(q, 20); q := IQ.Enqueue(q, 20);
    IQ.DequeueCorrect(q); var (a, q') := IQ.Dequeue(q);
    assert a == 20;
    assert IQ.Elements(q') == IQ.LL.Nil;
    }
}



/*module PowersOf2 {
    function One(): P
    ensures P == 1     
    function Next(p: P): P
    ensures P == P^^2
    function Prev(p: P): P
}*/

*/

method Test110d(){
 var x := 3;
 while x < 2
 invariant x % 2 == 0
  assert x % 2 == 0;
}


method Test110b(){
 var x := 20;
 while 10 < x
  invariant x % 2 == 0
 assert x == 10;
}


method Test110a(){
 var x := 0;
 while x != 100
  invariant true
 assert x == 100;
}


method Test110f(x: int){
 if 0 <= x {
 while x % 2 == 0
  invariant x < 100
 assert 0 <= x;
 }
}


method Test110e(x: int){
 if 50 < x < 100 {
  while x < 85
   invariant x % 2 == 0
  assert x < 85 && x % 2 == 1;
 }
}


method Test110c(){
 var x := 20;
 while x < 20
  invariant x % 2 == 0
 assert x == 20;
}


method Test110g(){
 var x := 0;
 while x < 100
  invariant 0 <= x < 100
 assert x == 25;
}


method Test111a(){
 var i := 101;
 while i < 100
  invariant 0 <= i
  {i := i + 1;}
  
 assert i == 100;
}


method Test111c(){
 var i := 98;
 while i < 97
  invariant 0 <= i <= 99
  {i := i + 1;}
 assert i == 99;
}

method Test111d(){
 var i := 60;
 while i % 5 != 0
  invariant 10 <= i <= 100
  {i := i + 1;}
 assert i == 55;
}


method Test111b(){
 var i := -1;
 while 0 < i
  invariant true
 assert i == 0;
}

method Test112b(){
 var i := 100;
 while 0 < i
  invariant true && 0 <= i
 assert i == 0;
}

method Test112a(){
 var i := 0;
 while i < 100
  invariant 0 <= i <= 100
 assert i == 100;
}

method Test112c(){
 var i := 0;
 while i < 97
  invariant 0 <= i <= 99 && i % 3 == 0
 assert i == 99;
}

method Test112d(){
 var i := 22;
 while i % 5 != 0
  invariant 10 <= i <= 100 && i % 11 == 0
 assert i == 55;
}

// var x:= 0; loop guard x < 100 invariant true
// var x:= 298; loop guard x < 300 invariant x % 2 == 0
// var x:= 35; loop guard x % 2 == 1 invariant 0 <= x <= 100

method m(){
var x:= 0;
while x < 100
invariant true
 {x := x + 2;}
}

method n(){
var x:= 35;
assert x >= 0;
while x % 2 == 1
invariant 0 <= x <= 100
decreases x
 {if x >= 3 {x := x - 3;}
  else { x := 0;}
 }
}


method Ex116(){
var x := 0;
while x < 100
invariant x % 3 == 0 && 0 <= x <= 104
{
 x := x + 3;
}
assert x == 102;
}

// invariant 0 <= i <= N decreases i
// invariant 0 <= i <= N decreases N - i

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


method DownWhileGreater(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
 i := N;
 while 0 < i
 invariant 0 <= i <= N
 decreases i
 {
  i := i - 1;
 }
}


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


method DownWhileNotEqual(N: int) returns (i: int)
requires 0 <= N
ensures i == 0
{
 i := N;
 while i != 0
 invariant 0 <= i <= N
 decreases i
 {
  i := i - 1;
 }
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
 match xs
 case Nil => 0
 case Cons(_, tail) => 1 + Length(tail)
}

method Question10(d: int, n: int)
    requires n < 0
    // ensures n == n.Length
{
    var i := n;
    while 0 <= i 
}

method Cube(n : nat) returns (c: nat)
ensures c == n * n * n
{
    var m:= n;
    var a,b := 0,0;
    while m >= 0
    invariant 0 <= m <= n 
    invariant c == m * m * m
    invariant 4*m*m*m + 2*m*m + 2*m + 4
    invariant m + n
}

/*function DeleteMin(pq: PQueue): PQueue 
    requires !IsEmpty(pq)
{
    if pq.left == Leaf || pq.right == Leaf then pq.left
    else if pq.left.x <= pq.right.x then Node(pq.left.x, pq.left)
    else Node(pq.right.x, pq.right)*
} */