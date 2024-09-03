/* Ex. 6.19

Prove 

Length(ReverseAux(xs, acc)) == Length(xs) + Length(acc),

for any lists xs and acc. 
*/

lemma {:induction false} ReverseAuxLength<T>(xs: List<T>, acc: List<T>)
ensures Length(ReverseAux(xs, acc)) == Length(xs) + Length(acc)
decreases xs
{
    match xs
    case Nil => 
    case Cons(x, tail) => 
        calc{
            Length(ReverseAux(xs, acc));
            == //def ReverseAux
            Length(ReverseAux(tail, Cons(x, acc)));
            == {ReverseAuxLength(tail, Cons(x, acc));}
            Length(tail) + Length(Cons(x, acc));
            == //def Length
            Length(tail) + 1 + Length(acc);
            == // def xs
            Length(xs) + Length(acc);
        }
}

/*
Ex. 6.20

Write an alternative proof for LengthReverse that uses the lemma in Ex. 6.19. 

*/

/*
function Reverse<T>(xs: List<T>): List<T> {
   ReverseAux(xs, Nil)
}
*/

lemma {:induction false} LengthReverse<T>(xs: List<T>)
ensures Length(Reverse(xs)) == Length(xs)
{
    //ReverseCorrect(xs);
    //LengthSlowReverse(xs);
    calc{
       Length(Reverse(xs));
       == // def Reverse
       Length(ReverseAux(xs, Nil));
       == {ReverseAuxLength(xs, Nil);}
       Length(xs);
    }
}

/*
Ex. 6.25 
In Section 6.4, we came across an initial problem with stating lemma AtDropHead,  because the expression in the proof goal 
was not well-deﬁned by itself. State a lemma
*/

lemma {:induction false} DropLessThanEverything<T>(xs: List<T>, i: nat) 
requires i < Length(xs) 
ensures Drop(xs, i).Cons? 
{
    if i != 0 
    {match xs
    case Nil =>
    case Cons(x, tail) => calc{
        Drop(xs, i);
        ==
        Drop(tail, i-1);
        == {DropLessThanEverything(tail, i-1);}
        Cons(Drop(tail, i-1).head, Drop(tail, i-1).tail);
    }
    }
}

/* 

and use this lemma in the proof goal of the original attempt at writing lemma AtDropHead. 

Then, prove both DropLessThanEverything and your new AtDropHead. 

*/

//lemma AtDropHead<T>(xs: List<T>, i: nat)
//  requires i < Length(xs)
//  ensures Drop(xs, i).Cons? && At(xs, i) == Drop(xs, i).head
//{}

lemma {:induction false} AtDropHead'<T>(xs: List<T>, i: nat)
  requires i < Length(xs)
  ensures (DropLessThanEverything(xs, i); At(xs, i) == Drop(xs, i).head)
{
    if i == 0 {
    }
    else {
        calc{
            At(xs, i);
            == {assert 0 < i < Length(xs);} //def At
            At(xs.tail, i - 1);
            == {AtDropHead'(xs.tail, i-1); DropLessThanEverything(xs.tail, i-1);}
            Drop(xs.tail, i-1).head;
            == //def Drop
            Drop(xs, i).head;
        }
    }
}

// Ex. 8.0
//Generalize the deﬁnition of Count beyond integer lists. What type characteristic is needed of the list’s element type? 

function CountGeneral<T(==)>(xs: List<T>, p: T): nat {
  match xs
  case Nil => 0
  case Cons(x, tail) => (if x == p then 1 else 0) + CountGeneral(tail, p)
}

//From Lecture 6

ghost function Count(xs: List<int>, p: int): nat {
  match xs
  case Nil => 0
  case Cons(x, tail) => (if x == p then 1 else 0) + Count(tail, p)
}


ghost function Project(xs: List<int>, p: int): List<int> {
  match xs
  case Nil => Nil
  case Cons(x, tail) => if x == p then Cons(p, Project(tail, p)) 
		                          else Project(tail, p)
}

ghost function ProjectGeneral<T>(xs: List<T>, p: T): List<T> {
  match xs
  case Nil => Nil
  case Cons(x, tail) => if x == p then Cons(p, ProjectGeneral (tail, p)) 
		                          else ProjectGeneral(tail, p)
}

// Ex. 8.1
// For any p and any two lists that, after projection to p, are equal, state and prove a lemma that says the two lists have 
//the same occurrence count of p.

lemma  {:induction false} LengthProject<T>(xs: List<T>, p: T) 
ensures Length(ProjectGeneral(xs, p)) == CountGeneral(xs, p)
{
  match xs
  case Nil =>
  case Cons(x, tail) => 
    calc{
      Length(ProjectGeneral(xs, p));
      ==
      Length(ProjectGeneral(Cons(x, tail), p));
      ==
      Length(if x == p then Cons(p, ProjectGeneral (tail, p)) 
		                          else ProjectGeneral(tail, p));
      ==
      if x == p then Length(Cons(p, ProjectGeneral (tail, p)))
                else Length(ProjectGeneral (tail, p));
      == {LengthProject(tail, p);}
      if x == p then 1 + Length(ProjectGeneral (tail, p))
                else CountGeneral(tail, p);
      == {LengthProject(tail, p);}
      if x == p then 1 + CountGeneral(tail, p)
                else CountGeneral(tail, p);
    }
}

lemma {:induction false} StabilityImpliesOccurrence<T>(xs: List<T>, ys: List<T>, p: T)
requires ProjectGeneral(xs, p) == ProjectGeneral(ys, p)
ensures CountGeneral(xs, p) == CountGeneral(ys, p)
{
  calc{
    CountGeneral(xs, p);
    == {LengthProject(xs, p);}
    Length(ProjectGeneral(xs, p));
    == // precondition
    Length(ProjectGeneral(ys,p));
    == {LengthProject(ys, p);}
    CountGeneral(ys, p);
  }   
}

//Ex. 9.0
/*
Function Elements provides an abstraction of the queue implementation. Another, more coarse-grained, abstraction would have 
been to instead introduce a function 
*/

//ghost function Length(q: Queue): nat 

/*
that returns the number of elements in the queue. 

Write a module interface that uses Length instead of Elements. 
*/
module ImmutableQueueTooSimple {
 type Queue<A>
 function Empty(): Queue
 function Enqueue<A>(q: Queue, a: A): Queue
 function Dequeue<A>(q: Queue): (A, Queue)
   requires q != Empty()
}

module ImmutableQueue {
  //import LL = ListLibrary

  type Queue<A>
  function Empty(): Queue
  function Enqueue<A>(q: Queue, a: A): Queue
  function Dequeue<A>(q: Queue): (A, Queue)
	  requires q != Empty()

  //ghost function Elements(q: Queue): LL.List 
  ghost function Length(q: Queue): nat 

  //lemma EmptyCorrect<A> ()
  //  ensures Elements(Empty<A>()) == LL.Nil
  lemma EmptyCorrect<A>() 
  ensures Length(Empty<A>()) == 0

  //lemma EnqueueCorrect<A>(q: Queue, x: A)
  //  ensures Elements(Enqueue(q, x)) == LL.Snoc(Elements(q), x)
  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Length(Enqueue(q, x)) == Length(q) + 1

  //lemma DequeueCorrect(q: Queue)
  //  requires q != Empty()
  //  ensures var (a, q') := Dequeue(q);
  //          LL.Cons(a, Elements(q')) == Elements(q)
  lemma DequeueCorrect<A>(q: Queue)
    requires q != Empty()
    ensures var (a, q') := Dequeue(q);
            Length(q') == Length(q) - 1
}

//////////////////////////
// from Lecture 5

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
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

function Append<T>(xs: List<T>, ys: List<T>): List<T>
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

function Take<T>(xs: List<T>, n: nat): List<T>
  requires n <= Length(xs)
{
  if n == 0 then Nil else Cons(xs.head, Take(xs.tail, n - 1))
}

function Drop<T>(xs: List<T>, i: nat): List<T>
  requires i <= Length(xs)
{
  if i == 0 then xs else Drop(xs.tail, i - 1)
}


lemma AppendTakeDrop<T>(xs: List<T>, n: nat)
  requires n <= Length(xs)
  ensures Append(Take(xs, n), Drop(xs, n)) == xs
{
}

lemma TakeDropAppend<T>(xs: List<T>, ys: List<T>)
  ensures Take(Append(xs, ys), Length(xs)) == xs
  ensures Drop(Append(xs, ys), Length(xs)) == ys
{
}

function At<T>(xs: List<T>, i: nat): T
  requires i < Length(xs)
{
  if i == 0 then xs.head else At(xs.tail, i - 1)
}

lemma AtDropHead<T>(xs: List<T>, i: nat)
  requires i < Length(xs)
  ensures Drop(xs, i).Cons? && At(xs, i) == Drop(xs, i).head
{
}

lemma AtAppend<T>(xs: List<T>, ys: List<T>, i: nat)
  requires i < Length(Append(xs, ys))
  ensures At(Append(xs, ys), i)
       == if i < Length(xs) then
            At(xs, i)
          else
            At(ys, i - Length(xs))
{
}


// Lecture 6, more lists

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

function ReverseAux''<T>(xs: List<T>, acc: List<T>): List<T>
  ensures ReverseAux''(xs, acc) == Append(SlowReverse(xs), acc)
{
  match xs
  case Nil => acc
  case Cons(x,tail) => 
      ReverseAuxHelper(xs, acc);
      ReverseAux''(tail, Cons(x, acc))
} 

lemma ReverseAuxHelper<T>(xs: List<T>, acc: List<T>)
  requires xs.Cons?
  ensures ReverseAux''(xs.tail, Cons(xs.head, acc)) == Append(SlowReverse(xs), acc)
  decreases xs, acc, 0
{
  var x, tail := xs.head, xs.tail;
    calc{
     Append(SlowReverse(xs), acc);
     ==
     Append(Snoc(SlowReverse(tail), x), acc);
    == {SnocAppend(SlowReverse(tail), x);}
    Append(Append(SlowReverse(tail), Cons(x, Nil)), acc);
     == {AppendAssociative(SlowReverse(tail), Cons(x, Nil), acc);}
    Append(SlowReverse(tail), Append(Cons(x, Nil), acc));
    == // postcondition of ReverseAux’’
    ReverseAux''(tail, Cons(x, acc));
    }
}

lemma AtReverse<T>(xs: List<T>, i: nat)
requires i < Length(xs)
ensures (LengthReverse'(xs);  At(xs,i) == At(Reverse(xs), Length(xs) - i - 1))

