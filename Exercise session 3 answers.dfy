datatype BWTree = BlueLeaf | WhiteLeaf | Node(left: BWTree, right: BWTree)

// Ex. 4.5
/* 
Consider a predicate HasLeftTree on two blue-yellow trees, t and u, that determines whether or not t is an internal node with 
u as its left subtree. Implement this function in two diﬀerent ways, one using a match expression and one using a 
discriminator and destructor. How do you make sure the destructor meets its precondition?
*/

predicate HasLeftTree(t: BWTree, u: BWTree) {
    match t
    case BlueLeaf => false
    case WhiteLeaf => false
    case Node(left, right) => left == u 
}


predicate HasLeftTreeAgain(t: BWTree, u: BWTree) {
    if !t.Node? then false
    else t.left == u 
}

method Test1() {
    var t1 := Node(BlueLeaf, Node(BlueLeaf, WhiteLeaf));
    var t2 := BlueLeaf;
    var t3 := Node(Node(Node(BlueLeaf, Node(BlueLeaf, WhiteLeaf)), BlueLeaf), WhiteLeaf);
    var t4 := Node(Node(BlueLeaf, Node(BlueLeaf, WhiteLeaf)), BlueLeaf);
    assert HasLeftTree(t1, t2);
    assert HasLeftTreeAgain(t1, t2);
    assert !HasLeftTree(t3, t1);
    assert HasLeftTreeAgain(t4, t1);
}

// Ex 4.6

/*
Deﬁne a predicate IsSwedishColoredTree on colored trees that determines whether or not all leaves have colors that also 
appear in the Swedish ﬂag. 
*/

datatype Color = Blue | White | Red | Yellow
datatype ColoredTree = Leaf(Color) | InternalNode(ColoredTree, ColoredTree)

predicate IsSwedishFlagColor(c:Color) {
c.Blue? || c.Yellow?
}

predicate IsSwedishColoredTree(t: ColoredTree){
    match t
    case InternalNode(left, right) => IsSwedishColoredTree(left) && IsSwedishColoredTree(right)
    case Leaf(c) => IsSwedishFlagColor(c)
}

method Test2() {
    var t1 := InternalNode(Leaf(Blue), InternalNode(Leaf(Blue), Leaf(White)));
    var t2 := Leaf(Blue);
    var t3 := InternalNode(InternalNode(InternalNode(Leaf(Blue), InternalNode(Leaf(Blue), Leaf(Yellow))), Leaf(Blue)), Leaf(Yellow));
    var t4 := InternalNode(InternalNode(Leaf(Blue), InternalNode(Leaf(Blue), Leaf(White))), Leaf(Blue));
    assert !IsSwedishColoredTree(t1);
    assert IsSwedishColoredTree(t2);
    assert IsSwedishColoredTree(t3);
    assert !IsSwedishColoredTree(t4);
}

// Ex 5.0

//Assume we have

function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
ensures x < More(x) 

method ExampleLemmaUse(a: int){
    Increasing(a); 
    var b := More(a);
    var c := More(b);
    if a < 1000 {
        Increasing(More(a)); 
        assert 2 <= c - a; 
    }
    assert 2 <= c - a ; 
}

//Change the last assertion in the method to
// assert 2 <= c - a || 200 <= a; 

//What happens? Why?

method ExampleLemmaUse1(a: int){
    Increasing(a); 
    var b := More(a);
    var c := More(b);
    if a < 1000 {
        Increasing(More(a)); 
        assert 2 <= c - a; 
    }
    assert 2 <= c - a || 200 <= a; 
}

// The assertion "assert 2 <= c - a || 200 <= a;" is now verified. This is because, either 
// 2 <= c - a, which always holds when we take the if branch (a < 1000) or a >= 1000. The latter
// implies a >= 200.

// Ex 5.6

// State and prove a lemma LemmaAck(n : nat) that, for any natural number n, Ack(1, n) == n + 2 , 
// where Ack is the Ackermann function deﬁned in Section 3.3.1.

function Ack(m: nat, n: nat): nat
decreases m, n
{
  if m == 0 then n + 1
  else if n == 0 then Ack(m-1, 1)
  else Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} LemmaAck(n: nat ) 
ensures Ack(1, n) == n + 2 
{ 
  if n==0 {
        // trivial 
} else { 
     calc { 
        Ack(1, n); 
        == // def. Ack 
        Ack(0, Ack(1, n - 1)); 
        == // def. Ack(0, _ ) 
        Ack(1, n - 1) + 1; 
        == { LemmaAck(n - 1); } // induction hypothesis 
        (n - 1) + 2 + 1; 
        == // arithmetic 
        n + 2;
    } 
}
}

// Ex. 5.8

/*
Maybe we can prove a tighter lower bound. Try changing the postcondition of the lemma ReduceLowerBound in Section 5.5 
from x - 2*m <= Reduce(m, x) to x - 2*m < Reduce(m, x). What happens?
 */

 function Reduce(m: nat, x: int): int {
    if m == 0 then x else Reduce(m/2, x+1) - m
}

lemma ReduceUpperBound(m: nat, x :int)
    ensures Reduce(m,x) <= x 
{
}

 lemma {:induction false} ReduceLowerBound(m: nat, x :int)
    ensures x - 2*m <= Reduce(m,x) 
{
    if m == 0 {
        //trivial
    } else {
        calc {
              Reduce(m, x);
            == // def Reduce
              Reduce(m/2, x+1) - m;
            >= {ReduceLowerBound(m/2, x+1);
                assert x+1 - 2*(m/2) <= Reduce(m/2, x+1);}
              x + 1 - 2*(m/2) - m;
            >= {assert 2*(m/2) <= m;}
              x + 1 - m - m;
            ==
              x - 2*m + 1;
            >
              x - 2*m;
        }
    }
}

// If we changed the postcondition to "x - 2*m < Reduce(m,x)", then the "else" branch would 
// be fine, but the "then" branch would not, because it reduces to "x < x", which is false.

// Ex. 5.14
/*
Prove a lemma that shows BlueCount(t) <= BlueCount(Oceanize(t)) for any blue-white tree t 
from Section 4.0, where function BlueCount is deﬁned in Section 4.1 and function Oceanize 
is deﬁned in Exercise 4.3. For your proof, turn oﬀ automatic induction and use a calc statement in the Node case. 
 */

function BlueCount(t: BWTree): nat {
match t
  case BlueLeaf => 1
  case WhiteLeaf => 0
  case Node(left, right) => BlueCount(left) + BlueCount(right)
}

function Oceanize(t: BWTree) : BWTree {
  match t
    case BlueLeaf => BlueLeaf
    case WhiteLeaf => BlueLeaf
    case Node(left, right) => Node(Oceanize(left), Oceanize(right))
}

lemma {:induction false } OceanizeUpsBlueCount(t: BWTree) 
ensures BlueCount(t) <= BlueCount(Oceanize(t)) 
 { 
    match t 
    case BlueLeaf => 
    case WhiteLeaf => 
    case Node(left, right) => 
        calc { 
            BlueCount(Node(left, right)); 
            == // def. BlueCount 
            BlueCount(left) + BlueCount(right); 
            <= { OceanizeUpsBlueCount(left); } 
            BlueCount(Oceanize(left)) + BlueCount(right); 
            <= { OceanizeUpsBlueCount(right); } 
            BlueCount(Oceanize(left)) + BlueCount(Oceanize(right)); 
            == // def. BlueCount 
            BlueCount(Node(Oceanize(left), Oceanize(right))); 
            == // def. Oceanize 
            BlueCount(Oceanize(Node(left, right))); 
        } 
}

// Ex. 6.2

/*
Prove that Snoc is just a special case of Append , that is, that Snoc(xs, y) == Append(xs, Cons(y, Nil)).
 */

 datatype List<T> = Nil | Cons(head: T, tail: List<T>)

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

lemma {:induction false} SnocAppend<T>(xs: List<T>, y: T)
    ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
{
    match xs
    case Nil => 
    case Cons(x, tail) => 
    calc{
        Snoc(xs, y);
        == // def xs
        Snoc(Cons(x, tail), y);
        == // def Snoc when xs is Cons(x, tail)
        Cons(x, Snoc(tail, y));
        == {SnocAppend(tail, y);}
        Cons(x, Append(tail, Cons(y, Nil)));
        == // def Append
        Append(xs, Cons(y, Nil));
    }
}

// Here also a shorter solution holds
lemma {:induction false} SnocAppend'<T>(xs: List<T>, y: T)
    ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
{
    match xs
    case Nil => 
    case Cons(x, tail) => SnocAppend'(tail, y); 
}


// Ex. 6.4

//Mark AppendAssociative below with the attribute {:induction false} and give a manual proof of the lemma.

lemma {:induction false} AppendAssociative <T>(xs: List<T>, ys: List<T>, zs: List<T>)
ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
    match xs
    case Nil =>
    case Cons(x, tail) => calc{
                            Append(Append(xs, ys), zs);
                            == // def inner Append
                            Append(Cons(x, Append(tail, ys)), zs);
                            == // def outer Append
                            Cons(x, Append(Append(tail, ys), zs));
                            == {AppendAssociative(tail, ys, zs);}
                            Cons(x, Append(tail, Append(ys, zs)));
                            == //def Append
                            Append(Cons(x, tail), Append(ys, zs));
                            == // def xs
                            Append(xs, Append(ys, zs));
    }   
}



// Ex. 6.11
//Disable automatic induction and prove lemma TakeDropAppend.

function Length<T>(xs: List<T>): nat {
 match xs
 case Nil => 0
 case Cons(_, tail) => 1 + Length(tail)
}

lemma LengthAppend<T>(xs: List<T>, ys: List<T>)
ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)

function Take<T>(xs: List<T>, n: nat): List<T>
  requires n <= Length(xs)
{
  if n == 0 then Nil else Cons(xs.head, Take(xs.tail, n-1))
}

function Drop<T>(xs: List<T>, n: nat): List<T>
  requires n <= Length(xs)
{
  if n == 0 then xs else Drop(xs.tail, n-1)
}

lemma {:induction false} TakeDropAppend<T>(xs: List<T>, ys: List<T>)
  ensures Take(Append(xs, ys), Length(xs)) == xs
  ensures Drop(Append(xs, ys), Length(xs)) == ys
{
    match xs
    case Nil => {}
    case Cons(x, tail) => {
        var len := Length(xs);
        calc {
            Take(Append(xs, ys), Length(xs));
            == //def len
            Take(Append(xs, ys), len);
            == //def Take, len != 0
            Cons(Append(xs, ys).head, Take(Append(xs, ys).tail, len - 1));
            == // trying Dafny's knowledge on Append, successfully
            Cons(x, Take(Append(xs, ys).tail, len - 1));
            == // trying Dafny's knowledge on Append, successfully again
            Cons(x, Take(Append(tail, ys), len - 1));
            =={TakeDropAppend(tail, ys);} //induction hypothesis
            Cons(x, tail); // from here on verifier has no protests
        }
        calc{
            Drop(Append(xs, ys), Length(xs));
            == //def len
            Drop(Append(xs, ys), len);
            == //def Drop, len != 0
            Drop(Append(xs, ys).tail, len - 1);
            == // trying Dafny's knowledge on Append, successfully
            Drop(Append(tail, ys), len - 1);
            == {TakeDropAppend(tail, ys);} //induction hypothesis
            ys;
        }
    }
}



//Ex. 6.15

// Prove lemma AtFind, with and without automatic induction. 

function Find<T(==)>(xs: List<T>, y: T): nat
 ensures Find(xs, y) <= Length(xs)
{
  match xs
  case Nil => 0
  case Cons(x, tail) => if x == y then 0 else 1 + Find(tail, y)
}

function At<T>(xs: List<T>, i: nat): T
 requires i < Length(xs)
{
 if i == 0 then xs.head else At(xs.tail, i-1)
}

lemma {:induction false} AtFind<T>(xs: List, y: T)
ensures Find(xs, y) == Length(xs) || At(xs, Find(xs, y)) == y
{
    match xs
    case Nil =>
    case Cons(x, tail) => {
        // assert Length(xs) > 0;
        if Find(xs, y) == Length(xs) {}
        else {
            // assert Find(xs, y) < Length(xs);
            calc {
                At(xs, Find(xs, y));
                == // def of xs and Find
                At(Cons(x, tail), if x == y then 0 else 1 + Find(tail, y));
                == {AtFind(tail, y);} //just throwing the induction hypothesis at Dafny
                y;
            }
        }
    
    }
}

lemma AtFind'<T>(xs: List, y: T)
ensures Find(xs, y) == Length(xs) || At(xs, Find(xs, y)) == y

