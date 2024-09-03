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
assert 2 <= c - a || 200 <= a;
}

function Reduce(m: nat, x: int): int {
    if m == 0 then x else Reduce(m / 2, x + 1) - m
}

/*
lemma {:induction false} ReduceLowerBound(m: nat, x: int)
    ensures x - 2 * m <= Reduce(m, x)
{
    if m == 0 {
    } 
    else {
        calc {
            Reduce(m, x);
        ==  // def. Reduce
            Reduce(m / 2, x + 1) - m
        >=  {ReduceLowerBound(m / 2, x + 1);
                assert x + 1 - 2 * (m / 2) <= Reduce(m / 2, x + 1); }
            x + 1 - 2 * (m / 2) - m; 
        >=  {   assert 2 * (m / 2) <= m;}
            x + 1 - m - m;
        >   // reduce it further by 1
            x - 2 * m;
        }
    }
}
*/

datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function BlueCount(t: BYTree): nat {
    match t
    case BlueLeaf => 1
    case YellowLeaf => 0
    case Node(left, right) => BlueCount(left) + BlueCount(right)
}

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


lemma {:induction false} AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
    ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
    match xs
    case Nil => 
    case Cons(x, tail) =>
    calc{
        Append(Append(xs, ys), zs);
            == { assert xs == Cons(x, tail); }  // Replaces xs with Cons(x, tail)
            Append(Append(Cons(x, tail), ys), zs);
            == { assert Append(Cons(x, tail), ys) == Cons(x, Append(tail, ys)); }   // Changing second append
            Append(Cons(x, Append(tail, ys)), zs);
            == { assert Append(Cons(x, tail), zs) == Cons(x, Append(tail, zs)); }   // Changing first append
            Cons(x, Append(Append(tail, ys), zs));
            == { AppendAssociative(tail, ys, zs); } // Applying inductive hypothesis
            Cons(x, Append(tail, Append(ys, zs)));
            == { assert Append(xs, Append(ys, zs)) == Cons(x, Append(tail, Append(ys, zs))); }  // Replacing Cons
            Append(xs, Append(ys, zs)); // proof I think :D
        }
        
}



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
    // if xs is not an empty list
    if xs != Nil {
        // Sets x as the head of the list and xs' as the tail of the list
        var x := xs.head;
        var xs' := xs.tail;

        // Proves the lemma for Cons(x, xs')
        TakeDropAppend(xs', ys);

        assert Append(Cons(x, xs'), ys) == Cons(x, Append(xs', ys));

        assert Take(Cons(x, Append(xs', ys)), Length(Cons(x, xs'))) == Cons(x, Take(Append(xs', ys), Length(xs')));

        // Assert proves the first ensures statement
        assert Take(Append(xs', ys), Length(xs')) == xs';

        assert Drop(Cons(x, Append(xs', ys)), Length(Cons(x, xs'))) == Drop(Append(xs', ys), Length(xs'));

        // Assert proves the second ensures statement
        assert Drop(Append(xs', ys), Length(xs')) == ys;
    }
}


