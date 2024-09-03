
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
 match xs
 case Nil => 0
 case Cons(_, tail) => 1 + Length(tail)
}
 
function ReverseAux<T>(xs: List<T>, acc: List<T>): List<T>{
 match xs
 case Nil => acc
 case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
}


function Reverse<T>(xs: List<T>): List<T> {
  ReverseAux(xs, Nil)
}


lemma {:induction false} LengthReverse<T>(xs: List<T>)
ensures Length(Reverse(xs)) == Length(xs)
{
    
    if xs != Nil {
        ReverseCorrect(xs);
        LengthSlowReverse(xs);

        assert Length(SlowReverse(xs)) == Length(xs);

        assert Length(Reverse(xs)) == Length(xs);

    }
    
}

lemma ReverseCorrect<T>(xs: List<T>)
ensures Reverse(xs) == SlowReverse(xs)

lemma LengthSlowReverse<T>(xs: List<T>)
ensures Length(SlowReverse(xs)) == Length(xs)

ghost function SlowReverse<T>(xs: List<T>): List<T>{
  match xs
  case Nil => Nil
  case Cons(x, tail) => Snoc(SlowReverse(tail), x)
}


function Snoc<T>(xs: List<T>, y: T): List<T> {
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail, y))
}
