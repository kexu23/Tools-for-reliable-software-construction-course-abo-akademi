// Ex 12.3 

/*
Generalize function Power to any base. That is, deﬁne a function 

ghost function Exp(b: nat , n: nat ): nat 

that evaluates to b^^n. Write a method ComputeExp that computes Exp(b, n) in O ( n ) iterations.
 */

ghost function Exp(b: nat, n: nat): nat{
    if n == 0 then 1 else b*Exp(b, n-1)
}

method ComputeExp(b: nat, n: nat) returns (exp: nat) 
  ensures exp == Exp(b, n)
{
  exp := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant exp == Exp(b, i)
    //decreases n-i
  {
    exp := b * exp;
    i := i + 1;
  }
}

// Ex. 12.4

/*
Prove the following two lemmas about function Exp from Exercise 12.3: 

lemma ExpAddExponent(b: nat , m: nat , n: nat ) 
ensures Exp(b, m + n) == Exp(b, m) * Exp(b, n) 

lemma ExpSquareBase(b: nat , n: nat ) 
ensures Exp(b * b, n) == Exp(b, 2 * n)

 */

lemma ExpAddExponent(b: nat, m: nat, n: nat)
ensures Exp(b, m + n) == Exp(b, m) * Exp(b, n)
decreases m + n
{
    if m == 0 {}
    else if n == 0 {}
    else {
        assert m != 0 && n != 0;
        calc{
            Exp(b, m + n);
            ==
            b * Exp(b, m + n - 1);
            == {ExpAddExponent(b, m-1, n);}
            b * Exp(b, n-1) * Exp(b, m);
        }
    }
}

lemma ExpSquareBase(b: nat, n: nat)
ensures Exp(b * b, n) == Exp(b, 2*n)
{
}

// Ex 13.12

/*
Specify and write a method to compute the maximum of an array of type array <nat>. 
Allow the array to be empty, and in that case return 0 as the maximum.
 */

 method Max(a: array<nat>) returns (M: nat)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= M
  ensures (M == 0) || exists i :: 0 <= i < a.Length && M == a[i]
{
  M := 0;
  if a.Length == 0 {return ;}
  M := a[0];
  var n := 1;
  while n != a.Length
    invariant 1 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i]<= M
    invariant exists i :: 0 <= i < a.Length && M == a[i]
  {
    if M < a[n] {
      M := a[n];
    }
    n := n + 1;
  }
}

// Ex. 14.8

/*
Specify and implement a method  

method DoubleArray(src: array < int >, dst: array < int >) 

that sets dst[i] to 2 * src[i] for each i. Assume the given arrays have the same lengths, and allow the possibility that they 
reference the same array.
 */

method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  //requires src != dst
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var n := 0;
  while n != src.Length
    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    invariant forall i :: n <= i < src.Length ==> src[i] == old(src[i])
  {
    dst[n] := 2 * src[n];
    n := n + 1;
  }
}

method Test(a: array<int>, b: array<int>, c: array<int>, d: array<int>)
requires a.Length == b.Length == c.Length == d.Length
modifies b, c, d
{
  DoubleArray(a, b);
  DoubleArray(b, c);
  DoubleArray(c, d);
  assert forall i :: 0 <= i < a.Length ==> d[i] == 8 * old(a[i]);
}

// Ex. 14.13
// Do Exercise 14.7 using a forall statement.
/*
Ex. 14.7
Specify and implement a method that copies the elements of one matrix to another of the same dimensions. Allow the source and 
destination matrices to be the same and make sure your speciﬁcation says the right thing in that case. 
(Write a little test harness if you’re uncertain.)
 */

 method CopyMatrix<T>(src: array2<T>, dst: array2<T>)
  requires src.Length0 == dst.Length0
  requires src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < dst.Length0 && 0 <= j < dst.Length1 ==>
    dst[i, j] == old(src[i, j])
{
  forall i, j | 0 <= i < dst.Length0 && 0 <= j < dst.Length1 {
    dst[i, j] := src[i, j];
  }
}

method TestHarness() {
  var m := new int[2, 1];
  m[0, 0], m[1, 0] := 5, 7;
  CopyMatrix(m, m);
  // the following assertion will not hold if you forget
  // 'old' in the specification of CopyMatrix
  assert m[1, 0] == 7;
  var n := new int[2, 1];
  CopyMatrix(m, n);
  assert m[1, 0] == n[1, 0] == 7;
}

// Ex. 14.14
// Do Exercise 14.8 using a forall statement.
/*
Ex. 14.8
Specify and implement a method method 

DoubleArray(src: array < int >, dst: array < int >) 

that sets dst[i] to 2 * src[i] for each i. Assume the given arrays have the same lengths, and allow the possibility that they 
reference the same array.
 */

 method DoubleArrayForall(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  //requires src != dst
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  /*var n := 0;
  while n != src.Length
    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    invariant forall i :: n <= i < src.Length ==> src[i] == old(src[i])
  {
    dst[n] := 2 * src[n];
    n := n + 1;
  }
  */

  forall i | 0 <= i < src.Length {
    dst[i] := 2 * src[i];
  }
}

// Ex. 14.15
// Do Exercise 14.9 using a forall statement.
/*
Ex. 14.9
Specify and implement a method that reverses the elements of a given array.
 */

 method ReverseArray<T>(a: array<T>)
 modifies a 
 ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - i - 1])
 {
    forall i|0 <= i < a.Length {
        a[i] := a[a.Length - i - 1];
    }
 }

 // Ex. 14.16
// Do Exercise 14.10 using a forall statement.
/*
Ex. 14.10
Specify and implement a method that takes a square matrix and transposes its elements.
 */

 method Transpose<T>(a: array2<T>)
 requires a.Length0 == a.Length1
 modifies a
 ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[j, i])
 {
    forall i, j | 0 <= i < a.Length0 && 0 <= j < a.Length1 {
        a[i, j] := a[j, i];
    }
 }

