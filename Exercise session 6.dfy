

ghost function Exp(b: nat , n: nat ): nat 
{
    if n == 0 then 1 else b * Exp(b, n-1)
}


method ComputeExp(b: nat, n: nat, i: nat) returns (exp: nat)
    ensures exp == Exp(b, i)
{
    while i != n
    invariant 0 <= i <= n
    decreases i
    {
        exp := Exp(b, i);
    }
    return exp;
}

lemma ExpAddExponent(b: nat , m: nat , n: nat )
ensures Exp(b, m + n) == Exp(b, m) * Exp(b, n) 

lemma ExpSquareBase(b: nat , n: nat )
ensures Exp(b * b, n) == Exp(b, 2 * n)


/* ------------------------------------------------------------- */

method Max1(a: array<nat>) returns (M: nat)
ensures forall i :: 0 <= i < a.Length ==> a[i] <= M
ensures (M == 0) || exists i :: 0 <= i < a.Length && M == a[i]

method Max2(a: array<nat>) returns (M: nat)
ensures exists i :: 0 <= i < a.Length && a[i] <= M
ensures forall i :: 0 <= i < a.Length ==> M == a[i]

method Max3(a: array<nat>) returns (M: nat)
ensures forall i :: 0 <= i < a.Length ==> a[i] <= M
ensures exists i :: 0 <= i < a.Length && M == a[i]
ensures M == 0

method Max4(a: array<nat>, M: nat) 
ensures forall i :: 0 <= i < a.Length ==> a[i] <= M
ensures exists i :: 0 <= i < a.Length && M == a[i]

method Max5(a: array<nat>) returns (M: nat)
ensures exists i :: 0 <= i < a.Length && M == a[i]
ensures (M == 0) || forall i :: 0 <= i < a.Length ==> a[i] <= M

/* ------------------------------------------------------------- */

method DoubleArray(src: array < int >, dst: array < int >) *