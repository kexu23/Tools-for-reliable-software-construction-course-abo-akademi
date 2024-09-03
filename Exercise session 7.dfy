datatype Color = Red  | White | Blue

ghost predicate Below(c: Color, d:Color) {
    c == Red || c == d || d == Blue
}

method Examples(){
    assert Below(Red,Blue);
    assert !Below(Blue, White);
}

method DutchFlag(a: array<Color>)
    modifies a 
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
    {
        if a.Length < 2 {return;}
        var r, w, b := 0, 0, a.Length;
        while w != b
            invariant 0 <= r <= w <= b <= a.Length
            invariant forall i :: 0 <= i < r ==> a[i] == Red
            invariant forall i :: r <= i < w ==> a[i] == White
            invariant forall i :: b <= i < a.Length ==> a[i] == Blue
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            if
                case a[w] == White =>
                    w := w + 1;
                case a[w] == Red =>
                    a[r], a[w] := a[w], a[r];
                    r, w := r + 1, w + 1;
                case a[w] == Blue =>
                    a[w], a[b-1] := a[b-1], a[w];
                    b := b - 1;
        }
    }

ghost predicate Less(c: bool, d: bool)
{
    c == false && d == true
}

ghost predicate CBelow<T>(color: T -> Color, x: T, y: T)

method DutchFlagKey<T>(a: array<T>, color: T -> Color)
    modifies a 
    ensures forall i, j :: 0 <= i < j < a.Length ==> CBelow(color, a[i], a[j])
    ensures multiset (a[..]) == old(multiset(a[..]))
{
    
}