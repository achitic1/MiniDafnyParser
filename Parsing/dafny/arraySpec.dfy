method ArrayTest(a : array<int>) returns (x : int)
  requires a.Length > 0
  requires forall i : int :: 0 <= i && i < a.Length ==> a[i] > 0
  ensures x > 0 
{
    x := a[0];
}