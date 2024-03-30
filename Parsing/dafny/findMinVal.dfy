method FindMinVal (a : array<int>) returns (min : int)
  requires a.Length > 0
  ensures forall i : int :: (0 <= i && i < a.Length) ==> min <= a[i]
{
  min := a[0];
  var i : int := 1;
  while (i < a.Length)
  {
    if a[i] < min
    { min := a[i]; }
    i := i+1;
  }
}
