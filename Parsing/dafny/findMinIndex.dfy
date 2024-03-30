method FindMinIndex (a : array<int>) returns (index : int)
{
  var min : int := a[0];
  var i : int := 0;
  index := 0;
  while (i < a.Length)
  {
    if a[i] < min {
        min := a[i]; 
        index := 1;
    }
    i := i+1;
  }
}
