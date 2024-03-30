method MinMax (x : int, y : int) returns (min : int, max : int)
{
    if (x < y) {
        min := x;
        max := y;
    }
    else {
        max := x;
        min := y;
    }
}
