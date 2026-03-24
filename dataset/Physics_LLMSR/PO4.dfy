include "math_library.dfy"

method agent_PO4(F0: real, beta: real, t: real, v: real) returns (r: real)
    requires beta >= 0.0
    ensures (t == 0.0 && v == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v > 0.0 && sin(v) >= 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v < 0.0 && sin(v) <= 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var sin_v: real := sin(v);
    
    if (t == 0.0) {
        assert sin_t == 0.0;
    }
    
    r := F0 * sin_t - beta * sin_v - 2.0 * beta * v;
}