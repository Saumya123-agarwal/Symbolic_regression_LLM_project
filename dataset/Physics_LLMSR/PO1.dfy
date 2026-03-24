include "math_library.dfy"

method agent_PO1(F0: real, beta: real, omega02: real, t: real, v: real, x: real) returns (r: real)
    requires omega02 >= 0.0
    requires beta >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var sin_v: real := sin(v);
    var x3: real := x * x * x;
    var abs_x: real := abs(x);
    var exp_term: real := exp(-abs_x);

    if (t == 0.0 && v == 0.0) {
        lemma_exp_zero();
        assert sin_t == 0.0;
        assert sin_v == 0.0;
        
        if (x > 0.0) {
            lemma_cube_pos(x);
            assert x3 >= 0.0;
        } else if (x < 0.0) {
            lemma_cube_neg(x);
            assert x3 <= 0.0;
        }
    }

    r := F0 * sin_t - beta * sin_v - omega02 * x3 - omega02 * x * exp_term;
}