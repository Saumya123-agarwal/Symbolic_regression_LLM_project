include "math_library.dfy"

method agent_PO17(F0: real, beta: real, omega02: real, t: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    requires omega02 >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0 && v > 0.0 && sin(v) >= 0.0) ==> r <= 0.0
    ensures (t == 0.0 && x == 0.0 && v < 0.0 && sin(v) <= 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var sin_x: real := sin(x);
    var sin_v: real := sin(v);
    var x3: real := x * x * x;
    
    var term1: real := beta * sin_x * v;
    var term2: real := beta * sin_v;
    var term3: real := omega02 * x3;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (v == 0.0 && x == 0.0) {
            assert term1 == 0.0;
        } else if (v == 0.0) {
            assert term1 == 0.0;
            assert term2 == 0.0;
            if (x > 0.0) {
                lemma_cube_pos(x);
                lemma_Mult_pos(omega02, x3);
                assert term3 >= 0.0;
            } else if (x < 0.0) {
                lemma_cube_neg(x);
                lemma_mult_le_ge_zero(x3, omega02);
                assert term3 <= 0.0;
            }
        } else if (x == 0.0) {
            assert sin_x == 0.0;
            assert term1 == 0.0;
            assert term3 == 0.0;
            
            if (v > 0.0 && sin_v >= 0.0) {
                lemma_Mult_pos(beta, sin_v);
                assert term2 >= 0.0;
            } else if (v < 0.0 && sin_v <= 0.0) {
                lemma_mult_le_ge_zero(sin_v, beta);
                assert term2 <= 0.0;
            }
        }
    }

    r := F0 * sin_t - term1 - term2 - term3;
}