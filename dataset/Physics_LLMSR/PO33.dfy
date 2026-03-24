include "math_library.dfy"

method agent_PO33(F0: real, alpha: real, beta: real, omega02: real, t: real, v: real, x: real) returns (r: real)
    requires alpha >= 0.0
    requires beta >= 0.0
    requires omega02 >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0 && v > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && x == 0.0 && v < 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var v3: real := v * v * v;
    var x3: real := x * x * x;
    var abs_v: real := abs(v);
    var exp_v: real := exp(-abs_v);
    
    var term1: real := alpha * v3;
    var term2_part: real := beta * exp_v;
    var term2: real := term2_part * v;
    var term3: real := omega02 * x3;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (v == 0.0) {
            assert v3 == 0.0;
            assert term1 == 0.0;
            assert term2 == 0.0;
            
            if (x == 0.0) {
                assert x3 == 0.0;
                assert term3 == 0.0;
            } else if (x > 0.0) {
                lemma_cube_pos(x);
                lemma_Mult_pos(omega02, x3);
                assert term3 >= 0.0;
            } else if (x < 0.0) {
                lemma_cube_neg(x);
                lemma_mult_le_ge_zero(x3, omega02);
                assert term3 <= 0.0;
            }
        } else if (x == 0.0) {
            assert x3 == 0.0;
            assert term3 == 0.0;
            
            if (v > 0.0) {
                lemma_cube_pos(v);
                lemma_Mult_pos(alpha, v3);
                assert term1 >= 0.0;
                
                lemma_Mult_pos(beta, exp_v);
                lemma_Mult_pos(term2_part, v);
                assert term2 >= 0.0;
            } else if (v < 0.0) {
                lemma_cube_neg(v);
                lemma_mult_le_ge_zero(v3, alpha);
                assert term1 <= 0.0;
                
                lemma_Mult_pos(beta, exp_v);
                lemma_mult_le_ge_zero(v, term2_part);
                assert term2 <= 0.0;
            }
        }
    }

    r := F0 * sin_t - term1 - term2 - term3;
}