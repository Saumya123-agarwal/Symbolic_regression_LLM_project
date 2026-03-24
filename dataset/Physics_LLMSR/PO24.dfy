include "math_library.dfy"

method agent_PO24(F0: real, beta: real, omega02: real, t: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    requires omega02 >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0 && v > 0.0) ==> r <= 0.0
{
    var sin_t: real := sin(t);
    var abs_v: real := abs(v);
    var log_term: real := log(abs_v + 1.0);
    var abs_x: real := abs(x);
    var exp_x: real := exp(-abs_x);
    
    var term1: real := beta * log_term;
    var term2_part: real := omega02 * x;
    var term2: real := term2_part * exp_x;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (v == 0.0) {
            assert abs_v == 0.0;
            assert log_term == 0.0;
            assert term1 == 0.0;
            
            if (x == 0.0) {
                assert term2_part == 0.0;
                assert term2 == 0.0;
            } else if (x > 0.0) {
                lemma_Mult_pos(omega02, x);
                assert term2_part >= 0.0;
                lemma_Mult_pos(term2_part, exp_x);
                assert term2 >= 0.0;
            } else if (x < 0.0) {
                lemma_mult_le_ge_zero(x, omega02);
                assert term2_part <= 0.0;
                lemma_mult_le_ge_zero(term2_part, exp_x);
                assert term2 <= 0.0;
            }
        } else if (x == 0.0 && v > 0.0) {
            assert term2_part == 0.0;
            assert term2 == 0.0;
            
            assert abs_v + 1.0 > 1.0;
            lemma_Mult_pos(beta, log_term);
            assert term1 >= 0.0;
        }
    }

    r := F0 * sin_t - term1 - term2;
}