include "math_library.dfy"

method agent_PO22(F0: real, beta: real, t: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v > 0.0 && sin(x) >= 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v < 0.0 && sin(x) >= 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var sin_x: real := sin(x);
    
    var term1_part: real := beta * sin_x;
    var term1: real := term1_part * v;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (x == 0.0) {
            assert sin_x == 0.0;
            assert term1_part == 0.0;
            assert term1 == 0.0;
        } else if (sin(x) >= 0.0) {
            lemma_Mult_pos(beta, sin_x);
            assert term1_part >= 0.0;
            
            if (v > 0.0) {
                lemma_Mult_pos(term1_part, v);
                assert term1 >= 0.0;
            } else if (v < 0.0) {
                lemma_mult_le_ge_zero(v, term1_part);
                assert term1 <= 0.0;
            }
        }
    }

    r := F0 * sin_t - term1;
}