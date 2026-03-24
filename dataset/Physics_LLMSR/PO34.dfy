include "math_library.dfy"

method agent_PO34(beta: real, mu: real, omega02: real, gamma: real, t: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    requires mu >= 0.0
    requires omega02 >= 0.0
    requires gamma >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0 && v > 0.0 && v <= 1.0) ==> r <= 0.0
    ensures (t == 0.0 && x == 0.0 && v < 0.0 && v >= -1.0) ==> r >= 0.0
{
    var v2: real := v * v;
    
    var term1: real := 2.0 * beta * v;
    var term2_part: real := mu * (1.0 - v2);
    var term2: real := term2_part * v;
    var term3_part: real := omega02 * (gamma * t + 1.0);
    var term3: real := term3_part * x;
    var term4: real := omega02 * x;

    if (t == 0.0) {
        if (v == 0.0) {
            assert term1 == 0.0;
            assert v2 == 0.0;
            assert term2 == 0.0;
            
            assert term3_part == omega02;
            
            if (x == 0.0) {
                assert term3 == 0.0;
                assert term4 == 0.0;
            } else if (x > 0.0) {
                lemma_Mult_pos(term3_part, x);
                assert term3 >= 0.0;
                lemma_Mult_pos(omega02, x);
                assert term4 >= 0.0;
            } else if (x < 0.0) {
                lemma_mult_le_ge_zero(x, term3_part);
                assert term3 <= 0.0;
                lemma_mult_le_ge_zero(x, omega02);
                assert term4 <= 0.0;
            }
        } else if (x == 0.0) {
            assert term3 == 0.0;
            assert term4 == 0.0;
            
            if (v > 0.0 && v <= 1.0) {
                lemma_Mult_pos(2.0 * beta, v);
                assert term1 >= 0.0;
                
                lemma_Mult_symbolic_ub(v, v, 1.0);
                assert v2 <= 1.0;
                assert 1.0 - v2 >= 0.0;
                lemma_Mult_pos(mu, 1.0 - v2);
                assert term2_part >= 0.0;
                lemma_Mult_pos(term2_part, v);
                assert term2 >= 0.0;
            } else if (v < 0.0 && v >= -1.0) {
                lemma_mult_le_ge_zero(v, 2.0 * beta);
                assert term1 <= 0.0;
                
                lemma_square_even(v);
                var neg_v := -v;
                assert neg_v > 0.0 && neg_v <= 1.0;
                lemma_Mult_symbolic_ub(neg_v, neg_v, 1.0);
                assert v2 <= 1.0;
                assert 1.0 - v2 >= 0.0;
                lemma_Mult_pos(mu, 1.0 - v2);
                assert term2_part >= 0.0;
                lemma_mult_le_ge_zero(v, term2_part);
                assert term2 <= 0.0;
            }
        }
    }

    r := -term1 - term2 - term3 - term4;
}