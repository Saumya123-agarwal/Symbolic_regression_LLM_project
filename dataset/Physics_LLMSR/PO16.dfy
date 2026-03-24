include "math_library.dfy"

method agent_PO16(F0: real, omega02: real, gamma: real, t: real, v: real, x: real) returns (r: real)
    requires omega02 >= 0.0
    requires gamma >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0) ==> r == 0.0
{
    var sin_t: real := sin(t);
    var abs_v: real := abs(v);
    var pow_term: real := pow(abs_v, 0.33);
    var abs_x: real := abs(x);
    var exp_term: real := exp(-abs_x);

    var term1: real := omega02 * x;
    var factor: real := gamma * pow_term + 1.0;
    var term2: real := term1 * factor;
    var term3: real := term1 * exp_term;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (x == 0.0) {
            assert term1 == 0.0;
            assert term2 == 0.0;
            assert term3 == 0.0;
        } else if (v == 0.0) {
            lemma_pow_zero_base(0.33);
            assert pow_term == 0.0;
            assert factor == 1.0;
            
            if (x > 0.0) {
                lemma_Mult_pos(omega02, x);
                assert term1 >= 0.0;
                
                lemma_Mult_pos(term1, factor);
                assert term2 >= 0.0;
                
                lemma_Mult_pos(term1, exp_term);
                assert term3 >= 0.0;
            } else if (x < 0.0) {
                lemma_mult_le_ge_zero(x, omega02);
                assert term1 <= 0.0;
                
                // term1 is <= 0, factor is >= 0
                lemma_mult_le_ge_zero(term1, factor);
                assert term2 <= 0.0;
                
                // term1 is <= 0, exp_term is >= 0
                lemma_mult_le_ge_zero(term1, exp_term);
                assert term3 <= 0.0;
            }
        }
    }

    r := F0 * sin_t - term2 - term1 - term3;
}