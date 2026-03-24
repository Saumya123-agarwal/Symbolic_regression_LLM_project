include "math_library.dfy"

method agent_PO32(omega02: real, gamma: real, v: real, x: real) returns (r: real)
    requires omega02 >= 0.0
    requires gamma >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0) ==> r == 0.0
{
    var abs_v: real := abs(v);
    var pow_term: real := pow(abs_v, 0.33);
    var factor: real := gamma * pow_term + 1.0;
    
    var x3: real := x * x * x;
    
    var term1_part: real := omega02 * x;
    var term1: real := term1_part * factor;
    var term2: real := omega02 * x3;

    if (x == 0.0) {
        assert term1_part == 0.0;
        assert term1 == 0.0;
        assert x3 == 0.0;
        assert term2 == 0.0;
    } else if (v == 0.0) {
        lemma_pow_zero_base(0.33);
        assert pow_term == 0.0;
        assert factor == 1.0;
        
        if (x > 0.0) {
            lemma_cube_pos(x);
            lemma_Mult_pos(omega02, x);
            assert term1_part >= 0.0;
            lemma_Mult_pos(term1_part, factor);
            assert term1 >= 0.0;
            
            lemma_Mult_pos(omega02, x3);
            assert term2 >= 0.0;
        } else if (x < 0.0) {
            lemma_cube_neg(x);
            lemma_mult_le_ge_zero(x, omega02);
            assert term1_part <= 0.0;
            lemma_mult_le_ge_zero(term1_part, factor);
            assert term1 <= 0.0;
            
            lemma_mult_le_ge_zero(x3, omega02);
            assert term2 <= 0.0;
        }
    }

    r := -term1 - term2;
}