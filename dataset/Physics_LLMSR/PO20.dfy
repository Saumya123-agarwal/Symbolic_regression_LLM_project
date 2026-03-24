include "math_library.dfy"

method agent_PO20(beta: real, omega02: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    requires omega02 >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0 && v > 0.0) ==> r <= 0.0
    ensures (x == 0.0 && v < 0.0) ==> r >= 0.0
{
    var term1: real := 2.0 * beta * v;
    var abs_x: real := abs(x);
    var exp_term: real := exp(-abs_x);
    
    var term2_part: real := omega02 * x;
    var term2: real := term2_part * exp_term;

    if (v == 0.0 && x == 0.0) {
        lemma_exp_zero();
        assert term1 == 0.0;
        assert term2_part == 0.0;
        assert term2 == 0.0;
    } else if (v == 0.0) {
        assert term1 == 0.0;
        if (x > 0.0) {
            lemma_Mult_pos(omega02, x);
            assert term2_part >= 0.0;
            
            lemma_Mult_pos(term2_part, exp_term);
            assert term2 >= 0.0;
        } else if (x < 0.0) {
            lemma_mult_le_ge_zero(x, omega02);
            assert term2_part <= 0.0;
            
            lemma_mult_le_ge_zero(term2_part, exp_term);
            assert term2 <= 0.0;
        }
    } else if (x == 0.0) {
        lemma_exp_zero();
        assert term2_part == 0.0;
        assert term2 == 0.0;
        if (v > 0.0) {
            lemma_Mult_pos(2.0 * beta, v);
            assert term1 >= 0.0;
        } else if (v < 0.0) {
            lemma_mult_le_ge_zero(v, 2.0 * beta);
            assert term1 <= 0.0;
        }
    }

    r := -term1 - term2;
}