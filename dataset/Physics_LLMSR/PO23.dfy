include "math_library.dfy"

method agent_PO23(beta: real, mu: real, omega02: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    requires mu >= 0.0
    requires omega02 >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0 && v > 0.0) ==> r <= 0.0
    ensures (x == 0.0 && v < 0.0) ==> r >= 0.0
{
    var abs_x: real := abs(x);
    var exp_x: real := exp(-abs_x);
    var x2: real := x * x;
    var x3: real := x * x * x;
    
    var term1: real := 2.0 * beta * v;
    var term2_part: real := beta * exp_x;
    var term2: real := term2_part * v;
    var term3_part: real := mu * (1.0 - x2);
    var term3: real := term3_part * v;
    var term4: real := omega02 * x3;

    if (v == 0.0) {
        assert term1 == 0.0 && term2 == 0.0 && term3 == 0.0;
        if (x == 0.0) {
            assert x3 == 0.0;
            assert term4 == 0.0;
        } else if (x > 0.0) {
            lemma_cube_pos(x);
            lemma_Mult_pos(omega02, x3);
            assert term4 >= 0.0;
        } else if (x < 0.0) {
            lemma_cube_neg(x);
            lemma_mult_le_ge_zero(x3, omega02);
            assert term4 <= 0.0;
        }
    } else if (x == 0.0) {
        lemma_exp_zero();
        assert exp_x == 1.0;
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert term4 == 0.0;
        
        assert term3_part == mu;
        
        if (v > 0.0) {
            lemma_Mult_pos(2.0 * beta, v);
            assert term1 >= 0.0;
            
            lemma_Mult_pos(beta, exp_x);
            lemma_Mult_pos(term2_part, v);
            assert term2 >= 0.0;
            
            lemma_Mult_pos(term3_part, v);
            assert term3 >= 0.0;
        } else if (v < 0.0) {
            lemma_mult_le_ge_zero(v, 2.0 * beta);
            assert term1 <= 0.0;
            
            lemma_Mult_pos(beta, exp_x);
            lemma_mult_le_ge_zero(v, term2_part);
            assert term2 <= 0.0;
            
            lemma_mult_le_ge_zero(v, term3_part);
            assert term3 <= 0.0;
        }
    }

    r := -term1 - term2 - term3 - term4;
}