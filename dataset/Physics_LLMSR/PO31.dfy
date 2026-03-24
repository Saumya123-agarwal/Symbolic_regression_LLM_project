include "math_library.dfy"

method agent_PO31(alpha: real, beta: real, omega02: real, v: real, x: real) returns (r: real)
    requires alpha >= 0.0
    requires beta >= 0.0
    requires omega02 >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0 && v > 0.0 && sin(v) >= 0.0) ==> r <= 0.0
    ensures (x == 0.0 && v < 0.0 && sin(v) <= 0.0) ==> r >= 0.0
{
    var v3: real := v * v * v;
    var x3: real := x * x * x;
    var sin_x: real := sin(x);
    var sin_v: real := sin(v);
    
    var term1: real := alpha * v3;
    var term2_part: real := beta * sin_x;
    var term2: real := term2_part * v;
    var term3: real := beta * sin_v;
    var term4: real := omega02 * x3;

    if (v == 0.0) {
        assert v3 == 0.0;
        assert sin_v == 0.0;
        assert term1 == 0.0;
        assert term2 == 0.0;
        assert term3 == 0.0;
        
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
        assert x3 == 0.0;
        assert sin_x == 0.0;
        assert term2_part == 0.0;
        assert term2 == 0.0;
        assert term4 == 0.0;
        
        if (v > 0.0 && sin_v >= 0.0) {
            lemma_cube_pos(v);
            lemma_Mult_pos(alpha, v3);
            assert term1 >= 0.0;
            
            lemma_Mult_pos(beta, sin_v);
            assert term3 >= 0.0;
        } else if (v < 0.0 && sin_v <= 0.0) {
            lemma_cube_neg(v);
            lemma_mult_le_ge_zero(v3, alpha);
            assert term1 <= 0.0;
            
            lemma_mult_le_ge_zero(sin_v, beta);
            assert term3 <= 0.0;
        }
    }

    r := -term1 - term2 - term3 - term4;
}