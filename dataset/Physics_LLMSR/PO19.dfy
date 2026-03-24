include "math_library.dfy"

method agent_PO19(beta: real, omega02: real, v: real, x: real) returns (r: real)
    requires omega02 >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0) ==> r == 0.0
{
    var sin_x: real := sin(x);
    var term1: real := beta * sin_x * v;
    var term2: real := omega02 * x;

    if (x == 0.0) {
        assert sin_x == 0.0;
        assert term1 == 0.0;
        assert term2 == 0.0;
    } else if (v == 0.0) {
        assert term1 == 0.0;
        if (x > 0.0) {
            lemma_Mult_pos(omega02, x);
            assert term2 >= 0.0;
        } else if (x < 0.0) {
            lemma_mult_le_ge_zero(x, omega02);
            assert term2 <= 0.0;
        }
    }

    r := -term1 - term2;
}