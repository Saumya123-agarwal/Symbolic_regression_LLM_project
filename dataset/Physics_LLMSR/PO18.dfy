include "math_library.dfy"

method agent_PO18(F0: real, beta: real, omega02: real, t: real, v: real, x: real) returns (r: real)
    requires beta >= 0.0
    requires omega02 >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0 && v > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && x == 0.0 && v < 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var sin_x: real := sin(x);
    
    var term1: real := beta * sin_x * v;
    var term2: real := 2.0 * beta * v;
    var term3: real := omega02 * x;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (v == 0.0 && x == 0.0) {
            assert term1 == 0.0;
        } else if (v == 0.0) {
            assert term1 == 0.0;
            assert term2 == 0.0;
            if (x > 0.0) {
                lemma_Mult_pos(omega02, x);
                assert term3 >= 0.0;
            } else if (x < 0.0) {
                lemma_mult_le_ge_zero(x, omega02);
                assert term3 <= 0.0;
            }
        } else if (x == 0.0) {
            assert sin_x == 0.0;
            assert term1 == 0.0;
            assert term3 == 0.0;
            if (v > 0.0) {
                lemma_Mult_pos(2.0 * beta, v);
                assert term2 >= 0.0;
            } else if (v < 0.0) {
                lemma_mult_le_ge_zero(v, 2.0 * beta);
                assert term2 <= 0.0;
            }
        }
    }

    r := F0 * sin_t - term1 - term2 - term3;
}