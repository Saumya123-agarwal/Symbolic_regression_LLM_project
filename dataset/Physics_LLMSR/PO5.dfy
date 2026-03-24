include "math_library.dfy"

method agent_PO5(F0: real, alpha: real, omega02: real, gamma: real, t: real, v: real, x: real) returns (r: real)
    requires alpha >= 0.0
    requires omega02 >= 0.0
    requires gamma >= 0.0
    ensures (t == 0.0 && v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (t == 0.0 && x == 0.0 && v > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && x == 0.0 && v < 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var v3: real := v * v * v;
    var abs_v: real := abs(v);
    var pow_term: real := pow(abs_v, 0.33);

    if (t == 0.0) {
        assert sin_t == 0.0;
        if (v == 0.0) {
            assert v3 == 0.0;
            lemma_pow_zero_base(0.33); 
        } else if (x == 0.0) {
            if (v > 0.0) {
                lemma_cube_pos(v);
            } else {
                lemma_cube_neg(v);
            }
        }
    }

    r := F0 * sin_t - alpha * v3 - omega02 * (gamma * pow_term + 1.0) * x - omega02 * x;
}