include "math_library.dfy"

method agent_PO8(x: real, v: real, alpha: real, beta: real, omega0: real) returns (r: real)
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= alpha
    requires 0.0 <= beta
    requires 0.0 <= omega0
    ensures r <= 0.0
    ensures (x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    var x3: real := x2 * x;
    lemma_Mult_pos(x2, x);

    var v2: real := v * v;
    lemma_Mult_pos(v, v);
    var v3: real := v2 * v;
    lemma_Mult_pos(v2, v);

    var av: real := abs(v);
    assert av >= 0.0;
    var powv: real := pow(av, 0.33);

    lemma_Mult_pos(alpha, v3);
    assert -(alpha * v3) <= 0.0;

    lemma_Mult_pos(beta, powv);
    assert -(beta * powv) <= 0.0;

    lemma_Mult_pos(w02, x3);
    assert -(w02 * x3) <= 0.0;

    r := -(alpha * v3) - (beta * powv) - (w02 * x3);
    assert r <= 0.0;

    if x == 0.0 && v == 0.0 {
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert v2 == 0.0;
        assert v3 == 0.0;
        assert av == v || av == -v;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert r == 0.0;
    }
}