include "math_library.dfy"

method agent_PO13(t: real, x: real, v: real, F0: real, alpha: real, beta: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= alpha
    requires 0.0 <= beta
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var s: real := sin(t);

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var gt: real := gamma * t;
    lemma_Mult_pos(gamma, t);
    assert gt >= 0.0;

    var inner: real := gt + 1.0;
    assert inner >= 1.0;

    var x2: real := x * x;
    lemma_Mult_pos(x, x);

    var v2: real := v * v;
    lemma_Mult_pos(v, v);
    var v3: real := v2 * v;
    lemma_Mult_pos(v2, v);

    var av: real := abs(v);
    assert av >= 0.0;

    var powv: real := pow(av, 0.33);

    var wi: real := w02 * inner;
    lemma_Mult_pos(w02, inner);
    assert wi >= 0.0;

    assert s <= 1.0;
    lemma_Mult_symbolic_ub(F0, s, 1.0);
    assert F0 * s <= F0;

    lemma_Mult_pos(alpha, v3);
    assert -(alpha * v3) <= 0.0;

    lemma_Mult_pos(beta, powv);
    assert -(beta * powv) <= 0.0;

    lemma_Mult_pos(wi, x);
    assert -(wi * x) <= 0.0;

    lemma_Mult_pos(w02, x);
    assert -(w02 * x) <= 0.0;

    r := F0 * s - (alpha * v3) - (beta * powv) - (wi * x) - (w02 * x);
    assert r <= F0;

    if t == 0.0 {
        assert s == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && x == 0.0 && v == 0.0 {
        assert s == 0.0;
        assert x2 == 0.0;
        assert v2 == 0.0;
        assert v3 == 0.0;
        assert av == v || av == -v;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert r == 0.0;
    }
}