include "math_library.dfy"

method agent_PO10(t: real, x: real, v: real, F0: real, mu: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= mu
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var s: real := sin(t);
    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    assert s <= 1.0;
    lemma_Mult_symbolic_ub(F0, s, 1.0);
    assert F0 * s <= F0;

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    lemma_Mult_symbolic_ub(x, x, 1.0);
    assert x2 <= x;
    assert x2 <= 1.0;
    assert 0.0 <= 1.0 - x2;

    var av: real := abs(v);
    assert av >= 0.0;
    var powv: real := pow(av, 0.33);

    var gp: real := gamma * powv;
    lemma_Mult_pos(gamma, powv);
    assert gp >= 0.0;

    var inner: real := gp + 1.0;
    assert inner >= 1.0;

    var dampCore: real := (1.0 - x2) * v;
    lemma_Mult_pos(1.0 - x2, v);
    assert dampCore >= 0.0;

    var damp: real := mu * dampCore;
    lemma_Mult_pos(mu, dampCore);
    assert damp >= 0.0;

    var wi: real := w02 * inner;
    lemma_Mult_pos(w02, inner);
    assert wi >= 0.0;

    var stiff1: real := wi * x;
    lemma_Mult_pos(wi, x);
    assert stiff1 >= 0.0;

    var stiff2: real := w02 * x;
    lemma_Mult_pos(w02, x);
    assert stiff2 >= 0.0;

    r := F0 * s - damp - stiff1 - stiff2;
    assert r <= F0;

    if t == 0.0 {
        assert s == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && x == 0.0 && v == 0.0 {
        assert s == 0.0;
        assert x2 == 0.0;
        assert av == v || av == -v;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert gp == 0.0;
        assert inner == 1.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert stiff1 == 0.0;
        assert stiff2 == 0.0;
        assert r == 0.0;
    }
}