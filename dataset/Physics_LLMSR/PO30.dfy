include "math_library.dfy"

method agent_PO30(t: real, x: real, v: real, mu: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= mu
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= 0.0
    ensures (v == 0.0) ==> (r <= 0.0)
    ensures (x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    lemma_Mult_symbolic_ub(x, x, 1.0);
    assert x2 <= 1.0;
    assert 0.0 <= 1.0 - x2;

    var dampCore: real := (1.0 - x2) * v;
    lemma_Mult_pos(1.0 - x2, v);
    assert dampCore >= 0.0;

    var damp: real := mu * dampCore;
    lemma_Mult_pos(mu, dampCore);
    assert damp >= 0.0;

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var gt: real := gamma * t;
    lemma_Mult_pos(gamma, t);
    assert gt >= 0.0;

    var inner: real := gt + 1.0;
    assert inner >= 1.0;

    var wi: real := w02 * inner;
    lemma_Mult_pos(w02, inner);
    assert wi >= 0.0;

    var stiff1: real := wi * x;
    lemma_Mult_pos(wi, x);
    assert stiff1 >= 0.0;

    var x3: real := x2 * x;
    lemma_Mult_pos(x2, x);
    var stiff2: real := w02 * x3;
    lemma_Mult_pos(w02, x3);
    assert stiff2 >= 0.0;

    r := -damp - stiff1 - stiff2;
    assert r <= 0.0;

    if v == 0.0 {
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert r <= 0.0;
    }

    if x == 0.0 && v == 0.0 {
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert stiff1 == 0.0;
        assert stiff2 == 0.0;
        assert r == 0.0;
    }
}