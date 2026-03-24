include "math_library.dfy"

method agent_PO12(t: real, x: real, v: real, beta: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= beta
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= beta
    ensures (v == 0.0) ==> (r <= 0.0)
    ensures (x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var s: real := sin(v);

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var gt: real := gamma * t;
    lemma_Mult_pos(gamma, t);
    assert gt >= 0.0;

    var inner: real := gt + 1.0;
    assert inner >= 1.0;

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    var x3: real := x2 * x;
    lemma_Mult_pos(x2, x);

    var wi: real := w02 * inner;
    lemma_Mult_pos(w02, inner);
    assert wi >= 0.0;

    assert -1.0 <= s <= 1.0;
    assert -s <= 1.0;
    lemma_Mult_symbolic_ub(beta, -s, 1.0);
    assert -(beta * s) <= beta;

    lemma_Mult_pos(wi, x);
    assert -(wi * x) <= 0.0;

    lemma_Mult_pos(w02, x3);
    assert -(w02 * x3) <= 0.0;

    r := -(beta * s) - (wi * x) - (w02 * x3);
    assert r <= beta;

    if v == 0.0 {
        assert s == 0.0;
        assert r <= 0.0;
    }

    if x == 0.0 && v == 0.0 {
        assert s == 0.0;
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert r == 0.0;
    }
}