include "math_library.dfy"

method agent_PO6(x: real, v: real, beta: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= beta
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= beta
    ensures (x == 0.0 && v == 0.0) ==> (r == 0.0)
    ensures (v == 0.0) ==> (r <= 0.0)
{
    var s: real := sin(v);
    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    var x3: real := x2 * x;
    lemma_Mult_pos(x2, x);

    var av: real := abs(v);
    assert av >= 0.0;
    var powv: real := pow(av, 0.33);

    var gp: real := gamma * powv;
    lemma_Mult_pos(gamma, powv);
    assert gp >= 0.0;

    var inner: real := gp + 1.0;
    assert inner >= 1.0;

    var wi: real := w02 * inner;
    lemma_Mult_pos(w02, inner);
    assert wi >= 0.0;

    var twoBeta: real := 2.0 * beta;
    lemma_Mult_pos(2.0, beta);
    assert twoBeta >= 0.0;

    assert -1.0 <= s <= 1.0;
    assert -s <= 1.0;
    lemma_Mult_symbolic_ub(beta, -s, 1.0);
    assert -(beta * s) <= beta;

    lemma_Mult_pos(twoBeta, v);
    assert -(twoBeta * v) <= 0.0;

    lemma_Mult_pos(wi, x);
    assert -(wi * x) <= 0.0;

    lemma_Mult_pos(w02, x3);
    assert -(w02 * x3) <= 0.0;

    lemma_Mult_pos(w02, x);
    assert -(w02 * x) <= 0.0;

    r := -(beta * s) - (twoBeta * v) - (wi * x) - (w02 * x3) - (w02 * x);
    assert r <= beta;

    if x == 0.0 && v == 0.0 {
        assert s == 0.0;
        assert av == v || av == -v;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert gp == 0.0;
        assert inner == 1.0;
        assert wi == w02;
        assert r == 0.0;
    }

    if v == 0.0 {
        assert s == 0.0;
        assert av == v || av == -v;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert gp == 0.0;
        assert inner == 1.0;
        assert wi == w02;
        assert r == -(w02 * x) - (w02 * x3) - (w02 * x);
        assert r <= 0.0;
    }
}