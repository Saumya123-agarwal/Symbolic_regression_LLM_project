include "math_library.dfy"

method agent_PO41(t: real, x: real, v: real, F0: real, beta: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);

    var av: real := abs(v);
    assert av >= 0.0;
    var powv: real := pow(av, 0.33);

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var gp: real := gamma * powv;
    lemma_Mult_pos(gamma, powv);
    assert gp >= 0.0;

    var inner: real := gp + 1.0;
    assert inner >= 1.0;

    var wi: real := w02 * inner;
    lemma_Mult_pos(w02, inner);
    assert wi >= 0.0;

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    var x3: real := x2 * x;
    lemma_Mult_pos(x2, x);

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(beta, powv);
    assert -(beta * powv) <= 0.0;

    lemma_Mult_pos(wi, x);
    assert -(wi * x) <= 0.0;

    lemma_Mult_pos(w02, x3);
    assert -(w02 * x3) <= 0.0;

    lemma_Mult_pos(w02, x);
    assert -(w02 * x) <= 0.0;

    r := F0 * st - beta * powv - wi * x - w02 * x3 - w02 * x;
    assert r <= F0;

    if t == 0.0 {
        assert st == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && x == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert gp == 0.0;
        assert inner == 1.0;
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert r == 0.0;
    }
}