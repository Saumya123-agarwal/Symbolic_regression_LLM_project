include "math_library.dfy"

method agent_PO36(t: real, x: real, v: real, F0: real, beta: real, gamma: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    requires 0.0 <= gamma
    requires 0.0 <= omega0
    ensures r <= F0 + beta
    ensures (v == 0.0) ==> (r <= F0)
    ensures (t == 0.0 && x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);
    var sv: real := sin(v);

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

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

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    assert -1.0 <= sv <= 1.0;
    assert -sv <= 1.0;
    lemma_Mult_symbolic_ub(beta, -sv, 1.0);
    assert -(beta * sv) <= beta;

    lemma_Mult_pos(wi, x);
    assert -(wi * x) <= 0.0;

    r := F0 * st - beta * sv - wi * x;
    assert r <= F0 + beta;

    if v == 0.0 {
        assert sv == 0.0;
        assert r == F0 * st - wi * x;
        assert r <= F0;
    }

    if t == 0.0 && x == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert sv == 0.0;
        assert av == 0.0;
        lemma_pow_zero_base(0.33);
        assert powv == 0.0;
        assert gp == 0.0;
        assert inner == 1.0;
        assert r == 0.0;
    }
}