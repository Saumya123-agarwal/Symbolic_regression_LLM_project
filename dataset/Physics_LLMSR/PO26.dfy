include "math_library.dfy"

method agent_PO26(t: real, v: real, F0: real, beta: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    ensures r <= F0 + beta
    ensures (v == 0.0) ==> (r <= F0)
    ensures (t == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);
    var sv: real := sin(v);

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    assert -1.0 <= sv <= 1.0;
    assert -sv <= 1.0;
    lemma_Mult_symbolic_ub(beta, -sv, 1.0);
    assert -(beta * sv) <= beta;

    r := F0 * st - beta * sv;
    assert r <= F0 + beta;

    if v == 0.0 {
        assert sv == 0.0;
        assert r == F0 * st;
        assert r <= F0;
    }

    if t == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert sv == 0.0;
        assert r == 0.0;
    }
}