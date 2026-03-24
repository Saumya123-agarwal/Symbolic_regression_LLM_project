include "math_library.dfy"

method agent_PO43(t: real, x: real, v: real, F0: real, alpha: real, beta: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= alpha
    requires 0.0 <= beta
    ensures r <= F0 + beta
    ensures (v == 0.0) ==> (r <= F0)
    ensures (t == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);
    var sx: real := sin(x);

    var v2: real := v * v;
    lemma_Mult_pos(v, v);
    var v3: real := v2 * v;
    lemma_Mult_pos(v2, v);

    var twoBeta: real := 2.0 * beta;
    lemma_Mult_pos(2.0, beta);
    assert twoBeta >= 0.0;

    var q: real := v * (-sx);
    assert -1.0 <= sx <= 1.0;
    assert -sx <= 1.0;
    lemma_Mult_symbolic_ub(v, -sx, 1.0);
    assert q <= v * 1.0;
    assert q <= v;
    assert v <= 1.0;
    assert q <= 1.0;

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(alpha, v3);
    assert -(alpha * v3) <= 0.0;

    lemma_Mult_symbolic_ub(beta, q, 1.0);
    assert beta * q <= beta;
    assert beta * q == -(beta * sx * v);
    assert -(beta * sx * v) <= beta;

    lemma_Mult_pos(twoBeta, v);
    assert -(twoBeta * v) <= 0.0;

    r := F0 * st - alpha * v3 - beta * sx * v - twoBeta * v;
    assert r <= F0 + beta;

    if v == 0.0 {
        assert v2 == 0.0;
        assert v3 == 0.0;
        assert q == 0.0;
        assert r == F0 * st;
        assert r <= F0;
    }

    if t == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert v2 == 0.0;
        assert v3 == 0.0;
        assert q == 0.0;
        assert r == 0.0;
    }
}