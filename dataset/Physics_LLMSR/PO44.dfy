include "math_library.dfy"

method agent_PO44(t: real, x: real, v: real, F0: real, beta: real, mu: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    requires 0.0 <= mu
    requires 0.0 <= omega0
    ensures r <= F0 + beta
    ensures (v == 0.0) ==> (r <= F0)
    ensures (t == 0.0 && x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);
    var sx: real := sin(x);

    var twoBeta: real := 2.0 * beta;
    lemma_Mult_pos(2.0, beta);
    assert twoBeta >= 0.0;

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    lemma_Mult_symbolic_ub(x, x, 1.0);
    assert x2 <= 1.0;

    var oneMinusX2: real := 1.0 - x2;
    assert oneMinusX2 >= 0.0;

    var dampCore: real := oneMinusX2 * v;
    lemma_Mult_pos(oneMinusX2, v);
    assert dampCore >= 0.0;

    var damp: real := mu * dampCore;
    lemma_Mult_pos(mu, dampCore);
    assert damp >= 0.0;

    var ax: real := abs(x);
    assert ax >= 0.0;
    var nax: real := -ax;
    assert nax <= 0.0;

    var ex: real := exp(nax);
    assert ex >= 0.0;

    var xe: real := x * ex;
    lemma_Mult_pos(x, ex);
    assert xe >= 0.0;

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

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

    lemma_Mult_symbolic_ub(beta, q, 1.0);
    assert beta * q <= beta;
    assert beta * q == -(beta * sx * v);
    assert -(beta * sx * v) <= beta;

    lemma_Mult_pos(twoBeta, v);
    assert -(twoBeta * v) <= 0.0;

    assert -damp <= 0.0;

    lemma_Mult_pos(w02, xe);
    assert -(w02 * xe) <= 0.0;

    r := F0 * st - beta * sx * v - twoBeta * v - damp - w02 * xe;
    assert r <= F0 + beta;

    if v == 0.0 {
        assert q == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert r == F0 * st - w02 * xe;
        assert r <= F0;
    }

    if t == 0.0 && x == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert x2 == 0.0;
        assert q == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert xe == 0.0;
        assert r == 0.0;
    }
}