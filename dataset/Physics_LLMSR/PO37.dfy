include "math_library.dfy"

method agent_PO37(t: real, x: real, v: real, F0: real, beta: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);

    var ax: real := abs(x);
    assert ax >= 0.0;
    var nax: real := -ax;
    assert nax <= 0.0;

    var ex: real := exp(nax);
    assert ex >= 0.0;

    var exv: real := ex * v;
    lemma_Mult_pos(ex, v);
    assert exv >= 0.0;

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(beta, exv);
    assert -(beta * exv) <= 0.0;

    r := F0 * st - beta * exv;
    assert r <= F0;

    if t == 0.0 {
        assert st == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert exv == 0.0;
        assert r == 0.0;
    }
}