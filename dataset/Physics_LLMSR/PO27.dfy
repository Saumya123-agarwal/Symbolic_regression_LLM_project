include "math_library.dfy"

method agent_PO27(t: real, x: real, v: real, F0: real, beta: real, omega0: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    requires 0.0 <= omega0
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);

    var av: real := abs(v);
    assert av >= 0.0;

    var arg: real := av + 1.0;
    assert arg >= 1.0;

    var lg: real := log(arg);
    assert lg >= 0.0;

    var twoBeta: real := 2.0 * beta;
    lemma_Mult_pos(2.0, beta);
    assert twoBeta >= 0.0;

    var w02: real := omega0 * omega0;
    lemma_Mult_pos(omega0, omega0);

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    var x3: real := x2 * x;
    lemma_Mult_pos(x2, x);

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(beta, lg);
    assert -(beta * lg) <= 0.0;

    lemma_Mult_pos(twoBeta, v);
    assert -(twoBeta * v) <= 0.0;

    lemma_Mult_pos(w02, x3);
    assert -(w02 * x3) <= 0.0;

    r := F0 * st - beta * lg - twoBeta * v - w02 * x3;
    assert r <= F0;

    if t == 0.0 {
        assert st == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && x == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert av == v || av == -v;
        assert av == 0.0;
        assert arg == 1.0;
        assert lg == 0.0;
        assert x2 == 0.0;
        assert x3 == 0.0;
        assert r == 0.0;
    }
}