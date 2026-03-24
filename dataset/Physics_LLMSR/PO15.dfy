include "math_library.dfy"

method agent_PO15(t: real, x: real, v: real, F0: real, beta: real, mu: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= beta
    requires 0.0 <= mu
    ensures r <= F0 + beta
    ensures (v == 0.0) ==> (r <= F0)
    ensures (t == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);
    var sv: real := sin(v);

    var av: real := abs(v);
    assert av >= 0.0;

    var arg: real := av + 1.0;
    assert arg >= 1.0;

    var lg: real := log(arg);
    assert lg >= 0.0;

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    lemma_Mult_symbolic_ub(x, x, 1.0);
    assert x2 <= x;
    assert x2 <= 1.0;
    assert 0.0 <= 1.0 - x2;

    var twoBeta: real := 2.0 * beta;
    lemma_Mult_pos(2.0, beta);
    assert twoBeta >= 0.0;

    var dampCore: real := (1.0 - x2) * v;
    lemma_Mult_pos(1.0 - x2, v);
    assert dampCore >= 0.0;

    var damp: real := mu * dampCore;
    lemma_Mult_pos(mu, dampCore);
    assert damp >= 0.0;

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(beta, lg);
    assert -(beta * lg) <= 0.0;

    assert -1.0 <= sv <= 1.0;
    assert -sv <= 1.0;
    lemma_Mult_symbolic_ub(beta, -sv, 1.0);
    assert -(beta * sv) <= beta;

    lemma_Mult_pos(twoBeta, v);
    assert -(twoBeta * v) <= 0.0;

    assert -damp <= 0.0;

    r := F0 * st - (beta * lg) - (beta * sv) - (twoBeta * v) - damp;
    assert r <= F0 + beta;

    if v == 0.0 {
        assert av == v || av == -v;
        assert av == 0.0;
        assert arg == 1.0;
        assert lg == 0.0;
        assert sv == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert r == F0 * st;
        assert r <= F0;
    }

    if t == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert av == 0.0;
        assert arg == 1.0;
        assert lg == 0.0;
        assert sv == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert r == 0.0;
    }
}