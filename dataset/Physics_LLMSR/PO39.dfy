include "math_library.dfy"

method agent_PO39(x: real, v: real, beta: real, mu: real, omega0: real) returns (r: real)
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= beta
    requires 0.0 <= mu
    requires 0.0 <= omega0
    ensures r <= beta
    ensures (v == 0.0) ==> (r <= 0.0)
    ensures (x == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var sv: real := sin(v);

    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    lemma_Mult_symbolic_ub(x, x, 1.0);
    assert x2 <= 1.0;
    assert 0.0 <= 1.0 - x2;

    var dampCore: real := (1.0 - x2) * v;
    lemma_Mult_pos(1.0 - x2, v);
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

    assert -1.0 <= sv <= 1.0;
    assert -sv <= 1.0;
    lemma_Mult_symbolic_ub(beta, -sv, 1.0);
    assert -(beta * sv) <= beta;

    assert -damp <= 0.0;

    lemma_Mult_pos(w02, xe);
    assert -(w02 * xe) <= 0.0;

    r := -(beta * sv) - damp - w02 * xe;
    assert r <= beta;

    if v == 0.0 {
        assert sv == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert r == -(w02 * xe);
        assert r <= 0.0;
    }

    if x == 0.0 && v == 0.0 {
        assert sv == 0.0;
        assert x2 == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert xe == 0.0;
        assert r == 0.0;
    }
}