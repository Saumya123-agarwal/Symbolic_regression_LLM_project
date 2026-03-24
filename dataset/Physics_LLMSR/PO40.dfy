include "math_library.dfy"

method agent_PO40(t: real, x: real, v: real, F0: real, alpha: real, beta: real, mu: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= x <= 1.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= alpha
    requires 0.0 <= beta
    requires 0.0 <= mu
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);

    var v2: real := v * v;
    lemma_Mult_pos(v, v);
    lemma_Mult_symbolic_ub(v, v, 1.0);
    assert v2 <= 1.0;

    var v3: real := v2 * v;
    lemma_Mult_pos(v2, v);

    var oneMinusV2: real := 1.0 - v2;
    assert oneMinusV2 >= 0.0;

    var dampCore: real := oneMinusV2 * v;
    lemma_Mult_pos(oneMinusV2, v);
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

    var exv: real := ex * v;
    lemma_Mult_pos(ex, v);
    assert exv >= 0.0;

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(alpha, v3);
    assert -(alpha * v3) <= 0.0;

    lemma_Mult_pos(beta, exv);
    assert -(beta * exv) <= 0.0;

    assert -damp <= 0.0;

    r := F0 * st - alpha * v3 - beta * exv - damp;
    assert r <= F0;

    if t == 0.0 {
        assert st == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert v2 == 0.0;
        assert v3 == 0.0;
        assert dampCore == 0.0;
        assert damp == 0.0;
        assert exv == 0.0;
        assert r == 0.0;
    }
}