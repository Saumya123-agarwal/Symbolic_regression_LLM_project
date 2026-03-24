include "math_library.dfy"

method agent_PO28(t: real, v: real, F0: real, alpha: real, beta: real) returns (r: real)
    requires 0.0 <= t <= 60.0
    requires 0.0 <= v <= 1.0
    requires 0.0 <= F0
    requires 0.0 <= alpha
    requires 0.0 <= beta
    ensures r <= F0
    ensures (t == 0.0) ==> (r <= 0.0)
    ensures (t == 0.0 && v == 0.0) ==> (r == 0.0)
{
    var st: real := sin(t);

    var v2: real := v * v;
    lemma_Mult_pos(v, v);
    var v3: real := v2 * v;
    lemma_Mult_pos(v2, v);

    var twoBeta: real := 2.0 * beta;
    lemma_Mult_pos(2.0, beta);
    assert twoBeta >= 0.0;

    var av: real := abs(v);
    assert av >= 0.0;
    var nav: real := -av;
    assert nav <= 0.0;

    var ev: real := exp(nav);
    assert ev >= 0.0;

    var evv: real := ev * v;
    lemma_Mult_pos(ev, v);
    assert evv >= 0.0;

    assert st <= 1.0;
    lemma_Mult_symbolic_ub(F0, st, 1.0);
    assert F0 * st <= F0;

    lemma_Mult_pos(alpha, v3);
    assert -(alpha * v3) <= 0.0;

    lemma_Mult_pos(twoBeta, v);
    assert -(twoBeta * v) <= 0.0;

    lemma_Mult_pos(beta, evv);
    assert -(beta * evv) <= 0.0;

    r := F0 * st - alpha * v3 - twoBeta * v - beta * evv;
    assert r <= F0;

    if t == 0.0 {
        assert st == 0.0;
        assert r <= 0.0;
    }

    if t == 0.0 && v == 0.0 {
        assert st == 0.0;
        assert v2 == 0.0;
        assert v3 == 0.0;
        assert evv == 0.0;
        assert r == 0.0;
    }
}