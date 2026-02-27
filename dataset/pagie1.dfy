include "prob_1_llm.dfy"


// ==========================================
// PROBLEM 3: pagie1
// Target: 1/(1+x^-4) + 1/(1+y^-4)
// ==========================================

ghost function f_pagie1(x: real, y: real): real 
    requires x != 0.0 && y != 0.0
{
    (1.0 / (1.0 + powInt(x, -4))) + (1.0 / (1.0 + powInt(y, -4)))
}

lemma Verify_pagie1(x: real, y: real)
    requires x != 0.0 && y != 0.0
    ensures f_pagie1(x, y) >= 0.0
    ensures f_pagie1(x, y) <= 2.0
    ensures f_pagie1(x, y) == f_pagie1(y, x)
{
    // The library guarantees powInt(x, -4) >= 0 because the exponent is even.
    // Therefore, the denominators are >= 1.0, making each fraction <= 1.0.
    lemma_pow_pos(x, -4);
    lemma_pow_pos(y, -4);
}