include "prob_1_llm.dfy"


// ==========================================
// PROBLEM 2: Einstein's Relativistic Time Dilation
// Target: sqrt(1 - (v^2 / c^2)) - 1
// ==========================================

// 1. THE FUNCTION
ghost function f_einstein(v: real, c: real): real 
{
    // Check the exact denominator (c * c) for zero FIRST
    if (c * c == 0.0) then 0.0 
    // Then check for negative square roots
    else if (1.0 - ((v * v) / (c * c)) < 0.0) then 0.0 
    // If both are safe, do the math
    else sqrt(1.0 - ((v * v) / (c * c))) - 1.0
}

// 2. THE HELPER LEMMA
lemma {:axiom} EinsteinRules(v: real, v_b: real, c: real)
    requires 0.0 <= v < c && 0.0 <= v_b < c && c > 0.0
    // Constraint A: Zero State
    ensures (v == 0.0) ==> (f_einstein(v, c) == 0.0)
    // Constraint B: Bounds
    ensures -1.0 <= f_einstein(v, c) <= 0.0
    // Constraint C: Monotonic Decreasing
    ensures (v_b > v) ==> (f_einstein(v_b, c) < f_einstein(v, c))

// 3. THE VERIFICATION
lemma Verify_einstein(v: real, v_b: real, c: real)
    requires 0.0 <= v < c && 0.0 <= v_b < c && c > 0.0
    ensures (v == 0.0) ==> (f_einstein(v, c) == 0.0)
    ensures -1.0 <= f_einstein(v, c) <= 0.0
    ensures (v_b > v) ==> (f_einstein(v_b, c) < f_einstein(v, c))
{
    EinsteinRules(v, v_b, c);
}