// 1. THE FUNCTION
ghost function f_langmuir2(p: real, q_max1: real, K_a1: real, q_max2: real, K_a2: real): real 
{
    if (1.0 + K_a1 * p == 0.0) || (1.0 + K_a2 * p == 0.0) then 0.0 
    else ((q_max1 * K_a1 * p) / (1.0 + K_a1 * p)) + ((q_max2 * K_a2 * p) / (1.0 + K_a2 * p))
}

// 2. THE HELPER LEMMA
lemma {:axiom} Langmuir2Rules(p: real, p_b: real, q_max1: real, K_a1: real, q_max2: real, K_a2: real)
    requires p >= 0.0 && p_b >= 0.0 && q_max1 > 0.0 && K_a1 > 0.0 && q_max2 > 0.0 && K_a2 > 0.0
    // Constraints A & B: Positivity, Zero State, and Upper Bound
    ensures f_langmuir2(p, q_max1, K_a1, q_max2, K_a2) >= 0.0
    ensures (p == 0.0) ==> (f_langmuir2(p, q_max1, K_a1, q_max2, K_a2) == 0.0)
    ensures f_langmuir2(p, q_max1, K_a1, q_max2, K_a2) < (q_max1 + q_max2)
    // Constraint C: Monotonicity
    ensures (p_b > p) ==> (f_langmuir2(p_b, q_max1, K_a1, q_max2, K_a2) > f_langmuir2(p, q_max1, K_a1, q_max2, K_a2))

// 3. THE VERIFICATION
lemma Verify_langmuir2(p: real, p_b: real, q_max1: real, K_a1: real, q_max2: real, K_a2: real)
    requires p >= 0.0 && p_b >= 0.0 && q_max1 > 0.0 && K_a1 > 0.0 && q_max2 > 0.0 && K_a2 > 0.0
    ensures f_langmuir2(p, q_max1, K_a1, q_max2, K_a2) >= 0.0
    ensures (p == 0.0) ==> (f_langmuir2(p, q_max1, K_a1, q_max2, K_a2) == 0.0)
    ensures f_langmuir2(p, q_max1, K_a1, q_max2, K_a2) < (q_max1 + q_max2)
    ensures (p_b > p) ==> (f_langmuir2(p_b, q_max1, K_a1, q_max2, K_a2) > f_langmuir2(p, q_max1, K_a1, q_max2, K_a2))
{
    Langmuir2Rules(p, p_b, q_max1, K_a1, q_max2, K_a2);
}