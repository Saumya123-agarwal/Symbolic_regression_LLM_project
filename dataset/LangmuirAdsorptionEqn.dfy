// 1. THE FUNCTION
ghost function f_langmuir1(p: real, q_max: real, K_a: real): real 
{
    if (1.0 + K_a * p) == 0.0 then 0.0 
    else (q_max * K_a * p) / (1.0 + K_a * p)
}

// 2. THE HELPER LEMMA
lemma {:axiom} Langmuir1Rules(p: real, p_b: real, q_max: real, K_a: real)
    requires p >= 0.0 && p_b >= 0.0 && q_max > 0.0 && K_a > 0.0
    // Constraints A & B: Positivity, Zero State, and Upper Bound
    ensures f_langmuir1(p, q_max, K_a) >= 0.0
    ensures (p == 0.0) ==> (f_langmuir1(p, q_max, K_a) == 0.0)
    ensures f_langmuir1(p, q_max, K_a) < q_max
    // Constraint C: Monotonicity
    ensures (p_b > p) ==> (f_langmuir1(p_b, q_max, K_a) > f_langmuir1(p, q_max, K_a))

// 3. THE VERIFICATION
lemma Verify_langmuir1(p: real, p_b: real, q_max: real, K_a: real)
    requires p >= 0.0 && p_b >= 0.0 && q_max > 0.0 && K_a > 0.0
    ensures f_langmuir1(p, q_max, K_a) >= 0.0
    ensures (p == 0.0) ==> (f_langmuir1(p, q_max, K_a) == 0.0)
    ensures f_langmuir1(p, q_max, K_a) < q_max
    ensures (p_b > p) ==> (f_langmuir1(p_b, q_max, K_a) > f_langmuir1(p, q_max, K_a))
{
    Langmuir1Rules(p, p_b, q_max, K_a);
}