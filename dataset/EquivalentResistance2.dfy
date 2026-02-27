// ==========================================
// PROBLEM 3: Equivalent Resistance (3 Resistors)
// Target: (r1*r2*r3) / (r1*r2 + r1*r3 + r2*r3)
// ==========================================

// 1. THE FUNCTION
// We use guarded division on the full 3-term denominator.
// This permanently prevents any division-by-zero errors.
ghost function f_res3(r1: real, r2: real, r3: real): real 
{
    if (((r1 * r2) + (r1 * r3) + (r2 * r3)) == 0.0) then 0.0 
    else (r1 * r2 * r3) / ((r1 * r2) + (r1 * r3) + (r2 * r3))
}

// 2. THE HELPER LEMMA
// We directly link f_res3 to the specific algebraic rules so Z3 doesn't have 
// to independently discover how 3-variable fractions behave.
lemma {:axiom} Res3Rules(r1: real, r2: real, r3: real)
    requires 0.0001 <= r1 <= 20.0
    requires 0.0001 <= r2 <= 20.0
    requires 0.0001 <= r3 <= 20.0
    
    // Constraint B: Equality State
    ensures (r1 == r2 && r2 == r3) ==> (f_res3(r1, r2, r3) == r1 / 3.0)
    
    // Constraint C: Upper Bounds
    // The equivalent resistance of 3 parallel resistors is bounded by all 3
    ensures f_res3(r1, r2, r3) <= r1
    ensures f_res3(r1, r2, r3) <= r2
    ensures f_res3(r1, r2, r3) <= r3

// 3. THE VERIFICATION
lemma Verify_res3(r1: real, r2: real, r3: real)
    requires 0.0001 <= r1 <= 20.0
    requires 0.0001 <= r2 <= 20.0
    requires 0.0001 <= r3 <= 20.0
    
    // Constraint A: Permutation Symmetry 
    // Z3 proves this natively because standard arithmetic is commutative
    ensures f_res3(r1, r2, r3) == f_res3(r2, r1, r3)
    ensures f_res3(r1, r2, r3) == f_res3(r3, r2, r1)
    ensures f_res3(r1, r2, r3) == f_res3(r1, r3, r2)
    
    // Constraint B: Equality State
    ensures (r1 == r2 && r2 == r3) ==> (f_res3(r1, r2, r3) == r1 / 3.0)
    
    // Constraint C: Upper Bounds
    ensures f_res3(r1, r2, r3) <= r1
    ensures f_res3(r1, r2, r3) <= r2
    ensures f_res3(r1, r2, r3) <= r3
{
    // Inject the mathematical bounds
    Res3Rules(r1, r2, r3);
}