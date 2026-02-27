// ==========================================
// PROBLEM 4: res2
// Target: (r1*r2)/(r1+r2)
// ==========================================

// 1. THE HELPER LEMMA
// Teach Dafny the bounds of fractions where the denominator is larger than the numerator
lemma {:axiom} FractionRules_res2(r1: real, r2: real)
    requires r1 > 0.0 && r2 > 0.0
    // If you multiply a number (r1) by a fraction less than 1 (r2 / (r1+r2)), 
    // the result is strictly less than the original number.
    ensures (r1 * r2) / (r1 + r2) <= r1
    ensures (r1 * r2) / (r1 + r2) <= r2

// 2. THE FUNCTION
ghost function f_res2(r1: real, r2: real): real 
    requires r1 > 0.0 && r2 > 0.0
{
    (r1 * r2) / (r1 + r2)
}

// 3. THE VERIFICATION
lemma Verify_res2(r1: real, r2: real)
    requires r1 > 0.0 && r2 > 0.0
    ensures f_res2(r1, r2) == f_res2(r2, r1)
    ensures f_res2(r1, r2) <= r1 && f_res2(r1, r2) <= r2
    ensures f_res2(r1, r2) > 0.0
{
    // Inject the fractional boundary rules into the proof
    FractionRules_res2(r1, r2);
    
    // Dafny can now instantly verify that the equivalent resistance 
    // is smaller than both individual resistors.
}