// tests.dfy

// ==========================================
// SHARED MATH DEFINITIONS (Leave uncommented)
// We declare these as ghost functions so Dafny 
// can parse the symbolic math.
// ==========================================
ghost function sin(x: real): real
ghost function cos(x: real): real
ghost function pow(base: real, exponent: real): real


// ==========================================
// PROBLEM 1: nguyen4 
// Target: x^6 + x^5 + x^4 + x^3 + x^2 + x
// ==========================================

// 1. THE HELPER LEMMA (The Math Rules)
// This axiom teaches Dafny how powers behave based on the value of x
/*
lemma {:axiom} PowRules(x: real)
    requires x >= 0.0
    // Rule A: Evaluating at zero
    ensures (x == 0.0) ==> (pow(x, 2.0) == 0.0 && pow(x, 3.0) == 0.0 && pow(x, 4.0) == 0.0 && pow(x, 5.0) == 0.0 && pow(x, 6.0) == 0.0)
    // Rule B: Positivity (positive base = positive result)
    ensures pow(x, 2.0) >= 0.0 && pow(x, 3.0) >= 0.0 && pow(x, 4.0) >= 0.0 && pow(x, 5.0) >= 0.0 && pow(x, 6.0) >= 0.0
    // Rule C: Monotonicity for x >= 1 (higher exponent = bigger number)
    ensures (x >= 1.0) ==> (x <= pow(x, 2.0) <= pow(x, 3.0) <= pow(x, 4.0) <= pow(x, 5.0) <= pow(x, 6.0))
    // Rule D: Monotonicity for 0 <= x <= 1 (higher exponent = SMALLER number)
    ensures (x <= 1.0) ==> (pow(x, 6.0) <= pow(x, 5.0) <= pow(x, 4.0) <= pow(x, 3.0) <= pow(x, 2.0) <= x)

// 2. THE FUNCTION
ghost function f_nguyen4(x: real): real {
    pow(x, 6.0) + pow(x, 5.0) + pow(x, 4.0) + pow(x, 3.0) + pow(x, 2.0) + x
}

// 3. THE VERIFICATION
lemma Verify_nguyen4(x: real)
    requires 0.0 <= x <= 5.0
    ensures f_nguyen4(x) >= 0.0
    ensures (x == 0.0) ==> (f_nguyen4(x) == 0.0)
    ensures (x >= 1.0) ==> (f_nguyen4(x) <= 6.0 * pow(x, 6.0))
    ensures (x <= 1.0) ==> (f_nguyen4(x) >= 6.0 * pow(x, 6.0))
    ensures (x <= 1.0) ==> (f_nguyen4(x) <= 6.0 * x)
    ensures (x >= 1.0) ==> (f_nguyen4(x) >= 6.0 * x)
{
    // Inject the mathematical facts into Dafny's current context
    PowRules(x);
    
    // By calling the lemma, Dafny now knows that:
    // If x >= 1, then x^6 is the largest term, so 6 * x^6 must be >= the sum.
    // If x <= 1, then x is the largest term, so 6 * x must be >= the sum.
    // Verification succeeds automatically!
}
*/

// ==========================================
// PROBLEM 2: nguyen1
// Target: x^3 + x^2 + x
// ==========================================
/*
// 1. THE HELPER LEMMA
// Teaches Dafny how powers 2 and 3 behave based on the value of x
lemma {:axiom} PowRules_nguyen1(x: real)
    requires x >= 0.0
    // Rule A: Evaluating at zero
    ensures (x == 0.0) ==> (pow(x, 2.0) == 0.0 && pow(x, 3.0) == 0.0)
    // Rule B: Positivity
    ensures pow(x, 2.0) >= 0.0 && pow(x, 3.0) >= 0.0
    // Rule C: Monotonicity for x >= 1
    ensures (x >= 1.0) ==> (x <= pow(x, 2.0) <= pow(x, 3.0))
    // Rule D: Monotonicity for 0 <= x <= 1
    ensures (x <= 1.0) ==> (pow(x, 3.0) <= pow(x, 2.0) <= x)

// 2. THE FUNCTION
ghost function f_nguyen1(x: real): real {
    pow(x, 3.0) + pow(x, 2.0) + x
}

// 3. THE VERIFICATION
lemma Verify_nguyen1(x: real)
    requires 0.0 <= x <= 5.0
    ensures f_nguyen1(x) >= 0.0
    ensures (x == 0.0) ==> (f_nguyen1(x) == 0.0)
    ensures (x >= 1.0) ==> (f_nguyen1(x) <= 3.0 * pow(x, 3.0))
    ensures (x <= 1.0) ==> (f_nguyen1(x) >= 3.0 * pow(x, 3.0))
    ensures (x <= 1.0) ==> (f_nguyen1(x) <= 3.0 * x)
    ensures (x >= 1.0) ==> (f_nguyen1(x) >= 3.0 * x)
{
    // Inject the mathematical facts to satisfy the constraints
    PowRules_nguyen1(x);
}
*/

// ==========================================
// PROBLEM 3: nguyen6
// Target: sin(x) + sin(x + x^2)
// ==========================================

// 1. THE HELPER LEMMAS (Trigonometry & Powers)
/*
// Axiom A: Sine is bounded between -1 and 1
lemma {:axiom} SinBounds(y: real)
    ensures -1.0 <= sin(y) <= 1.0

// Axiom B: Sine of zero is zero
lemma {:axiom} SinZero()
    ensures sin(0.0) == 0.0

// Axiom C: Zero squared is zero
lemma {:axiom} PowZero_nguyen6(x: real)
    ensures (x == 0.0) ==> pow(x, 2.0) == 0.0


// 2. THE FUNCTION
ghost function f_nguyen6(x: real): real {
    sin(x) + sin(x + pow(x, 2.0))
}

// 3. THE VERIFICATION
lemma Verify_nguyen6(x: real)
    requires 0.0 <= x <= 5.0
    ensures f_nguyen6(x) >= -2.0
    ensures f_nguyen6(x) <= 2.0
    ensures (x == 0.0) ==> (f_nguyen6(x) == 0.0)
{
    // 1. Inject the bounds for our specific inputs
    SinBounds(x);                  // Teaches Dafny: -1 <= sin(x) <= 1
    SinBounds(x + pow(x, 2.0));    // Teaches Dafny: -1 <= sin(x + x^2) <= 1
    
    // Because both terms are bounded between -1 and 1, 
    // Dafny instantly deduces the sum is bounded between -2 and 2.

    // 2. Inject the zero rules
    if x == 0.0 {
        PowZero_nguyen6(x);        // Teaches Dafny: 0^2 = 0
        SinZero();                 // Teaches Dafny: sin(0) = 0
    }
}
*/

// ==========================================
// PROBLEM 4: nguyen3
// Target: x^5 + x^4 + x^3 + x^2 + x
// ==========================================
/*
// 1. THE HELPER LEMMA
// Teaches Dafny how powers 2, 3, 4, and 5 behave based on the value of x
lemma {:axiom} PowRules_nguyen3(x: real)
    requires x >= 0.0
    // Rule A: Evaluating at zero
    ensures (x == 0.0) ==> (pow(x, 2.0) == 0.0 && pow(x, 3.0) == 0.0 && pow(x, 4.0) == 0.0 && pow(x, 5.0) == 0.0)
    // Rule B: Positivity
    ensures pow(x, 2.0) >= 0.0 && pow(x, 3.0) >= 0.0 && pow(x, 4.0) >= 0.0 && pow(x, 5.0) >= 0.0
    // Rule C: Monotonicity for x >= 1
    ensures (x >= 1.0) ==> (x <= pow(x, 2.0) <= pow(x, 3.0) <= pow(x, 4.0) <= pow(x, 5.0))
    // Rule D: Monotonicity for 0 <= x <= 1
    ensures (x <= 1.0) ==> (pow(x, 5.0) <= pow(x, 4.0) <= pow(x, 3.0) <= pow(x, 2.0) <= x)

// 2. THE FUNCTION
ghost function f_nguyen3(x: real): real {
    pow(x, 5.0) + pow(x, 4.0) + pow(x, 3.0) + pow(x, 2.0) + x
}

// 3. THE VERIFICATION
lemma Verify_nguyen3(x: real)
    requires 0.0 <= x <= 5.0
    ensures f_nguyen3(x) >= 0.0
    ensures (x == 0.0) ==> (f_nguyen3(x) == 0.0)
    ensures (x >= 1.0) ==> (f_nguyen3(x) <= 5.0 * pow(x, 5.0))
    ensures (x <= 1.0) ==> (f_nguyen3(x) >= 5.0 * pow(x, 5.0))
    ensures (x <= 1.0) ==> (f_nguyen3(x) <= 5.0 * x)
    ensures (x >= 1.0) ==> (f_nguyen3(x) >= 5.0 * x)
{
    // Inject the mathematical facts to satisfy the constraints
    PowRules_nguyen3(x);
}
*/

// ==========================================
// PROBLEM 5: nguyen5
// Target: sin(x^2) * cos(x) - 1
// ==========================================

// 1. THE HELPER LEMMAS (Trig, Powers, and Multiplication)
/*
// Axiom A: Sine and Cosine are bounded between -1 and 1
lemma {:axiom} TrigBounds(y: real)
    ensures -1.0 <= sin(y) <= 1.0
    ensures -1.0 <= cos(y) <= 1.0

// Axiom B: The product of two fractions is a fraction
// Z3 struggles with non-linear arithmetic, so we explicitly state this rule.
lemma {:axiom} MulBounds(a: real, b: real)
    requires -1.0 <= a <= 1.0
    requires -1.0 <= b <= 1.0
    ensures -1.0 <= a * b <= 1.0

// Axiom C: Trig values at zero
lemma {:axiom} TrigZero_nguyen5()
    ensures sin(0.0) == 0.0
    ensures cos(0.0) == 1.0

// Axiom D: Zero squared is zero
lemma {:axiom} PowZero_nguyen5(x: real)
    ensures (x == 0.0) ==> pow(x, 2.0) == 0.0


// 2. THE FUNCTION
ghost function f_nguyen5(x: real): real {
    sin(pow(x, 2.0)) * cos(x) - 1.0
}

// 3. THE VERIFICATION
lemma Verify_nguyen5(x: real)
    requires 0.0 <= x <= 5.0
    ensures f_nguyen5(x) >= -2.0
    ensures f_nguyen5(x) <= 0.0
    ensures (x == 0.0) ==> (f_nguyen5(x) == -1.0)
{
    // 1. Establish the bounds for the individual trig components
    TrigBounds(pow(x, 2.0));  // Tells Dafny: -1 <= sin(x^2) <= 1
    TrigBounds(x);            // Tells Dafny: -1 <= cos(x) <= 1
    
    // 2. Combine them using our multiplication rule
    MulBounds(sin(pow(x, 2.0)), cos(x)); 
    // Now Dafny knows: -1 <= sin(x^2) * cos(x) <= 1.
    // Subtracting 1 from this range perfectly matches our ensures statements [-2.0, 0.0].

    // 3. Handle the exact edge case where x = 0
    if x == 0.0 {
        PowZero_nguyen5(x);   // 0^2 = 0
        TrigZero_nguyen5();   // sin(0) = 0, cos(0) = 1
        // Therefore: 0 * 1 - 1 = -1
    }
}
*/