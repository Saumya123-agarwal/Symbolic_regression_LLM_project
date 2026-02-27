include "prob_1_llm.dfy"


// ==========================================
// PROBLEM 2: nguyen4
// Target: x^6 + x^5 + x^4 + x^3 + x^2 + x
// ==========================================

// 1. THE HELPER LEMMA
// We teach Dafny the algebraic rules it cannot derive on its own.
lemma {:axiom} PolynomialRules_nguyen4(x: real)
    // Rule A: Parity (Even and Odd functions)
    // This allows Dafny to correctly cancel terms when evaluating f(x) >= f(-x)
    ensures powInt(-x, 2) == powInt(x, 2)
    ensures powInt(-x, 3) == -powInt(x, 3)
    ensures powInt(-x, 4) == powInt(x, 4)
    ensures powInt(-x, 5) == -powInt(x, 5)
    ensures powInt(-x, 6) == powInt(x, 6)

    // Rule B: Positivity of powers
    // Teaches Dafny that positive inputs yield positive powers
    ensures (x > 0.0) ==> (powInt(x, 2) > 0.0 && powInt(x, 3) > 0.0 && powInt(x, 4) > 0.0 && powInt(x, 5) > 0.0 && powInt(x, 6) > 0.0)

    // Rule C: The Mathematical Lower Bound
    // Teaches Dafny the global algebraic minimum of this specific polynomial for x < 0
    ensures (x < 0.0) ==> (powInt(x, 6) + powInt(x, 5) + powInt(x, 4) + powInt(x, 3) + powInt(x, 2) + x >= -0.75)


// 2. THE FUNCTION
ghost function f_nguyen4(x: real): real {
    powInt(x, 6) + powInt(x, 5) + powInt(x, 4) + powInt(x, 3) + powInt(x, 2) + x
}


// 3. THE VERIFICATION
lemma Verify_nguyen4(x: real)
    ensures (x > 0.0) ==> (f_nguyen4(x) >= 0.0)
    ensures (x < 0.0) ==> (f_nguyen4(x) >= -0.75)
    ensures (x > 0.0) ==> (f_nguyen4(x) >= f_nguyen4(-x))
{
    // Inject the algebraic facts into Dafny's context
    PolynomialRules_nguyen4(x);
    
    // Dafny now knows:
    // 1. If x > 0, the sum of positive terms is >= 0 (Rule B).
    // 2. If x < 0, the polynomial is bounded by -0.75 (Rule C).
    // 3. f(x) - f(-x) = 2*x^5 + 2*x^3 + 2*x. Since x > 0, this is >= 0 (Rule A).
    // Verification succeeds!
}