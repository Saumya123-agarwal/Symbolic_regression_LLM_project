// ==========================================
// PROBLEM 4: Spring Restoring Force
// Target: -k * x
// ==========================================

// 2. THE FUNCTION (No lemma needed for purely linear algebra)
ghost function f_spring(x: real, k: real): real {
    -k * x
}

// 3. THE VERIFICATION
lemma Verify_spring(x: real, k: real)
    // Constraint A: Odd Function (Domain Symmetry)
    // The negative of the function is equal to the function of the negative input
    ensures -f_spring(x, k) == f_spring(-x, k)
{
    // Z3 natively understands that -(-k * x) == -k * (-x), 
    // so this will verify instantly without any helper axioms!
}