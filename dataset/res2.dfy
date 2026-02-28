include "math_library.dfy"

// 1. The equation: f(r1, r2) = (r1 * r2) / (r1 + r2)
function res2(r1: real, r2: real): real
    requires r1 > 0.0 && r2 > 0.0
    requires r1 + r2 != 0.0 // Strict zero-check for the denominator
{
    (r1 * r2) / (r1 + r2)
}

// 2. Constraint 1: f(r1, r2) == f(r2, r1) (Symmetry)
lemma prove_constraint_1(r1: real, r2: real)
    requires r1 > 0.0 && r2 > 0.0
    requires r1 + r2 != 0.0
    ensures res2(r1, r2) == res2(r2, r1)
{
    // Dafny natively handles the commutative properties of addition and multiplication
    assert (r1 * r2) == (r2 * r1);
    assert (r1 + r2) == (r2 + r1);
}

// 3. Constraint 2: f(r1, r2) <= r1 AND f(r1, r2) <= r2
lemma prove_constraint_2(r1: real, r2: real)
    requires r1 > 0.0 && r2 > 0.0
    requires r1 + r2 != 0.0
    ensures res2(r1, r2) <= r1
    ensures res2(r1, r2) <= r2
{
    var den := r1 + r2;
    
    // Prove the denominator bounds (because r1 and r2 are strictly positive)
    assert den >= r2; 
    assert den >= r1;
    assert den > 0.0;
    
    // Part A: Prove f <= r1
    lemma_fraction_upper_bound(r1, r2, den);
    assert (r1 * r2) / den <= r1;
    
    // Part B: Prove f <= r2
    // We swap the numerator factors to match the axiom's requirement
    assert (r1 * r2) == (r2 * r1);
    lemma_fraction_upper_bound(r2, r1, den);
    
    assert (r2 * r1) / den <= r2;
    assert (r1 * r2) / den <= r2; // Map it back to the original equation
}

// 4. Constraint 3: f(r1, r2) > 0 (Strict Positivity)
lemma prove_constraint_3(r1: real, r2: real)
    requires r1 > 0.0 && r2 > 0.0
    requires r1 + r2 != 0.0
    ensures res2(r1, r2) > 0.0
{
    var den := r1 + r2;
    assert den > 0.0;
    
    // Prove the numerator is strictly positive
    lemma_strict_mult_pos(r1, r2);
    assert (r1 * r2) > 0.0;
    
    // Prove strictly positive / strictly positive > 0
    lemma_strict_div_pos((r1 * r2), den);
}
