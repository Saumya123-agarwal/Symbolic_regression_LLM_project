include "math_library.dfy"

// 1. The equation
function res3(r1: real, r2: real, r3: real): real
    requires r1 > 0.0 && r2 > 0.0 && r3 > 0.0
    requires ((r1 * r2) + (r1 * r3) + (r2 * r3)) != 0.0
{
    (r1 * r2 * r3) / ((r1 * r2) + (r1 * r3) + (r2 * r3))
}

// Helper Lemma: Prove the denominator is always strictly positive
lemma prove_denominator_valid(r1: real, r2: real, r3: real)
    requires r1 > 0.0 && r2 > 0.0 && r3 > 0.0
    ensures ((r1 * r2) + (r1 * r3) + (r2 * r3)) > 0.0
{
    lemma_strict_mult_pos(r1, r2);
    lemma_strict_mult_pos(r1, r3);
    lemma_strict_mult_pos(r2, r3);
}

// 2. Constraint 1: Symmetry across permutations
lemma prove_constraint_1(r1: real, r2: real, r3: real)
    requires r1 > 0.0 && r2 > 0.0 && r3 > 0.0
    requires ((r1 * r2) + (r1 * r3) + (r2 * r3)) != 0.0
    ensures res3(r1, r2, r3) == res3(r2, r1, r3)
    ensures res3(r1, r2, r3) == res3(r3, r2, r1)
    ensures res3(r1, r2, r3) == res3(r1, r3, r2)
{
    // Dafny natively handles the commutative properties
}

// 3. Constraint 2: f <= r1 AND f <= r2 AND f <= r3
lemma prove_constraint_2(r1: real, r2: real, r3: real)
    requires r1 > 0.0 && r2 > 0.0 && r3 > 0.0
    requires ((r1 * r2) + (r1 * r3) + (r2 * r3)) != 0.0
    ensures res3(r1, r2, r3) <= r1
    ensures res3(r1, r2, r3) <= r2
    ensures res3(r1, r2, r3) <= r3
{
    prove_denominator_valid(r1, r2, r3);
    var den := (r1 * r2) + (r1 * r3) + (r2 * r3);
    
    // Part A: Prove f <= r1
    lemma_strict_mult_pos(r2, r3); 
    assert den >= (r2 * r3); 
    lemma_res3_bound_r1(r1, r2, r3, den); 
    
    // Part B: Prove f <= r2
    lemma_strict_mult_pos(r1, r3);
    assert den >= (r1 * r3);
    lemma_res3_bound_r2(r1, r2, r3, den);
    
    // Part C: Prove f <= r3
    lemma_strict_mult_pos(r1, r2);
    assert den >= (r1 * r2);
    lemma_res3_bound_r3(r1, r2, r3, den);
}

// 4. Constraint 3: f > 0 (Strict Positivity)
lemma prove_constraint_3(r1: real, r2: real, r3: real)
    requires r1 > 0.0 && r2 > 0.0 && r3 > 0.0
    requires ((r1 * r2) + (r1 * r3) + (r2 * r3)) != 0.0
    ensures res3(r1, r2, r3) > 0.0
{
    prove_denominator_valid(r1, r2, r3);
    var den := (r1 * r2) + (r1 * r3) + (r2 * r3);
    
    // Prove the numerator is strictly positive
    lemma_strict_mult_pos(r2, r3);
    lemma_strict_mult_pos(r1, r2 * r3); 
    assert (r1 * r2 * r3) == r1 * (r2 * r3);
    assert (r1 * r2 * r3) > 0.0;
    
    // Prove strictly positive / strictly positive > 0
    lemma_strict_div_pos((r1 * r2 * r3), den);
}
