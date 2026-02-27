include "math_library.dfy"

// 1. The equation
function gravity(m1: real, m2: real, dist: real): real
    requires m1 > 0.0 && m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0 // Bypasses the division-by-zero error
{
    var G: real := 0.00000000006674; 
    (G * m1 * m2) / (dist * dist)
}

// 2. Pointwise Constraint: Positivity (f >= 0)
lemma prove_positivity(m1: real, m2: real, dist: real)
    requires m1 > 0.0 && m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0
    ensures gravity(m1, m2, dist) >= 0.0
{
    var G: real := 0.00000000006674;
    
    lemma_Mult_pos(m1, m2); 
    lemma_Mult_pos(G, m1 * m2);
    // Use the new division axiom to assure Dafny the final fraction is >= 0
    lemma_div_pos(G * m1 * m2, dist * dist);
}

// 3. Relational Constraint: Symmetry
lemma prove_symmetry(m1: real, m2: real, dist: real)
    requires m1 > 0.0 && m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0
    ensures gravity(m1, m2, dist) == gravity(m2, m1, dist)
{
    var f1 := gravity(m1, m2, dist);
    var f2 := gravity(m2, m1, dist);
    assert f1 == f2;
}

// 4. Relational Constraint: Monotonicity (Delta f(m1) > 0)
lemma prove_monotonicity_m1(m1a: real, m1b: real, m2: real, dist: real)
    requires 0.0 < m1a < m1b
    requires m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0
    ensures gravity(m1a, m2, dist) < gravity(m1b, m2, dist)
{
    var G: real := 0.00000000006674;
    
    // Explicitly prove that (G * m2) > 0.0 to satisfy lemma_strict_mult's precondition
    lemma_strict_mult_pos(G, m2); 
    assert (G * m2) > 0.0;
    
    lemma_strict_mult(m1a, m1b, G * m2);
    lemma_strict_div(G * m1a * m2, G * m1b * m2, dist * dist);
}

// 5. Relational Constraint: Monotonicity (Delta f(m2) > 0)
lemma prove_monotonicity_m2(m1: real, m2a: real, m2b: real, dist: real)
    requires m1 > 0.0
    requires 0.0 < m2a < m2b
    requires dist > 0.0
    requires dist * dist > 0.0
    ensures gravity(m1, m2a, dist) < gravity(m1, m2b, dist)
{
    var G: real := 0.00000000006674;
    
    // Explicitly prove that (G * m1) > 0.0 to satisfy lemma_strict_mult's precondition
    lemma_strict_mult_pos(G, m1);
    assert (G * m1) > 0.0;
    
    lemma_strict_mult(m2a, m2b, G * m1);
    lemma_strict_div(G * m1 * m2a, G * m1 * m2b, dist * dist);
}