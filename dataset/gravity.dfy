include "math_library.dfy"

// 1. The equation, with explicit grouping and strict zero-checks
function gravity(m1: real, m2: real, dist: real): real
    requires m1 > 0.0 && m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0 
    requires dist * dist != 0.0 // Shuts down the "possible division by zero" error
{
    var G: real := 0.00000000006674; 
    (G * (m1 * m2)) / (dist * dist)
}

// 2. Pointwise Constraint: Positivity (f >= 0)
lemma prove_positivity(m1: real, m2: real, dist: real)
    requires m1 > 0.0 && m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0 && dist * dist != 0.0
    ensures gravity(m1, m2, dist) >= 0.0
{
    var G: real := 0.00000000006674;
    
    // Prove m1 * m2 is strictly positive
    lemma_strict_mult_pos(m1, m2); 
    assert (m1 * m2) > 0.0;
    
    // Prove G * (m1 * m2) is strictly positive
    lemma_strict_mult_pos(G, (m1 * m2));
    assert G * (m1 * m2) > 0.0;
    assert G * (m1 * m2) >= 0.0;
    
    // Prove the division remains positive
    lemma_div_pos(G * (m1 * m2), dist * dist);
}

// 3. Relational Constraint: Symmetry
lemma prove_symmetry(m1: real, m2: real, dist: real)
    requires m1 > 0.0 && m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0 && dist * dist != 0.0
    ensures gravity(m1, m2, dist) == gravity(m2, m1, dist)
{
    // Dafny can automatically prove this because real multiplication is commutative
    assert m1 * m2 == m2 * m1;
}

// 4. Relational Constraint: Monotonicity (Delta f(m1) > 0)
lemma prove_monotonicity_m1(m1a: real, m1b: real, m2: real, dist: real)
    requires 0.0 < m1a < m1b
    requires m2 > 0.0 && dist > 0.0
    requires dist * dist > 0.0 && dist * dist != 0.0
    ensures gravity(m1a, m2, dist) < gravity(m1b, m2, dist)
{
    var G: real := 0.00000000006674;
    
    // Step 1: Prove (m1a * m2) < (m1b * m2)
    lemma_strict_mult(m1a, m1b, m2);
    assert (m1a * m2) < (m1b * m2);
    
    // Step 2: Multiply by G. (We pass G as 'c' to the lemma)
    lemma_strict_mult(m1a * m2, m1b * m2, G);
    assert (m1a * m2) * G < (m1b * m2) * G;
    
    // Remind Dafny about commutativity so it matches our function
    assert G * (m1a * m2) == (m1a * m2) * G;
    assert G * (m1b * m2) == (m1b * m2) * G;
    assert G * (m1a * m2) < G * (m1b * m2);
    
    // Step 3: Divide by dist^2
    lemma_strict_div(G * (m1a * m2), G * (m1b * m2), dist * dist);
}

// 5. Relational Constraint: Monotonicity (Delta f(m2) > 0)
lemma prove_monotonicity_m2(m1: real, m2a: real, m2b: real, dist: real)
    requires m1 > 0.0
    requires 0.0 < m2a < m2b
    requires dist > 0.0
    requires dist * dist > 0.0 && dist * dist != 0.0
    ensures gravity(m1, m2a, dist) < gravity(m1, m2b, dist)
{
    var G: real := 0.00000000006674;
    
    // Step 1: Prove (m2a * m1) < (m2b * m1)
    lemma_strict_mult(m2a, m2b, m1);
    assert (m2a * m1) < (m2b * m1);
    
    // Remind Dafny about commutativity
    assert (m1 * m2a) == (m2a * m1);
    assert (m1 * m2b) == (m2b * m1);
    assert (m1 * m2a) < (m1 * m2b);
    
    // Step 2: Multiply by G
    lemma_strict_mult(m1 * m2a, m1 * m2b, G);
    assert (m1 * m2a) * G < (m1 * m2b) * G;
    assert G * (m1 * m2a) == (m1 * m2a) * G;
    assert G * (m1 * m2b) == (m1 * m2b) * G;
    assert G * (m1 * m2a) < G * (m1 * m2b);
    
    // Step 3: Divide by dist^2
    lemma_strict_div(G * (m1 * m2a), G * (m1 * m2b), dist * dist);
}
