include "math_library.dfy"

ghost function f_kepler(m1: real, m2: real, d: real, G: real): real 
{
    // Check for division by zero FIRST
    if (G * (m1 + m2) == 0.0) then 0.0 
    // Then check for negative square roots
    else if (((4.0 * 3.14159 * 3.14159 * d * d * d) / (G * (m1 + m2))) < 0.0) then 0.0
    // If both are safe, do the math
    else sqrt(((4.0 * 3.14159 * 3.14159 * d * d * d) / (G * (m1 + m2))))
}


lemma Verify_kepler(m1: real, m2: real, d: real, d_b: real, G: real)
    requires m1 > 0.0 && m2 > 0.0 && d > 0.0 && G > 0.0 && d_b > 0.0
    // Constraint A: Positivity
    ensures f_kepler(m1, m2, d, G) > 0.0
    // Constraint B: Mass Symmetry
    ensures f_kepler(m1, m2, d, G) == f_kepler(m2, m1, d, G)
    // Constraint C: Monotonicity
    ensures (d_b > d) ==> (f_kepler(m1, m2, d_b, G) > f_kepler(m1, m2, d, G))
{
    lemma_kepler_rules(m1, m2, d, d_b, G);
}












