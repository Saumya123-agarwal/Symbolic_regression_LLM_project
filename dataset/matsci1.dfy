include "math_library.dfy"

// MatSci1: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) - beta * (T - T_0) + epsilon^M * eta * (T - T_0)
function MatSci1(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, beta: real, M: real, eta: real): real
    requires epsilon >= 0.0    // FIX: Tells Dafny the base of pow() is safe (non-negative)
    requires M >= 1.0          // FIX: Tells Dafny the exponent is strictly positive
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) - beta * (T - T0) + pow(epsilon, M) * eta * (T - T0)
}

// Constraint: Zero strain and baseline temperature yields zero stress.
lemma prove_MatSci1_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, beta: real, M: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires M >= 1.0 
    ensures MatSci1(epsilon, T, E0, alpha_T, T0, beta, M, eta) == 0.0
{
    // We invoke the axiom to teach Dafny that 0.0^M = 0.0
    lemma_pow_zero_base(M);
}