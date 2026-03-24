include "math_library.dfy"

// MatSci9: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + epsilon^M * eta * (T - T_0)
function MatSci9(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, M: real, eta: real): real
    requires epsilon >= 0.0        // Prevents imaginary numbers in pow()
    requires M >= 1.0              // Exponent must be valid
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + pow(epsilon, M) * eta * (T - T0)
}

lemma prove_MatSci9_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, M: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires M >= 1.0
    ensures MatSci9(epsilon, T, E0, alpha_T, T0, M, eta) == 0.0
{
    lemma_pow_zero_base(M);
}