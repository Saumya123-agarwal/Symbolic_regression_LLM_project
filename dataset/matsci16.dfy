include "math_library.dfy"

// MatSci16: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + epsilon * eta * exp(-(T - T_0)^2)
function MatSci16(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, eta: real): real
    requires epsilon >= 0.0
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + epsilon * eta * exp(-((T - T0) * (T - T0)))
}

lemma prove_MatSci16_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci16(epsilon, T, E0, alpha_T, T0, eta) == 0.0
{
    lemma_exp_zero();
}