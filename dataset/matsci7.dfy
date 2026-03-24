include "math_library.dfy"

// MatSci7: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + epsilon * eta * (T - T_0)^2
function MatSci7(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, eta: real): real
    requires epsilon >= 0.0 
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + epsilon * eta * (T - T0) * (T - T0)
}

lemma prove_MatSci7_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci7(epsilon, T, E0, alpha_T, T0, eta) == 0.0
{
    // No special lemmas needed, standard algebra handles this
}