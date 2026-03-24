include "math_library.dfy"

// MatSci25: E_0 * epsilon^2 + E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + eta * (T - T_0) * log(epsilon + 1)
function MatSci25(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, eta: real): real
    requires epsilon >= 0.0
{
    E0 * (epsilon * epsilon) + E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + eta * (T - T0) * log(epsilon + 1.0)
}

lemma prove_MatSci25_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci25(epsilon, T, E0, alpha_T, T0, eta) == 0.0
{
    // Dafny knows log(1.0) = 0.0
}