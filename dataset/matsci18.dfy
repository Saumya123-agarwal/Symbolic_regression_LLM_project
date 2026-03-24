include "math_library.dfy"

// MatSci18: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) - beta * (T - T_0) + eta * (T - T_0) * log(epsilon + 1)
function MatSci18(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, beta: real, eta: real): real
    requires epsilon >= 0.0    // Protects log() from negative inputs
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) - beta * (T - T0) + eta * (T - T0) * log(epsilon + 1.0)
}

lemma prove_MatSci18_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, beta: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci18(epsilon, T, E0, alpha_T, T0, beta, eta) == 0.0
{
    // Dafny's extern log definition knows log(1.0) == 0.0
}