include "math_library.dfy"

// MatSci23: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + H * epsilon^3 + eta * (T - T_0) * sin(epsilon)
function MatSci23(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, H: real, eta: real): real
    requires epsilon >= 0.0
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + H * (epsilon * epsilon * epsilon) + eta * (T - T0) * sin(epsilon)
}

lemma prove_MatSci23_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, H: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci23(epsilon, T, E0, alpha_T, T0, H, eta) == 0.0
{
    // Standard algebra + sin(0) = 0
}