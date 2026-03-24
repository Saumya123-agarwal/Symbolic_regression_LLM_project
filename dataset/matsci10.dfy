include "math_library.dfy"

// MatSci10: H * epsilon^3 - beta * (T - T_0) + epsilon^3 * eta * (T - T_0)
function MatSci10(epsilon: real, T: real, H: real, beta: real, T0: real, eta: real): real
    requires epsilon >= 0.0
{
    H * (epsilon * epsilon * epsilon) - beta * (T - T0) + (epsilon * epsilon * epsilon) * eta * (T - T0)
}

lemma prove_MatSci10_zero_state(epsilon: real, T: real, H: real, beta: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci10(epsilon, T, H, beta, T0, eta) == 0.0
{
    // Standard algebra handles this perfectly
}