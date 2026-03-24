include "math_library.dfy"

// MatSci17: E_0 * epsilon^2 + epsilon * eta * (T - T_0)^2
function MatSci17(epsilon: real, T: real, E0: real, eta: real, T0: real): real
    requires epsilon >= 0.0
{
    E0 * (epsilon * epsilon) + epsilon * eta * (T - T0) * (T - T0)
}

lemma prove_MatSci17_zero_state(epsilon: real, T: real, E0: real, eta: real, T0: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci17(epsilon, T, E0, eta, T0) == 0.0
{
    // Standard algebra handles this perfectly
}