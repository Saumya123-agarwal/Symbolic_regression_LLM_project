include "math_library.dfy"

// MatSci20: E_0 * epsilon^2 - beta * (T - T_0) + epsilon^3 * eta * (T - T_0)
function MatSci20(epsilon: real, T: real, E0: real, beta: real, T0: real, eta: real): real
    requires epsilon >= 0.0
{
    E0 * (epsilon * epsilon) - beta * (T - T0) + (epsilon * epsilon * epsilon) * eta * (T - T0)
}

lemma prove_MatSci20_zero_state(epsilon: real, T: real, E0: real, beta: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci20(epsilon, T, E0, beta, T0, eta) == 0.0
{
}