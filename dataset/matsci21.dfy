include "math_library.dfy"

// MatSci21: E_0 * epsilon^2 + epsilon * eta * sin(T - T_0)
function MatSci21(epsilon: real, T: real, E0: real, eta: real, T0: real): real
    requires epsilon >= 0.0
{
    E0 * (epsilon * epsilon) + epsilon * eta * sin(T - T0)
}

lemma prove_MatSci21_zero_state(epsilon: real, T: real, E0: real, eta: real, T0: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci21(epsilon, T, E0, eta, T0) == 0.0
{
    // Dafny knows sin(0) = 0
}