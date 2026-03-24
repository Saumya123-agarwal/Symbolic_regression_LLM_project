include "math_library.dfy"

// MatSci5: E_0 * epsilon^2 + eta * (T - T_0) * log(epsilon + 1)
function MatSci5(epsilon: real, T: real, E0: real, eta: real, T0: real): real
    requires epsilon >= 0.0        // FIX: Protects log() from negative inputs or zero
{
    E0 * (epsilon * epsilon) + eta * (T - T0) * log(epsilon + 1.0)
}

lemma prove_MatSci5_zero_state(epsilon: real, T: real, E0: real, eta: real, T0: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci5(epsilon, T, E0, eta, T0) == 0.0
{
}