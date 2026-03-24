include "math_library.dfy"

// MatSci8: H * epsilon^3 - beta * (T - T_0) + eta * (T - T_0) * log(epsilon + 1)
function MatSci8(epsilon: real, T: real, H: real, beta: real, T0: real, eta: real): real
    requires epsilon >= 0.0       // Protects log() from negative inputs
{
    H * (epsilon * epsilon * epsilon) - beta * (T - T0) + eta * (T - T0) * log(epsilon + 1.0)
}

lemma prove_MatSci8_zero_state(epsilon: real, T: real, H: real, beta: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci8(epsilon, T, H, beta, T0, eta) == 0.0
{
    // Dafny's extern log definition knows log(1.0) == 0.0
}