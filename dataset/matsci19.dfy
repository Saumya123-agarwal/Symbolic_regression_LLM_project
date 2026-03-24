include "math_library.dfy"

// MatSci19: H * epsilon^3 + eta * (T - T_0) * sin(epsilon)
function MatSci19(epsilon: real, T: real, H: real, eta: real, T0: real): real
    requires epsilon >= 0.0
{
    H * (epsilon * epsilon * epsilon) + eta * (T - T0) * sin(epsilon)
}

lemma prove_MatSci19_zero_state(epsilon: real, T: real, H: real, eta: real, T0: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci19(epsilon, T, H, eta, T0) == 0.0
{
    // Dafny knows sin(0) = 0
}