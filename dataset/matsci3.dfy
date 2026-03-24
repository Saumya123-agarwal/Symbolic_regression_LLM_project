include "math_library.dfy"

// MatSci3: H * epsilon^3 + eta * (T - T_0) * exp(-epsilon)
function MatSci3(epsilon: real, T: real, H: real, eta: real, T0: real): real
{
    H * (epsilon * epsilon * epsilon) + eta * (T - T0) * exp(-epsilon)
}

lemma prove_MatSci3_zero_state(epsilon: real, T: real, H: real, eta: real, T0: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci3(epsilon, T, H, eta, T0) == 0.0
{
    lemma_exp_zero();
}