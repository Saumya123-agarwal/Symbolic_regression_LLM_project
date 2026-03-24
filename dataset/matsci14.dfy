include "math_library.dfy"

// MatSci14: -beta * (T - T_0) + epsilon * eta * exp(-(T - T_0)^2)
function MatSci14(epsilon: real, T: real, beta: real, T0: real, eta: real): real
    requires epsilon >= 0.0
{
    -beta * (T - T0) + epsilon * eta * exp(-((T - T0) * (T - T0)))
}

lemma prove_MatSci14_zero_state(epsilon: real, T: real, beta: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    ensures MatSci14(epsilon, T, beta, T0, eta) == 0.0
{
    lemma_exp_zero();
}