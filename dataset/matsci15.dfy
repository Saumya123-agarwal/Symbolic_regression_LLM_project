include "math_library.dfy"

// MatSci15: -beta * (T - T_0) + epsilon^M * eta * (T - T_0)
function MatSci15(epsilon: real, T: real, beta: real, T0: real, M: real, eta: real): real
    requires epsilon >= 0.0
    requires M >= 1.0
{
    -beta * (T - T0) + pow(epsilon, M) * eta * (T - T0)
}

lemma prove_MatSci15_zero_state(epsilon: real, T: real, beta: real, T0: real, M: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires M >= 1.0
    ensures MatSci15(epsilon, T, beta, T0, M, eta) == 0.0
{
    lemma_pow_zero_base(M);
}