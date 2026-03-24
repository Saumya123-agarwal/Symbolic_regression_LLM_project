include "math_library.dfy"

// MatSci12: K * epsilon^N * exp(-Q / (R * T)) + epsilon^3 * eta * (T - T_0)
function MatSci12(epsilon: real, T: real, K: real, N: real, Q: real, R: real, T0: real, eta: real): real
    requires epsilon >= 0.0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0
{
    K * pow(epsilon, N) * exp(-Q / (R * T)) + (epsilon * epsilon * epsilon) * eta * (T - T0)
}

lemma prove_MatSci12_zero_state(epsilon: real, T: real, K: real, N: real, Q: real, R: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0
    ensures MatSci12(epsilon, T, K, N, Q, R, T0, eta) == 0.0
{
    lemma_pow_zero_base(N);
}