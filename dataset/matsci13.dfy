include "math_library.dfy"

// MatSci13: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + K * epsilon^N * exp(-Q / (R * T)) + epsilon * eta * exp(-(T - T_0)^2)
function MatSci13(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, K: real, N: real, Q: real, R: real, eta: real): real
    requires epsilon >= 0.0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + K * pow(epsilon, N) * exp(-Q / (R * T)) + epsilon * eta * exp(-((T - T0) * (T - T0)))
}

lemma prove_MatSci13_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, K: real, N: real, Q: real, R: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0
    ensures MatSci13(epsilon, T, E0, alpha_T, T0, K, N, Q, R, eta) == 0.0
{
    lemma_pow_zero_base(N);
    lemma_exp_zero();
}