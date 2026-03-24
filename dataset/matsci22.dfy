include "math_library.dfy"

// MatSci22: K * epsilon^N * exp(-Q / (R * T)) - beta * (T - T_0) + eta * (T - T_0) * log(epsilon + 1)
function MatSci22(epsilon: real, T: real, K: real, N: real, Q: real, R: real, T0: real, beta: real, eta: real): real
    requires epsilon >= 0.0        // Protects log() and pow() from negative inputs
    requires R > 0.0 && T > 0.0    // Prevents division by zero
    requires N >= 1.0              // Exponent must be valid
{
    K * pow(epsilon, N) * exp(-Q / (R * T)) - beta * (T - T0) + eta * (T - T0) * log(epsilon + 1.0)
}

lemma prove_MatSci22_zero_state(epsilon: real, T: real, K: real, N: real, Q: real, R: real, T0: real, beta: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0
    ensures MatSci22(epsilon, T, K, N, Q, R, T0, beta, eta) == 0.0
{
    lemma_pow_zero_base(N);
}