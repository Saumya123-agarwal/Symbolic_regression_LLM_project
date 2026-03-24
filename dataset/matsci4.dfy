include "math_library.dfy"

// MatSci4: H * epsilon^3 + K * epsilon^N * exp(-Q / (R * T)) + epsilon^3 * eta * (T - T_0)
function MatSci4(epsilon: real, T: real, H: real, K: real, N: real, Q: real, R: real, T0: real, eta: real): real
    requires epsilon >= 0.0        // FIX: Pow base must be non-negative
    requires N >= 1.0              // FIX: Pow exponent constraint
    requires R > 0.0 && T > 0.0    // Prevent division by zero
{
    H * (epsilon * epsilon * epsilon) + K * pow(epsilon, N) * exp(-Q / (R * T)) + (epsilon * epsilon * epsilon) * eta * (T - T0)
}

lemma prove_MatSci4_zero_state(epsilon: real, T: real, H: real, K: real, N: real, Q: real, R: real, T0: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0
    ensures MatSci4(epsilon, T, H, K, N, Q, R, T0, eta) == 0.0
{
    lemma_pow_zero_base(N);
}