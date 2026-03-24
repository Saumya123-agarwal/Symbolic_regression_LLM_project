include "math_library.dfy"

// MatSci6: E_0 * epsilon * (-alpha_T * (T - T_0) + 1) + K * epsilon^N * exp(-Q / (R * T)) + epsilon^M * eta * (T - T_0)
function MatSci6(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, K: real, N: real, Q: real, R: real, M: real, eta: real): real
    requires epsilon >= 0.0        // Prevents imaginary numbers in pow()
    requires R > 0.0 && T > 0.0    // Prevents division by zero in exp()
    requires N >= 1.0 && M >= 1.0  // Exponents must be valid positive numbers
{
    E0 * epsilon * (-alpha_T * (T - T0) + 1.0) + K * pow(epsilon, N) * exp(-Q / (R * T)) + pow(epsilon, M) * eta * (T - T0)
}

lemma prove_MatSci6_zero_state(epsilon: real, T: real, E0: real, alpha_T: real, T0: real, K: real, N: real, Q: real, R: real, M: real, eta: real)
    requires epsilon == 0.0
    requires T == T0
    requires R > 0.0 && T > 0.0
    requires N >= 1.0 && M >= 1.0
    ensures MatSci6(epsilon, T, E0, alpha_T, T0, K, N, Q, R, M, eta) == 0.0
{
    // Teach Dafny that 0^N = 0 and 0^M = 0
    lemma_pow_zero_base(N);
    lemma_pow_zero_base(M);
}