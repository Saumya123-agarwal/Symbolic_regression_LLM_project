include "math_library.dfy"

// line no. 1851-1891 in dataset

method agent(x1: real, x2: real) returns (r: real)
    requires -1.0 <= x1 <= 5.0
    requires -1.0 <= x2 <= 5.0
    ensures r >= -2.0
    ensures r <= 2.0
    ensures (x1 == 0.0) ==> (r == 0.0)
{
    // Target Expression: 2 * sin(x1) * cos(x2)

    // 1. Compute the sine component
    var s := sin(x1);
    // From library: -1.0 <= s <= 1.0 [cite: 4]

    // 2. Compute the cosine component
    var c := cos(x2);
    // From library: -1.0 <= c <= 1.0 [cite: 4]

    // 3. Verify the product of sine and cosine
    // We use lemma_wave_multiplication to prove that the product of two bounded 
    // wave functions is bounded by the product of their amplitudes.
    // Here, both have an implicit amplitude of 1.0.
    lemma_wave_multiplication(s, 1.0, c, 1.0);
    
    // The lemma guarantees: -(1.0*1.0) <= s*c <= (1.0*1.0)
    assert -1.0 <= s * c <= 1.0;

    // 4. Compute final result
    r := 2.0 * (s * c);

    // 5. Verify constraints
    // Since -1.0 <= s*c <= 1.0, multiplying by 2.0 results in -2.0 <= r <= 2.0.
    assert -2.0 <= r <= 2.0;
    // Specific check for x1 == 0.0
    if (x1 == 0.0) {
        // Library specifies: (x == 0.0) ==> (sin(x) == 0.0) [cite: 4]
        // Therefore s == 0.0, and 0.0 * c == 0.0
        assert r == 0.0;
    }
}