include "math_library.dfy"

// line no. 1933-1979 in dataset

method agent(x1: real, x2: real) returns (r: real)
    requires 0.0 <= x1 <= 5.0
    requires 0.0 <= x2 <= 5.0
    ensures r >= 0.0
    ensures (x2 == 0.0) ==> (r == 1.0)
    ensures (x1 >= 1.0 && x2 >= 2.0) ==> (r >= pow(x1, 2.0))
    ensures (x1 >= 1.0 && x2 >= 3.0) ==> (r >= pow(x1, 3.0))
    ensures (x1 <= 1.0 && x2 >= 3.0) ==> (r <= pow(x1, 3.0))
    ensures (x1 <= 1.0 && x2 >= 2.0) ==> (r <= pow(x1, 2.0))
{
    // Target Expression: x1^x2
    r := pow(x1, x2);

    // Verification Logic

    // Case 1: x1 >= 1.0
    // When the base is >= 1, the power function is monotonically increasing.
    // lemma_pow_comparator states: (1.0 <= x) && (d1 <= d2) ==> (pow(x, d1) <= pow(x, d2))
    if (x1 >= 1.0) {
        if (x2 >= 2.0) {
            // Apply lemma with d1=2.0, d2=x2. Since 2.0 <= x2, pow(x1, 2.0) <= pow(x1, x2)
            lemma_pow_comparator(x1, 2.0, x2);
        }
        if (x2 >= 3.0) {
            // Apply lemma with d1=3.0, d2=x2. Since 3.0 <= x2, pow(x1, 3.0) <= pow(x1, x2)
            lemma_pow_comparator(x1, 3.0, x2);
        }
    }

    // Case 2: x1 <= 1.0
    // When the base is <= 1 (and >= 0), the power function is monotonically decreasing.
    // lemma_pow_comparator states: (0.0 <= x <= 1.0) && (d1 <= d2) ==> (pow(x, d1) >= pow(x, d2))
    if (x1 <= 1.0) {
        if (x2 >= 2.0) {
            // Apply lemma with d1=2.0, d2=x2. Since 2.0 <= x2, pow(x1, 2.0) >= pow(x1, x2)
            // This proves r <= pow(x1, 2.0)
            lemma_pow_comparator(x1, 2.0, x2);
        }
        if (x2 >= 3.0) {
            // Apply lemma with d1=3.0, d2=x2. Since 3.0 <= x2, pow(x1, 3.0) >= pow(x1, x2)
            // This proves r <= pow(x1, 3.0)
            lemma_pow_comparator(x1, 3.0, x2);
        }
    }
}
