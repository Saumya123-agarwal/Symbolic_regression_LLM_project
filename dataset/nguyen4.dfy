include "math_library.dfy"

// line no. 1980-2018 in dataset

method agent(x: real) returns (r: real)
    requires 0.0 <= x <= 5.0
    ensures r >= 0.0
    ensures (x >= 1.0) ==> (r <= 6.0 * pow(x, 6.0))
    ensures (x <= 1.0) ==> (r >= 6.0 * pow(x, 6.0))
    ensures (x <= 1.0) ==> (r <= 6.0 * x)
    ensures (x >= 1.0) ==> (r >= 6.0 * x)
{
    var p1 := pow(x, 1.0);
    var p2 := pow(x, 2.0);
    var p3 := pow(x, 3.0);
    var p4 := pow(x, 4.0);
    var p5 := pow(x, 5.0);
    var p6 := pow(x, 6.0);

    r := p6 + p5 + p4 + p3 + p2 + p1;

    lemma_pow_mult(x, x);

    if (x >= 1.0) {
        // Case: x >= 1.0
        // We use lemma_pow_comparator to prove that lower powers are smaller than higher powers.
        // For x >= 1.0 and d1 <= d2, pow(x, d1) <= pow(x, d2).

        // 1. Prove r <= 6 * x^6
        // We show that p1...p5 are all <= p6 (x^6)
        lemma_pow_comparator(x, 1.0, 6.0); // x^1 <= x^6
        lemma_pow_comparator(x, 2.0, 6.0); // x^2 <= x^6
        lemma_pow_comparator(x, 3.0, 6.0);
        lemma_pow_comparator(x, 4.0, 6.0);
        lemma_pow_comparator(x, 5.0, 6.0);
        // Therefore, sum(p_i) <= 6 * p6

        // 2. Prove r >= 6 * x
        // We show that p2...p6 are all >= p1 (x)
        lemma_pow_comparator(x, 1.0, 2.0); // x^1 <= x^2
        lemma_pow_comparator(x, 1.0, 3.0);
        lemma_pow_comparator(x, 1.0, 4.0);
        lemma_pow_comparator(x, 1.0, 5.0);
        lemma_pow_comparator(x, 1.0, 6.0);
        // Therefore, sum(p_i) >= 6 * p1
    }

    if (x <= 1.0) {
        // Case: 0.0 <= x <= 1.0
        // We use lemma_pow_comparator to prove that lower powers are larger than higher powers.
        // For 0 <= x <= 1.0 and d1 <= d2, pow(x, d1) >= pow(x, d2).

        // 1. Prove r >= 6 * x^6
        // We show that p1...p5 are all >= p6 (x^6)
        lemma_pow_comparator(x, 1.0, 6.0); // x^1 >= x^6
        lemma_pow_comparator(x, 2.0, 6.0); // x^2 >= x^6
        lemma_pow_comparator(x, 3.0, 6.0);
        lemma_pow_comparator(x, 4.0, 6.0);
        lemma_pow_comparator(x, 5.0, 6.0);
        // Therefore, sum(p_i) >= 6 * p6

        // 2. Prove r <= 6 * x
        // We show that p2...p6 are all <= p1 (x)
        lemma_pow_comparator(x, 1.0, 2.0); // x^1 >= x^2
        lemma_pow_comparator(x, 1.0, 3.0);
        lemma_pow_comparator(x, 1.0, 4.0);
        lemma_pow_comparator(x, 1.0, 5.0);
        lemma_pow_comparator(x, 1.0, 6.0);
        // Therefore, sum(p_i) <= 6 * p1
    }
}