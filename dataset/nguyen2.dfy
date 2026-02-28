include "math_library.dfy"

// line no. 1810-1850 in dataset

method agent(x: real) returns (r: real)
    requires 0.0 <= x <= 5.0
    ensures r >= 0.0
    ensures (x == 0.0) ==> (r == 0.0)
    ensures (x <= 1.0) ==> (r <= 4.0 * x)
    ensures (x >= 1.0) ==> (r >= 4.0 * x)
    ensures (x >= 1.0) ==> (r <= 4.0 * pow(x, 4.0))
    ensures (x <= 1.0) ==> (r >= 4.0 * pow(x, 4.0))
{
    // Target Expression: x^4 + x^3 + x^2 + x
    
    // 1. Calculate individual terms
    var p1 := pow(x, 1.0);
    var p2 := pow(x, 2.0);
    var p3 := pow(x, 3.0);
    var p4 := pow(x, 4.0);

    r := p4 + p3 + p2 + p1;

    // 2. Establish Base Identity
    // Use lemma to prove pow(x, 1.0) is exactly x [cite: 14]
    lemma_pow_mult(x, p1);

    // 3. Verification for x >= 1.0
    // When base >= 1, power function is monotonic increasing with the exponent 
    if (x >= 1.0) {
        // Prove r >= 4.0 * x (i.e., sum(p_i) >= 4 * p1)
        // We show p2, p3, p4 are all >= p1
        lemma_pow_comparator(x, 1.0, 2.0); // p1 <= p2
        lemma_pow_comparator(x, 1.0, 3.0); // p1 <= p3
        lemma_pow_comparator(x, 1.0, 4.0); // p1 <= p4

        // Prove r <= 4.0 * x^4 (i.e., sum(p_i) <= 4 * p4)
        // We show p1, p2, p3 are all <= p4
        lemma_pow_comparator(x, 1.0, 4.0); // p1 <= p4
        lemma_pow_comparator(x, 2.0, 4.0); // p2 <= p4
        lemma_pow_comparator(x, 3.0, 4.0); // p3 <= p4
    }

    // 4. Verification for x <= 1.0
    // When base <= 1, power function is monotonic decreasing with the exponent 
    if (x <= 1.0) {
        // Prove r <= 4.0 * x (i.e., sum(p_i) <= 4 * p1)
        // We show p2, p3, p4 are all <= p1
        lemma_pow_comparator(x, 1.0, 2.0); // p1 >= p2
        lemma_pow_comparator(x, 1.0, 3.0); // p1 >= p3
        lemma_pow_comparator(x, 1.0, 4.0); // p1 >= p4

        // Prove r >= 4.0 * x^4 (i.e., sum(p_i) >= 4 * p4)
        // We show p1, p2, p3 are all >= p4
        lemma_pow_comparator(x, 1.0, 4.0); // p1 >= p4
        lemma_pow_comparator(x, 2.0, 4.0); // p2 >= p4
        lemma_pow_comparator(x, 3.0, 4.0); // p3 >= p4
    }

    // 5. Verification for x == 0.0
    if (x == 0.0) {
        // p1 is 0.0 via lemma_pow_mult.
        // p4 <= p1 (proven in x <= 1.0 block) implies p4 == 0.0 (since p4 >= 0.0).
        // Similarly for p2, p3.
        assert r == 0.0;
    }
}