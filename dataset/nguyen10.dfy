include "math_library.dfy"

// line no. 1892-1932 in dataset

method agent(x1: real, x2: real) returns (r: real)
    requires -1.0 <= x1 <= 5.0
    requires -1.0 <= x2 <= 5.0
    ensures r >= -2.0
    ensures r <= 2.0
    ensures (x1 == 0.0) ==> (r == 0.0)
{
    // Target Expression: 2 * sin(x1)^2 * cos(x2)

    // 1. Calculate sin(x1)
    var s := sin(x1);
    // Postcondition of sin ensures -1.0 <= s <= 1.0

    // 2. Calculate sin(x1)^2
    var s2 := s * s;
    
    // Bounds for s^2
    // Lower bound: Square is always non-negative
    lemma_square(s, s2);
    assert s2 >= 0.0;
    
    // Upper bound: Use interval multiplication on s * s with range [-1, 1]
    // max(max(-1*-1, -1*1), max(1*-1, 1*1)) = max(1, 1) = 1.0
    lemma_interval_bounds_multiplication(s, -1.0, 1.0, s, -1.0, 1.0);
    assert s2 <= 1.0;

    // 3. Calculate cos(x2)
    var c := cos(x2);
    // Postcondition of cos ensures -1.0 <= c <= 1.0

    // 4. Calculate s^2 * cos(x2)
    var term := s2 * c;
    
    // Bounds for term
    // s2 is [0, 1], c is [-1, 1]
    // min bounds: min(min(0*-1, 0*1), min(1*-1, 1*1)) = min(0, -1) = -1.0
    // max bounds: max(max(0*-1, 0*1), max(1*-1, 1*1)) = max(0, 1) = 1.0
    lemma_interval_bounds_multiplication(s2, 0.0, 1.0, c, -1.0, 1.0);
    assert -1.0 <= term <= 1.0;

    // 5. Final result
    r := 2.0 * term;
    // Since -1.0 <= term <= 1.0, multiplying by 2.0 gives -2.0 <= r <= 2.0
    
    // Verification for x1 == 0.0 case
    if (x1 == 0.0) {
        // sin(0.0) == 0.0 implies s == 0.0, s2 == 0.0, term == 0.0, r == 0.0
        assert r == 0.0;
    }
}