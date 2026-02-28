include "math_library.dfy"


method agent(x: real) returns (r: real)
    requires 0.0 <= x <= 5.0
    ensures r >= 0.0
    ensures (x == 0.0) ==> (r <= 0.0)
    ensures (x >= exp(3.0)) ==> (r >= 9.0)
    ensures (x >= exp(2.0)) ==> (r >= 5.0)
    ensures (x <= 1.0) ==> (r <= 2.0)
{
    //"target_expression": "log(x + 1) + log(x^2 + 1)",
    // 1. Establish constant bounds to resolve vacuous truths
    lemma_exp_bounds();

    // 2. Compute intermediate terms
    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    
    var term1: real := x + 1.0;
    var term2: real := x2 + 1.0;
    
    var log1: real := log(term1);
    var log2: real := log(term2);
    
    r := log1 + log2;

    // 3. Prove behavior at x == 0.0
    if x == 0.0 {
        assert term1 == 1.0;
        assert term2 == 1.0;
        // From math_library.dfy: log(1.0) == 0.0
        assert log1 == 0.0;
        assert log2 == 0.0;
        assert r == 0.0;
    }
    
    // 4. Prove upper bounds when x <= 1.0
    if x <= 1.0 {
        // Prove that x^2 <= x for x in [0, 1]
        lemma_Mult_symbolic_ub(x, x, 1.0);
        assert x2 <= x;
        assert x2 <= 1.0;
        
        // Both inner terms are bounded by 2.0
        assert term1 <= 2.0;
        assert term2 <= 2.0;
        
        // Apply our custom upper-bound lemma
        lemma_log_upper_bound_2(term1);
        lemma_log_upper_bound_2(term2);
        
        assert log1 <= 1.0;
        assert log2 <= 1.0;
        assert r <= 2.0;
    }
}