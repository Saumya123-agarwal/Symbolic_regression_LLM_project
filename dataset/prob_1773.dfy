include "math_library.dfy"

method agent(x: real) returns (r: real)
    requires 0.0 <= x <= 5.0
    ensures r >= 0.0
    ensures (x == 0.0) ==> (r == 0.0)
    ensures (x <= 1.0) ==> (r <= 4.0 * x)
    ensures (x >= 1.0) ==> (r >= 4.0 * x)
{
    //"target_expression": "x^4 + x^3 + x^2 + x",
    // Compute powers of x incrementally
    var x2: real := x * x;
    lemma_Mult_pos(x, x);
    
    var x3: real := x * x2;
    lemma_Mult_pos(x, x2);
    
    var x4: real := x * x3;
    lemma_Mult_pos(x, x3);
    
    r := x4 + x3 + x2 + x;

    // Prove upper bounds when x < 1.0
    if x < 1.0 {
        lemma_Mult_symbolic_ub(x, x, 1.0);
        assert x2 <= x;
        
        lemma_Mult_symbolic_ub(x, x2, x);
        assert x3 <= x2;
        assert x3 <= x;
        
        lemma_Mult_symbolic_ub(x, x3, x);
        assert x4 <= x2;
        assert x4 <= x;
    } 
    // Prove lower bounds when x > 1.0
    else if x > 1.0 {
        lemma_Mult_symbolic_lb(x, x, 1.0);
        assert x2 >= x;
        
        lemma_Mult_symbolic_lb(x, x2, x);
        assert x3 >= x2;
        assert x3 >= x;
        
        lemma_Mult_symbolic_lb(x, x3, x);
        assert x4 >= x2;
        assert x4 >= x;
    } 
    // Trivial case for x == 1.0
    else {
        assert x == 1.0;
        assert x2 == 1.0;
        assert x3 == 1.0;
        assert x4 == 1.0;
        assert r == 4.0;
    }
}