include "math_library.dfy"

// 1. The equation: f(x) = x^5 + x^4 + x^3 + x^2 + x
function nguyen3(x: real): real
{
    (x*x*x*x*x) + (x*x*x*x) + (x*x*x) + (x*x) + x
}

// 2. Constraint 1: x > 0 ==> f(x) >= 0
lemma prove_constraint_1(x: real)
    requires x > 0.0
    ensures nguyen3(x) >= 0.0
{
    // Extract the 4th-degree term to prevent Z3 pattern-matching failures
    var poly4 := (x*x*x*x) + (x*x*x) + (x*x) + x + 1.0;
    
    lemma_factor_quintic(x);
    lemma_poly4_always_pos(x);
    
    assert poly4 > 0.0; // The solver perfectly maps this variable
    
    lemma_strict_mult_pos(x, poly4);
    
    // Explicitly connect the math back to the function
    assert x * poly4 > 0.0;
    assert nguyen3(x) == x * poly4;
    assert nguyen3(x) > 0.0;
    assert nguyen3(x) >= 0.0;
}

// 3. Constraint 2: x < 0 ==> f(x) <= 0
lemma prove_constraint_2(x: real)
    requires x < 0.0
    ensures nguyen3(x) <= 0.0
{
    // Extract the 4th-degree term
    var poly4 := (x*x*x*x) + (x*x*x) + (x*x) + x + 1.0;
    
    lemma_factor_quintic(x);
    lemma_poly4_always_pos(x);
    
    assert poly4 > 0.0; 
    
    lemma_mult_neg_pos_is_neg(x, poly4);
    
    // Explicitly connect the math back to the function
    assert x * poly4 < 0.0;
    assert nguyen3(x) == x * poly4;
    assert nguyen3(x) < 0.0;
    assert nguyen3(x) <= 0.0;
}

// 4. Constraint 3: x > 0 ==> f(x) >= f(-x)
lemma prove_constraint_3(x: real)
    requires x > 0.0
    ensures nguyen3(x) >= nguyen3(-x)
{
    // Teach Dafny how signs work with all powers up to 5
    lemma_odd_pow5(x);    // (-x)^5 == -(x^5)
    lemma_even_pow4(x);   // (-x)^4 == x^4
    lemma_odd_pow3(x);    // (-x)^3 == -(x^3)
    lemma_square_even(x); // (-x)^2 == x^2
    
    var f_x := nguyen3(x);
    var f_minus_x := nguyen3(-x);
    
    // Explicitly expand the negative evaluation
    assert f_minus_x == ((-x)*(-x)*(-x)*(-x)*(-x)) + ((-x)*(-x)*(-x)*(-x)) + ((-x)*(-x)*(-x)) + ((-x)*(-x)) + (-x);
    assert f_minus_x == -(x*x*x*x*x) + (x*x*x*x) - (x*x*x) + (x*x) - x;
    
    // Calculate the difference: f(x) - f(-x)
    // The even powers (x^4 and x^2) cancel out, doubling the odd powers
    var diff := f_x - f_minus_x;
    assert diff == 2.0 * (x*x*x*x*x) + 2.0 * (x*x*x) + 2.0 * x;
    
    // Prove the difference is > 0
    lemma_pow5_pos(x); // x^5 > 0
    lemma_cube_pos(x); // x^3 > 0
    assert (x*x*x*x*x) > 0.0;
    assert (x*x*x) > 0.0;
    
    assert diff > 0.0;
    assert diff >= 0.0;
    assert f_x >= f_minus_x;
}
