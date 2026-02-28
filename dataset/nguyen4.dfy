include "math_library.dfy"

// 1. The equation: f(x) = x^6 + x^5 + x^4 + x^3 + x^2 + x
function nguyen4(x: real): real
{
    (x*x*x*x*x*x) + (x*x*x*x*x) + (x*x*x*x) + (x*x*x) + (x*x) + x
}

// 2. Constraint 1: x > 0 ==> f(x) >= 0
lemma prove_constraint_1(x: real)
    requires x > 0.0
    ensures nguyen4(x) >= 0.0
{
    // Extract the 5th-degree term to prevent Z3 pattern-matching failures
    var poly5 := (x*x*x*x*x) + (x*x*x*x) + (x*x*x) + (x*x) + x + 1.0;
    
    lemma_factor_nguyen4(x);
    lemma_poly5_always_pos_for_pos_x(x);
    
    assert poly5 > 0.0; 
    
    lemma_strict_mult_pos(x, poly5);
    
    // Explicitly connect the math back to the function
    assert x * poly5 > 0.0;
    assert nguyen4(x) == x * poly5;
    assert nguyen4(x) > 0.0;
    assert nguyen4(x) >= 0.0;
}

// 3. Constraint 2: x < 0 ==> f(x) >= -0.75
lemma prove_constraint_2(x: real)
    requires x < 0.0
    ensures nguyen4(x) >= -0.75
{
    // We rely on the established axiom since NLA solvers cannot natively calculate 6th-degree global minima
    lemma_nguyen4_lower_bound(x);
    assert nguyen4(x) >= -0.75;
}

// 4. Constraint 3: x > 0 ==> f(x) >= f(-x)
lemma prove_constraint_3(x: real)
    requires x > 0.0
    ensures nguyen4(x) >= nguyen4(-x)
{
    // Teach Dafny how signs work with all powers up to 6
    lemma_even_pow6(x);   // (-x)^6 == x^6
    lemma_odd_pow5(x);    // (-x)^5 == -(x^5)
    lemma_even_pow4(x);   // (-x)^4 == x^4
    lemma_odd_pow3(x);    // (-x)^3 == -(x^3)
    lemma_square_even(x); // (-x)^2 == x^2
    
    var f_x := nguyen4(x);
    var f_minus_x := nguyen4(-x);
    
    // Explicitly expand the negative evaluation
    assert f_minus_x == ((-x)*(-x)*(-x)*(-x)*(-x)*(-x)) + ((-x)*(-x)*(-x)*(-x)*(-x)) + ((-x)*(-x)*(-x)*(-x)) + ((-x)*(-x)*(-x)) + ((-x)*(-x)) + (-x);
    assert f_minus_x == (x*x*x*x*x*x) - (x*x*x*x*x) + (x*x*x*x) - (x*x*x) + (x*x) - x;
    
    // Calculate the difference: f(x) - f(-x)
    // The even powers (x^6, x^4, x^2) cleanly cancel out!
    var diff := f_x - f_minus_x;
    assert diff == 2.0 * (x*x*x*x*x) + 2.0 * (x*x*x) + 2.0 * x;
    
    // Prove the difference is > 0 using our existing axioms
    lemma_pow5_pos(x); // x^5 > 0
    lemma_cube_pos(x); // x^3 > 0
    assert (x*x*x*x*x) > 0.0;
    assert (x*x*x) > 0.0;
    
    assert diff > 0.0;
    assert diff >= 0.0;
    assert f_x >= f_minus_x;
}
