include "math_library.dfy"

// 1. The equation
function nguyen1(x: real): real
{
    (x * x * x) + (x * x) + x
}

// 2. Constraint 1: x > 0 ==> f(x) >= 0
lemma prove_constraint_1(x: real)
    requires x > 0.0
    ensures nguyen1(x) >= 0.0
{
    // Extract the quadratic term to prevent Z3 pattern-matching failures
    var quad := (x * x) + x + 1.0;
    
    lemma_factor_cubic(x);
    lemma_quad_always_pos(x);
    
    assert quad > 0.0; // The solver now perfectly maps this variable
    
    lemma_strict_mult_pos(x, quad);
    
    // Explicitly connect the math back to the function
    assert x * quad > 0.0;
    assert (x * x * x) + (x * x) + x == x * quad;
    assert (x * x * x) + (x * x) + x > 0.0;
    
    assert nguyen1(x) > 0.0;
    assert nguyen1(x) >= 0.0;
}

// 3. Constraint 2: x < 0 ==> f(x) <= 0
lemma prove_constraint_2(x: real)
    requires x < 0.0
    ensures nguyen1(x) <= 0.0
{
    // Extract the quadratic term
    var quad := (x * x) + x + 1.0;
    
    lemma_factor_cubic(x);
    lemma_quad_always_pos(x);
    
    assert quad > 0.0; 
    
    lemma_mult_neg_pos_is_neg(x, quad);
    
    // Explicitly connect the math back to the function
    assert x * quad < 0.0;
    assert (x * x * x) + (x * x) + x == x * quad;
    assert (x * x * x) + (x * x) + x < 0.0;
    
    assert nguyen1(x) < 0.0;
    assert nguyen1(x) <= 0.0;
}

// 4. Constraint 3: x > 0 ==> f(x) >= f(-x)
lemma prove_constraint_3(x: real)
    requires x > 0.0
    ensures nguyen1(x) >= nguyen1(-x)
{
    lemma_odd_pow3(x);    // (-x)^3 == -(x^3)
    lemma_square_even(x); // (-x)^2 == x^2
    
    var f_x := nguyen1(x);
    var f_minus_x := nguyen1(-x);
    
    // Explicitly teach Dafny how to expand the negative version
    assert f_minus_x == ((-x) * (-x) * (-x)) + ((-x) * (-x)) + (-x);
    assert f_minus_x == -(x * x * x) + (x * x) - x;
    
    var diff := f_x - f_minus_x;
    assert diff == 2.0 * (x * x * x) + 2.0 * x;
    
    lemma_cube_pos(x); 
    assert (x * x * x) >= 0.0;
    
    assert diff >= 0.0;
    assert f_x >= f_minus_x;
}