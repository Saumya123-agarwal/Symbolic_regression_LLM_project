include "math_library.dfy"

// 1. The equation
function keijzer15(x: real, y: real): real
{
    ((x * x * x) / 5.0) + ((y * y * y) / 2.0) - y - x
}

// 2. Constraint 1: x = y = 0 ==> f(x,y) = 0
lemma prove_constraint_1(x: real, y: real)
    requires x == 0.0 && y == 0.0
    ensures keijzer15(x, y) == 0.0
{
    // Trivial for Dafny to evaluate zeros
}

// 3. Constraint 2: x = -y and x <= 0 ==> f(x,y) >= 0
lemma prove_constraint_2(x: real, y: real)
    requires x == -y
    requires x <= 0.0
    ensures keijzer15(x, y) >= 0.0
{
    // Step 1: Handle the substitution for y^3
    assert y == -x;
    lemma_odd_pow3(x); // (-x)^3 == -(x^3)
    assert (y * y * y) == -(x * x * x);
    
    var x3 := x * x * x;
    
    // Step 2: Simplify the equation down to -0.3 * x^3
    assert keijzer15(x, y) == (x3 / 5.0) - (x3 / 2.0) - (-x) - x;
    assert -(-x) - x == 0.0; // Linear terms cancel
    assert (x3 / 5.0) - (x3 / 2.0) == -0.3 * x3; // Combine fractions
    assert keijzer15(x, y) == -0.3 * x3;
    
    // Step 3: Apply sign rules (negative * negative >= 0)
    lemma_cube_neg(x);
    assert x3 <= 0.0;
    lemma_mult_le_zero(-0.3, x3);
}

// 4. Constraint 3: x = -y and x >= 0 ==> f(x,y) <= 0
lemma prove_constraint_3(x: real, y: real)
    requires x == -y
    requires x >= 0.0
    ensures keijzer15(x, y) <= 0.0
{
    // Step 1: Handle the substitution
    assert y == -x;
    lemma_odd_pow3(x);
    assert (y * y * y) == -(x * x * x);
    
    var x3 := x * x * x;
    
    // Step 2: Simplify the equation
    assert keijzer15(x, y) == (x3 / 5.0) - (x3 / 2.0) - (-x) - x;
    assert (x3 / 5.0) - (x3 / 2.0) == -0.3 * x3;
    assert keijzer15(x, y) == -0.3 * x3;
    
    // Step 3: Apply sign rules (negative * positive <= 0)
    lemma_cube_pos(x);
    assert x3 >= 0.0;
    lemma_mult_le_ge_zero(-0.3, x3);
}