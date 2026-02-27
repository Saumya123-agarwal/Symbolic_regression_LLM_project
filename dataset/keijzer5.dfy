include "math_library.dfy"

// 1. The equation
function keijzer5(x: real, y: real, z: real): real
    requires y != 0.0
    requires x != 10.0
    requires y * y != 0.0 
    requires (x - 10.0) * (y * y) != 0.0 // Strict zero-check for the entire denominator
{
    (30.0 * (x * z)) / ((x - 10.0) * (y * y))
}

// 2. Constraint 1: x = z = 0 ==> f(x,y,z) = 0
lemma prove_constraint_1(x: real, y: real, z: real)
    requires y != 0.0
    requires x != 10.0
    requires y * y != 0.0
    requires (x - 10.0) * (y * y) != 0.0
    requires x == 0.0 && z == 0.0
    ensures keijzer5(x, y, z) == 0.0
{
    // Dafny can trivially prove 0 divided by a non-zero number is 0
    assert 30.0 * (x * z) == 0.0;
}

// 3. Constraint 2: x = y = z && x > 10 ==> f(x,y,z) > 0
lemma prove_constraint_2(x: real, y: real, z: real)
    requires y != 0.0
    requires x != 10.0
    requires y * y != 0.0
    requires (x - 10.0) * (y * y) != 0.0
    requires x == y && y == z
    requires x > 10.0
    ensures keijzer5(x, y, z) > 0.0
{
    // Since x > 10, x is strictly positive
    assert x > 0.0;
    
    // Prove Numerator > 0
    lemma_strict_mult_pos(x, x);
    assert (x * x) > 0.0;
    lemma_strict_mult_pos(30.0, x * x);
    assert 30.0 * (x * x) > 0.0;
    assert 30.0 * (x * z) > 0.0; // because z == x
    
    // Prove Denominator > 0
    assert x - 10.0 > 0.0;
    lemma_strict_mult_pos(x - 10.0, x * x);
    assert (x - 10.0) * (x * x) > 0.0;
    assert (x - 10.0) * (y * y) > 0.0; // because y == x
    
    // Prove positive / positive > 0
    lemma_strict_div_pos(30.0 * (x * z), (x - 10.0) * (y * y));
}

// 4. Constraint 3: x = y = z && x < 10 ==> f(x,y,z) < 0
lemma prove_constraint_3(x: real, y: real, z: real)
    requires y != 0.0
    requires x != 10.0
    requires y * y != 0.0
    requires (x - 10.0) * (y * y) != 0.0
    requires x == y && y == z
    requires x < 10.0
    ensures keijzer5(x, y, z) < 0.0
{
    // If x = y, and y != 0, then x cannot be 0.
    assert x != 0.0; 
    
    // Prove x^2 is strictly positive, even if x is negative
    lemma_square_strictly_pos(x);
    assert (x * x) > 0.0;
    
    // Prove Numerator > 0
    lemma_strict_mult_pos(30.0, x * x);
    assert 30.0 * (x * x) > 0.0;
    assert 30.0 * (x * z) > 0.0; // because z == x
    
    // Prove Denominator < 0
    assert x - 10.0 < 0.0;
    lemma_mult_neg_pos_is_neg(x - 10.0, x * x);
    assert (x - 10.0) * (x * x) < 0.0;
    assert (x - 10.0) * (y * y) < 0.0; // because y == x
    
    // Prove positive / negative < 0
    lemma_div_pos_neg_is_neg(30.0 * (x * z), (x - 10.0) * (y * y));
}