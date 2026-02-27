include "math_library.dfy"

// 1. The equation
function keijzer14(x: real, y: real): real
    // We add these to satisfy Dafny's division-by-zero checker. 
    // We will mathematically prove they hold true in the lemmas.
    requires 2.0 + (x * x) + (y * y) > 0.0 
    requires 2.0 + (x * x) + (y * y) != 0.0
{
    8.0 / (2.0 + (x * x) + (y * y))
}

// Helper Lemma: Prove the denominator is always valid and >= 2.0
lemma prove_denominator_valid(x: real, y: real)
    ensures 2.0 + (x * x) + (y * y) >= 2.0
    ensures 2.0 + (x * x) + (y * y) > 0.0
{
    lemma_square_non_negative(x);
    lemma_square_non_negative(y);
    assert (x * x) >= 0.0;
    assert (y * y) >= 0.0;
}

// 2. Constraint 1: f(x,y) >= 0
lemma prove_constraint_1(x: real, y: real)
    requires 2.0 + (x * x) + (y * y) > 0.0
    requires 2.0 + (x * x) + (y * y) != 0.0
    ensures keijzer14(x, y) >= 0.0
{
    // 8.0 is positive, and the denominator is positive. 
    // We use the division positivity axiom you added earlier.
    lemma_div_pos(8.0, 2.0 + (x * x) + (y * y));
}

// 3. Constraint 2: f(x,y) <= 4
lemma prove_constraint_2(x: real, y: real)
    requires 2.0 + (x * x) + (y * y) > 0.0
    requires 2.0 + (x * x) + (y * y) != 0.0
    ensures keijzer14(x, y) <= 4.0
{
    var den := 2.0 + (x * x) + (y * y);
    
    // Prove the denominator is >= 2.0
    prove_denominator_valid(x, y);
    assert den >= 2.0;
    
    // Mathematically: 8.0 <= (2.0 + x^2 + y^2) * 4.0
    // Because 8.0 <= 8.0 + 4x^2 + 4y^2
    assert 8.0 <= den * 4.0;
    
    // Use our new axiom to prove: since 8 <= den * 4, then 8/den <= 4
    lemma_div_upper_bound(8.0, den, 4.0);
}

// 4. Constraint 3: f(x,y) <= f(0,0)
lemma prove_constraint_3(x: real, y: real)
    requires 2.0 + (x * x) + (y * y) > 0.0
    requires 2.0 + (x * x) + (y * y) != 0.0
    ensures keijzer14(x, y) <= keijzer14(0.0, 0.0)
{
    // Evaluate the maximum point
    assert keijzer14(0.0, 0.0) == 8.0 / 2.0;
    assert keijzer14(0.0, 0.0) == 4.0;
    
    // Since f(0,0) is exactly 4.0, we just reuse the logic from Constraint 2!
    prove_constraint_2(x, y);
}

// 5. Constraint 4: f(x,y) == f(y,x) (Symmetry)
lemma prove_constraint_4(x: real, y: real)
    requires 2.0 + (x * x) + (y * y) > 0.0
    requires 2.0 + (y * y) + (x * x) > 0.0
    requires 2.0 + (x * x) + (y * y) != 0.0
    requires 2.0 + (y * y) + (x * x) != 0.0
    ensures keijzer14(x, y) == keijzer14(y, x)
{
    // Commutative property of addition
    assert (x * x) + (y * y) == (y * y) + (x * x);
}