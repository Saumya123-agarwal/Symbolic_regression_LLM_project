include "math_library.dfy"

// 1. The equation: f(x,y) = 1/(1 + x^-4) + 1/(1 + y^-4)
function pagie1(x: real, y: real): real
    requires x != 0.0 && y != 0.0
    // Strict zero-checks to bypass Dafny's division-by-zero NLA panic
    requires (x*x*x*x) != 0.0 && (y*y*y*y) != 0.0
    requires 1.0 + (1.0 / (x*x*x*x)) != 0.0
    requires 1.0 + (1.0 / (y*y*y*y)) != 0.0
{
    (1.0 / (1.0 + (1.0 / (x*x*x*x)))) + (1.0 / (1.0 + (1.0 / (y*y*y*y))))
}

// 2. Constraint 1: f(x,y) >= 0
lemma prove_constraint_1(x: real, y: real)
    requires x != 0.0 && y != 0.0
    requires (x*x*x*x) != 0.0 && (y*y*y*y) != 0.0
    requires 1.0 + (1.0 / (x*x*x*x)) != 0.0
    requires 1.0 + (1.0 / (y*y*y*y)) != 0.0
    ensures pagie1(x, y) >= 0.0
{
    // Step 1: Prove x^4 and y^4 are positive
    lemma_pow4_strictly_pos(x);
    lemma_pow4_strictly_pos(y);
    
    // Step 2: Extract the inverses (x^-4 and y^-4)
    var x4_inv := 1.0 / (x*x*x*x);
    var y4_inv := 1.0 / (y*y*y*y);
    
    lemma_inverse_strictly_pos(x*x*x*x);
    lemma_inverse_strictly_pos(y*y*y*y);
    assert x4_inv > 0.0;
    assert y4_inv > 0.0;
    
    // Step 3: Apply the bound axioms
    lemma_pagie_fraction_bounds(x4_inv);
    lemma_pagie_fraction_bounds(y4_inv);
    
    var term_x := 1.0 / (1.0 + x4_inv);
    var term_y := 1.0 / (1.0 + y4_inv);
    
    assert term_x > 0.0;
    assert term_y > 0.0;
    
    // Connect back to function
    assert pagie1(x, y) == term_x + term_y;
    assert pagie1(x, y) > 0.0;
    assert pagie1(x, y) >= 0.0;
}

// 3. Constraint 2: f(x,y) <= 2
lemma prove_constraint_2(x: real, y: real)
    requires x != 0.0 && y != 0.0
    requires (x*x*x*x) != 0.0 && (y*y*y*y) != 0.0
    requires 1.0 + (1.0 / (x*x*x*x)) != 0.0
    requires 1.0 + (1.0 / (y*y*y*y)) != 0.0
    ensures pagie1(x, y) <= 2.0
{
    // The proof structure is identical to Constraint 1, 
    // but we utilize the upper bound (< 1.0) instead of the lower bound!
    
    lemma_pow4_strictly_pos(x);
    lemma_pow4_strictly_pos(y);
    
    var x4_inv := 1.0 / (x*x*x*x);
    var y4_inv := 1.0 / (y*y*y*y);
    
    lemma_inverse_strictly_pos(x*x*x*x);
    lemma_inverse_strictly_pos(y*y*y*y);
    
    lemma_pagie_fraction_bounds(x4_inv);
    lemma_pagie_fraction_bounds(y4_inv);
    
    var term_x := 1.0 / (1.0 + x4_inv);
    var term_y := 1.0 / (1.0 + y4_inv);
    
    assert term_x < 1.0;
    assert term_y < 1.0;
    
    // Connect back to function
    assert pagie1(x, y) == term_x + term_y;
    assert pagie1(x, y) < 2.0;
    assert pagie1(x, y) <= 2.0;
}

// 4. Constraint 3: f(x,y) = f(y,x) (Symmetry)
lemma prove_constraint_3(x: real, y: real)
    requires x != 0.0 && y != 0.0
    requires (x*x*x*x) != 0.0 && (y*y*y*y) != 0.0
    requires 1.0 + (1.0 / (x*x*x*x)) != 0.0
    requires 1.0 + (1.0 / (y*y*y*y)) != 0.0
    requires 1.0 + (1.0 / (y*y*y*y)) != 0.0
    requires 1.0 + (1.0 / (x*x*x*x)) != 0.0
    ensures pagie1(x, y) == pagie1(y, x)
{
    // Dafny's NLA handles the commutative property of addition perfectly natively!
}
