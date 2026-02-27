include "math_library.dfy"

// 1. The equation (using explicit multiplication to help Dafny's parser)
function keijzer12(x: real, y: real): real
{
    (x * x * x * x) - (x * x * x) + ((y * y) / 2.0) - y
}

// 2. Constraint 1: x >= 0 ==> f(x,y) <= f(-x,y)
lemma prove_constraint_1(x: real, y: real)
    requires x >= 0.0
    ensures keijzer12(x, y) <= keijzer12(-x, y)
{
    // Teach Dafny how the signs expand
    lemma_even_pow4(x);
    lemma_odd_pow3(x);
    
    // With those rules, Dafny can easily see that:
    // x^4 - x^3 <= x^4 - (-x^3)
    // x^4 - x^3 <= x^4 + x^3  (which is true for x >= 0)
}

// 3. Constraint 2: y >= 0 ==> f(x,y) <= f(x,-y)
lemma prove_constraint_2(x: real, y: real)
    requires y >= 0.0
    ensures keijzer12(x, y) <= keijzer12(x, -y)
{
    lemma_square_even(y);
}

// 4. Constraint 3: x = y = 0 ==> f(x,y) = 0
lemma prove_constraint_3(x: real, y: real)
    requires x == 0.0 && y == 0.0
    ensures keijzer12(x, y) == 0.0
{
    // Trivial for Dafny
}

// 5. Constraint 4: x <= 0 ==> Delta f(x) < 0 (Strictly Decreasing)
lemma prove_constraint_4(x1: real, x2: real, y: real)
    requires x1 < x2 <= 0.0
    ensures keijzer12(x1, y) > keijzer12(x2, y)
{
    lemma_poly_mono_x(x1, x2);
}

// 6. Constraint 5: y >= 1 ==> Delta f(y) > 0 (Strictly Increasing)
lemma prove_constraint_5(x: real, y1: real, y2: real)
    requires 1.0 <= y1 < y2
    ensures keijzer12(x, y1) < keijzer12(x, y2)
{
    lemma_poly_mono_y_inc(y1, y2);
}

// 7. Constraint 6: y <= 1 ==> Delta f(y) < 0 (Strictly Decreasing)
lemma prove_constraint_6(x: real, y1: real, y2: real)
    requires y1 < y2 <= 1.0
    ensures keijzer12(x, y1) > keijzer12(x, y2)
{
    lemma_poly_mono_y_dec(y1, y2);
}