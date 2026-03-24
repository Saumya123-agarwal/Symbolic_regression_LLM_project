include "math_library.dfy"

method agent_PO3(alpha: real, mu: real, omega02: real, v: real, x: real) returns (r: real)
    requires omega02 >= 0.0
    requires alpha >= 0.0
    requires mu >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0 && v > 0.0) ==> r <= 0.0
    ensures (x == 0.0 && v < 0.0) ==> r >= 0.0
{
    var v3: real := v * v * v;
    var x2: real := x * x;
    var abs_x: real := abs(x);
    var exp_term: real := exp(-abs_x);

    // Break the equation down to help Dafny's non-linear arithmetic
    var term1: real := alpha * v3;
    var term2: real := mu * (1.0 - x2) * v;
    var term3: real := omega02 * x;
    var term4: real := term3 * exp_term;

    if (v == 0.0 && x == 0.0) {
        lemma_exp_zero();
        assert v3 == 0.0;
        assert x2 == 0.0;
        
    } else if (v == 0.0 && x > 0.0) {
        // Restoring force check (pulled right, pulled back left)
        assert v3 == 0.0;
        assert term1 == 0.0;
        assert term2 == 0.0;
        
        lemma_Mult_pos(omega02, x);
        assert term3 >= 0.0;
        
        lemma_Mult_pos(term3, exp_term);
        assert term4 >= 0.0;
        
    } else if (v == 0.0 && x < 0.0) {
        // Restoring force check (pushed left, pushed back right)
        assert v3 == 0.0;
        assert term1 == 0.0;
        assert term2 == 0.0;
        
        // lemma_mult_le_ge_zero requires (<= 0.0, >= 0.0)
        lemma_mult_le_ge_zero(x, omega02); 
        assert term3 <= 0.0;
        
        lemma_mult_le_ge_zero(term3, exp_term);
        assert term4 <= 0.0;
        
    } else if (x == 0.0 && v > 0.0) {
        // Damping check (moving right, slowed down)
        lemma_exp_zero();
        assert x2 == 0.0;
        assert term3 == 0.0;
        assert term4 == 0.0;
        assert (1.0 - x2) == 1.0; 
        
        lemma_cube_pos(v);
        assert v3 >= 0.0;
        
        lemma_Mult_pos(alpha, v3);
        assert term1 >= 0.0;
        
        lemma_Mult_pos(mu, v);
        assert term2 >= 0.0;
        
    } else if (x == 0.0 && v < 0.0) {
        // Damping check (moving left, slowed down)
        lemma_exp_zero();
        assert x2 == 0.0;
        assert term3 == 0.0;
        assert term4 == 0.0;
        assert (1.0 - x2) == 1.0;
        
        lemma_cube_neg(v);
        assert v3 <= 0.0;
        
        lemma_mult_le_ge_zero(v3, alpha);
        assert term1 <= 0.0;
        
        lemma_mult_le_ge_zero(v, mu);
        assert term2 <= 0.0;
    }

    // Final recombination
    r := -term1 - term2 - term3 - term4;
}