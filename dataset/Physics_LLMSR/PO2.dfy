include "math_library.dfy"

method agent_PO2(F0: real, omega02: real, t: real, x: real) returns (r: real)
    requires omega02 >= 0.0
    ensures (t == 0.0 && x == 0.0) ==> r == 0.0
    ensures (t == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (t == 0.0 && x < 0.0) ==> r >= 0.0
{
    var sin_t: real := sin(t);
    var abs_x: real := abs(x);
    var exp_term: real := exp(-abs_x);
    
    // Break down the non-linear multiplication
    var term1: real := omega02 * x;
    var term2: real := term1 * exp_term;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (x == 0.0) {
            lemma_exp_zero();
            
        } else if (x > 0.0) {
            // Prove term1 >= 0.0
            lemma_Mult_pos(omega02, x);
            assert term1 >= 0.0;
            
            // Prove term2 >= 0.0
            lemma_Mult_pos(term1, exp_term); 
            assert term2 >= 0.0;
            
        } else if (x < 0.0) {
            // Prove term1 <= 0.0
            lemma_mult_le_ge_zero(x, omega02);
            assert term1 <= 0.0;
            
            // Prove term2 <= 0.0
            lemma_mult_le_ge_zero(term1, exp_term);
            assert term2 <= 0.0;
        }
    }

    r := F0 * sin_t - term1 - term2;
}