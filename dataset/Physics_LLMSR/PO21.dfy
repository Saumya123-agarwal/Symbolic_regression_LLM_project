include "math_library.dfy"

method agent_PO21(alpha: real, beta: real, mu: real, omega02: real, gamma: real, v: real, x: real) returns (r: real)
    requires alpha >= 0.0
    requires beta >= 0.0
    requires mu >= 0.0
    requires omega02 >= 0.0
    requires gamma >= 0.0
    ensures (v == 0.0 && x == 0.0) ==> r == 0.0
    ensures (v == 0.0 && x > 0.0) ==> r <= 0.0
    ensures (v == 0.0 && x < 0.0) ==> r >= 0.0
    ensures (x == 0.0 && v > 0.0 && v <= 1.0) ==> r <= 0.0
{
    var abs_v: real := abs(v);
    var log_term: real := log(abs_v + 1.0);
    var v2: real := v * v;
    var v3: real := v * v * v;
    var pow_term: real := pow(abs_v, 0.33);

    var term1: real := alpha * v3;
    var term2: real := beta * log_term;
    var term3: real := 2.0 * beta * v;
    
    var term4_part: real := mu * (1.0 - v2);
    var term4: real := term4_part * v;
    
    var term5_part1: real := omega02 * (gamma * pow_term + 1.0);
    var term5: real := term5_part1 * x;

    if (v == 0.0) {
        assert abs_v == 0.0;
        assert log_term == 0.0; 
        assert v3 == 0.0;
        assert term1 == 0.0 && term2 == 0.0 && term3 == 0.0 && term4 == 0.0;
        
        lemma_pow_zero_base(0.33);
        assert pow_term == 0.0;
        assert term5_part1 == omega02;
        
        if (x == 0.0) {
            assert term5 == 0.0;
        } else if (x > 0.0) {
            lemma_Mult_pos(omega02, x);
            assert term5 >= 0.0;
        } else if (x < 0.0) {
            lemma_mult_le_ge_zero(x, omega02);
            assert term5 <= 0.0;
        }
    } else if (x == 0.0 && v > 0.0 && v <= 1.0) {
        assert term5 == 0.0;
        
        lemma_cube_pos(v);
        lemma_Mult_pos(alpha, v3);
        assert term1 >= 0.0;
        
        assert abs_v + 1.0 > 1.0; 
        // log(x) >= 0 for x >= 1
        lemma_Mult_pos(beta, log_term);
        assert term2 >= 0.0;
        
        lemma_Mult_pos(2.0 * beta, v);
        assert term3 >= 0.0;
        
        lemma_Mult_symbolic_ub(v, v, 1.0);
        assert v2 <= v;
        assert v2 <= 1.0;
        assert 1.0 - v2 >= 0.0;
        
        lemma_Mult_pos(mu, 1.0 - v2);
        assert term4_part >= 0.0;
        lemma_Mult_pos(term4_part, v);
        assert term4 >= 0.0;
    }

    r := -term1 - term2 - term3 - term4 - term5;
}