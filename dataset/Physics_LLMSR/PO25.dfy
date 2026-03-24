include "math_library.dfy"

method agent_PO25(F0: real, alpha: real, beta: real, t: real, v: real) returns (r: real)
    requires alpha >= 0.0
    requires beta >= 0.0
    ensures (t == 0.0 && v == 0.0) ==> r == 0.0
    ensures (t == 0.0 && v > 0.0) ==> r <= 0.0
{
    var sin_t: real := sin(t);
    var v3: real := v * v * v;
    var abs_v: real := abs(v);
    var log_term: real := log(abs_v + 1.0);
    
    var term1: real := alpha * v3;
    var term2: real := beta * log_term;

    if (t == 0.0) {
        assert sin_t == 0.0;
        
        if (v == 0.0) {
            assert v3 == 0.0;
            assert term1 == 0.0;
            assert abs_v == 0.0;
            assert log_term == 0.0;
            assert term2 == 0.0;
        } else if (v > 0.0) {
            lemma_cube_pos(v);
            lemma_Mult_pos(alpha, v3);
            assert term1 >= 0.0;
            
            assert abs_v + 1.0 > 1.0;
            lemma_Mult_pos(beta, log_term);
            assert term2 >= 0.0;
        }
    }

    r := F0 * sin_t - term1 - term2;
}