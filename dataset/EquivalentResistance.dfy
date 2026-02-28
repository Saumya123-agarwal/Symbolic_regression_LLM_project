include "math_library.dfy"

ghost function f_res2(r1: real, r2: real): real 
{
    if (r1 + r2 == 0.0) then 0.0 
    else (r1 * r2) / (r1 + r2)
}

lemma Verify_res2(r1: real, r2: real)
    requires 0.0001 <= r1 <= 20.0
    requires 0.0001 <= r2 <= 20.0
    
    // Constraint A: Symmetry 
    // Z3 proves this natively because r1*r2 == r2*r1 and r1+r2 == r2+r1
    ensures f_res2(r1, r2) == f_res2(r2, r1)
    
    // Constraint B: Equality State
    ensures (r1 == r2) ==> (f_res2(r1, r2) == r1 / 2.0)
    
    // Constraint C: Upper Bounds
    ensures f_res2(r1, r2) <= r1
    ensures f_res2(r1, r2) <= r2
{
    // Inject the mathematical rules to satisfy the fractional bounds
    Res2Rules(r1, r2);

}
