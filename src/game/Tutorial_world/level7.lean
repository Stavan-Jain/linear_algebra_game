

/-
# Tutorial World. 

## Level 7 : The `linarith` , `ring` tactics

The linarith tactic solves certain kind of linear equalities and inequalities.
Unlike the ring tactic, linarith uses hypotheses in the tactic state.

The ring tactic proves identities in commutative rings such as (x+y)^2=x^2+2*x*y+y^2. 
It works on concrete rings such as ℝ and abstract rings, and will also prove some results in “semirings” such as ℕ.
Note that ring does not and cannot look at hypotheses.

Ring is a “finishing tactic”; this means that it should only be used to close goals. 
If ring does not close a goal it will issue a warning that you should use the related tactic ring_nf.


-/