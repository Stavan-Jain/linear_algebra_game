

/-
# Tutorial World 

## Level 5: The `linarith` tactics

When dealing with complicated equalities, using the basic tactics
solely relying on the axoims of addition and multiplication can be tedious sometimes. 

Here, we introduce the `linarith` and  `ring` tactics, aiming to simply the process. 


The linarith (linear arithmatic）tactic solves certain kinds of linear equalities and inequalities.
Unlike the ring tactic, linarith uses hypotheses in the tactic state.





-/

lemma linarith (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin 
  rw h,
  

end


/- 
For the `ring` tactic, I'll provide an example here: 

-/