import game.dot_prod_world.dot_dist --hide

namespace tuple -- hide

/- 
# Vector world

## Level 5: `zero dot vector equals zero` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/


lemma zero_dot: ∀ {n : ℕ} (x : ℝ ^ n), 0 ⬝ x = 0 :=
begin 
   intro n , 
   induction n with d hd, 
   intro x, 
   cases x, 
   simp, 
   intro x, 
   cases x, 
   simp,  
   exact hd x_tail,  
end

end tuple -- hide
