import vectors.tuple -- hide
import data.real.basic
import game.vector_world.div_norm_unit --hide

namespace tuple -- hide

/- 
# Vector world

Background:
 Here we'll be proving that the dot product of the zero vector with any vector x is 0. This follows from the definition of the dot product. 

 Strategy:
 As seen before, it may make sense to begin with induction, and first prove that 0 ⬝ x = 0  for x equal to the zero vector. 
 Good luck!


## Level 17: `zero dot vector equals zero` 

-/

/- Lemma
 0 ⬝ x = 0 

 
-/


lemma zero_dot: ∀ {n : ℕ} (x : ℝ ^ n), 0 ⬝ x = 0 :=
begin 
   intro n , 
   induction n with d hd, 
   intro x, 
   cases x, 
   dsimp [tuple.zero, dot_product], refl, 
   intro x, 
   cases x, 
   dsimp [tuple.zero, dot_product], simp, 
   exact hd x_tail,  
end

end tuple -- hide
