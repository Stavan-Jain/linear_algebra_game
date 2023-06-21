import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level14 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 15: `zero dot vector equals zero` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/


#check abs_eq_self
#check scalar_norm
#check inv_mul_cancel
lemma zero_dot: ∀ {n : ℕ} (x : tuple n), tuple.zero ⬝ x = 0 :=
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