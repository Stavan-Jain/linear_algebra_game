import vectors.tuple -- hide
import data.real.basic
import game.vector_world.div_norm_unit --hide

namespace tuple -- hide

/- 
# Vector world

## Level 17: `zero dot vector equals zero` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/


lemma zero_dot: ∀ {n : ℕ} (x : ℝ ^ n), 0 ⬝ x = 0 :=
begin 
   intros n x, 
   induction n with d hd, 
   { cases x, 
     simp, },
   { cases x with n head tail, 
     simp, 
     exact hd tail, },
end

end tuple -- hide
