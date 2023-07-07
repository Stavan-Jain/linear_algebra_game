import vectors.tuple -- hide
import data.real.basic
import game.vector_world.cauchy_schwarz_unit --hide

namespace tuple -- hide

/- 
# Vector world

## Level 13: `norm of neg equals norm` 

-/

/- Lemma
||-x|| = ||x||
-/


lemma norm_neg_eq_neg: ∀ {n : ℕ} (x : ℝ ^ n)
, ‖-x‖ = ‖x‖   :=
begin 
  intros n x,
  simp [has_norm.norm, tuple.norm, norm_sq],
  congr' 1,
  induction n with n hn generalizing x,
  { cases x, refl, },
  { cases x with n head tail,
    simp [dot_product],
    exact hn tail, },
end

end tuple -- hide
