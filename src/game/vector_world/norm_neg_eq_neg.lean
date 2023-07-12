import vectors.tuple -- hide
import data.real.basic
import game.vector_world.cauchy_schwarz_unit --hide

namespace tuple -- hide

/- 
# Vector world

Background: 

Here we'll be proving that the magnitude of a vector is equal to the magnitude of it's negative. 
In R² this describes two vectors of same length pointing in exactly opposite directions.

Strategy: 
As we've done before, let's take some vector x of length n. It makes sense to apply induction next. 
Remember, "simp at *"  simplifies all current hypotheses and the current goal

Hint: 
Think about how we can use ||x|| = x ⬝ x and try to prove that ||-x||= x ⬝ x


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
