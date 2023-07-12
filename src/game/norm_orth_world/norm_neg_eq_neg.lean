import game.cauchy_schwarz_world.cauchy_schwarz --hide
import vectors.orthogonal --hide
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


## Level 1: `norm of neg equals norm` 

-/

/- Lemma

||-x|| = ||x||

-/


lemma norm_neg_eq_neg : ∀ {n : ℕ} (x : ℝ ^ n), ‖-x‖ = ‖x‖ :=
begin 
  intros n x,
  repeat {rw norm_eq_sqrt_norm_sq}, simp,
  congr' 1,
  induction n with n hn generalizing x,
  { cases x, 
    refl, },
  { cases x with n head tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
