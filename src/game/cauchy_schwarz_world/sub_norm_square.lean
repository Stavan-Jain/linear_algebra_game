import game.cauchy_schwarz_world.add_norm_square --hide
namespace tuple -- hide

/- 
# Cauchy Schwarz world

Background:

This is very similar to the proof we just did. Let's see if you can develop a structure similar to the last proof for this one!

Good luck!

Strategy:


## Level 7: `Subtract norm square` 

-/

/- Lemma

||x - y||² = ||x||² - 2 * (x ⬝ y) + ||y||²


-/


lemma sub_norm_square : ∀ {n : ℕ} (x y : ℝ ^ n),
↑‖x - y‖² = ↑‖x‖² - (2 * (x ⬝ y)) + ↑‖y‖² :=
begin 
  intros n x y,
  rw [sub_eq_add_neg, add_norm_square, neg_eq_neg_mul],
  rw [dot_comm x, scalar_through, dot_comm y],
  simp,
  rw [scalar_through, dot_comm y, scalar_through],
  linarith,
end

end tuple -- hide
