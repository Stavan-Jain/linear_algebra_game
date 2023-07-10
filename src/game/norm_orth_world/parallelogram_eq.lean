import game.norm_orth_world.zero_orth_all

namespace tuple -- hide

/- 
# Vector world

## Level 4: `Parallelogram equality` 

-/

/- Lemma

-/

lemma parallelogram_eq: ∀ {n : ℕ} (u v : ℝ ^ n)
, (norm_sq (u + v) : ℝ) + ↑(norm_sq (u - v)) = 2 * (↑(norm_sq u) + ↑(norm_sq v)) :=
begin
  intros n u v,
  rw add_norm_square,
  rw sub_norm_square,
  linarith,
end

end tuple
