import game.norm_orth_world.parallelogram_eq

namespace tuple -- hide

/- 
# Vector world

## Level 5: `Pythogaras Theorem` 

-/

/- Lemma
x ⟂ y iff ||x+y||² = ||x||² + ||y||²  
-/

lemma pythogaras_theorem : ∀ {n : ℕ} (x y : ℝ ^ n),  
x ⟂ y ↔ (x + y).norm_sq = x.norm_sq + y.norm_sq :=
begin 
  intros n x y, 
  split, 
  { intro perp_xy,
    simp,
    rw [dot_dist, dot_comm, dot_comm (x + y)], 
    repeat {rw dot_dist},
    rw dot_comm y,
    simp at perp_xy,
    rw perp_xy,
    simp, },
  { intro h,
    simp at *,
    rw [dot_dist, dot_comm, dot_comm (x + y)] at h,
    repeat {rw dot_dist at h},
    rw dot_comm y at h,
    linarith, },
end


end tuple
