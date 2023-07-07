import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.parallelogram_eq --hide

namespace tuple -- hide

/- 
# Vector world

## Level 20: `Pythogaras Theorem` 

-/

/- Lemma
x ⟂ y iff ||x+y||² = ||x||² + ||y||²  
-/

lemma pythogaras_theorem: ∀ {n : ℕ} (x y : ℝ ^ n)
,  x ⟂ y ↔ (x + y).norm_sq = x.norm_sq + y.norm_sq   :=
begin 
  intros n x y, 
  split, 
  { intro perp_xy,
    simp [norm_sq],
    have dot_right_dist : ∀ {n : ℕ} (x y z : ℝ ^ n), (y + z) ⬝ x = y ⬝ x + z ⬝ x,
    { intros n x y z,
      repeat {rw dot_comm _ x},
      exact dot_dist x y z, },
    simp [dot_dist, dot_right_dist],
    simp at perp_xy,
    rw perp_xy, rw dot_comm at perp_xy, rw perp_xy,
    simp, },
  {
    intro h, 
    dsimp [norm_sq] at h, simp at *, 
    rw dot_dist at h,
    nth_rewrite 0 dot_comm at h, 
    nth_rewrite 1 dot_comm at h, 
    repeat {rw dot_dist at h},
    have : x ⬝ x + x ⬝ y + (y ⬝ x + y ⬝ y) = x ⬝ x + x ⬝ y + y ⬝ x + y ⬝ y := by linarith,

    rw this at h,
    simp at h, 
    have : x ⬝ x + x ⬝ y + y ⬝ x = x ⬝ x + ( x ⬝ y + y ⬝ x) := by linarith,
    rw this at h,  simp at h, 
    nth_rewrite 1 dot_comm at h, 
    linarith, 
  }
end


end tuple
