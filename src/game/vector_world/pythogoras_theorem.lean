import vectors.tuple -- hide
import vectors.orthogonal --hide
import data.real.basic
import game.vector_world.orth_self_unique_zero --hide

namespace tuple -- hide

/- 
# Vector world

## Level 20: `Pythogaras Theorem` 

-/

/- Lemma
x ⟂ y iff ||x+y||² = ||x||² + ||y||²  
-/

lemma pythogaras_theorem: ∀ {n : ℕ} (x: tuple n) (y : tuple n)
,  x ⟂ y ↔ norm_sq(x + y) = norm_sq x + norm_sq y   :=
begin 
  intros n x y, 
  split, 
  {
    intro perp_xy, 
    dsimp [norm_sq], simp, 
    repeat {rw dot_dist}, rw dot_comm, 
    nth_rewrite 1 dot_comm, 
    repeat {rw dot_dist}, simp, 
    simp at perp_xy, 
    rw perp_xy, 
    nth_rewrite 1 dot_comm, 
    rw perp_xy, 
    simp, 
  }, 
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