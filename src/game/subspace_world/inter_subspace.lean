import game.subspace_world.dot_prod

namespace vector_spaces
open tuple

instance inter_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u: subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V]: subspace (ℝ ^ n) ℝ (U ∩ V):= 
begin
  split,

  { intros, 
  simp at *, 
  exact ⟨u.1 u_1 H.left v_1 H_1.left, v.1 u_1 H.right v_1 H_1.right⟩,},

  { intros, 
  simp at *, 
  exact ⟨ u.2 c v_1 H.1, v.2 c v_1 H.2⟩, },

  { simp at *,
  exact ⟨u.3, v.3⟩,},
end

end vector_spaces