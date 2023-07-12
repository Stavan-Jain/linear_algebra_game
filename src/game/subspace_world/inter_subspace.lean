import game.subspace_world.dot_prod

namespace vector_spaces
open tuple

/-

# Subspace World

Background:
Here we'll be proving that given subspaces U and V, U ∩ V is a subspace.
As we have seen before, U ∩ V must fufil the following conditions:-
 1. It contains the 0 vector 
 2. It is closed under addition 
 3. It is closed under scalar multiplication 

Strategy:
As before the split tactic will break the goal into the three conditions needed for something to be a subspace. 

Let's take a minute to get introduced to the tactics "left" and "right" in lean. When applied to a goal of the form 
p ∧ q, left and right consider the left or right side of the ∧ symbol respectively.


# Level

-/

/- Lemma 
-/

instance inter_subspace {n : ℕ} {U V : set (ℝ ^ n)} [u: subspace (ℝ ^ n) ℝ U] [v : subspace (ℝ ^ n) ℝ V]: subspace (ℝ ^ n) ℝ (U ∩ V):= 
begin
  split,

  { intros xᵤ hᵤ xᵥ hᵥ, 
    simp at *, 
    exact ⟨u.closed_add xᵤ hᵤ.left xᵥ hᵥ.left, 
    v.closed_add xᵤ hᵤ.right xᵥ hᵥ.right⟩, },

  { intros c xᵥ h, 
    simp at *, 
    exact ⟨u.closed_smul c xᵥ h.left, v.closed_smul c xᵥ h.right⟩, },

  { simp at *,
    exact ⟨u.contains_zero, v.contains_zero⟩, },
end

end vector_spaces