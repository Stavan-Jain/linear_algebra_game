import game.subspace_world.add_subspace
import game.auxiliary_theorems.dist_dot --hide

namespace vector_spaces
open tuple

/-

# Subspace World

Background: 
Here we will be proving that the orthogonal complement of subspace V is also a subpsace.
Recall that if Vᗮ is denoted as the orthogonal complement of a subpsace V, then every vector in Vᗮ is orthogonal to every vector in V.
Here we must show that Vᗮ fulfils the conditions needed for a subspace: 
 1. It contains the 0 vector 
 2. It is closed under addition 
 3. It is closed under scalar multiplication 

Strategy: 

Think about how you can go about proving the above conditions with Lean one by one. 
The split tactic will break the goal into the three conditions needed to prove that something is a subspace.  

Notation:

ᗮ : `\^perp`

^⟂ : `^\perp`

Due to limitations of the game web editor you might need to use the ^⟂ notation. However, if you're using VSCode, both notations work.

# Level 6: Prove orthogonal complement Vᗮ of subspace V is also a subspace


-/

/- Lemma 
The orthogonal complement Vᗮ of subspace V is also a subspace.
-/


instance orth_complement_subspace {n : ℕ} (V: set (ℝ ^ n)) [v : subspace (ℝ ^ n) ℝ V] : subspace (ℝ ^ n) ℝ (Vᗮ) := 
begin
  split, 

  { intros xᵤ hᵤ xᵥ hᵥ,
    intros v₁ v₁_V, 
    rw dist_dot,
    rw hᵤ v₁ v₁_V, 
    rw hᵥ v₁ v₁_V, 
    simp, }, 

  { intros c xᵥ hᵥ, 
    intros v₁ v₁_V, 
    rw scalar_through,
    rw hᵥ v₁ v₁_V, 
    simp, },

  { intros v₁ v₁_V, 
    rw zero_dot, },
end

end vector_spaces