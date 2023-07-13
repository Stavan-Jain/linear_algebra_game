import vectors.tuple
import vectors.vector_spaces
import vectors.tuple.tactics
import game.vector_spaces_world.vector_space


namespace vector_spaces
open tuple

class subspace (𝕍 : Type*) (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽] (𝕊 : set 𝕍) :=
  (closed_add : ∀ (u v ∈ 𝕊), u + v ∈ 𝕊)
  (closed_smul : ∀ (c : 𝔽) (v ∈ 𝕊), c • v ∈ 𝕊)
  (contains_zero : (0 : 𝕍) ∈ 𝕊)

--def zero_set {n : ℕ }: set (ℝ ^ n) := {v : ℝ ^ n | v = 0}

@[simp]
def orth_complement {n : ℕ} (V : set (ℝ ^ n)) [v : subspace (ℝ ^ n) ℝ V] : set (ℝ ^ n) := 
{x : ℝ ^ n | ∀ v ∈ V, x ⬝ v = 0}

@[simp]
def orthogonal {n : ℕ} (V : set (ℝ ^ n)) (W : set (ℝ ^ n)) [subspace (ℝ^ n) ℝ V] [subspace (ℝ^ n) ℝ W]
: Prop := ∀ v : ℝ ^ n, ∀ w : ℝ ^ n , v ∈ V  → w ∈ W → v ⬝ w = 0 

notation V`ᗮ`:1200 := orth_complement V

end vector_spaces