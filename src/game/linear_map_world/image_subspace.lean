import game.linear_map_world.kernel_subspace --hide
namespace vector_spaces
open tuple

/- 

# Linear Transformation world

Background: The image of a linear transformation is all of the vectors that can show up as an output
(you might also know this as the "range" of a function). When considering a matrix representation,
the image of the linear transformation is the span of the column vectors of the matrix.

That is, for a linear map T from V to W, the image of T is the subset of W consisting of those
vectors that are of the form T(v) for some v ∈ V. Strictly,
img T = {w ∈ W | exists v ∈ V, T(v) = w}.

In this level, you are going to prove that the image of a linear transformation is a subspace.

Hint: Use the tactics `split` and `specialize`.

## Level 7: `The Image of a linear transformation is a subspace`

img(A) is a subspace for any linear transformation A.

-/

/- Lemma
Let T: Rⁿ → Rᵐ be a linear transformation, then image(T) is a subspace of Rᵐ 
-/
instance image_subspace {n m : ℕ} (T : ℝ ^ n → ℝ ^ m) :
  linear_transformation T ℝ → subspace (ℝ^ m) ℝ (image T) :=
begin 
  intro h, 
  split,
  { intros u hᵤ v hᵥ,
    cases hᵤ with x₁ Tx₁,
    cases hᵥ with x₂ Tx₂, 
    use (x₁ + x₂),
    specialize h 1 1 x₁ x₂,
    repeat {rw tuple.one_smul at h},
    rw [h, Tx₁, Tx₂], },
  
  { intros c v hᵥ,
    cases hᵥ with x Tx, 
    specialize h c 0 x 0,
    repeat {rw zero_smul' at h},
    simp at *,
    use (c • x),
    rw [h, Tx], },

  { use 0,  
    exact zero_in_kernel T h, },
end


end vector_spaces --hide
