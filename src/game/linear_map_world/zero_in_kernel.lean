import vectors.lin_maps --hide
import game.subspace_world.orth_of_sum_eq_inter_of_orth--hide
open tuple -- hide
namespace vector_spaces --hide

/- 

# Linear Transformation world

Background: In this level, you will prove a property of linear maps that 
they always take 0 to 0. That is, suppose T is a linear map from V to W, then T(0) = 0. 

(p.s. This property is not hard to prove, but for someone who has just learned the concept of 
linear maps, it might not be an obvious conclusion. Therefore, understanding this 
is beneficial for developing mathematical intuition. It can also lead to interesting theorems
especially after having proved the Fundamental Theorem of Linear Maps (important as it sounds),
which is that dim(V) = dim null(T) + dim range(T). You can prove this with some knowledge
of basis of a vector space. 

If you are interested in further learning properties of linear maps, go discover the concept of 
injective and surjective. You'll be able to prove interesting results with the theorem above and 
the theorem to be proved in this level, such as that a map to a smaller dimensional space is not
injective, and that a map to a larger dimensional space is not surjective. ) 

Hint: You may find smul_zero' and zero_smul' useful.

## Level 1: `T(0) = 0` 

-/

/- Lemma
Let T: Rⁿ → Rᵐ be a linear transformation, then T(0) = 0
-/

lemma zero_in_kernel : ∀ {n m : ℕ} (T : ℝ ^ n → ℝ ^ m),
linear_transformation T ℝ → (T 0) = 0 :=
begin 
  simp, 
  intros n m T h,
  specialize h 0 0 0 0,
  repeat {rw smul_zero' at h,  rw zero_smul' at h}, 
  simp at h, 
  exact h, 
end

end vector_spaces -- hide
