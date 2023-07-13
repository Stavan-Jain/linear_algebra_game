import game.linear_map_world.lin_transformation_def2
namespace vector_spaces -- hide

/- 

# Linear Transformation world

Background: In this level, you'll also prove that something is a linear transformation.
Before that, we are introducing the definition of zero and identity map:

Zero: In math textbooks, you can often see 0 denoting the function that takes each element
of some vector space to the additive identity of another vector space. To be specific, 
0 \in L(V, W) is defined by 0 v = 0. 
(The 0 on the left side of the equation is a function from V to W, whereas the 0 on the right 
is the additive identity in W)

Identity: We use I to denote identity map, which is the function on some vector space that 
takes each element to itself. To be specific, I \in L(V, V) is defined by Iv = v.

What you are going to do is to prove that the map defined by Tv = v is a linear map.

Hint: Do similarly as in the previous level.

## Level 3: `T(v) = v is a linear transformation` 

-/

/- Lemma
T: Rⁿ → Rⁿ defined by T(v) = v ∀v ∈ Rⁿ is a linear transformation
-/
lemma id_transformation : ∀ {n : ℕ} (T : ℝ ^ n  → ℝ ^ n),
  (∀ (v : ℝ ^ n), (T v) = v) → linear_transformation T ℝ :=
begin 
  intros n T h,
  simp,
  intros c d u v,
  repeat {rw h},
end

end vector_spaces -- hide