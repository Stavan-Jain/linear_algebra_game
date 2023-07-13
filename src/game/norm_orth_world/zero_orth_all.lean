import game.norm_orth_world.orth_self_unique_zero --hide

namespace tuple -- hide

/- 
# Norm Orth world

## Level 3: `Zero orthogonal to all vectors`

Background:
Here we will be proving that the zero vector is orthogonal to all vectors. We know that two vectors are orthogonal if their dot product is zero.
We've proved in dot product world that the zero dotted with any vector gives 0. This allows us to say that zero is orthogonal to all vectors. 
Let's see how to appraoch this proof in Lean. 

Strategy:
As seen before, it may make sense to begin this proof with induction, and show that 0 ⬝ x is true for x = 0, and then use that to prove that
it is true for any value of x. 

-/

/- Lemma
**0** is orthogonal to all vectors. 
-/

lemma zero_orth_all: ∀ {n : ℕ} (x: ℝ ^ n)
,  orthogonal 0 x   :=
begin
  intros n x,
  induction n with n hn,
  { cases x,
    simp, },
  { cases x with n head tail,
    simp,
    exact hn tail, },
end

end tuple --hide
