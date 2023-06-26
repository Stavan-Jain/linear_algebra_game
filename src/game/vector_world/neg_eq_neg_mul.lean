import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level4 
namespace tuple -- hide

/- 

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 
# Vector world

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level x (before 9): `dot product is postive definite part 2 ` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/
lemma neg_eq_neg_mul : ∀ {n : ℕ} (x : ℝ ^ n),  -x = -1 ** x :=
begin 
  intro n,
  induction n with n hn,
  { intro x, cases x, refl, },
  { intro x,
    cases x with n x₁ xₙ,
    simp,
    specialize hn xₙ,
    exact hn, },
end

end tuple -- hide
