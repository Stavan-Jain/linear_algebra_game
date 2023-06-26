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
lemma add_right_neg : ∀ {n : ℕ} (x : ℝ ^ n), x - x = 0 :=
begin 
  intros n,
  induction n with n hn,
  { intro v, cases v, refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
