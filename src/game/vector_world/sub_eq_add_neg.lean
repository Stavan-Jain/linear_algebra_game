import vectors.tuple -- hide
import data.real.basic
import game.vector_world.neg_eq_neg_mul --hide
namespace tuple -- hide

/- 

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 
# Vector world

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level 10: `sub equals add neg ` 

-/

/- Lemma
x ⬝ x = 0 ↔ x = tuple.zero
-/

lemma sub_eq_add_neg' {n : ℕ} (v u : ℝ ^ n) : v - u = v + -u :=
begin 
  induction n with n hn generalizing v u,
  { cases v, cases u,
    refl, },
  { cases v with n v₁ vₙ,
    cases u with n u₁ uₙ,
    simp,
    split,
    { ring, },
    { exact hn vₙ uₙ, }, },
end

end tuple -- hide
