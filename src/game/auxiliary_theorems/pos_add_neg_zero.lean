import vectors.tuple -- hide
import data.real.basic
import game.auxiliary_theorems.scalar_comm --hide
namespace tuple -- hide

/- 

Let's come back to thinking about what the dot product describes. It gives us an idea for how much one vector aligns with another. 
The amount that a vector aligns with itself can only be zero if it itself is the zero vector. 
# Vector world

We're going to prove that if dot product of a vector with itself is 0 then it must be the zero vector. 

## Level 4: `self neg equals zero ` 

-/

/- Lemma

-/
lemma self_neg_eq_zero : ∀ {n : ℕ} (x : ℝ ^ n), x - x = 0 :=
begin 
  intro n,
  induction n with n hn,
  { intro v,
    cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

end tuple -- hide
