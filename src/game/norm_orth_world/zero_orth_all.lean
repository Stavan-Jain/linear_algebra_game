import game.norm_orth_world.orth_self_unique_zero

namespace tuple -- hide

/- 
# Vector world

## Level 3: `Zero orthogonal to all vectors` 

-/

/- Lemma
**0** is orthogonal to all vectors. 
-/

lemma zero_orth_all: ∀ {n : ℕ} (x: ℝ ^ n)
,  orthogonal 0 x   :=
begin
  intro n,
  induction n with n hn,
  { intro x,
    cases x,
    simp,},
  { intro x,
    cases x with n head tail,
    simp,
    exact hn tail, },
end

end tuple
