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
  intros n x,
  induction n with n hn,
  { cases x,
    simp, },
  { cases x with n head tail,
    simp,
    exact hn tail, },
end

end tuple
