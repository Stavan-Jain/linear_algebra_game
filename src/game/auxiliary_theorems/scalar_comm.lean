import game.auxiliary_theorems.smul_zero --hide
namespace tuple -- hide

/- 
# Vector world

## Level 3: `Scalars multiplication is commutative` 

-/

/- Lemma

-/

lemma scalar_comm : ∀ {n : ℕ} (c d : ℝ) (v : ℝ ^ n), c • d • v = d • c • v :=
begin 
  intros n c d,
  induction n with n hn,
  { intro v,
    cases v,
    simp, },
  { intro v,
    cases v with n head tail,
    simp,
    split,
    { linarith, },
    { exact hn tail, }, },
end

end tuple -- hide
