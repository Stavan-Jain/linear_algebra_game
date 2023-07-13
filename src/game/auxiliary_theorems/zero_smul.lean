import game.auxiliary_theorems.self_neg_eq_zero --hide
namespace tuple -- hide


/- 

# Vector world

## Level 5: `zero_smul` 

-/

/- Lemma

-/

lemma zero_smul' : ∀ {n : ℕ} (v : ℝ ^ n), (0 : ℝ) • v = 0 :=
begin
  intro n,
  induction n with n hn,
  { intro c, 
    cases c, 
    refl, },
  { intro c,
    cases c with n head tail, 
    simp,
    exact hn tail,},
end

end tuple -- hide