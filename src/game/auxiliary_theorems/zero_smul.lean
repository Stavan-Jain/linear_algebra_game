import game.auxiliary_theorems.pos_add_neg_zero --hide
namespace tuple -- hide


/- 

# Vector world

## Level 5: `zero_smul` 

-/

/- Lemma

-/

lemma zero_smul' : ∀ {n : ℕ} (v : ℝ ^ n), (0 : ℝ) • v = 0 :=
begin
  intros n,
  induction n with n hn,
  { intro c, cases c, 
    refl, },
  { intro c,
    cases c, simp,
    exact hn c_tail,},
end

end tuple -- hide