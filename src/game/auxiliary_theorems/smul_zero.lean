import game.auxiliary_theorems.vector_dist --hide
namespace tuple -- hide


/- 

# Vector world

## Level 2: `smul_zero` 

-/

/- Lemma

-/

set_option pp.numeral_types true

lemma smul_zero' : ∀ {n : ℕ} (c : ℝ), c • (0 : ℝ ^ n) = 0 :=
begin
  intros n,
  induction n with n hn,
  { intro c,
    refl, },
  { intro c,
    simp,
    exact hn c,},
end

end tuple -- hide
