import game.auxiliary_theorems.neg_eq_neg_mul --hide
namespace tuple -- hide

/- 

# Auxiliary Theorems


## Level 7: `sub equals add neg ` 

-/

/- Lemma

-/

lemma sub_eq_add_neg {n : ℕ} (v u : ℝ ^ n) : v - u = v + -u :=
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
