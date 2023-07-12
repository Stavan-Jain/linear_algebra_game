import game.norm_orth_world.norm_neg_eq_neg --hide

namespace tuple -- hide

/- 
# Vector world

## Level 2: `**0** is uniquely orthogonal to itself` 

-/

/- Lemma
**0** is the only vector orthogonal to itself
-/

lemma orth_self_unique_zero : ∀ {n : ℕ} (x : ℝ ^ n),  x ⟂ x → x = 0 :=
begin 
  intros n x perp,
  simp at perp,
  rwa dot_self_zero at perp,
end

end tuple
