import vectors.tuple

open tuple

@[simp]
lemma add_cons_eq_cons_add {n : ℕ} (u₁ v₁ : ℝ) (uₙ vₙ : tuple n)
  : (cons u₁ uₙ) + (cons v₁ vₙ) = cons (u₁ + v₁) (uₙ + vₙ) := begin
  simp [has_add.add],
  simp [tuple.add],
  refl,
end
