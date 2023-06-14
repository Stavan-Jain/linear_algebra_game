import vectors.tuple

open tuple

@[simp]
lemma add_cons_eq_cons_add {n : ℕ} (u₁ v₁ : ℝ) (uₙ vₙ : tuple n)
  : (cons u₁ uₙ) + (cons v₁ vₙ) = cons (u₁ + v₁) (uₙ + vₙ) := begin
  simp [has_add.add, tuple.add],
end

@[simp]
lemma mul_cons_eq_cons_mul {n : ℕ} (c u₁ : ℝ) (uₙ : tuple n)
  : c ** (cons u₁ uₙ) = cons (c * u₁) (c ** uₙ) := begin
  simp [tuple.scalar_mul, has_mul.mul, tuple.map],
end
