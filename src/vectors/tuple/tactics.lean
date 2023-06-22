import vectors.tuple

namespace tuple


@[simp]
lemma add_cons_eq_cons_add {n : ℕ} (u₁ v₁ : ℝ) (uₙ vₙ : tuple n)
  : (cons u₁ uₙ) + (cons v₁ vₙ) = cons (u₁ + v₁) (uₙ + vₙ) := rfl

@[simp]
lemma sub_cons_eq_cons_sub {n : ℕ} (u₁ v₁ : ℝ) (uₙ vₙ : tuple n)
  : (cons u₁ uₙ) - (cons v₁ vₙ) = cons (u₁ - v₁) (uₙ - vₙ) := rfl

@[simp]
lemma mul_cons_eq_cons_mul {n : ℕ} (c head : ℝ) (tail : tuple n)
  : c ** (cons head tail) = cons (c * head) (c ** tail) := rfl

@[simp]
lemma mul_nil (c : ℝ) : c ** nil = nil := rfl

@[simp]
lemma neg_cons_eq_cons_neg {n : ℕ} (head : ℝ) (tail : tuple n)
  : -(cons head tail) = (cons (-head) (-tail)) := rfl

@[simp]
lemma nil_add_nil : nil + nil = nil := rfl

@[simp]
lemma zero_cons {n : ℕ} : (0 : tuple n.succ) = (cons 0 0) := rfl


end tuple
