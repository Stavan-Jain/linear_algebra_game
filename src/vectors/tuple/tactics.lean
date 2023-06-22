import vectors.tuple

namespace tuple


universe u
variable {α : Type u}


@[simp]
lemma add_cons_eq_cons_add [has_add α] {n : ℕ} (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) + (cons v₁ vₙ) = cons (u₁ + v₁) (uₙ + vₙ) := rfl

@[simp]
lemma sub_cons_eq_cons_sub [has_sub α] {n : ℕ} (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) - (cons v₁ vₙ) = cons (u₁ - v₁) (uₙ - vₙ) := rfl

@[simp]
lemma mul_cons_eq_cons_mul [has_mul α] {n : ℕ} (c head : α) (tail : α ^ n)
  : c ** (cons head tail) = cons (c * head) (c ** tail) := rfl

@[simp]
lemma neg_cons_eq_cons_neg [has_neg α] {n : ℕ} (head : α) (tail : α ^ n)
  : -(cons head tail) = (cons (-head) (-tail)) := rfl

@[simp]
lemma nil_add_nil [has_add α] : (nil : tuple α 0) + nil = nil := rfl

@[simp]
lemma zero_cons [has_zero α] {n : ℕ} : (0 : α ^ n.succ) = (cons 0 0) := rfl

@[simp]
lemma eq_cons_iff_and_eq {n : ℕ} (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) = (cons v₁ vₙ) ↔ (u₁ = v₁) ∧ (uₙ = vₙ) := by simp


end tuple
