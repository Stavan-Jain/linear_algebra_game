import vectors.tuple

namespace tuple


variables {α : Type*} {β : Type*}  {n : ℕ}


@[simp]
lemma add_cons_eq_cons_add [has_add α] (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) + (cons v₁ vₙ) = cons (u₁ + v₁) (uₙ + vₙ) := rfl

@[simp]
lemma sub_cons_eq_cons_sub [has_sub α] (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) - (cons v₁ vₙ) = cons (u₁ - v₁) (uₙ - vₙ) := rfl

@[simp]
lemma smul_cons_eq_mul_cons_smul [has_mul α] (c head : α) (tail : α ^ n)
  : c • (cons head tail) = cons (c * head) (c • tail) := rfl

@[simp]
lemma smul_cons_eq_smul_cons_smul [has_smul β α] (c : β) (head : α) (tail : α ^ n)
  : c • (cons head tail) = cons (c • head) (c • tail) := rfl

@[simp]
lemma smul_nil [has_mul α] (c : α) : c • (nil : tuple α 0) = nil := rfl

@[simp]
lemma neg_cons_eq_cons_neg [has_neg α] (head : α) (tail : α ^ n)
  : -(cons head tail) = (cons (-head) (-tail)) := rfl

@[simp]
lemma nil_add_nil [has_add α] : (nil : tuple α 0) + nil = nil := rfl

@[simp]
lemma zero_cons [has_zero α] : (0 : α ^ n.succ) = (cons 0 0) := rfl

@[simp]
lemma eq_cons_iff_and_eq (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) = (cons v₁ vₙ) ↔ (u₁ = v₁) ∧ (uₙ = vₙ) := by simp

@[simp]
lemma empty_vec_eq_nil (v : α ^ 0) : v = nil := by { cases v, refl, }

lemma cast_nnnorm_eq_norm (v : ℝ ^ n) : ↑‖v‖₊ = ‖v‖ := rfl
lemma nnnorm_eq_sqrt_norm_sq (v : ℝ ^ n) : ‖v‖₊ = nnreal.sqrt (norm_sq v) := rfl
lemma norm_eq_sqrt_norm_sq (v : ℝ ^ n) : ‖v‖ = ↑(nnreal.sqrt (norm_sq v)) := rfl


end tuple
