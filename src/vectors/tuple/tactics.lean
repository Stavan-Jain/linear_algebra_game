import vectors.tuple

namespace tuple

section simp

universe u
variables {α : Type u} {n : ℕ}


@[simp]
lemma add_cons_eq_cons_add [has_add α] (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) + (cons v₁ vₙ) = cons (u₁ + v₁) (uₙ + vₙ) := rfl

@[simp]
lemma sub_cons_eq_cons_sub [has_sub α] (u₁ v₁ : α) (uₙ vₙ : α ^ n)
  : (cons u₁ uₙ) - (cons v₁ vₙ) = cons (u₁ - v₁) (uₙ - vₙ) := rfl

@[simp]
lemma smul_cons_eq_cons_smul [has_mul α] (c head : α) (tail : α ^ n)
  : c • (cons head tail) = cons (c * head) (c • tail) := rfl

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

lemma cast_nnnorm_eq_norm (v : ℝ ^ n) : ↑‖v‖₊ = ‖v‖ := rfl
lemma nnnorm_eq_sqrt_norm_sq (v : ℝ ^ n) : ‖v‖₊ = nnreal.sqrt (norm_sq v) := rfl
lemma norm_eq_sqrt_norm_sq (v : ℝ ^ n) : ‖v‖ = ↑(nnreal.sqrt (norm_sq v)) := rfl


end simp
end tuple


namespace tactic

open lean.parser (tk small_nat ident)
open _root_.interactive (parse)
open _root_.interactive.types (texpr using_ident)
open interactive («have»)


private meta def char.to_subscript : char → char
| '0' := '₀'
| '1' := '₁'
| '2' := '₂'
| '3' := '₃'
| '4' := '₄'
| '5' := '₅'
| '6' := '₆'
| '7' := '₇'
| '8' := '₈'
| '9' := '₉'
| x := x

private meta def string.to_subscript (str : string) : string := ⟨char.to_subscript <$> str.to_list⟩


meta def destruct_tuple_core (nam : name) (curr : ℕ) : tactic unit :=
  get_local nam >>= λ e,
    interactive.cases_core e [`_ , ↑(to_string nam ++ string.to_subscript (to_string curr)), nam]

meta def destruct_tuple_recurse (nam : name) : ℕ → ℕ → tactic unit
| 0 curr := destruct_tuple_core nam curr
| (n+1) curr := destruct_tuple_core nam curr >> destruct_tuple_recurse n (curr+1)

meta def interactive.destruct_tuple
  (n : parse small_nat)
  (id : parse ident)
  (name : parse using_ident)
  : tactic unit := do
    let nam := name.get_or_else id,
    rename id nam <|> tactic.fail "Hypothesis or variable not found.",
    destruct_tuple_recurse (name.get_or_else "v") n 1 <|>
      tactic.fail "Could not destruct tuple. Make sure that it is of the correct type."


end tactic
