import vectors.tuple

namespace tuple

section simp

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

@[simp]
lemma zero_empty_vec_eq_nil [has_zero α] : (0 : tuple α 0) = (nil : tuple α 0) := rfl

lemma cast_nnnorm_eq_norm (v : ℝ ^ n) : ↑‖v‖₊ = ‖v‖ := rfl
lemma nnnorm_eq_sqrt_norm_sq (v : ℝ ^ n) : ‖v‖₊ = nnreal.sqrt (norm_sq v) := rfl
lemma norm_eq_sqrt_norm_sq (v : ℝ ^ n) : ‖v‖ = ↑(nnreal.sqrt (norm_sq v)) := rfl

lemma to_real (v : ℝ ^ n) : ‖v‖ = real.sqrt (v ⬝ v) := by simp [has_norm.norm, tuple.norm]

end simp
end tuple


namespace tactic

open lean.parser (tk small_nat ident)
open _root_.interactive
open _root_.interactive.types
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


meta def cases_tuple_core (nam : name) (curr : ℕ) : tactic unit :=
  get_local nam >>= λ e,
    interactive.cases_core e [`_ , ↑(to_string nam ++ string.to_subscript (to_string curr)), nam]

meta def cases_tuple_recurse (nam : name) : ℕ → ℕ → tactic unit
| 0 curr := cases_tuple_core nam curr
| (n+1) curr := cases_tuple_core nam curr >> cases_tuple_recurse n (curr+1)

meta def interactive.cases_tuple
  (id : parse ident)
  (n : parse small_nat)
  (name : parse using_ident)
  : tactic unit := do
    let nam := name.get_or_else id,
    rename id nam <|> tactic.fail "Hypothesis or variable not found.",
    cases_tuple_recurse nam n 1 <|>
      tactic.fail "Could not cases tuple. Make sure that it is of the correct type."


meta def interactive.simpr (use_iota_eqn : parse $ optional (tk "!"))
  (trace_lemmas : parse $ optional (tk "?")) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
  (attr_names : parse with_ident_list) (locat : parse location) (cfg : simp_config_ext := {})
  : tactic unit :=
  interactive.simp use_iota_eqn trace_lemmas no_dflt hs attr_names locat cfg  >> interactive.refl


end tactic
