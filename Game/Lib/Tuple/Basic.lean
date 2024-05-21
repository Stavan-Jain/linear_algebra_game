import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Tuple

section defn
  universe u
  instance : HPow (Type u) ℕ (Type u) where
    hPow T := Nat.rec PUnit (λ _ T' ↦ T × T')
end defn

variable {α β γ : Type*} {n : ℕ}

def nil {T : Type*} : T ^ 0 := PUnit.unit
def cons {T : Type*} {n : ℕ} (head : T) (tail : T ^ n) : T ^ (n+1) := (head, tail)
attribute [match_pattern] nil cons

protected def rec {motive : ∀ {n : ℕ}, α ^ n → Sort*}
  (zero : motive nil)
  (succ : ∀ (n : ℕ) (head : α) (tail : α ^ n), motive tail → motive (cons head tail))
  : ∀ (n : ℕ) (v : α ^ n), motive v
| 0, Tuple.nil => zero
| n+1, Tuple.cons head tail => succ _ head tail (Tuple.rec zero succ n tail)

protected def casesOn {motive : ∀ {n : ℕ}, α ^ n → Sort*}
  (zero : motive nil)
  (succ : ∀ (n : ℕ) (head : α) (tail : α ^ n), motive (cons head tail))
  : ∀ (n : ℕ) (v : α ^ n), motive v := Tuple.rec zero (λ _ _ _ _ ↦ succ _ _ _)


@[inline]
def length : (α ^ n) → ℕ := n

@[simp]
theorem length_zero_nil : ∀ (v : α ^ 0), v = nil | nil => rfl

theorem length_succ_cons : ∀ (v : α ^ (n+1)), ∃ (head : α) (tail : α ^ n), v = cons head tail
  | cons head tail => Exists.intro head <| Exists.intro tail rfl


protected def hAdd [HAdd α β γ] : ∀ {n : ℕ}, α ^ n → β ^ n → γ ^ n
| 0, nil, nil => nil
| _+1, cons head₁ tail₁, cons head₂ tail₂ => cons (head₁ + head₂) (Tuple.hAdd tail₁ tail₂)

instance [HAdd α β γ] {n : ℕ} : HAdd (α ^ n) (β ^ n) (γ ^ n) := ⟨Tuple.hAdd⟩

instance [Add α] {n : ℕ} : Add (α ^ n) := ⟨Tuple.hAdd⟩

theorem add_cons [HAdd α β γ] (head₁ : α) (tail₁ : α ^ n) (head₂ : β) (tail₂ : β ^ n)
  : cons head₁ tail₁ + cons head₂ tail₂ = cons (head₁ + head₂) (tail₁ + tail₂) := rfl


protected def hSub [HSub α β γ] : ∀ {n : ℕ}, α ^ n → β ^ n → γ ^ n
| 0, nil, nil => nil
| _+1, cons head₁ tail₁, cons head₂ tail₂ => cons (head₁ - head₂) (Tuple.hSub tail₁ tail₂)

instance [HSub α β γ] : HSub (α ^ n) (β ^ n) (γ ^ n) := ⟨Tuple.hSub⟩

instance [Sub α] : Sub (α ^ n) := ⟨Tuple.hSub⟩

theorem sub_cons [HSub α β γ] (head₁ : α) (tail₁ : α ^ n) (head₂ : β) (tail₂ : β ^ n)
  : cons head₁ tail₁ - cons head₂ tail₂ = cons (head₁ - head₂) (tail₁ - tail₂) := rfl


protected def hMul [HMul α β γ] : ∀ {n : ℕ}, α ^ n → β ^ n → γ ^ n
| 0, nil, nil => nil
| _+1, cons head₁ tail₁, cons head₂ tail₂ => cons (head₁ * head₂) (Tuple.hMul tail₁ tail₂)

instance [HMul α β γ] : HMul (α ^ n) (β ^ n) (γ ^ n) := ⟨Tuple.hMul⟩

instance [Mul α] : Mul (α ^ n) := ⟨Tuple.hMul⟩

theorem mul_cons [HMul α β γ] (head₁ : α) (tail₁ : α ^ n) (head₂ : β) (tail₂ : β ^ n)
  : cons head₁ tail₁ * cons head₂ tail₂ = cons (head₁ * head₂) (tail₁ * tail₂) := rfl


protected def zero [Zero α] : ∀ {n : ℕ}, α ^ n
| 0 => nil
| _+1 => cons 0 Tuple.zero

instance [Zero α] : Zero (α ^ n) := ⟨Tuple.zero⟩

theorem zero_cons [Zero α] : (0 : α ^ (n+1)) = cons 0 0 := rfl


protected def neg [Neg α] : ∀ {n : ℕ}, α ^ n → α ^ n
| 0, nil => nil
| _+1, cons head tail => cons (-head) (Tuple.neg tail)

instance [Neg α] : Neg (α ^ n) := ⟨Tuple.neg⟩

theorem neg_cons [Neg α] (head : α) (tail : α ^ n) : -(cons head tail) = cons (-head) (-tail) := rfl


protected def hSMul [HSMul α β γ] : ∀ {n : ℕ}, α → β ^ n → γ ^ n
| 0, _, nil => nil
| _+1, c, cons head tail => cons (c • head) (Tuple.hSMul c tail)

instance [HSMul α β γ] : HSMul α (β ^ n) (γ ^ n) := ⟨Tuple.hSMul⟩

instance [SMul α β] : SMul α (β ^ n) := ⟨Tuple.hSMul⟩

theorem smul_cons [HSMul α β γ] (c : α) (head : β) (tail : β ^ n)
  : c • cons head tail = cons (c • head) (c • tail) := rfl


protected inductive mem : ∀ {n : ℕ}, α → α ^ n → Prop
| here : Tuple.mem head (cons head tail)
| there : Tuple.mem x tail → Tuple.mem x (cons head tail)

instance {n : ℕ} : Membership α (α ^ n) := ⟨Tuple.mem⟩

theorem mem_nil {a : α} : Tuple.mem a nil → False := by
  intro h
  cases h
  done

theorem mem_cons (a : α) (head : α) (tail : α ^ n) (h : a ∈ (cons head tail))
  : a = head ∨ a ∈ tail := by
  cases h with
  | here => left; rfl
  | there h =>
    cases n with
    | zero =>
      exfalso
      rw [length_zero_nil tail] at h
      exact mem_nil h
    | succ n =>
      right
      exact h
  done


section dotProduct
  variable [HMul α β γ] [Add γ] [Zero γ]

  def sum : ∀ {n : ℕ}, γ ^ n → γ
  | 0, nil => 0
  | _+1, cons head tail => head + sum tail

  theorem sum_nil : sum nil = 0 := rfl

  theorem sum_cons (head : γ) (tail : γ ^ n) : sum (cons head tail) = head + sum tail := rfl


  def dotProduct (v₁ : α ^ n) (v₂ : β ^ n) : γ := sum (v₁ * v₂)

  infixl:67 " ⬝ " => dotProduct

  theorem dotProduct_nil : (nil : α ^ 0) ⬝ (nil : β ^ 0) = (0 : γ) := rfl

  theorem dotProduct_cons (head₁ : α) (tail₁ : α ^ n) (head₂ : β) (tail₂ : β ^ n)
    : (cons head₁ tail₁) ⬝ (cons head₂ tail₂) = head₁ * head₂ + tail₁ ⬝ tail₂ := rfl
end dotProduct


section Norm
  variable [HMul α α ℝ]

  def normSq (v : α ^ n) : ℝ := v ⬝ v

  theorem normSq_nil : normSq (nil : α ^ 0) = 0 := rfl

  theorem normSq_cons (head : α) (tail : α ^ n)
    : normSq (cons head tail) = head * head + normSq tail := rfl

  protected noncomputable def norm (v : α ^ n) : ℝ := Real.sqrt (normSq v)

  noncomputable instance {n : ℕ} : Norm (α ^ n) := ⟨Tuple.norm⟩
end Norm

theorem normSq_pos (v : ℝ ^ n) : normSq v ≥ 0 := by
  induction n, v using Tuple.rec with
  | zero => rfl
  | succ n head tail ih =>
    rw [normSq_cons]
    apply add_nonneg
    · exact mul_self_nonneg head
    · exact ih
  done


def nnnormSq {n : ℕ} (v : ℝ ^ n) : NNReal := ⟨normSq v, normSq_pos v⟩

theorem nnnormSq_nil : nnnormSq (nil : ℝ ^ 0) = 0 := rfl

theorem nnnormSq_cons (head : ℝ) (tail : ℝ ^ n)
  : nnnormSq (cons head tail) = head * head + nnnormSq tail := rfl

protected noncomputable def nnnorm {n : ℕ} (v : ℝ ^ n) : NNReal := NNReal.sqrt (nnnormSq v)

noncomputable instance {n : ℕ} : NNNorm (ℝ ^ n) := ⟨Tuple.nnnorm⟩
