import data.real.basic
import data.real.nnreal
import data.real.sqrt
import analysis.normed.group.basic


inductive tuple : ℕ → Type
| nil : tuple 0
| cons {n : ℕ} (head : ℝ) (tail : tuple n) : (tuple (n + 1))

namespace tuple


notation `[[` l:(foldr `, ` (h t, cons h t) nil `]]`) := l


protected meta def repr_aux : ∀ {n : ℕ}, bool → tuple n → string
| 0 _ _ := ""
| _ tt (cons a b) := repr a ++ repr_aux ff b
| _ ff (cons a b) := ", " ++ repr a ++ repr_aux ff b

protected meta def repr : ∀ {n : ℕ}, tuple n → string
| 0 _     := "[[]]"
| _ (cons a b) := "[[" ++ tuple.repr_aux tt (cons a b) ++ "]]"

meta instance {n : ℕ} : has_repr (tuple n) := ⟨tuple.repr⟩


protected def add : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := nil
| _ (cons head₁ tail₁) (cons head₂ tail₂) := cons (head₁ + head₂) (add tail₁ tail₂)

instance {n : ℕ} : has_add (tuple n) := ⟨tuple.add⟩


protected def sub : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := nil
| _ (cons head₁ tail₁) (cons head₂ tail₂) := cons (head₁ - head₂) (sub tail₁ tail₂)

instance {n : ℕ} : has_sub (tuple n) := ⟨tuple.sub⟩


def length {n : ℕ} : tuple n → ℕ := n


def dot_product : ∀ {n : ℕ}, tuple n → tuple n → ℝ
| 0 _ _ := 0
| _ (cons head₁ tail₁) (cons head₂ tail₂) := (head₁ * head₂) + dot_product tail₁ tail₂

infix ` ⬝ `:72 := dot_product


def cross_product : tuple 3 → tuple 3 → tuple 3
| [[a, b, c]] [[d, e, f]] := [[b * f - c * e, c * d - a * f, a * e - b * d]]

infixl ` ×ᵥ `:74 := cross_product


def map : ∀ {n : ℕ}, (ℝ → ℝ) → tuple n → tuple n
| 0 _ _ := [[]]
| _ f (cons head tail) := cons (f head) (map f tail)


def scalar_mul {n : ℕ} (c : ℝ) : tuple n → tuple n := map (has_mul.mul c)
infix ` ** `:69 := scalar_mul


def norm_sq {n : ℕ} (v : tuple n) : nnreal := ⟨v ⬝ v, begin
  induction n with n hn generalizing v,
  { cases v, refl, },
  { cases v with _ head tail,
    specialize hn tail,
    dsimp [dot_product],
    have : 0 ≤ head * head,
    { exact mul_self_nonneg head, },
    exact add_nonneg this hn, },
end⟩

protected noncomputable def norm {n : ℕ} (v : tuple n) : nnreal := nnreal.sqrt (norm_sq v)
noncomputable instance {n : ℕ} : has_norm (tuple n) := ⟨coe ∘ tuple.norm⟩
noncomputable instance {n : ℕ} : has_nnnorm (tuple n) := ⟨tuple.norm⟩


def nth : ∀ {n : ℕ} (i : ℕ), tuple n → i < n → ℝ
| 0 i _ prf := absurd prf i.not_lt_zero
| _ 0 (cons head _) prf := head
| _ (i+1) (cons _ tail) prf := nth i (tail) (nat.le_of_succ_le_succ prf)

def update_nth : ∀ {n : ℕ} (i : ℕ), tuple n → ℝ → i < n → tuple n
| 0 i _ _ prf := absurd prf i.not_lt_zero
| n 0 (cons head tail) a prf := cons a tail
| n (i + 1) (cons head tail) a prf := cons head (update_nth i tail a (nat.le_of_succ_le_succ prf))

def remove_nth : ∀ {n : ℕ} (i : ℕ), tuple (n + 1) → i ≤ n → tuple n
| 0 0 _ prf := nil
| 0 (i + 1) _ prf := absurd prf (by linarith)
| (n + 1) 0 (cons _ tail) prf := tail
| (n + 1) (i + 1) (cons head tail) prf := cons head (remove_nth i tail (by linarith))


protected def zero : ∀ {n : ℕ}, tuple n
| 0 := [[]]
| (n + 1) := cons 0 zero

instance {n : ℕ} : has_zero (tuple n) := ⟨tuple.zero⟩


protected def neg : ∀ {n : ℕ}, tuple n → tuple n
| 0 _ := [[]]
| (n + 1) (cons head tail) := cons (-head) (neg tail)

instance {n : ℕ} : has_neg (tuple n) := ⟨tuple.neg⟩


end tuple
