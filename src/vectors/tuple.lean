import data.real.basic
import data.real.nnreal
import data.real.sqrt
import analysis.normed.group.basic


inductive tuple : ℕ → Type
| nil : tuple 0
| cons {n : ℕ} (car : ℝ) (cdr : tuple n) : (tuple (n + 1))

notation `[[` l:(foldr `, ` (h t, tuple.cons h t) tuple.nil `]]`) := l


protected meta def tuple.repr_aux : ∀ {n : ℕ}, bool → tuple n → string
| 0 _ _ := ""
| _ tt (tuple.cons a b) := repr a ++ tuple.repr_aux ff b
| _ ff (tuple.cons a b) := ", " ++ repr a ++ tuple.repr_aux ff b

protected meta def tuple.repr : ∀ {n : ℕ}, tuple n → string
| 0 _     := "[[]]"
| _ (tuple.cons a b) := "[[" ++ tuple.repr_aux tt (tuple.cons a b) ++ "]]"

meta instance (n : ℕ) : has_repr (tuple n) := ⟨tuple.repr⟩


protected def tuple.add : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := tuple.nil
| _ (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := tuple.cons (head₁ + head₂) (tuple.add tail₁ tail₂)

instance (n : ℕ) : has_add (tuple n) := ⟨tuple.add⟩


protected def tuple.subtract : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := tuple.nil
| _ (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := tuple.cons (head₁ - head₂) (tuple.subtract tail₁ tail₂)

instance (n : ℕ) : has_sub (tuple n) := ⟨tuple.subtract⟩


def tuple.dot_product : ∀ {n : ℕ}, tuple n → tuple n → ℝ
| 0 _ _ := 0
| _ (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := (head₁ * head₂) + tuple.dot_product tail₁ tail₂

infix ` ⬝ `:72 := tuple.dot_product


def tuple.cross_product : tuple 3 → tuple 3 → tuple 3
| [[a, b, c]] [[d, e, f]] := [[b * f - c * e, c * d - a * f, a * e - b * d]]

infixl ` ×ᵥ `:74 := tuple.cross_product


def tuple.map: ∀ {n : ℕ}, (ℝ → ℝ) → tuple n → tuple n
| 0 _ _ := [[]]
| _ f (tuple.cons head tail) := tuple.cons (f head) (tuple.map f tail)


def tuple.scalar_mul {n : ℕ} (c : ℝ) : tuple n → tuple n := tuple.map (has_mul.mul c)
infix ` ** `:69 := tuple.scalar_mul


def tuple.norm_sq {n : ℕ} (v : tuple n) : nnreal := ⟨v ⬝ v, begin
  induction n with n hn generalizing v,
  { cases v, refl, },
  { cases v with _ head tail,
    specialize hn tail,
    dsimp [tuple.dot_product],
    have : 0 ≤ head * head,
    { exact mul_self_nonneg head, },
    exact add_nonneg this hn, },
end⟩

protected noncomputable def tuple.norm {n : ℕ} (v : tuple n) : nnreal :=
  nnreal.sqrt (tuple.norm_sq v)

noncomputable instance (n : ℕ) : has_norm (tuple n) := ⟨coe ∘ tuple.norm⟩
noncomputable instance (n : ℕ) : has_nnnorm (tuple n) := ⟨tuple.norm⟩
