import data.real.basic

inductive tuple : ℕ → Type
| nil : tuple 0
| cons {n : ℕ} (car : ℤ) (cdr : tuple n) : (tuple (n + 1))


notation `[[` l:(foldr `, ` (h t, tuple.cons h t) tuple.nil `]]`) := l


protected def tuple.repr : ∀ {n : ℕ}, tuple n → string
| 0 _ := "tuple.nil"
| _ (tuple.cons a b) := "(tuple.cons " ++ has_repr.repr a ++ " " ++ tuple.repr b ++ ")"
instance (n : ℕ) : has_repr (tuple n) := ⟨tuple.repr⟩


protected def tuple.add : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := tuple.nil
| n (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := tuple.cons (head₁ + head₂) (tuple.add tail₁ tail₂)
instance (n : ℕ) : has_add (tuple n) := ⟨tuple.add⟩

def tuple.dotproduct : ∀ {n : ℕ}, tuple n → tuple n → ℤ
| 0 _ _ := 0
| _ (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := (head₁ * head₂) + tuple.dotproduct tail₁ tail₂

def tuple.crossproduct : tuple 3 → tuple 3 → tuple 3
| [[a, b, c]] [[d, e, f]] := [[b * f - c * e, c * d - a * f, a * e - b * d]]

def tuple.normsq {n : ℕ} (v : tuple n) : ℤ := tuple.dotproduct v v

#eval tuple.normsq [[1, 2, 3]]
