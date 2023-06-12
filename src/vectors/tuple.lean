import data.real.basic
import init.logic init.data.nat.basic init.data.bool.basic init.propext

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


def tuple.scalar_mul: ∀ {n : ℕ}, ℝ → tuple n → tuple n
| 0 _ _ := [[]]
| _ a (tuple.cons head tail) := tuple.cons (a*head) (tuple.scalar_mul a tail)

infix ` ** `:69 := tuple.scalar_mul


def tuple.norm_sq {n : ℕ} (v : tuple n) : ℝ  := v ⬝ v

def tuple.len {n : ℕ} (v : tuple n) : ℕ := n

--What I originally had, works if input is valid and returns sorry if invalid
-- 
-- def tuple.ith_element: ∀{n : ℕ}, ℕ → tuple n → ℝ
-- | 0 _ _ := sorry
-- | n 0 (tuple.cons head tail) := head
-- | n i (tuple.cons head tail) := tuple.ith_element (i - 1) tail
--
--
--This is what I have now. Trying to do something similar to the original 
--documentation. Havent been able to test it yet since le_of_succ_le_succ
--doesn't work
def tuple.ith : ∀ {n : ℕ}, tuple n → nat → option ℝ 
| 0 _ _ := none
| n (tuple.cons head tail) 0 := some head
| n (tuple.cons head tail) (i+1) := tuple.ith tail i

def tuple.ith_le : Π (n) (i), tuple n → i < n → ℝ
| 0 i _ h := absurd h i.not_lt_zero
| n 0 (tuple.cons head tail) h := head
| n (i + 1) (tuple.cons head tail) h := tuple.ith_le n i (le_of_succ_le_succ h)
