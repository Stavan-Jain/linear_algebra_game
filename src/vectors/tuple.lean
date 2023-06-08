import data.real.basic
import tactic.norm_num
import data.int.basic


inductive tuple : ℕ → Type
| nil : tuple 0
| cons {n : ℕ} (car : ℤ) (cdr : tuple n) : (tuple (n + 1))


notation `[[` l:(foldr `, ` (h t, tuple.cons h t) tuple.nil `]]`) := l

protected def tuple.repr_aux : ∀ {n : ℕ}, bool → tuple n → string
| 0 _ _    := ""
| _ tt (tuple.cons a b) := has_repr.repr a ++ tuple.repr_aux ff b
| _ ff (tuple.cons a b) := ", " ++ has_repr.repr a ++ tuple.repr_aux ff b

protected def tuple.repr : ∀ {n : ℕ}, tuple n → string
| 0 _     := "[[]]"
| _ (tuple.cons a b) := "[[" ++ tuple.repr_aux tt (tuple.cons a b) ++ "]]"

instance (n : ℕ) : has_repr (tuple n) :=
⟨tuple.repr⟩

-- protected def tuple.repr : ∀ {n : ℕ}, tuple n → string
-- | 0 _ := ""
-- | _ (tuple.cons a b) := has_repr.repr a ++ " " ++ tuple.repr b
-- instance (n : ℕ) : has_repr (tuple n) := ⟨tuple.repr⟩


protected def tuple.add : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := tuple.nil
| n (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := tuple.cons (head₁ + head₂) (tuple.add tail₁ tail₂)
instance (n : ℕ) : has_add (tuple n) := ⟨tuple.add⟩

protected def tuple.subtract : ∀ {n : ℕ}, tuple n → tuple n → tuple n
| 0 _ _ := tuple.nil
| n (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := tuple.cons (head₁ - head₂) (tuple.subtract tail₁ tail₂)
instance (n : ℕ) : has_sub (tuple n) := ⟨tuple.subtract⟩

def tuple.dotproduct : ∀ {n : ℕ}, tuple n → tuple n → ℤ  
| 0 _ _ := 0
| _ (tuple.cons head₁ tail₁) (tuple.cons head₂ tail₂) := (head₁ * head₂) + tuple.dotproduct tail₁ tail₂

notation  a ⬝ b := tuple.dotproduct a b 

def tuple.crossproduct : tuple 3 → tuple 3 → tuple 3
| [[a, b, c]] [[d, e, f]] := [[b * f - c * e, c * d - a * f, a * e - b * d]]

notation a × b := tuple.crossproduct a b

def tuple.normsq {n : ℕ} (v : tuple n) : ℤ   :=  tuple.dotproduct v v

--def tuple.norm {n : ℕ} (v : tuple n) : ℝ  :=  (nat.sqrt (int.to_nat (tuple.normsq v)))

def tuple.scalar_mul: ∀ {n : ℕ}, ℤ → tuple n → tuple n
| 0 _ _ := [[]]
| n a (tuple.cons head tail) := tuple.cons (a*head) (tuple.scalar_mul a tail)

notation a `**` b := tuple.scalar_mul a b

namespace tuple 
#eval normsq [[1, 2, 3]]
#eval [[3 , 4 , 5]] + [[3, 6, 7]]
#eval crossproduct [[12, 10, 5]] [[13, 14, 17]]
#eval scalar_mul 4 [[1, 2, 3]]
#eval [[1,2]] ⬝ [[2, 3]]  
#eval [[12, 10, 5]] × [[13, 14, 17]]
#eval 4 ** [[1, 2, 5]]

end tuple
