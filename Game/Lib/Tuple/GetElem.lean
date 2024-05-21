import Game.Lib.Tuple.Basic
import Mathlib.Tactic

namespace Tuple

variable {α : Type*} {n : ℕ}

protected def getElem : ∀ {n : ℕ}, α ^ n → Fin n → α
| _+1, cons head _, 0 => head
| _+1, cons _ tail, ⟨i+1, prf⟩ => Tuple.getElem tail ⟨i, (Nat.lt_of_succ_lt_succ prf)⟩

instance : GetElem (α ^ n) (Fin n) α ⊤ := ⟨λ v i _ ↦ Tuple.getElem v i⟩

instance : GetElem (α ^ n) ℕ α (λ _ i ↦ i < n) := ⟨λ v i prf ↦ Tuple.getElem v ⟨i, prf⟩⟩

theorem getElem_elem (v : α ^ n) (i : Fin n) : v[i] ∈ v := by
  induction i using Fin.succRec with
  | zero n => exact mem.here
  | succ n i ih => exact mem.there (ih _)
  done

theorem getElem_elem_Nat (v : α ^ n) (i : ℕ) (prf : i < n) : v[i] ∈ v := getElem_elem _ _

-- TODO: instance : LawfulGetElem


def updateElem : ∀ {n : ℕ}, α ^ n → Fin n → α → α ^ n
| _+1, cons _ tail, 0, x => cons x tail
| _+1, cons head tail, ⟨i+1, prf⟩, x => cons head (updateElem tail ⟨i, Nat.lt_of_succ_lt_succ prf⟩ x)

def removeElem : ∀ {n : ℕ}, α ^ (n+1) → Fin n → α ^ n
| _, cons _ tail, ⟨0, _⟩ => tail
| _+1, cons head tail, ⟨i+1, prf⟩ => cons head (removeElem tail ⟨i, Nat.lt_of_succ_lt_succ prf⟩)
