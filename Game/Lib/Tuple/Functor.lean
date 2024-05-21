import Game.Lib.Tuple.Basic
import Mathlib.Tactic

namespace Tuple

protected def map {α β : Type*} : ∀ {n : ℕ}, (α → β) → α ^ n → β ^ n
| 0, _, nil => nil
| _+1, f, cons head tail => cons (f head) (Tuple.map f tail)

instance {n : ℕ} : Functor (· ^ n) where
  map f := n.rec (λ _ ↦ nil) (λ _ ih (cons head tail) ↦ cons (f head) (ih tail))

theorem map_cons {α β : Type _} {n : ℕ} (f : α → β) (head : α) (tail : α ^ n)
  : @Functor.map (· ^ (n+1)) _ α β f (cons head tail)
    = cons (f head) (@Functor.map (· ^ n) _ α β f tail) := rfl


instance {n : ℕ} : LawfulFunctor (· ^ n) where
  map_const := rfl
  id_map := by
    intros
    induction n, x using Tuple.rec with
    | zero => rfl
    | succ n head tail ih => rw [map_cons]; congr
    done
  comp_map := by
    intros
    induction n, x using Tuple.rec with
    | zero => rfl
    | succ n head tail ih => repeat rw [map_cons]; congr
    done
