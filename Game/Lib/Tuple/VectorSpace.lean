import Game.Lib.Tuple.Basic
import Game.Lib.VectorSpace.Basic
import Mathlib.Tactic

namespace Tuple

variable {𝔽 α : Type*} {n : ℕ}

instance [AddCommMagma α] : AddCommMagma (α ^ n) where
  add_comm := by
    intros
    induction n with
    | zero => rfl
    | succ n ih =>
      let (cons a a_tail) := a
      let (cons b b_tail) := b
      specialize ih a_tail b_tail
      repeat rw [add_cons]
      rw [add_comm]
      congr 1
    done

instance [AddSemigroup α] : AddSemigroup (α ^ n) where
  add_assoc := by
    intro a b c
    induction n with
    | zero => rfl
    | succ n ih =>
      let (cons a a_tail) := a
      let (cons b b_tail) := b
      let (cons c c_tail) := c
      specialize ih a_tail b_tail c_tail
      repeat rw [add_cons]
      rw [add_assoc]
      congr 1
    done

instance [AddCommSemigroup α] : AddCommSemigroup (α ^ n) where
  add_comm := add_comm

instance [AddZeroClass α] : AddZeroClass (α ^ n) where
  zero_add := by
    intro a
    induction n, a using Tuple.rec with
    | zero => rfl
    | succ n head tail =>
      rw [zero_cons, add_cons, zero_add]
      congr 1
    done
  add_zero := by
    intro a
    induction n, a using Tuple.rec with
    | zero => rfl
    | succ n head tail =>
      rw [zero_cons, add_cons, add_zero]
      congr 1
    done

instance [AddMonoid α] : AddMonoid (α ^ n) where
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

instance [AddCommMonoid α] : AddCommMonoid (α ^ n) where
  add_comm := add_comm

instance [SubNegMonoid α] : SubNegMonoid (α ^ n) where
  sub_eq_add_neg := by
    intros
    induction n with
    | zero => rfl
    | succ n ih =>
      let (cons a a_tail) := a
      let (cons b b_tail) := b
      specialize ih a_tail b_tail
      rw [sub_cons, neg_cons, add_cons, sub_eq_add_neg]
      congr 1
    done
  zsmul := zsmulRec

instance [AddGroup α] : AddGroup (α ^ n) where
  add_left_neg := by
    intros
    induction n, a using Tuple.rec with
    | zero => rfl
    | succ n head tail ih =>
      rw [neg_cons, add_cons, add_left_neg]
      congr 1
    done

instance [AddCommGroup α] : AddCommGroup (α ^ n) where
  add_comm := add_comm

instance [Monoid 𝔽] [MulAction 𝔽 α] : MulAction 𝔽 (α ^ n) where
  one_smul := by
    intros
    induction n, b using Tuple.rec with
    | zero => rfl
    | succ n head tail ih =>
      rw [smul_cons, one_smul]
      congr 1
    done
  mul_smul := by
    intros
    induction n, b using Tuple.rec with
    | zero => rfl
    | succ n head tail ih =>
      rw [smul_cons, mul_smul]
      congr 1
    done

instance [Monoid M] [AddMonoid α] [DistribMulAction M α] : DistribMulAction M (α ^ n) where
  smul_zero := by
    intros
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [zero_cons, smul_cons, smul_zero]
      congr 1
    done
  smul_add := by
    intros
    induction n with
    | zero => rfl
    | succ n ih =>
      let (cons head₁ tail₁) := x
      let (cons head₂ tail₂) := y
      specialize ih tail₁ tail₂
      rw [add_cons]
      repeat rw [smul_cons]
      rw [add_cons, smul_add]
      congr 1
    done

instance [Semiring 𝔽] [AddCommMonoid α] [Module 𝔽 α] : Module 𝔽 (α ^ n) where
  add_smul := by
    intros
    induction n, x using Tuple.rec with
    | zero => rfl
    | succ n head tail ih =>
      repeat rw [smul_cons]
      rw [add_cons, add_smul]
      congr 1
    done
  zero_smul := by
    intros
    induction n, x using Tuple.rec with
    | zero => rfl
    | succ n head tail ih =>
      rw [smul_cons, zero_cons, zero_smul]
      congr 1
    done

instance [Field 𝔽] [AddCommGroup α] [VectorSpace 𝔽 α] : VectorSpace 𝔽 (α ^ n) := VectorSpace.mk
