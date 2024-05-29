import Game.Lib.VectorSpace.Basic
import Mathlib.Data.Subtype
import Mathlib.Tactic

namespace VectorSpace

instance (𝔽 V U : Type*) [Field 𝔽] [AddCommGroup U] [VectorSpace 𝔽 U]
  : VectorSpace 𝔽 (V → U) := VectorSpace.mk


section IsLinearMap

  variable (𝔽 : Type*) [Field 𝔽]
  variable {V : Type*} [AddCommGroup V] [VectorSpace 𝔽 V]
  variable {U : Type*} [AddCommGroup U] [VectorSpace 𝔽 U]

  class IsLinearMap (map : V → U) : Prop where
    protected linear_add : ∀ (v₁ v₂ : V), map v₁ + map v₂ = map (v₁ + v₂)
    protected linear_smul : ∀ (c : 𝔽) (v : V), c • map v = map (c • v)

  variable (map : V → U) [IsLinearMap 𝔽 map]

  theorem linear_add : ∀ (v₁ v₂ : V), map v₁ + map v₂ = map (v₁ + v₂) :=
    IsLinearMap.linear_add 𝔽

  theorem linear_smul : ∀ (c : 𝔽) (v : V), c • map v = map (c • v) :=
    IsLinearMap.linear_smul

  instance IsLinearMap_add (f g : V → U) [IsLinearMap 𝔽 f] [IsLinearMap 𝔽 g]
    : IsLinearMap 𝔽 (f + g) where
      linear_add := by
        intros
        calc (f + g) v₁ + (f + g) v₂
          _ = (f v₁ + g v₁) + (f v₂ + g v₂) := by repeat rw [Pi.add_apply]
          _ = f v₁ + (g v₁ + f v₂) + g v₂   := by repeat rw [add_assoc]
          _ = f v₁ + (f v₂ + g v₁) + g v₂   := by rw [add_comm (f v₂)]
          _ = (f v₁ + f v₂) + (g v₁ + g v₂) := by repeat rw [add_assoc]
          _ = f (v₁ + v₂) + g (v₁ + v₂)     := by rw [linear_add 𝔽, linear_add 𝔽]
          _ = (f + g) (v₁ + v₂)             := by rw [Pi.add_apply]
        done
      linear_smul := by
        intros
        calc c • (f + g) v
          _ = c • (f v + g v)       := by rw [Pi.add_apply]
          _ = c • (f v) + c • (g v) := by rw [smul_add]
          _ = f (c • v) + g (c • v) := by rw [linear_smul 𝔽, linear_smul 𝔽]
          _ = (f + g) (c • v)       := by rw [Pi.add_apply]
        done

  instance IsLinearMap_smul (c : 𝔽) (f : V → U) [IsLinearMap 𝔽 f] : IsLinearMap 𝔽 (c • f) where
    linear_add := by
      intros
      calc (c • f) v₁ + (c • f) v₂
        _ = c • (f v₁) + c • (f v₂) := by repeat rw [Pi.smul_apply]
        _ = f (c • v₁) + f (c • v₂) := by repeat rw [linear_smul 𝔽]
        _ = f (c • v₁ + c • v₂)     := by rw [linear_add 𝔽]
        _ = f (c • (v₁ + v₂))       := by rw [smul_add]
        _ = c • f (v₁ + v₂)         := by rw [linear_smul 𝔽 f]
        _ = (c • f) (v₁ + v₂)       := by rw [Pi.smul_apply]
      done
    linear_smul := by
      intro d v
      calc d • (c • f) v
        _ = d • c • f v     := by rw [Pi.smul_apply]
        _ = c • d • f v     := by rw [←mul_smul, mul_comm, mul_smul]
        _ = c • f (d • v)   := by rw [linear_smul 𝔽 f]
        _ = (c • f) (d • v) := by rw [Pi.smul_apply]
      done

  instance IsLinearMap_zero : IsLinearMap 𝔽 (Function.const V (0 : U)) where
    linear_add := λ _ _ ↦ add_zero 0
    linear_smul := λ c _ ↦ smul_zero c

  instance IsLinearMap_neg (f : V → U) [IsLinearMap 𝔽 f] : IsLinearMap 𝔽 (-f) where
    linear_add := by
      intros
      calc (-f) v₁ + (-f) v₂
        _ = -(f v₁) + -(f v₂) := by repeat rw [Pi.neg_apply]
        _ = -(f v₁ + f v₂)    := by rw [neg_add]
        _ = -(f (v₁ + v₂))    := by rw [linear_add 𝔽]
        _ = (-f) (v₁ + v₂)    := by rw [Pi.neg_apply]
      done
    linear_smul := by
      intros
      calc c • (-f) v
        _ = c • (-f v)   := by rw [Pi.neg_apply]
        _ = -(c • f v)   := by rw [smul_neg]
        _ = -(f (c • v)) := by rw [linear_smul 𝔽]
        _ = (-f) (c • v) := by rw [Pi.neg_apply]
      done

end IsLinearMap


section LinearMap

  variable (𝔽 : Type*) [Field 𝔽]
  variable (V : Type*) [AddCommGroup V] [VectorSpace 𝔽 V]
  variable (U : Type*) [AddCommGroup U] [VectorSpace 𝔽 U]

  def LinearMap : Type _ := {map : V → U // IsLinearMap 𝔽 map}

  namespace LinearMap

  instance {f : LinearMap 𝔽 V U} : IsLinearMap 𝔽 f.val := f.prop

  @[ext]
  theorem ext (f g : LinearMap 𝔽 V U) : f.val = g.val → f = g := Subtype.ext


  protected def add (f g : LinearMap 𝔽 V U) : LinearMap 𝔽 V U :=
    ⟨f.val + g.val, IsLinearMap_add 𝔽 f.val g.val⟩

  instance : Add (LinearMap 𝔽 V U) := ⟨LinearMap.add 𝔽 V U⟩

  @[simp]
  theorem add_apply (f g : LinearMap 𝔽 V U) (v : V) : (f + g).val v = f.val v + g.val v := rfl


  protected def smul (c : 𝔽) (f : LinearMap 𝔽 V U) : LinearMap 𝔽 V U :=
    ⟨c • f.val, IsLinearMap_smul 𝔽 c f.val⟩

  instance : SMul 𝔽 (LinearMap 𝔽 V U) := ⟨LinearMap.smul 𝔽 V U⟩

  @[simp]
  theorem smul_apply (c : 𝔽) (f : LinearMap 𝔽 V U) (v : V) : (c • f).val v = c • (f.val v) := rfl


  protected def zero : LinearMap 𝔽 V U := ⟨_, IsLinearMap_zero _⟩

  instance : Zero (LinearMap 𝔽 V U) := ⟨LinearMap.zero 𝔽 V U⟩

  @[simp]
  theorem zero_apply (v : V) : (0 : LinearMap 𝔽 V U).val v = 0 := rfl


  protected def neg (f : LinearMap 𝔽 V U) : LinearMap 𝔽 V U := ⟨-f.val, IsLinearMap_neg 𝔽 f.val⟩

  instance : Neg (LinearMap 𝔽 V U) := ⟨LinearMap.neg 𝔽 V U⟩

  @[simp]
  theorem neg_apply (f : LinearMap 𝔽 V U) (v : V) : (-f).val v = -(f.val v) := rfl

  instance : AddCommSemigroup (LinearMap 𝔽 V U) where
    add_assoc := by
      intro f g h
      ext v
      simp only [add_apply, add_assoc]
      done
    add_comm := by
      intro f g
      ext v
      rw [add_apply, add_apply, add_comm]
      done

  instance : AddCommMonoid (LinearMap 𝔽 V U) where
    zero_add := by
      intro f
      ext v
      simp only [add_apply, zero_apply, zero_add]
      done
    add_zero := by
      intro f
      ext v
      simp only [add_apply, zero_apply, add_zero]
      done
    nsmul := HSMul.hSMul ∘ Nat.cast
    nsmul_zero := by
      intro f
      ext v
      rw [Function.comp_apply, zero_apply, smul_apply, Nat.cast_zero, zero_smul]
      done
    nsmul_succ := by
      intro n f
      ext v
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, smul_apply, add_smul, one_smul,
        add_apply]
      done
    add_comm := add_comm

  instance : AddCommGroup (LinearMap 𝔽 V U) where
    zsmul := HSMul.hSMul ∘ Int.cast
    zsmul_zero' := by
      intro f
      ext v
      rw [Function.comp_apply, zero_apply, smul_apply, Int.cast_zero, zero_smul]
      done
    zsmul_succ' := by
      intro n f
      ext v
      simp only [Int.ofNat_eq_coe, Nat.cast_succ, Function.comp_apply, Int.cast_add, Int.cast_ofNat,
        Int.cast_one, smul_apply, add_smul, one_smul, add_apply]
      done
    zsmul_neg' := by
      intro n f
      ext v
      simp only [Function.comp_apply, Int.cast_negSucc, Nat.cast_succ, neg_add_rev, smul_apply,
        add_smul, neg_smul, one_smul, Int.cast_add, Int.cast_ofNat, Int.cast_one, neg_apply]
      done
    add_left_neg := by
      intro f
      ext v
      simp only [add_apply, neg_apply, add_left_neg, zero_apply]
      done
    add_comm := add_comm

  instance : Module 𝔽 (LinearMap 𝔽 V U) where
    one_smul := by
      intro f
      ext v
      rw [smul_apply, one_smul]
      done
    mul_smul := by
      intro c d f
      ext v
      repeat rw [smul_apply]
      rw [mul_smul]
      done
    smul_zero := by
      intro c
      ext v
      rw [smul_apply]
      repeat rw [zero_apply]
      rw [smul_zero]
      done
    smul_add := by
      intro c f g
      ext v
      simp only [smul_apply, add_apply, smul_add]
      done
    add_smul := by
      intros c d f
      ext v
      rw [add_apply]
      repeat rw [smul_apply]
      rw [add_smul]
      done
    zero_smul := by
      intro f
      ext v
      rw [smul_apply, zero_smul, zero_apply]
      done

  instance : VectorSpace 𝔽 (LinearMap 𝔽 V U) := VectorSpace.mk

  end LinearMap

end LinearMap

end VectorSpace
