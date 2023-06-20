import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level13 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 14: `Unit vector stuff` 

-/

/- Lemma
||(1 / ||x|| ) *x || = 1
-/


#check abs_eq_self
#check scalar_norm
#check inv_mul_cancel
lemma div_norm_unit: ∀ {n : ℕ} (x: tuple n)
, x ≠ tuple.zero → ↑(tuple.norm ((1 / tuple.norm x) ** x)) = (1:ℝ)   :=
begin 
  intros n x xneq, 
  have i:= scalar_norm (1 / tuple.norm x) x,
  rw ← i, 
  simp, 
  have j : 0 ≤ ((x.norm)⁻¹ : ℝ)   , 
  {
    simp, 
  },
  rw abs_eq_self.mpr j, 
  apply inv_mul_cancel, 
  have m : ↑(x.norm) = (0:ℝ) ↔ x = tuple.zero , 
  {
    exact norm_zero_iff x,
  }, 
  by_contra, 
  have k := m.mp h, 
  exact xneq k, 
end

end tuple -- hide