import algebra.field.defs
import data.real.basic
import analysis.inner_product_space.basic

universes u w

class vector_space (𝕍 : Type u) (𝔽 : Type w) [field 𝔽] extends add_comm_group 𝕍, has_smul 𝔽 𝕍 :=
  (smul_comp_mul : ∀ (a b : 𝔽) (v : 𝕍), a • (b • v) = (a * b) • v)
  (one_smul : ∀ (v : 𝕍), 1 • v = v)
  (smul_dist_vec_add : ∀ (a : 𝔽) (u v : 𝕍), a • (u + v) = a • u + a • v)
  (smul_dist_scalar_add : ∀ (a b : 𝔽) (v : 𝕍), (a + b) • v = a • v + b • v)

class inner_prod_space_real (𝕍 : Type u) extends vector_space 𝕍 ℝ, has_inner ℝ 𝕍 :=
  (add_left : ∀ (u v w : 𝕍), inner (u + v) w = inner u w + inner v w)
  (smul_left : ∀ (u v : 𝕍) (α : ℝ), inner (α • u) v = α • (inner u v))
  (inner_comm : ∀ (u v : 𝕍), inner u v = inner v u)
  (inner_self_ge_zero : ∀ (v : 𝕍), inner v v ≥ 0)
  (inner_self_zero_iff_zero : ∀ (v : 𝕍), inner v v = 0 ↔ v = 0)

