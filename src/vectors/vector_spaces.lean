import algebra.field.defs

universes u w

class vector_space (𝕍 : Type u) [add_comm_group 𝕍] (𝔽 : Type w) [field 𝔽] [has_smul 𝔽 𝕍]:=
  (smul_comp_mul : ∀ (a b : 𝔽) (v : 𝕍), a • (b • v) = (a * b) • v)
  (one_smul : ∀ (v : 𝕍), 1 • v = v)
  (smul_dist_vec_add : ∀ (a : 𝔽) (u v : 𝕍), a • (u + v) = a • u + a • v)
  (smul_dist_scalar_add : ∀ (a b : 𝔽) (v : 𝕍), (a + b) • v = a • v + b • v)
