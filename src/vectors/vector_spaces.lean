import algebra.field.defs
import group_theory.group_action.defs

namespace vector_spaces


class vector_space (𝕍 : Type*) (𝔽 : Type*) [field 𝔽] extends add_comm_group 𝕍, has_smul 𝔽 𝕍 :=
  (smul_comp_mul : ∀ (a b : 𝔽) (v : 𝕍), a • (b • v) = (a * b) • v)
  (one_smul : ∀ (v : 𝕍), (1 : 𝔽) • v = v)
  (smul_dist_vec_add : ∀ (a : 𝔽) (u v : 𝕍), a • (u + v) = a • u + a • v)
  (smul_dist_scalar_add : ∀ (a b : 𝔽) (v : 𝕍), (a + b) • v = a • v + b • v)


instance field_vector_self {𝔽 : Type*} [field 𝔽] : vector_space 𝔽 𝔽 :=
begin
  constructor,
  { intros a b v,
    simp [mul_assoc], },
  { intro v,
    simp, },
  { intros a u v,
    simp [left_distrib], },
  { intros a b v,
    simp [right_distrib], },
end


end vector_space
