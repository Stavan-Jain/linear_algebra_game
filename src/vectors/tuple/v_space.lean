import vectors.tuple
import vectors.tuple.tactics
import vectors.vector_spaces
import vectors.tuple.group

namespace tuple
open vector_spaces
open vector_spaces.vector_space

variables {α : Type*} {𝔽 : Type*} [field 𝔽] [vector_space α 𝔽]

instance {n : ℕ} : vector_space (α ^ n) 𝔽 := 
begin
  constructor,
  { intros a b v,
    induction n with d hd,
    { cases v, refl, },
    { cases v,
      simp,
      exact ⟨smul_comp_mul a b v_head, hd v_tail⟩, }, }, 
  { intros v, 
  induction n with d hd, 
    { cases v, refl, }, 
    { cases v, 
      simp, 
      exact ⟨vector_space.one_smul v_head, hd v_tail⟩ , } },
  { intros a u v, 
  induction n with d hd, 
    { cases u, cases v, refl, }, 
    { cases u, cases v,
      simp,
      exact ⟨ smul_dist_vec_add a u_head v_head, hd u_tail v_tail⟩ , } },
  { intros a b v, 
  induction n with d hd,
    { cases v, refl, }, 
    { cases v, 
      simp,
      exact ⟨smul_dist_scalar_add a b v_head, hd v_tail ⟩ , } },
end

end tuple