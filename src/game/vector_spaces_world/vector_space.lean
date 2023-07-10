import game.vector_spaces_world.scalar_dist_2
import vectors.vector_spaces
import game.vector_spaces_world.rn_group
namespace tuple

-- TODO!
instance {n : ℕ} : add_comm_group (ℝ  ^ n) := 
⟨
  tuple.add,
  add_assoc,
  tuple.zero,
  zero_add,
  add_zero,
  tuple.nsmul,
  tuple.nsmul_zero,
  tuple.nsmul_succ,
  tuple.neg,
  tuple.sub,
  sub_eq_add_neg',
  tuple.zsmul,
  tuple.zsmul_zero,
  tuple.zsmul_succ,
  tuple.zsmul_neg,
  add_left_neg,
  add_comm,
  ⟩



open vector_spaces
instance {n : ℕ} : vector_space (ℝ ^ n) ℝ := 
begin
  split, 
  { intros, 
    rw scalar_assoc, }, 
  { intros, 
    rw one_smul, }, 
  { intros, 
    rw scalar_dist_1, }, 
  { intros, 
    rw scalar_dist_2, },
end

end tuple
 

