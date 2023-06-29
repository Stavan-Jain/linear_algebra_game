import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.vec_comm --hide
namespace tuple -- hide


/- 

# Vector world

## Level 3: `add_zero` 

-/

/- Lemma

-/

lemma add_zero : ∀ (u : ℝ ^ 3), u + 0 = u :=
begin 
  intro u,

  cases u with _ u₁ u_tail,
  cases u_tail with _ u₂ u_tail,
  cases u_tail with _ u₃ u_tail,
  cases u_tail,
  
  simp,
  refl,
end

end tuple -- hide
