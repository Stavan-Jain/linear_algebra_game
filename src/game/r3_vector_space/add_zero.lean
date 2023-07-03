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
  cases_tuple u 3,
  simpa,
end

end tuple -- hide
