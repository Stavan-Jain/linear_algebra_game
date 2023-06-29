import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.vec_assoc --hide
namespace tuple -- hide


/- 

# Vector world

## Level 2: `vector_assoc` 

-/

/- Lemma

-/

lemma vec_comm : ∀ (u v : ℝ ^ 3), u + v = v + u :=
begin
  intros u v,
  cases_tuple u 3,
  cases_tuple v 3,
  simp,
  exact ⟨by ring, by ring, by ring⟩,
end

end tuple -- hide
