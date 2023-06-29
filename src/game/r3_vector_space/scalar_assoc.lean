import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.scalar_dist_1 --hide
namespace tuple -- hide


/- 

# Vector world

## Level 6: `scalar_assoc` 

-/

/- Lemma

-/

lemma scalar_assoc : ∀ (c d : ℝ) (u : ℝ ^ 3), c • d • u = (c * d) • u :=
begin 
  intros c d u,
  cases_tuple u 3,
  simp,
  exact ⟨by ring, by ring, by ring⟩,
end

end tuple -- hide
