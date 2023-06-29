import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.vec_add_neg --hide
namespace tuple -- hide


/- 

# Vector world

## Level 5: `Distributive property 1` 

-/

/- Lemma

-/

lemma scalar_dist_1 : ∀ (c : ℝ) (u v : ℝ ^ 3), c • (u + v) = c • u + c • v :=
begin 
  intros c u v,

  cases u with _ u₁ tail,
  cases tail with _ u₂ tail,
  cases tail with _ u₃ tail,
  cases tail,

  cases v with _ v₁ tail,
  cases tail with _ v₂ tail,
  cases tail with _ v₃ tail,
  cases tail,

  simp,
  split, ring,
  split; ring,
end

end tuple -- hide
