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
