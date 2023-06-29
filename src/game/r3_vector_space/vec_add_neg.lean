import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.add_zero --hide

namespace tuple -- hide


/- 

# Vector world

## Level 4: `additive inverse` 

-/

/- Lemma

-/

lemma vec_add_neg : ∀ (v : ℝ ^ 3), v + -v = 0 :=
begin
  intros v,

  cases v with _ v₁ tail,
  cases tail with _ v₂ tail,
  cases tail with _ v₃ tail,
  cases tail,

  simp,
  refl,
end

end tuple -- hide
