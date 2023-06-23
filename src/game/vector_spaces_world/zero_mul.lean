import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.zero_smul --hide
namespace tuple -- hide


/- 

# Vector world

## Level 9: `zero_mul` 

-/

/- Lemma

-/

lemma zero_mul : ∀ {n : ℕ } (u : tuple n), (0 : tuple n) ⬝ u = (0 : ℝ)   :=
begin
  intros n u,
  rw ← zero_smul (0 : tuple n),
  rw scalar_through,
  simp,
end

end tuple -- hide