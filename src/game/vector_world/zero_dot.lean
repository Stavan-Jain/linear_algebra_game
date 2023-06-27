import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_world.zero_smul
namespace tuple -- hide


/- 

# Vector world

## Level 9: `zero_mul` 

-/

/- Lemma

-/

lemma zero_mul : ∀ {n : ℕ} (u : ℝ ^ n), 0 ⬝ u = 0 :=
begin
  intros n u,
  rw ← zero_smul (0 : ℝ ^ n),
  rw scalar_through,
  simp,
end

end tuple -- hide
