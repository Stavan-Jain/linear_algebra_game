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

lemma vec_comm : ∀ {n : ℕ} (u v : ℝ ^ n), u + v = v + u :=
begin
  intro n,
  induction n with n hn,
  { intros u v,
    casesm* (ℝ ^ 0),
    refl, },
  { intros u v,
    cases u with n u₁ uₙ,
    cases v with n v₁ vₙ,
    simp,
    split,
    { linarith, },
    { exact hn uₙ vₙ, }, },
end

end tuple -- hide
