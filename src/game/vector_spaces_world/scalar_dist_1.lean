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

lemma scalar_dist_1 : ∀ {n : ℕ} (c : ℝ) (u v : ℝ ^ n), c • (u + v) = c • u + c • v :=
begin 
  intros n c,
  induction n with n hn,
  { intros u v,
    casesm* (ℝ ^ 0),
    simp, },
  { intros u v,
    cases u with n u₁ uₙ,
    cases v with n v₁ vₙ,
    simp,
    split,
    { linarith, },
    { exact hn uₙ vₙ, }, },
end

end tuple -- hide
