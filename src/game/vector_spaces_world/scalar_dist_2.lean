import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
import game.vector_spaces_world.one_smul --hide
namespace tuple -- hide


/- 

# Vector Spaces World

Strategy:
This level will give you more practice with induction!

## Level 8: `Distributive property 2` 

-/

/- Lemma
(a + b) • v = a • v + b • v

-/

lemma scalar_dist_2 : ∀ {n : ℕ} (a b : ℝ) (v : ℝ ^ n), (a + b) • v = a • v + b • v :=
begin 
  intros,
  induction n with n hn,
  { cases v,
    simp, },
  { cases v with n v₁ vₙ,
    simp,
    split,
    { linarith, },
    { exact hn vₙ, }, },
end

end tuple -- hide