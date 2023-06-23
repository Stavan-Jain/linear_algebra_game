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

lemma scalar_assoc : ∀ {n :ℕ } (c d : ℝ)(u : tuple n),(c ** (d ** u)) = (c * d)** u :=
begin 
  intro n,
  induction n with n hn, 
  {intros c d v, 
  cases v, 
  simp,},
  {intros c d v, 
  cases v,
    simp,
    split,
    {linarith,},
    {rw hn,},
  },
end

end tuple -- hide