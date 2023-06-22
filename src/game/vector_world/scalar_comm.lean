import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level5 
namespace tuple -- hide

/- 
# Vector world

## Level 6: `Scalars pass through` 

-/

/- Lemma
(cx)·y=c (x·y) for all x, y ∈ ℝⁿ and c ∈ R
-/

lemma scalar_comm: ∀ {n : ℕ} (c d: ℝ) (v: tuple n), c**(d**v) = d**(c**v) :=
begin 
  intro n,
  induction n with n hn, 
  {intros c d v, 
  cases v, 
  dsimp [scalar_mul, map],
  refl,},
  {intros c d v, 
  cases v,
    simp,
    split,
    {linarith,},
    {rw hn,},
  },
end

end tuple -- hide