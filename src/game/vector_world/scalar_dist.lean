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

lemma scalar_dist: ∀ {n : ℕ} (c: ℝ) (x: tuple n) (y : tuple n) ,  c**(x + y) = (c**x) + (c**y) :=
begin 
  intro n,
  induction n with d hd, 
  {intros c x y, 
  casesm* (tuple 0), 
  simp,
  dsimp [scalar_mul, map],
  refl,},
  {intros c x y, 
    casesm* (tuple d.succ),
    simp,
    split,
    {linarith,},
    {rw hd,},
  },
end

end tuple -- hide