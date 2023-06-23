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

lemma scalar_dist_1 : ∀ {n : ℕ} (c : ℝ) (u v : tuple n), c** (u + v) = c** u + c** v :=
begin 
  intro n,
  induction n with d hd, 
  {intros c x y, 
  casesm* (tuple 0), 
  simp,},
  {intros c x y, 
    casesm* (tuple d.succ),
    simp,
    split,
    {linarith,},
    {rw hd,},
  },
end

end tuple -- hide