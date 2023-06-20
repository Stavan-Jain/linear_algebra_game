import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level6 --hide
namespace tuple -- hide

/- 
# Vector world

## Level 7: `Distributive Property` 

-/

/- Lemma
x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z)
-/

lemma dot_dist: ∀ {n : ℕ} (x: tuple n) (y : tuple n) (z:tuple n)
,  x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z) :=
begin 
  intro n,
  induction n with d hd, 
  {intros x y z, 
  casesm* (tuple 0), 
  dsimp [dot_product],
  rw add_zero, 
  },
  {
    intros x y z, 
    casesm* (tuple d.succ), 
    dsimp [dot_product], 
    have i : x_head * y_head + x_tail ⬝ y_tail + (x_head * z_head + x_tail ⬝ z_tail)
    = x_tail ⬝ y_tail + x_tail ⬝ z_tail +  x_head * y_head + x_head * z_head , 
    {
      linarith, 
    }, 
    rw i, 
    rw ← hd x_tail y_tail z_tail,  
    linarith, 
  },
end

end tuple -- hide