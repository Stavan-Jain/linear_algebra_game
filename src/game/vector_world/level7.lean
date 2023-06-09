import vectors.tuple -- hide
import data.real.basic
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
  cases x, 
  cases y,  
  cases z,
  dsimp [dot_product],
  rw add_zero, 
  },
  {
    intros x y z, 
    cases x, 
    cases y, 
    cases z, 
    dsimp [dot_product], 
    have i : x_head * y_head + x_tail ⬝ y_tail + (x_head * z_head + x_tail ⬝ z_tail)
    = x_tail ⬝ y_tail + x_tail ⬝ z_tail +  x_head * y_head + x_head * z_head , 
    {
      linarith, 
    }, 
    rw i, 
    rw ← hd x_tail y_tail z_tail,  
    dsimp [has_add.add], simp [tuple.add], 
    dsimp [dot_product],  
    repeat {dsimp [has_add.add]} , 
    sorry,
  }

end

end tuple -- hide