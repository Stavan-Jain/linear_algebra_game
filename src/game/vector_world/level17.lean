import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level16 --hide

namespace tuple -- hide

/- 
# Vector world

## Level 17: `Triangle Inequality` 

-/

/- Lemma
||x + y|| ≤ ||x|| + ||y||
-/

lemma triangle_ineq: ∀ {n : ℕ} (x: tuple n) (y : tuple n) 
, (x + y).norm ≤ x.norm + y.norm    :=
begin 
  intros n x y, 
  have h1:= add_norm_square x y,
  have h2 := cauchy_schwarz x y,
  have h3 : x ⬝ y ≤ |x ⬝ y|, 
  {
    exact le_abs_self (x ⬝ y), 
  },
  have h4 : ↑((x + y).norm_sq) ≤ ((x.norm + y.norm)^2), 
  {
    calc 
      ↑((x + y).norm_sq) = ↑(x.norm_sq) + 2 * x ⬝ y + ↑(y.norm_sq) : 
        begin 
          exact h1
        end
      ... ≤ ↑(x.norm_sq) + 2 * |x ⬝ y| + ↑(y.norm_sq) :
      begin 
        linarith, 
      end
      ... ≤ ↑(x.norm_sq) + 2 * x.norm * y.norm + ↑(y.norm_sq) :
      begin
        linarith, 
      end
      ... =  ((x.norm + y.norm)^2) :
      begin 
        rw add_sq, 
        dsimp [tuple.norm], simp, refl, 
      end
  }, 
  sorry, 

end

end tuple