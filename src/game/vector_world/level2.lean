import vectors.tuple -- hide
import data.real.basic
namespace tuple -- hide

/- 
# Vector world

We're going to prove that { [0, 1] , [1, 0] } forms a basis for ℝ² 

## Level 2: `basis_for_r2` 

-/

/- Lemma
And vector in ℝ² can be expressed as a linear combination of the vectors [0, 1] and [1, 0]
-/
lemma lin_comb: ∀  (i: ℝ) (j :ℝ ), ∃(d₁ : ℝ )(d₂ : ℝ ) , [[i, j]] =   (d₁ ** [[1, 0]]) + (d₂** [[0, 1]]) :=
begin 
  intros i j ,
  use [i, j], 
  dsimp [scalar_mul, map], 
  simp, 
  simp [has_add.add], dsimp [tuple.add], 
  simp, 
end

end tuple -- hide