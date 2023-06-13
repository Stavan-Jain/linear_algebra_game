import vectors.tuple -- hide
import data.real.basic --hide
namespace tuple -- hide


/- 
# Vector world

We're going to prove that [3, 4] is a linear combination of the standard basis vectors in ℝ²  

## Level 1: `lin_comb` 

-/

/- Lemma
The vector [3, 4] is a linear combination of the vectors [0, 1] and [1, 0]
-/

lemma lin_comb: ∃ (d₁ : ℝ )(d₂ : ℝ) , [[3, 4]] = tuple.add (d₁ ** [[0, 1]]) (d₂** [[1, 0]]) :=
begin 
  use 4,
  use 3,
  dsimp [scalar_mul, map, tuple.add], norm_num,
end

end tuple -- hide
