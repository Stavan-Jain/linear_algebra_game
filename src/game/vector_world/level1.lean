import vectors.tuple -- hide
namespace tuple -- hide

/- 
# Vector world

We're going to prove that { [0, 1] , [1, 0] } forms a basis for ℝ² 

## Level 2: `basis_for_r2` 

-/

/- Lemma
And vector in ℝ² can be expressed as a linear combination of the vectors [0, 1] and [1, 0]
-/

lemma lin_comb: ∀  (a: tuple 2), ∃(d₁ : ℤ)(d₂ : ℤ) , a = (d₁ ** [[0, 1]]) + (d₂** [[1, 0]]) :=
begin 
 sorry, 
end

end tuple -- hide
