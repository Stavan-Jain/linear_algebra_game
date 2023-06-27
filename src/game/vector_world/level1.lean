import vectors.tuple -- hide
import data.real.basic --hide
import vectors.tuple.tactics --hide
namespace tuple -- hide


/- 

Introduction

In the following portion we will be looking at a problem related to linear combinations. 
A linear combination is essentially a sum. Vectors are added to get new vectors. A vector is said to be
a linear combination of another set of vectors if it can be obtained by adding some combination of their scalar products. 
Essentially, vec(z) is a linear combination of vec(x) and vec(y) if there exist scalars a, b such that 
a(vec(x)) + b(vec(y)) = vec(c)

# Vector world

We're going to prove that [3, 4] is a linear combination of the standard basis vectors in ℝ²  

## Level 1: `lin_comb` 

-/

/- Lemma
The vector [3, 4] is a linear combination of the vectors [0, 1] and [1, 0]
-/

lemma lin_comb: ∃ (d₁ d₂ : ℝ), [[(3 : ℝ), 4]] = (d₁ • [[0, 1]]) + (d₂ • [[1, 0]]) :=
begin 
  use 4,
  use 3,
  simp,
end

end tuple -- hide
