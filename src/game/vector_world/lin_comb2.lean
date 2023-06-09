import vectors.tuple -- hide
import data.real.basic
import game.vector_world.lin_comb --hide
namespace tuple -- hide

/- 

# Vector world

Here we'll be looking at another application of linear combinations. 

First, let's review what basis vectors are. A set of vectors can be called the basis of 
a vector space or a sub-space if every vector in that space can be expressed as a linear combination of that set of vectors. 
Basically, the entire space can be constructed using its basis vectors.

For a set of vectors to be basis vectors they must fulfill the following conditions:

1. They must be linearly independent 
2. A space of dimension n must have n vectors in its basis i.e for any finite dimensional vector space, 
   the dimension of the vector space will equal the number of basis vectors.

Introduce definition of spanning sets instead of basis 

Now let's move on to our proof :-


We're going to prove that { [0, 1] , [1, 0] } forms a basis for ℝ² 

## Level 2: `basis_for_r2` 

-/

/- Lemma
All vector in ℝ² can be expressed as a linear combination of the vectors [0, 1] and [1, 0]
-/
lemma lin_comb2 : ∀ (i j : ℝ), ∃ (d₁ d₂ : ℝ), [[i, j]] = (d₁ • [[1, 0]]) + (d₂ • [[0, 1]]) :=
begin 
  intros i j,
  use [i, j],
  simp,
end

end tuple -- hide
