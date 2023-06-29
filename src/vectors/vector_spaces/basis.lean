import algebra.big_operators.basic

import vectors.vector_spaces

open set
open_locale big_operators


namespace vector_spaces

variables {𝕍 : Type*} (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽]


def lin_comb (S : set 𝕍) {n : ℕ} (s : fin n → {x : 𝕍 // x ∈ S}) (c : fin n → 𝔽) : 𝕍 :=
  ∑ m, c m • s m

def span (S : set 𝕍) : set 𝕍 :=
  {v : 𝕍 | ∃ (n : ℕ) (s : fin n → {x : 𝕍 // x ∈ S}) (c : fin n → 𝔽), v = lin_comb 𝔽 S s c }


@[simp]
def linear_dependent (S : set 𝕍) : Prop := ∃ (v ∈ S), v ∈ span 𝔽 {x ∈ S | x ≠ v}

@[simp]
def linear_independent (S : set 𝕍) : Prop := ¬ linear_dependent 𝔽 S


class basis (S : set 𝕍) : Prop :=
  (lin_indep : linear_independent 𝔽 S)
  (spanning : span 𝔽 S = univ)


end vector_spaces
