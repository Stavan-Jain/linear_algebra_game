import set_theory.cardinal.basic

import vectors.vector_spaces.basis

open_locale cardinal


namespace vector_spaces

variables {𝕍 : Type*} (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽]


class dimension (dim : cardinal) :=
  (basis_set : set 𝕍)
  (is_basis : basis 𝔽 basis_set)
  (cardinality : dim = #basis_set)


class fin_dimension (dim : ℕ) :=
  (basis_set : 𝕍 ^ dim)
  (is_basis : fin_basis 𝔽 basis_set)


end vector_spaces
