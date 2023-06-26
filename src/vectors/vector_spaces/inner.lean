import data.real.basic
import data.complex.basic
import analysis.inner_product_space.basic

import vectors.vector_spaces.linearity

namespace vector_spaces


open_locale complex_conjugate
open is_R_or_C (re)
class inner_prod_space (𝕍 : Type*) (𝔽 : Type*) [is_R_or_C 𝔽] extends vector_space 𝕍 𝔽, has_inner 𝔽 𝕍 :=
  (bilinear : bilinear_form inner)
  (inner_comm : ∀ (u v : 𝕍), conj (inner u v) = inner v u)
  (inner_self_ge_zero : ∀ (v : 𝕍), re (inner v v) ≥ 0)
  (inner_self_zero_iff_zero : ∀ (v : 𝕍), inner v v = 0 ↔ v = 0)


@[simp]
def orthogonal {𝕍 : Type*} {𝔽 : Type*} [is_R_or_C 𝔽] [inner_prod_space 𝕍 𝔽] (x y : 𝕍) : Prop :=
  inner x y = (0 : 𝔽)

infix ` ⊥ `:63 := orthogonal
infix ` ⟂ `:63 := orthogonal
-- for some reason the vscode lean extension has \bot and \perp being different


end vector_space
