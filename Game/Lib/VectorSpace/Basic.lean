import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

class VectorSpace (𝔽 : Type*) (V : Type*) [Field 𝔽] [AddCommGroup V] extends Module 𝔽 V

namespace VectorSpace

variable (𝔽 : Type*) [Field 𝔽]
instance FieldVectorSelf {𝔽 : Type*} [Field 𝔽] : VectorSpace 𝔽 𝔽 where

end VectorSpace
