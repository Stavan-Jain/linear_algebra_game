import vectors.tuple -- hide
import data.real.basic
import game.vector_world.scalar_through--hide
namespace tuple -- hide

/- 
# Vector world

## Level 7: `Distributive Property` 

-/

/- Lemma
x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z)
-/

lemma dot_dist: ∀ {n : ℕ} (x y z : ℝ ^ n), x ⬝ (y + z) = (x ⬝ y) + (x ⬝ z) :=
begin 
  intros n x y z,
  induction n with d hd, 
  { casesm* (ℝ ^ 0),
    simp, },
  { cases x with _ x₁ xₙ,
    cases y with _ y₁ yₙ,
    cases z with _ z₁ zₙ,
    simp,
    calc x₁ * (y₁ + z₁) + xₙ ⬝ (yₙ + zₙ) = x₁ * y₁ + x₁ * z₁ + xₙ ⬝ (yₙ + zₙ) : by ring_nf
      ... = x₁ * y₁ + x₁ * z₁ + (xₙ ⬝ yₙ + xₙ ⬝ zₙ) : by rw hd xₙ yₙ zₙ
      ... = x₁ * y₁ + xₙ ⬝ yₙ + (x₁ * z₁ + xₙ ⬝ zₙ) : by ring_nf, },
end

end tuple -- hide
