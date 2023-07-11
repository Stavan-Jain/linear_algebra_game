import vectors.tuple -- hide
import data.real.basic
import game.vector_world.dot_pos_def_2 
namespace tuple -- hide

/- 
# Vector world

## Level 6: `Scalars pass through` 

-/

/- Lemma
(cx)·y=c (x·y) for all x, y ∈ ℝⁿ and c ∈ R
-/

lemma scalar_through: ∀ {n : ℕ} (c : ℝ) (x y : ℝ ^ n), (c • x) ⬝ y = c * (x ⬝ y) :=
begin 
  intros n c x y,
  induction n with d hd, 
  { cases x, cases y, 
    simp, },
  { cases x with _ x₁ xₙ, 
    cases y with _ y₁ yₙ, 
    simp,
    rw mul_add,
    rw hd xₙ yₙ,
    linarith, },
end

end tuple -- hide
