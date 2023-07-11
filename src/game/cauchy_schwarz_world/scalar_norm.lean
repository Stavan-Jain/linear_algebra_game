import game.cauchy_schwarz_world.scalar_through --hide
namespace tuple -- hide

/- 
# Cauchy Schwarz world

## Level 3: `scalar pass through norms` 

-/

/- Lemma

|c|*||x|| = ||cx||

Background:

Here we'll be proving that multiplying the magnitude of vector x by the scalar c yields the same 
result as finding the magnitude of the vector cx. 

Strategy and Hints: 

In class you'll probably prove this using the formula for the magnitude of a vector. Here we will do it differently. 

Let's remember that we've already proved "scalar_through" which tells us that (c**x) ⬝ y =c * (x ⬝ y), which looks like it could be useful here. 

When doing a proof it is sometimes useful to change the goal to something that implies that the initial goal is also true. 

-/

lemma scalar_norm : ∀ {n : ℕ} (c : ℝ) (x : ℝ ^ n), (|c| * ‖x‖ : ℝ)  = ‖c • x‖ :=
begin 
  intros n c x,
  repeat {rw norm_eq_sqrt_norm_sq}, 
  simp, 
  have h : ∀ (x : real), (0 ≤ x) → x = real.sqrt(x * x),
  { intros x xgeq, 
    simp [xgeq], },
  have h₁ : |c| = real.sqrt(|c|*|c|) := by exact h (|c|) (by simp),  
  rw h₁,
  simp,
  rw ← real.sqrt_mul,
  { congr' 1,  
    rw [scalar_through, dot_comm],
    rw dot_comm x (c • x), 
    rw ← scalar_through,  
    rw [scalar_through, scalar_through c, mul_assoc], },
 { exact mul_self_nonneg c, },
end

end tuple -- hide
