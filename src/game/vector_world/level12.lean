import vectors.tuple -- hide
import data.real.basic
import game.vector_world.level11 --hide


namespace tuple -- hide

/- 
# Vector world

## Level 12: `scalar pass through norms` 

-/

/- Lemma
|c|*||x|| = ||cx||
-/

lemma scalar_norm: ∀ {n : ℕ} (c : ℝ) (x: tuple n)
,(|c| * x.norm : ℝ)  = ((c**x).norm : ℝ)   :=
begin 
  intros n c x,
  dsimp [tuple.norm], simp,
  have j : ∀ (x : real), (0 ≤ x) → x = real.sqrt(x * x),
  {
    intros x xgeq, 
    simp [xgeq],   
  },
  by_cases c ≥ 0,
  {
  rw abs_eq_self.mpr h, 

  have i := j c h, 
  nth_rewrite 0 i, 
  rw ← real.sqrt_mul ,
  dsimp [norm_sq],
  simp [scalar_through],  
  nth_rewrite 1 dot_comm, 
  simp [scalar_through],  
  rw mul_assoc, 
  exact mul_nonneg h h},
  
  have clt : c < 0 , 
  {
    linarith, 
  }, 
  have r : ∀(x :real), (x < 0)→ ∃ y ≥ 0, x = -y, {
    intros x xleq, use (-x), 
    split, 
    refine neg_nonneg.mpr _,
    linarith, 
    linarith,
  },
  have s : ∀ (y: real), (-y)*(-y) = y * y , 
  {
    intro y, 
    linarith,
  },
  
  have k : ∀ (x : real), (x < 0) → x = - real.sqrt(x * x),
  {
    intros x xleq, 
    have y := r x xleq,
    cases y with y1 y2, 
    cases y2,
    rw y2_h , 
    rw s, 
    rw ← j y1 y2_w,  
    
  },
  nth_rewrite 0 k c clt,
  have : -real.sqrt (c * c) * real.sqrt ↑(x.norm_sq) = -(real.sqrt (c * c) * real.sqrt ↑(x.norm_sq)), 
  {
    linarith, 
  },
  simp, 
  have m : real.sqrt (c * c) ≥ 0 ,
  {
    exact real.sqrt_nonneg (c*c), 
  }, 
  rw abs_eq_self.mpr m,
  rw ← real.sqrt_mul ,
  dsimp [norm_sq],
  simp [scalar_through],    
  nth_rewrite 1 dot_comm, 
  simp [scalar_through], 
  rw mul_assoc,
  exact mul_self_nonneg c,
end

end tuple -- hide