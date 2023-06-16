import vectors.tuple
import vectors.tuple.tactics
import algebra.group.basic

namespace tuple


lemma add_assoc {n : ℕ} : ∀ (u v w : tuple n), u + v + w = u + (v + w) := begin
  induction n with n hn,
  { intros u v w,
    cases u, cases v, cases w,
    refl, },
  { intros u v w,
    cases u with n u₁ uₙ,
    cases v with n v₁ vₙ,
    cases w with n w₁ wₙ,
    simp,
    split,
    { ring, },
    { exact hn uₙ vₙ wₙ, }, },
end

lemma zero_add {n : ℕ} : ∀ (v : tuple n), 0 + v = v := begin
  induction n with n hn,
  { intro v, cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end

lemma add_zero {n : ℕ} : ∀ (v : tuple n), v + 0 = v := begin
  induction n with n hn,
  { intro v, cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, }
end

lemma add_comm {n : ℕ} : ∀ (u v : tuple n), u + v = v + u := begin
  induction n with n hn,
  { intros u v,
    cases u, cases v,
    refl, },
  { intros u v,
    cases u with n u₁ uₙ,
    cases v with n v₁ vₙ,
    simp,
    split,
    { ring, },
    { exact hn uₙ vₙ, }, },
end


protected def nsmul {n : ℕ} (c : ℕ) (v : tuple n) : tuple n := ↑c ** v

protected lemma nsmul_zero {n : ℕ} : ∀ (v : tuple n), (tuple.nsmul 0 v = 0) := begin
  induction n with n hn,
  { intro v, cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp [tuple.nsmul] at *,
    exact hn tail, },
end

protected lemma nsmul_succ {n : ℕ}
  : (∀ (c : ℕ) (v : tuple n), tuple.nsmul c.succ v = v + tuple.nsmul c v) := begin
  intro c,
  induction n with n hn,
  { intro v, cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp [tuple.nsmul] at *,
    split,
    { ring, },
    { exact hn tail, }, },
end


lemma sub_eq_add_neg {n : ℕ} : (∀ (v u : tuple n), v - u = v + -u) := begin
  induction n with n hn,
  { intros v u,
    cases v, cases u,
    refl, },
  { intros v u,
    cases v with n v₁ vₙ,
    cases u with n u₁ uₙ,
    simp,
    split,
    { ring, },
    { exact hn vₙ uₙ, }, }
end


protected def zsmul {n : ℕ} (c : ℤ) (v : tuple n) : tuple n := ↑c ** v

protected lemma zsmul_zero {n : ℕ} : ∀ (v : tuple n), (tuple.zsmul 0 v = 0) := begin
  induction n with n hn,
  { intro v, cases v,
    refl, },
  { intro v,
    cases v with n head tail,
    simp [tuple.zsmul] at *,
    exact hn tail, },
end

protected lemma zsmul_succ {n : ℕ}
  : (∀ (c : ℕ) (v : tuple n),
    tuple.zsmul (int.of_nat c.succ) v = v + tuple.zsmul (int.of_nat c) v) := begin
  intro c,
  induction n with n hn,
  { intro v, cases v, refl, },
  { intro v,
    cases v with n head tail,
    simp [tuple.zsmul] at *,
    split,
    { ring, },
    { exact hn tail, }, },
end

protected lemma zsmul_neg {n : ℕ} : (∀ (c : ℕ) (v : tuple n),
  tuple.zsmul -[1+ c] v = -tuple.zsmul ↑(c.succ) v) := begin
  intro c,
  induction n with n hn,
  { intro v, cases v, refl, },
  { intro v,
    cases v with n head tail,
    simp [tuple.zsmul] at *,
    split,
    { ring, },
    { exact hn tail, }, },
end


lemma add_left_neg {n : ℕ} : ∀ (v : tuple n), -v + v = 0 := begin
  induction n with n hn,
  { intro v, cases v, refl, },
  { intro v,
    cases v with n head tail,
    simp,
    exact hn tail, },
end


instance {n : ℕ} : add_comm_group (tuple n) := ⟨
  tuple.add,
  add_assoc,
  tuple.zero,
  zero_add,
  add_zero,
  tuple.nsmul,
  tuple.nsmul_zero,
  tuple.nsmul_succ,
  tuple.neg,
  tuple.sub,
  sub_eq_add_neg,
  tuple.zsmul,
  tuple.zsmul_zero,
  tuple.zsmul_succ,
  tuple.zsmul_neg,
  add_left_neg,
  add_comm,
  ⟩


end tuple
