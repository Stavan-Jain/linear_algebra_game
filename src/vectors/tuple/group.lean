import vectors.tuple
import algebra.group.basic

namespace tuple

lemma add_assoc {n : ℕ} : ∀ (u v w : tuple n), u + v + w = u + (v + w) := sorry

lemma zero_add {n : ℕ} : ∀ (v : tuple n), 0 + v = v := sorry

lemma add_zero {n : ℕ} : ∀ (v : tuple n), v + 0 = v := sorry

lemma add_comm {n : ℕ} : ∀ (u v : tuple n), u + v = v + u := sorry


protected def nsmul {n : ℕ} (c : ℕ) (v : tuple n) : tuple n := ↑c ** v

protected lemma nsmul_zero {n : ℕ} : ∀ (v : tuple n), (tuple.nsmul 0 v = 0) := sorry

protected lemma nsmul_succ {n : ℕ} : (∀ (c : ℕ) (v : tuple n),
  tuple.nsmul c.succ v = v + tuple.nsmul c v) := sorry


lemma sub_eq_add_neg {n : ℕ} : (∀ (v u : tuple n), v - u = v + -u) := sorry


protected def zsmul {n : ℕ} (c : ℤ) (v : tuple n) : tuple n := ↑c ** v

protected lemma zsmul_zero {n : ℕ} : ∀ (v : tuple n), (tuple.zsmul 0 v = 0) := sorry

protected lemma zsmul_succ {n : ℕ} : (∀ (c : ℕ) (v : tuple n),
  tuple.zsmul (int.of_nat c.succ) v = v + tuple.zsmul (int.of_nat c) v) := sorry

protected lemma zsmul_neg {n : ℕ} : (∀ (c : ℕ) (v : tuple n),
  tuple.zsmul -[1+ c] v = -tuple.zsmul ↑(c.succ) v) := sorry


lemma add_left_neg {n : ℕ} : ∀ (v : tuple n), -v + v = 0 := sorry


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
