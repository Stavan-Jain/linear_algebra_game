import algebra.big_operators.basic

import vectors.vector_spaces
import vectors.tuple

open set
open tuple
open_locale big_operators


namespace vector_spaces

variables {𝕍 : Type*} (𝔽 : Type*) [field 𝔽] [vector_space 𝕍 𝔽]


def lin_comb (S : set 𝕍) {n : ℕ} (s : fin n → {x : 𝕍 // x ∈ S}) (c : fin n → 𝔽) : 𝕍 :=
  ∑ m, c m • s m

def span (S : set 𝕍) : set 𝕍 :=
  {v : 𝕍 | ∃ (n : ℕ) (s : fin n → {x : 𝕍 // x ∈ S}) (c : fin n → 𝔽), v = lin_comb 𝔽 S s c}


@[simp]
def linear_dependent (S : set 𝕍) : Prop := ∃ (v ∈ S), v ∈ span 𝔽 {x ∈ S | x ≠ v}

@[simp]
def linear_independent (S : set 𝕍) : Prop := ¬ linear_dependent 𝔽 S


class basis (S : set 𝕍) : Prop :=
  (lin_indep : linear_independent 𝔽 S)
  (spanning : span 𝔽 S = univ)


def fin_lin_comb {n : ℕ} (S : 𝕍 ^ n) (c : 𝔽 ^ n) : 𝕍 :=
  ∑ (m : fin n), (finth c m)  • (finth S m)

lemma lin_comb_of_fin_lin_comb {n : ℕ} (S : 𝕍 ^ n) (c : 𝔽 ^ n)
  : fin_lin_comb 𝔽 S c = lin_comb 𝔽 {v : 𝕍 | v ∈ S} (finth_elem S) (finth c) := rfl

lemma fin_lin_comb_of_lin_comb (S : set 𝕍) {n : ℕ} (s : fin n → S) (c : fin n → 𝔽)
  : lin_comb 𝔽 S s c = fin_lin_comb 𝔽 (from_fin_fn (coe ∘ s)) (from_fin_fn c) :=
begin
  simp [lin_comb, fin_lin_comb, finth],
  congr,
  funext,
  induction n with n ihn,
  { exact m.elim0', },
  set s' := λ (x : fin n), (s x.succ) with ← hs,
  set c' := λ (x : fin n), (c x.succ) with ← hc,
  specialize ihn s' c',
  cases m with m hm,
  induction m with m ihm,
  { refl, },
  { set m' : fin n := ⟨m, nat.succ_lt_succ_iff.mp hm⟩ with ← hm',
    specialize ihn m',
    simp [from_fin_fn, nth],
    have hs' : s ⟨m.succ, hm⟩ = s' m' := rfl,
    have hc' : c ⟨m.succ, hm⟩ = c' m' := rfl,
    rwa [hs', hc, hc'], },
end


def fin_span {n : ℕ} (S : 𝕍 ^ n) : set 𝕍 :=
  {v : 𝕍 | ∃ (c : 𝔽 ^ n), v = fin_lin_comb 𝔽 S c}

lemma fin_span_equiv {n : ℕ} (S : 𝕍 ^ n) : fin_span 𝔽 S = span 𝔽 {v : 𝕍 | v ∈ S} :=
begin
  apply eq_of_subset_of_subset,
  { intros v hv,
    cases hv with c hv,
    use [n, finth_elem S, finth c],
    simp [lin_comb, fin_lin_comb] at *,
    rw hv,
    congr, },
  { intros v hv,
    rcases hv with ⟨m, s, c, hv⟩,
    rw fin_lin_comb_of_lin_comb 𝔽 {v : 𝕍 | v ∈ S} s c at hv,
    -- TODO: very hard
    sorry },
end


@[simp]
def fin_linear_dependent : ∀ {n : ℕ}, 𝕍 ^ n → Prop
| 0 _ := true
| (n+1) S := ∃ (m : fin n.succ), (S.finth m) ∈ fin_span 𝔽 (S.remove_finth m)

@[simp]
def fin_linear_independent {n : ℕ} (S : 𝕍 ^ n) : Prop := ¬ fin_linear_dependent 𝔽 S


class fin_basis {n : ℕ} (S : 𝕍 ^ n) : Prop :=
  (lin_indep : fin_linear_independent 𝔽 S)
  (spanning : fin_span 𝔽 S = univ)


end vector_spaces
