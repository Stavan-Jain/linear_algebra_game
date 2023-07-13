import analysis.normed.group.basic
import data.real.basic
import data.real.nnreal
import data.real.sqrt
-- TODO: stuff for complex numbers, including complex dot product and norm

universe u


inductive tuple (α : Type u) : ℕ → Type u
| nil : tuple 0
| cons {n : ℕ} (head : α) (tail : tuple n) : (tuple (n + 1))

instance : has_pow (Type u) ℕ := ⟨tuple⟩
notation:min `(` t:79 ` ^ `:79 d:(foldl:34 ` × `:34 (n x, tuple x n) t `)` ) := d


namespace tuple

notation `[[` l:(foldr `, ` (h t, cons h t) nil `]]`) := l


variable {α : Type u}


def length {n : ℕ} : tuple α n → ℕ := n


section repr
  variable [has_repr α]

  protected meta def repr_aux : ∀ {n : ℕ}, bool → α ^ n → string
  | 0 _ _ := ""
  | _ tt (cons a b) := repr a ++ repr_aux ff b
  | _ ff (cons a b) := ", " ++ repr a ++ repr_aux ff b

  protected meta def repr : ∀ {n : ℕ}, α ^ n → string
  | 0 _     := "[[]]"
  | _ (cons a b) := "[[" ++ tuple.repr_aux tt (cons a b) ++ "]]"

  meta instance {n : ℕ} : has_repr (α ^ n) := ⟨tuple.repr⟩
end repr


section add
  variable [has_add α]

  protected def add : ∀ {n : ℕ}, α ^ n → α ^ n → α ^ n
  | 0 _ _ := nil
  | _ (cons head₁ tail₁) (cons head₂ tail₂) := cons (head₁ + head₂) (add tail₁ tail₂)

  instance {n : ℕ} : has_add (α ^ n) := ⟨tuple.add⟩
end add


section sub
  variable [has_sub α]

  protected def sub [has_sub α] : ∀ {n : ℕ}, α ^ n → α ^ n → α ^ n
  | 0 _ _ := nil
  | _ (cons head₁ tail₁) (cons head₂ tail₂) := cons (head₁ - head₂) (sub tail₁ tail₂)

  instance {n : ℕ} : has_sub (α ^ n) := ⟨tuple.sub⟩
end sub


section zero
  variable [has_zero α]

  protected def zero : ∀ {n : ℕ}, α ^ n
  | 0 := [[]]
  | (n + 1) := cons 0 zero

  instance {n : ℕ} : has_zero (α ^ n) := ⟨tuple.zero⟩
end zero


section neg
  variable [has_neg α]

  protected def neg : ∀ {n : ℕ}, α ^ n → α ^ n
  | 0 _ := [[]]
  | (n + 1) (cons head tail) := cons (-head) (neg tail)

  instance {n : ℕ} : has_neg (α ^ n) := ⟨tuple.neg⟩
end neg


section functor
  universe v
  variable {β : Type v}

  def map : ∀ {n : ℕ}, (α → β) → α ^ n → β ^ n
  | 0 _ _ := [[]]
  | _ f (cons head tail) := cons (f head) (map f tail)

  protected def map_const {n : ℕ} (x : α) : β ^ n → α ^ n := tuple.map (λ b, x)

  --instance {n : ℕ} : functor (λ γ, tuple γ n) :=
end functor


section scalar_mul
  universe v
  variables {β : Type v} [has_smul β α]
  open has_smul

  protected def smul {n : ℕ} (c : β) : α ^ n → α ^ n := map (smul c)

  instance {n : ℕ} : has_smul β (α ^ n) := ⟨tuple.smul⟩
end scalar_mul


section mem
  protected def mem : ∀ {n : ℕ}, α → α ^ n → Prop
  | 0 _ _ := false
  | (n+1) x (cons head tail) := x = head ∨ mem x tail

  instance {n : ℕ} : has_mem α (α ^ n) := ⟨tuple.mem⟩
end mem


section dot_product
  variables [has_add α] [has_mul α] [has_zero α]

  @[simp]
  def dot_product : ∀ {n : ℕ}, α ^ n → α ^ n → α
  | 0 _ _ := 0
  | _ (cons head₁ tail₁) (cons head₂ tail₂) := (head₁ * head₂) + dot_product tail₁ tail₂

  infix ` ⬝ `:72 := dot_product
end dot_product


section cross_product
  variables [has_add α] [has_sub α] [has_mul α]

  def cross_product : α ^ 3 → α ^ 3 → α ^ 3
  | [[a, b, c]] [[d, e, f]] := [[b * f - c * e, c * d - a * f, a * e - b * d]]

  infixl ` ×ᵥ `:74 := cross_product
end cross_product


section norm_real
  @[simp]
  def norm_sq {n : ℕ} (v : ℝ ^ n) : nnreal := ⟨v ⬝ v, begin
    induction n with n hn generalizing v,
    { cases v, refl, },
    { cases v with _ head tail,
      specialize hn tail,
      dsimp [dot_product],
      have : 0 ≤ head * head,
      { exact mul_self_nonneg head, },
      exact add_nonneg this hn, },
  end⟩

  
  protected noncomputable def norm {n : ℕ} (v : ℝ ^ n) : nnreal := nnreal.sqrt (norm_sq v)
  @[simp]
  noncomputable instance {n : ℕ} : has_norm (ℝ ^ n) := ⟨coe ∘ tuple.norm⟩
  noncomputable instance {n : ℕ} : has_nnnorm (ℝ ^ n) := ⟨tuple.norm⟩
  notation `‖`x`‖²` := norm_sq x
end norm_real


section nth
  def nth : ∀ {n : ℕ} (i : ℕ), α ^ n → i < n → α
  | 0 i _ prf := absurd prf i.not_lt_zero
  | _ 0 (cons head _) prf := head
  | _ (i+1) (cons _ tail) prf := nth i (tail) (nat.le_of_succ_le_succ prf)

  def update_nth : ∀ {n : ℕ} (i : ℕ), α ^ n → α → i < n → α ^ n
  | 0 i _ _ prf := absurd prf i.not_lt_zero
  | n 0 (cons head tail) a prf := cons a tail
  | n (i + 1) (cons head tail) a prf := cons head (update_nth i tail a (nat.le_of_succ_le_succ prf))

  def remove_nth : ∀ {n : ℕ} (i : ℕ), α ^ (n+1) → i ≤ n → α ^ n
  | 0 0 _ prf := nil
  | 0 (i + 1) _ prf := absurd prf (by linarith)
  | (n + 1) 0 (cons _ tail) prf := tail
  | (n + 1) (i + 1) (cons head tail) prf := cons head (remove_nth i tail (by linarith))


  lemma nth_elem : ∀ {n : ℕ} (i : ℕ) (v : α ^ n) (prf : i < n), nth i v prf ∈ v := begin
    intros n i v prf,
    induction n with n ihn generalizing i,
    { exfalso,
      exact i.not_lt_zero prf, },
    { cases v with n head tail,
      simp [has_mem.mem],
      cases i,
      { left,
        refl, },
      { simp [nth],
        right,
        exact ihn tail i (nat.lt_of_succ_lt_succ prf), }, },
  end


  def finth {n : ℕ} (v : α ^ n) (i : fin n) : α := nth i v i.prop
  def finth_elem {n : ℕ} (v : α ^ n) (i : fin n) : {x : α // x ∈ v} := ⟨finth v i, nth_elem i v _⟩

  def update_finth {n : ℕ} (v : α ^ n) (i : fin n) (x : α) : α ^ n := update_nth i v x i.prop

  def remove_finth {n : ℕ} (v : α ^ (n+1)) (i : fin (n+1)) : α ^ n :=
    remove_nth i v (nat.le_of_lt_succ i.prop)

  def from_fin_fn {α : Type*} : ∀ {n : ℕ}, (fin n → α) → α ^ n
  | 0 _ := [[ ]]
  | (n+1) f := cons (f 0) (from_fin_fn (λ (x : fin n), f (x + 1)))
end nth


end tuple
