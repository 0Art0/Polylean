/-
Miscellaneous theorems on natural numbers.
-/
namespace Nat

attribute [simp] Nat.le_refl
attribute [simp] Nat.lt_succ_self

protected theorem le_shift_left {a b c : Nat} : a ≤ b → c + a ≤ c + b := by
  intro h
  induction c with
  | zero => simp [h]
  | succ _ ih => simp [Nat.succ_add, Nat.succ_le_succ ih]

protected theorem le_shift_right {a b c : Nat} : a ≤ b → a + c ≤ b + c := by
  intro h
  induction c with
    | zero => simp [h]
    | succ _ ih => simp [Nat.add_succ, Nat.succ_le_succ ih]

protected theorem succ_eq_one_add : ∀ m : Nat, Nat.succ m = (Nat.succ Nat.zero) + m :=
  λ m => by simp [Nat.succ_add]

protected theorem lt_add_right : ∀ m n : Nat, m < m + (Nat.succ n) := by
  intro m n
  induction n with
  | zero =>
    rw [Nat.add_succ, Nat.add_zero]
    apply Nat.lt_succ_self
  | succ n ih =>
    rw [Nat.add_succ]
    apply Nat.lt_trans ih (Nat.lt_succ_self _)

protected theorem lt_add_left : ∀ m n : Nat, m < Nat.succ n + m := by
  intro m n
  induction n with
    | zero =>
      rw [Nat.succ_add, Nat.zero_add]
      apply Nat.lt_succ_self
    | succ n ih =>
      rw [Nat.succ_add]
      apply Nat.lt_trans ih (Nat.lt_succ_self _)

end Nat

class TotalOrder (α : Type _) [LE α] [DecidableRel (@LE.le α _)] where
  (reflLE : ∀ a : α, a ≤ a)
--  (antisymmLE : ∀ {a b : α}, a ≤ b → b ≤ a → a = b) -- this is not strictly necessary for the proofs
  (transLE : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)
  (totalLE : ∀ a b : α, a ≤ b ∨ b ≤ a)

open TotalOrder

variable {α : Type _} [LE α] [DecidableRel (@LE.le α _)] [∀ a b : α, Decidable (a = b)] [TotalOrder α]
variable {β : Type _} [LE β] [DecidableRel (@LE.le β _)] [∀ a b : β, Decidable (a = b)] [TotalOrder β]

@[simp] theorem minFst (a b : α) : min a b ≤ a :=
  if h:a ≤ b then by
    simp [min, h, reflLE]
  else by
    simp [min, h]
    match (totalLE a b) with
      | Or.inl _ => apply False.elim; apply h; assumption
      | Or.inr _ => assumption

@[simp] theorem minSnd (a b : α) : min a b ≤ b :=
  if h:a ≤ b then by
    simp [min, h]
  else by
    simp [min, h, reflLE]

namespace List

theorem foldMinBase (b : α) : (as : List α) → foldl min b as ≤ b
  | [] => reflLE _
  | h :: tail => transLE (foldMinBase (min b h) tail) (minFst _ _)

def mem (a : α) : List α → Bool
  | [] => false
  | h :: tail => if (h = a) then true else mem a tail

infix:100 " ∈ " => mem

theorem foldMinMem (a b : α) (as : List α) (amember : a ∈ as) : foldl min b as ≤ a :=
  match as with
    | [] => by
      apply False.elim
      simp [mem] at amember
    | h :: tail =>
      if headmatch:(h = a) then by
        simp [*, headmatch, foldl, mem] at *
        apply transLE
        exact foldMinBase _ tail
        simp
      else by
        simp [*, headmatch, foldl, mem] at *
        exact foldMinMem a _ tail amember

theorem mapMem (f : α → β) {a : α} {l : List α} (amember : a ∈ l) :
  (f a) ∈ (map f l) := by
  induction l with
    | nil =>
      apply False.elim
      simp [mem] at amember
    | cons h t ih =>
      simp [map, mem] at *
      exact if headmatch:h = a then by
        simp [congrArg f headmatch]
      else by
        simp [headmatch] at amember
        simp [amember] at ih
        exact if fheadmatch:(f h = f a) then by
          simp [fheadmatch]
        else by
          simp [fheadmatch, ih]

theorem memAppendLeft {a : α} {l₁ l₂ : List α} :
  a ∈ l₂ → a ∈ (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    simp
    exact id
  | cons h t ih =>
    simp [mem]
    exact if headmatch:(h = a) then by
      simp [headmatch]
    else by
      simp [headmatch]
      exact ih

theorem memAppendRight {a : α} {l₁ l₂ : List α} :
  a ∈ l₁ → a ∈ (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    intro hyp
    simp [mem] at hyp
  | cons h t ih =>
    simp [mem]
    exact if headmatch:(h = a) then by
      simp [headmatch]
    else by
      simp [headmatch]
      exact ih

@[simp] theorem appendLength {α : Type _} {l₁ l₂ : List α} :
  List.length (List.append l₁ l₂) = l₁.length + l₂.length := by
  show (List.length (l₁ ++ l₂)) = l₁.length + l₂.length
  simp

end List

instance : TotalOrder Nat :=
  {
    reflLE := Nat.le_refl,
--    antisymmLE := Nat.le_antisymm,
    transLE := Nat.le_trans,
    totalLE := Nat.le_total
  }
