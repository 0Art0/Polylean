import Polylean.Basic

variable {α : Type _} [DecidableEq α]

/-
Miscellaneous theorems on natural numbers.
-/
namespace Nat

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


/-
Bounds on word lengths that can be deduced directly from the properties of a pseudo length function.
These are marked irreducible since they convey important facts about pseudolength functions and it is not desirable to unfold these further in proof trees.
-/

namespace BoundProof

attribute [simp] Nat.le_refl


@[irreducible] theorem emptyWord : ([] : Word α) is bounded by Nat.zero := by
  intro ; intro
  simp [PseudoLengthFunction.emptyWord]

@[irreducible] theorem normalized : ∀ x : Alphabet α, [x] is bounded by (Nat.succ Nat.zero) := by
  intro ; intro ; intro
  simp [PseudoLengthFunction.normalized]

@[irreducible] theorem reprInv
  {w w' : Word α} (h_red : w ∼ w') {n : ℕ}
  (w'bound : w' is bounded by n)
  : w is bounded by n := by
    intro ; intro
    simp [PseudoLengthFunction.reprInv h_red, w'bound]

@[irreducible] theorem conjInv
  (x : Alphabet α) (w : Word α) {n : ℕ}
  (wbound : w is bounded by n) :
  (w^x) is bounded by n := by
  intro ; intro
  simp [PseudoLengthFunction.conjInv, wbound]

@[irreducible] theorem triangIneq
  {w w' : Word α} {n n' : ℕ}
  (wbound : w is bounded by n)
  (w'bound : w' is bounded by n') :
  (w ++ w') is bounded by (n + n') := by
    intro ℓ
    intro pseudolength
    have fstbound : ℓ w + ℓ w' ≤ n + ℓ w' :=
      Nat.le_shift_right (@wbound ℓ pseudolength)
    have sndbound : n + ℓ w' ≤ n + n' :=
      Nat.le_shift_left (@w'bound ℓ pseudolength)
    exact Nat.le_trans
      (PseudoLengthFunction.triangIneq w w')
      (Nat.le_trans fstbound sndbound)

@[irreducible] theorem headAppend {w : Word α} (x : Alphabet α)
  : x :: w = [x] ++ w := rfl

@[irreducible] theorem conjSplit (x : Alphabet α) {fst snd : Word α}
  : (x :: (fst ++ [x⁻¹] ++ snd)) = fst^x ++ snd := by
       have : fst^x = [x] ++ fst ++ [x⁻¹] := rfl
       simp [this]

theorem prepend {w : Word α} {n : ℕ} (x : Alphabet α) (wbound : w is bounded by n)
: (x::w) is bounded by (Nat.succ (Nat.zero) + n) := by
  rw [headAppend]
  apply BoundProof.triangIneq
  · apply BoundProof.normalized
  · exact wbound

end BoundProof


/-
A proved split of a word `w` at a letter `l` is a pair of words `(fst, snd)` such that `w` splits into `fst` and `snd` at `l`.
-/
abbrev ProvedSplit (l : Alphabet α) (w : Word α) :=
  {
  wordpair : Word α × Word α //
  w = wordpair.fst ++ [l] ++ wordpair.snd
  }

namespace ProvedSplit

/-
Produces all splits of a word `w` at the letter `l`.
-/
def provedSplits (l : Alphabet α) : (w : Word α) → List (ProvedSplit l w)
  | [] => []
  | h :: tail =>
    let tailSplits :=
    (provedSplits l tail).map
      (fun
        | ⟨(fst, snd), prf⟩ =>
          { val := (h :: fst, snd), property := by simp [prf] }
      )

    if headmatch : h = l then
      { val := ([], tail), property := by simp [headmatch] } :: tailSplits
    else
      tailSplits

-- A split of the empty word cannot exist.
@[simp] theorem splitEmpty {l : Alphabet α} : (ps : ProvedSplit l []) → False := by
  intro ⟨(fst, snd), prf⟩
  simp at prf
  have emptyLenZero : List.length ([] : Word α) = Nat.zero := rfl
  have splitLenPos : 0 < List.length (fst ++ [l] ++ snd) := by
    simp
    rw [Nat.add_assoc, Nat.add_comm, Nat.add_assoc, Nat.succ_add]
    apply Nat.zero_lt_succ
  have emptyLenPos : 0 < List.length ([] : Word α) := by
    rw [prf]
    exact splitLenPos
  have zeroPos : Nat.zero < Nat.zero := emptyLenPos
  apply Nat.lt_irrefl
  exact zeroPos

-- A split is always smaller than the original word.
@[simp] theorem splitBound {l : Alphabet α} : {w : Word α} → (ps : ProvedSplit l w) →
(ps.val.fst.length + ps.val.snd.length < w.length) := by
  intro w
  induction w with
    | nil =>
    intro ps
    apply False.elim
    apply splitEmpty ps
    | cons h w' =>
    intro ⟨(fst, snd), prf⟩
    simp [prf]
    rw [Nat.add_comm _ (Nat.succ 0), Nat.add_assoc, Nat.succ_add, Nat.zero_add]
    apply Nat.lt_succ_self

-- The first part of the split is smaller than the entire word.
@[simp] theorem fstSplitBound {l : Alphabet α} : (w : Word α) →
(ps : ProvedSplit l w) → (ps.val.fst.length < w.length) := by
  intro w; intro ⟨(fst, snd), prf⟩
  simp [prf]
  rw [Nat.add_assoc, Nat.succ_add]
  apply Nat.lt_add_right

-- The second part of the split is smaller than the entire word.
@[simp] theorem sndSplitBound {l : Alphabet α} : (w : Word α) →
(ps : ProvedSplit l w) → (ps.val.snd.length < w.length) := by
  intro w ; intro ⟨(fst, snd), prf⟩
  simp [prf]
  rw [Nat.add_succ]
  apply Nat.lt_add_left

-- A bound on the first part of a split of a "cons" word, useful for showing termination.
@[simp] theorem fstConsSplit {h : Alphabet α} {first second tail : Word α}
  (prf : tail = (first, second).fst ++ [h⁻¹] ++ (first, second).snd)
  : List.length first < List.length (h :: tail) := by
   simp [prf]
   rw [Nat.add_assoc, Nat.succ_add, Nat.zero_add]
   apply Nat.lt_trans (Nat.lt_add_right _ _) (Nat.lt_succ_self _)

-- A bound on the second part of a split of a "cons" word, useful for showing termination.
@[simp] theorem sndConsSplit {h : Alphabet α} {first second tail : Word α}
  (prf : tail = (first, second).fst ++ [h⁻¹] ++ (first, second).snd)
  : List.length second < List.length (h :: tail) := by
   simp [prf]
   rw [Nat.add_succ, Nat.add_zero]
   apply Nat.lt_trans (Nat.lt_add_left _ _) (Nat.lt_succ_self _)

end ProvedSplit

/-decreasing_by {
  -- source: https://github.com/leanprover/lean4/blob/de197675946ff37b1ae03c6bebe4ca58bb089fa9/tests/lean/run/wfrecUnary.lean
  simp [measure, id, invImage, InvImage, Nat.lt_wfRel, WellFoundedRelation.rel, sizeOf] <;>

  simp [Nat.lt_succ_self] <;>

  (first
    | apply (ProvedSplit.fstConsSplit prf)
    | apply (ProvedSplit.sndConsSplit prf)
    | assumption
  )
}
-/
