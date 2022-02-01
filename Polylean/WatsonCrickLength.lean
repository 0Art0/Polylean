import Polylean.BoundsAndSplits

/-
A non-crossing match is inductively defined to be one of
- the empty word
- a letter of the alphabet attached to the front of a non-crossing match
- a conjugate of a non-crossing match appended to the front of a non-crossing match
-/
inductive MatchWord {α : Type _} [DecidableEq α] : Word α → Type _
  | nil : MatchWord []
  | cons {w' : Word α} : (l : Alphabet α) → MatchWord w' → MatchWord (l :: w')
  | matching {fst snd : Word α} : (l : Alphabet α) → MatchWord fst → MatchWord snd → MatchWord (fst^l ++ snd)
  deriving Repr


namespace MatchWord

variable {α : Type _} [DecidableEq α]

/-
The number of un-matched letters in a matching.
-/
@[simp] def unmatchedCount : {w : Word α} → (MatchWord w) → ℕ
  | _, nil              => Nat.zero
  | _, cons _ m'        => Nat.succ (unmatchedCount m')
  | _, matching _ m₁ m₂ => unmatchedCount m₁ + unmatchedCount m₂

/-
A total order on the matchings of a word in terms of the "energy" (the number of unmatched letters).
-/
instance {w : Word α} : LE (MatchWord w) :=
 ⟨λ m m' => unmatchedCount m ≤ unmatchedCount m'⟩

instance {w : Word α} : ∀ m m' : MatchWord w, Decidable (m ≤ m') := by
  intro ; intro ; simp [LE.le] ; exact inferInstance

instance {w : Word α} : TotalOrder (MatchWord w) := {
  reflLE := by { intro a; simp [LE.le] ; cases a <;> simp },
  -- antisymmetry does not hold for `MatchWord`
  transLE := by {intro a b c; simp [LE.le]; intro hab hbc; exact Nat.le_trans hab hbc}
  totalLE := by {intro a b; simp [LE.le]; apply Nat.le_total}
}

/-
Takes a word `w` as input and returns a maximal matching
(a matching with the lowest number of unmatched letters) of the word.
-/
def maxMatch : (w : Word α) → MatchWord w
  | List.nil => MatchWord.nil
  | List.cons l w' =>
    let base := MatchWord.cons l (maxMatch w')
    let splits := (Word.conjugateSplits (l :: w')).map
      ( fun
          | ConjugateSplit.split l fst snd =>
            matching l (maxMatch fst) (maxMatch snd) )
    List.foldl min base splits
termination_by _ w => List.length w
decreasing_by {
  -- source: https://github.com/leanprover/lean4/blob/de197675946ff37b1ae03c6bebe4ca58bb089fa9/tests/lean/run/wfrecUnary.lean
  simp [measure, id, invImage, InvImage, Nat.lt_wfRel, WellFoundedRelation.rel, sizeOf] <;>
  first
    | rw [← Nat.add_succ, Nat.add_assoc]; apply Nat.lt_add_right
    | rw [← Nat.succ_add]; apply Nat.lt_add_left
}

/-
The definition of Watson-Crick length, as the number of unmatched letters in a minimal matching of the word.
-/
def WatsonCrickLength : FreeGroupLength α :=
  λ w => unmatchedCount $ maxMatch w


/-
If `m` is a matching of a word `w`, the length of `w` under any pseudo-length function is
bounded by the "energy" of `m` (the number of unmatched letters).

This theorem is crucial for proving the maximality of the Watson-Crick length.
-/
theorem unmatchedCountBound {w : Word α} (m : MatchWord w) :
  (w is bounded by m.unmatchedCount) := by
  induction m with
    | nil =>
      intro ; intro
      simp [PseudoLengthFunction.emptyWord]
    | cons =>
      intro ; intro
      simp ; rw [Nat.succ_eq_one_add]
      apply BoundProof.prepend ; assumption
    | matching =>
      intro ; intro
      apply BoundProof.triangIneq
      · apply BoundProof.conjInv ; assumption
      · assumption

/-
A proof that the output of `maxMatch` has the least number of unmatched letters among all possible matchings of a word.
-/
theorem maximalMatching {w : Word α} : (m : MatchWord w) → (maxMatch w) ≤ m
  | nil => sorry
  | cons l m' => sorry
  | matching l m₁ m₂ => sorry

end MatchWord
