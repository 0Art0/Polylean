import Polylean.BoundsAndSplits

/-
A non-crossing match is inductively defined to be one of
- the empty word
- a letter of the alphabet attached to the front of a non-crossing match
- a conjugate of a non-crossing match appended to the front of a non-crossing match

Example:

  .---------.
    .--.
α β α α⁻¹ β β⁻¹  ↦   α :: (matching β (matching α [] (β :: [])) [])
-/
inductive MatchWord (α : Type _) [DecidableEq α]
  | nil : MatchWord α
  | cons : Alphabet α → MatchWord α → MatchWord α
  | matching : Alphabet α → MatchWord α → MatchWord α → MatchWord α
  deriving Repr --, DecidableEq


namespace MatchWord

variable {α : Type _} [DecidableEq α]

/-
The number of un-matched letters in a matching.
-/
@[reducible, simp] def unmatchedCount : MatchWord α → ℕ
  | nil => 0
  | cons l w => 1 + unmatchedCount w
  | matching _ w w' => unmatchedCount w + unmatchedCount w'

/-
Converts a non-crossing match word to the corresponding usual word.
-/
@[reducible, simp] def toWord : MatchWord α → Word α
  | nil => []
  | cons l w => l :: (toWord w)
  | matching l w w' => (toWord w)^l ++ (toWord w')


/-
Defining a "matching" corresponding to a word.
-/
@[reducible] def isMatching (m : MatchWord α) (w : Word α) := m.toWord = w

infix:100 " is a matching of " => MatchWord.isMatching

abbrev Matching (w : Word α) := {m : MatchWord α // m is a matching of w}


/-
A total order on the matchings of a word in terms of the "energy" (the number of unmatched letters).
-/
instance {w : Word α} : LE (Matching w) :=
 ⟨λ m m' => unmatchedCount m.val ≤ unmatchedCount m'.val⟩

instance {w : Word α} : ∀ m m' : Matching w, Decidable (m ≤ m') := by
  intro ; intro
  simp [LE.le]; exact inferInstance


/-
The empty matching cannot correspond to a non-empty word.
-/
theorem consNeEmptyMatch (l : Alphabet α) (w : Word α) : ¬(nil is a matching of (l :: w)) := by
  intro h_match ; simp [isMatching] at h_match

/-
If `m` is a matching of a word `w`, the length of `w` under any pseudo-length function is
bounded by the "energy" of `m` (the number of unmatched letters).

This theorem is crucial for proving the maximality of the Watson-Crick length.
-/
theorem unmatchedCountBound (m : MatchWord α)
  : (m.toWord is bounded by m.unmatchedCount) := by
  induction m with
    | nil =>
      intro ; intro
      simp [PseudoLengthFunction.emptyWord]
    | cons =>
      intro ; intro
      apply BoundProof.prepend
      assumption
    | matching =>
      intro ; intro
      apply BoundProof.triangIneq
      · apply BoundProof.conjInv ; assumption
      · assumption

/-
Takes a word `w` as input and returns a maximal matching
(a matching with the lowest number of unmatched letters) of the word.
-/
def maxMatch : (w : Word α) → Matching w
  | List.nil => ⟨MatchWord.nil, rfl⟩  -- the trivial case of the empty word
  | List.cons l w' =>

    -- the case where the first letter is unmatched
    let base : Matching (l :: w') :=
      let ⟨w'Match, w'Prf⟩ := maxMatch w'
      ⟨MatchWord.cons l w'Match, by simp [w'Prf]⟩

    -- the case where the first letter is matched
    let splits : List (Matching (l :: w')) :=
    (ProvedSplit.provedSplits l⁻¹ w').map (λ ⟨⟨fst, snd⟩, prf⟩ =>
          -- proof that the length of the word decreases, required for showing termination
          have : fst.length < (l :: w').length := ProvedSplit.fstConsSplit prf
          let ⟨fstMatch, fstPrf⟩ := maxMatch fst -- a maximal matching of the first part of the split

          -- proof that the length of the word decreases, required for showing termination
          have : snd.length < (l :: w').length := ProvedSplit.sndConsSplit prf
          let ⟨sndMatch, sndPrf⟩ := maxMatch snd -- a maximal matching of the second part of the split

          {
            -- creates a matching involving the first letter of the word
            val := (MatchWord.matching l fstMatch sndMatch),
            property := by
             rw [prf, BoundProof.conjSplit, ← fstPrf, ← sndPrf]
          }
      )

    -- the best matching of the ones above, i.e., the one with the least unmatched letters ("energy")
    splits.foldl min base

termination_by _ w => List.length w -- this function terminates since the length of the input list decreases on each recursive call

namespace MatchWord
