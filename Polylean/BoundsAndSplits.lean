import Polylean.Basic
import Polylean.Misc

variable {α : Type _} [DecidableEq α]


/-
Bounds on word lengths that can be deduced directly from the properties of a pseudo length function.
These are marked irreducible since they convey important facts about pseudolength functions and it is not desirable to unfold these further in proof trees.
-/

namespace BoundProof

@[irreducible] theorem emptyWord : ([] : Word α) is bounded by Nat.zero := by
  intro ; intro
  simp [PseudoLengthFunction.emptyWord]

@[irreducible] theorem normalized : ∀ x : Alphabet α, [x] is bounded by (Nat.succ Nat.zero) := by
  intro ; intro ; intro
  simp [PseudoLengthFunction.normalized]

@[irreducible] theorem reprInv
  {w w' : Word α} (h_red : w ∼ w') {n : ℕ} (w'bound : w' is bounded by n)
  : w is bounded by n := by
    intro ; intro
    simp [PseudoLengthFunction.reprInv h_red, w'bound]

@[irreducible] theorem conjInv
  (x : Alphabet α) (w : Word α) {n : ℕ} (wbound : w is bounded by n) :
  (w^x) is bounded by n := by
  intro ; intro
  simp [PseudoLengthFunction.conjInv, wbound]

@[irreducible] theorem triangIneq
  {w w' : Word α} {n n' : ℕ} (wbound : w is bounded by n) (w'bound : w' is bounded by n')
  : (w ++ w') is bounded by (n + n') := by
    intro ℓ
    intro pseudolength
    have fstbound : ℓ w + ℓ w' ≤ n + ℓ w' := Nat.le_shift_right (@wbound ℓ pseudolength)
    have sndbound : n + ℓ w' ≤ n + n' := Nat.le_shift_left (@w'bound ℓ pseudolength)
    exact Nat.le_trans
      (PseudoLengthFunction.triangIneq w w')
      (Nat.le_trans fstbound sndbound)

theorem headAppend {w : Word α} (x : Alphabet α)
  : x :: w = [x] ++ w := rfl

theorem conj {x : Alphabet α} {w : Word α} : w^x = [x] ++ w ++ [x⁻¹] := rfl

@[simp] theorem conjSplit (x : Alphabet α) {fst snd : Word α}
  : (x :: (fst ++ [x⁻¹] ++ snd)) = fst^x ++ snd := by simp [conj]

theorem prepend {w : Word α} {n : ℕ} (x : Alphabet α) (wbound : w is bounded by n)
: (x :: w) is bounded by (Nat.succ (Nat.zero) + n) := by
  rw [headAppend]
  apply BoundProof.triangIneq
  · apply BoundProof.normalized
  · exact wbound

end BoundProof

/-
An inductive definition of the split of a list at a letter `a`.
-/
inductive ListSplit {α : Type _} [DecidableEq α] (a : α) : List α → Type _
  | head : (t : List α) → ListSplit a (a :: t)
  | cons {t : List α} : (h : α) → ListSplit a t → ListSplit a (h :: t)

/-
All possible splits of a list at a letter `a`.

The suggestion of using `▹` for the re-write is due to Sebastian Ullrich.
-/
def List.splits {α : Type _} [DecidableEq α] (a : α) : (l : List α) → List (ListSplit a l)
  | []     => []
  | h :: t =>  (if headmatch:h = a then headmatch ▸ [ListSplit.head t] else []) ++
               ( (splits a t).map (ListSplit.cons h) )

instance ListSplit.decideSplit : (l : List α) → (a : α) → DecidableEq (ListSplit a l)
  | [] => by
    intro ; intro ls₁
    cases ls₁ <;> simp
  | h :: t => by
    intro; intro ls₁ ls₂
    cases ls₁ <;> cases ls₂ <;> simp <;> (try (apply inferInstance));
    exact (decideSplit t _ _ _)

/-
A proof that every possible split of a list is contained in the output of `List.splits`.
-/
theorem ListSplit.allSplits {l : List α} {a : α} : ∀ ls : ListSplit a l, ls ∈ (l.splits a) := by
  match l with
    | [] =>
      intro ls
      cases ls <;> simp
    | h :: t =>
      intro ls
      cases ls
      · simp [List.mem, List.splits]
      · simp [List.mem, List.splits]
        apply List.memAppendLeft
        apply List.mapMem
        exact allSplits _

/-
Converts a `ListSplit` to the corresponding pair of lists created by the split.
-/
def ListSplit.toList {a : α} {l : List α}
  : ListSplit a l → { listpair : List α × List α // l = listpair.fst ++ [a] ++ listpair.snd }
  | head t => ⟨([], t), by simp⟩
  | cons h ls =>
    match ls.toList with
      | ⟨(lsfst, lssnd), lsprf⟩ => ⟨(h :: lsfst, lssnd), by simp [lsprf]⟩

/-
A inductive definition of a split of a word into two words such that a conjugate of the first appended to the second gives the full word.
-/
inductive ConjugateSplit : Word α → Type _
  | split : (l : Alphabet α) → (fstword : Word α) → (sndword : Word α) → ConjugateSplit (fstword^l ++ sndword)
  deriving Repr

def ListSplit.toConjugate {l : Alphabet α} {w : Word α} : ListSplit l⁻¹ w → ConjugateSplit (l :: w)
  | ls =>
    match ls.toList with
      | ⟨(lsfst, lssnd), lsprf⟩ =>
      let splitprf : l :: w = lsfst^l ++ lssnd := by simp [lsprf]
      splitprf ▸ (ConjugateSplit.split l lsfst lssnd)

def ConjugateSplit.toListSplit {l : Alphabet α} {w : Word α} : ConjugateSplit (l :: w) → ListSplit l⁻¹ w
  | split _ fstword sndword =>
    match fstword with
      | [] => ListSplit.head _
      | h :: t => ListSplit.cons _ (toListSplit (ConjugateSplit.split _ t sndword))


theorem ListSplit.conjsplitid {l : Alphabet α} {w : Word α} (ls : ListSplit l⁻¹ w) : ls.toConjugate.toListSplit = ls := sorry
theorem ConjugateSplit.conjsplitid {l : Alphabet α} {w : Word α} (cs : ConjugateSplit (l :: w)) : cs = cs.toListSplit.toConjugate := by
  match cs with
    | split _ fstword sndword =>
      induction fstword with
        | nil =>
          simp [ConjugateSplit.toListSplit]
          simp [ListSplit.toConjugate]
          match (ListSplit.head (List.append [] sndword)).toList with
            | ⟨(lsfst, lssnd), lsprf⟩ =>
              sorry
        | cons h t ih => sorry

/-
All conjugate splits of a word.
-/
def Word.conjugateSplits : (w : Word α) → List (ConjugateSplit w)
  | [] => []
  | l :: w' => (w'.splits l⁻¹).map (ListSplit.toConjugate)

instance {w : Word α} : DecidableEq (ConjugateSplit w) := by
  intro cs₁ cs₂; sorry

/-
A proof that every possible split is contained in the output of `conjugateSplits`
-/
theorem ConjugateSplit.allSplits {w : Word α} : ∀ cs : ConjugateSplit w, cs ∈ w.conjugateSplits := by
  match w with
    | [] =>
      intro cs
      cases cs
    | l :: w' =>
      intro cs
      simp [Word.conjugateSplits, List.mem]
      rw [ConjugateSplit.conjsplitid cs]
      apply List.mapMem
      apply ListSplit.allSplits

/-
@[simp] def ConjugateSplit.fstword {w : Word α} : ConjugateSplit w → Word α
  | split _ fstword _ => fstword

@[simp] def ConjugateSplit.sndword {w : Word α} : ConjugateSplit w → Word α
  | split _ _ sndword => sndword

@[simp] theorem ConjugateSplit.fstwordLen {w : Word α} : (cs : ConjugateSplit w) → cs.fstword.length < w.length
  | split l fst snd => by
    simp; rw [BoundProof.conj]; simp
    have : Nat.succ (fst.length + Nat.succ Nat.zero) = fst.length + (Nat.succ (Nat.succ Nat.zero)) := by simp
    rw [this, Nat.add_assoc, Nat.succ_add]
    apply Nat.lt_add_right

@[simp] theorem ConjugateSplit.sndwordLen {w : Word α} : (cs : ConjugateSplit w) → cs.sndword.length < w.length
  | split l fst snd => by
    simp; apply Nat.lt_add_left
-/
