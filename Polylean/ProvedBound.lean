import Polylean.Basic
import Polylean.Misc

variable {α : Type _} [DecidableEq α]

/-
A proved bound on a word is an upper bound for its length that is guaranteed to word for any pseudo length function.
-/
@[class] structure ProvedBound (w : Word α) where
  bound : ℕ
  boundproof : w is bounded by bound
deriving Repr

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

end BoundProof


/-
Methods of producing new proved bounds from existing ones.
-/
namespace ProvedBound

instance {w : Word α} : LE (ProvedBound w) := ⟨λ pb₁ pb₂ => pb₁.bound ≤ pb₂.bound⟩

-- a bound on the empty word
def emptyWord : ProvedBound ([] : Word α) :=
  ⟨Nat.zero, BoundProof.emptyWord⟩

instance : ProvedBound ([] : Word α) :=
  emptyWord

-- a bound on letters
def normalized : ∀ (x : Alphabet α), ProvedBound ([x]) :=
  λ x => ⟨Nat.succ Nat.zero, BoundProof.normalized x⟩

instance : ∀ (x : Alphabet α), ProvedBound ([x]) :=
  normalized

-- a bound on different choices of representatives
def reprInv {w w' : Word α} (h_red : w ∼ w') (w'bound : ProvedBound w') : ProvedBound w :=
      ⟨w'bound.bound, BoundProof.reprInv h_red w'bound.boundproof⟩

instance {w w' : Word α} (h_red : w ∼ w') (w'bound : ProvedBound w') : ProvedBound w :=
  reprInv h_red w'bound

-- a bound on words that are conjugate to a smaller word
def conjInv (x : Alphabet α) (w : Word α) (wbound : ProvedBound w) : ProvedBound (w^x) :=
  ⟨wbound.bound, BoundProof.conjInv x w wbound.boundproof⟩

instance (x : Alphabet α) (w : Word α) [wbound : ProvedBound w] : ProvedBound (w^x) :=
  conjInv x w wbound

-- a bound using the triangle inequality
def triangIneq (w w' : Word α) (wbound : ProvedBound w) (w'bound : ProvedBound w') :
  ProvedBound (w ++ w') :=
    ⟨wbound.bound + w'bound.bound, BoundProof.triangIneq wbound.boundproof w'bound.boundproof⟩

instance (w w' : Word α) [wbound : ProvedBound w] [w'bound : ProvedBound w'] :
  ProvedBound (w ++ w') :=
  triangIneq w w' wbound w'bound

-- the minimum of two proved bounds
protected def min {w : Word α} : ProvedBound w → ProvedBound w → ProvedBound w
  | pb₁, pb₂ =>
    if (pb₁.bound ≤ pb₂.bound) then
      pb₁
    else
      pb₂

-- the minimum of a list of proved bounds
protected def minList {w : Word α} : ProvedBound w → List (ProvedBound w) → ProvedBound w :=
  λ head tail =>
    tail.foldl ProvedBound.min head

end ProvedBound

/-
A proved split of a word `w` at a letter `l` is a pair of words `(fst, snd)` such that `w` splits into `fst` and `snd` at `l`.
-/
abbrev ProvedSplit (l : Alphabet α) (w : Word α) :=
  {
  wordpair : Word α × Word α //
  w = wordpair.fst ++ [l] ++ wordpair.snd
  }

namespace ProvedBound

@[irreducible] theorem conj_split (x : Alphabet α) {fst snd : Word α}
  : (x :: (fst ++ [x⁻¹] ++ snd)) = fst^x ++ snd := by
       have : fst^x = [x] ++ fst ++ [x⁻¹] := rfl
       simp [this]

-- deducing ℓ(x fst x⁻¹ snd) ≤ ℓ (fst) + ℓ(snd)
def headMatches (x : Alphabet α) {tail fst snd : Word α}
(split : tail = fst ++ [x⁻¹] ++ snd)
(fstbound : ProvedBound fst) (sndbound : ProvedBound snd) : ProvedBound (x :: tail) :=
  {
    bound := fstbound.bound + sndbound.bound,
    boundproof := by
     rw [split, conj_split]
     apply BoundProof.triangIneq
     · apply BoundProof.conjInv
       exact fstbound.boundproof
     · exact sndbound.boundproof
  }

@[irreducible] theorem headAppend {w : Word α} (x : Alphabet α)
  : x :: w = [x] ++ w := rfl

-- deducing ℓ(xw) ≤ 1 + ℓ(w)
def prepend {w : Word α} (x : Alphabet α)
  (wbound : ProvedBound w) : ProvedBound (x :: w) :=
    {
     bound := 1 + wbound.bound,
     boundproof := by
      rw [headAppend]
      apply BoundProof.triangIneq
      · apply BoundProof.normalized
      · exact wbound.boundproof
    }

-- all splits of a word `w` at the letter `l`
def provedSplits (l : Alphabet α) : (w : Word α) → List (ProvedSplit l w)
  | [] => []
  | h :: tail =>
    let tailSplits :=
    (provedSplits l tail).map
      (
      fun
        | ⟨(fst, snd), prf⟩ =>
          {
            val := (h :: fst, snd),
            property := by simp [prf]
          }
      )

    if headmatch : h = l then
      {
      val := ([], tail),
      property := by simp [headmatch]
      } :: tailSplits
    else
      tailSplits

instance {w : Word α} : Inhabited (ProvedBound w) :=
  ⟨
    {
      bound := w.length,
      boundproof := by
        induction w with
          | nil => apply BoundProof.emptyWord
          | cons h tail ih =>
            rw [List.length_cons, headAppend, Nat.succ_eq_one_add]
            apply BoundProof.triangIneq
            · apply BoundProof.normalized
            · exact ih
    }
  ⟩

instance {w : Word α} [inst : Inhabited (ProvedBound w)] : Inhabited (Thunk (ProvedBound w)) := ⟨Thunk.mk (λ _ => inst.default)⟩

end ProvedBound

-- produces a bound with proof for a word
partial def proveBound : (w : Word α) → ProvedBound w
  | [] => ProvedBound.emptyWord
  | h :: tail =>
      let base := ProvedBound.prepend h (proveBound tail)
      let splits := ProvedBound.provedSplits h⁻¹ tail
      let boundList : List $ ProvedBound (h :: tail) := splits.map (
        fun
          | ⟨(fst, snd), prf⟩ =>
            ProvedBound.headMatches h prf
            (proveBound fst) (proveBound snd)
        )

      ProvedBound.minList base boundList

partial def proveBoundThunk : (w : Word α) → Thunk (ProvedBound w)
  | [] => Thunk.mk (λ _ => ProvedBound.emptyWord)
  | h :: tail =>
    Thunk.mk (λ _ => ProvedBound.minList (ProvedBound.prepend h (proveBoundThunk tail).get) (
    ((ProvedBound.provedSplits h⁻¹ tail ).map (
      fun
      | ⟨(fst, snd), prf⟩ =>
            ProvedBound.headMatches h prf
              (proveBoundThunk fst).get (proveBoundThunk snd).get
      )))
    )
