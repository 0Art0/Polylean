import Polylean.Basic
import Polylean.Misc

variable {α : Type _} [DecidableEq α]

@[class] structure ProvedBound (w : Word α) where
  bound : ℕ
  boundproof : w is bounded by bound


namespace BoundProof

attribute [simp] Nat.le_refl


theorem emptyWord : ([] : Word α) is bounded by Nat.zero := by
  repeat intro ; intro pseudolength
  simp [pseudolength.emptyWord]

theorem normalized : ∀ x : Alphabet α, [x] is bounded by (Nat.succ Nat.zero) := by
  intro ; intro ; intro pseudolength
  simp [pseudolength.normalized]

theorem reprInv
  {w w' : Word α} (h_red : w ∼ w') {n : ℕ}
  (w'bound : w' is bounded by n)
  : w is bounded by n := by
    intro ; intro pseudolength
    simp [pseudolength.reprInv h_red, w'bound]

theorem conjInv
  (x : Alphabet α) (w : Word α) {n : ℕ}
  (wbound : w is bounded by n) :
  (w^x) is bounded by n := by
  intro ; intro pseudolength
  simp [pseudolength.conjInv, wbound]


theorem triangIneq
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
      (pseudolength.triangIneq w w')
      (Nat.le_trans fstbound sndbound)

end BoundProof


namespace ProvedBound

instance {w : Word α} : LE (ProvedBound w) := ⟨λ pb₁ pb₂ => pb₁.bound ≤ pb₂.bound⟩

def emptyWord : ProvedBound ([] : Word α) :=
  ⟨Nat.zero, BoundProof.emptyWord⟩

instance : ProvedBound ([] : Word α) :=
  emptyWord

def normalized : ∀ (x : Alphabet α), ProvedBound ([x]) :=
  λ x => ⟨Nat.succ Nat.zero, BoundProof.normalized x⟩

instance : ∀ (x : Alphabet α), ProvedBound ([x]) :=
  normalized

def reprInv {w w' : Word α} (h_red : w ∼ w') (w'bound : ProvedBound w') : ProvedBound w :=
      ⟨w'bound.bound, BoundProof.reprInv h_red w'bound.boundproof⟩

instance {w w' : Word α} (h_red : w ∼ w') (w'bound : ProvedBound w') : ProvedBound w :=
  reprInv h_red w'bound

def conjInv (x : Alphabet α) (w : Word α) (wbound : ProvedBound w) : ProvedBound (w^x) :=
  ⟨wbound.bound, BoundProof.conjInv x w wbound.boundproof⟩

instance (x : Alphabet α) (w : Word α) [wbound : ProvedBound w] : ProvedBound (w^x) :=
  conjInv x w wbound

def triangIneq (w w' : Word α) (wbound : ProvedBound w) (w'bound : ProvedBound w') :
  ProvedBound (w ++ w') :=
    ⟨wbound.bound + w'bound.bound, BoundProof.triangIneq wbound.boundproof w'bound.boundproof⟩

instance (w w' : Word α) [wbound : ProvedBound w] [w'bound : ProvedBound w'] :
  ProvedBound (w ++ w') :=
  triangIneq w w' wbound w'bound

end ProvedBound
