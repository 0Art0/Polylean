import Std
import Polylean.Basic

open Std


/-
An element of type `ConjWord α` is a representation of a word as
  a finite product      ∏ yᵢ xᵢ yᵢ⁻¹
, where (xᵢ yᵢ : Alphabet α)
-/
abbrev ConjWord (α : Type _) [DecidableEq α]:= AssocList (Alphabet α) (Alphabet α)

variable {α : Type _} [DecidableEq α]

-- converting a conjugate word to a regular word
def ConjWord.toWord : ConjWord α → Word α
  | AssocList.nil => []
  | AssocList.cons x y tail => [y, x, y⁻¹] ++ (toWord tail)

-- coercion between the types
instance : Coe (ConjWord α) (Word α) := ⟨ConjWord.toWord⟩
