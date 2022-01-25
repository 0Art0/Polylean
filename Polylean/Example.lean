import Polylean.ProvedBound

inductive FreeGroup2
  | a
  | b
  deriving DecidableEq, Repr


open FreeGroup2

open Alphabet

def testBound : ProvedBound ([pos a]) :=
  proveBound [pos a]

#eval testBound.bound -- 1
#reduce testBound.boundproof -- does not reduce

#eval (proveBoundThunk [pos a, pos b]).get.bound -- 2
