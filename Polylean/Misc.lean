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

end Nat
