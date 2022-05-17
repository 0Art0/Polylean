import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Defs

/-
Free module over a ring `R` which may be assumed to be commutative, will eventually be $Z/2`$. 

Outline:

* Define formal sums; coordinates of formal sums.
* Define the relation corresponding to equal coordinates and prove that it is an equivalence relation.
* Define the free module as a quotient of the above relation, via setoids.
* Introduce an inductive type giving the elementary relations, i.e., single moves.
* Define an auxiliary quotient by this relation (which is not an equivalence relation); and an auxiliary equivalence relation corresponding to this quotient.
* Show that coordsicients are equal if and only if formal sums satisfy the auxiliary relation.
* Deduce that the auxiliary relation is the original relation (may not need to make this explicit).
* Deduce a universal property and construct the sum and product operations : these depend on each other, so one may need a weaker version of the universal property first. Alternatively, the operations may be constructed as special cases of the universal property.
-/

/-!
Defining the free module. The basis set is `X` and the ring is `R`.
-/
variable (R: Type)[Ring R][DecidableEq R]
variable (X: Type)[DecidableEq X]

abbrev FormalSum := List (R × X)

def monomCoeff (x₀ : X) (nx : R × X) : R := 
  match  (nx.2 == x₀) with 
  | true => nx.1
  | false => 0

#check monomCoeff

theorem monom_coords_hom (x₀ x : X)(a b : R) :
    monomCoeff R X x₀ (a + b, x) = 
      monomCoeff R X x₀ (a, x) + monomCoeff R X x₀ (b, x) := by
    repeat (rw [monomCoeff])
    cases x==x₀ <;> simp 

theorem monom_coords_mul (x₀ : X)(a b : R) :
    monomCoeff R X x₀ (a * b, x) = 
      a * monomCoeff R X x₀ (b, x) := by
    repeat (rw [monomCoeff])
    cases x==x₀ <;> simp

theorem monom_coords_at_zero (x₀ x : X) : monomCoeff R X x₀ (0, x) = 0 :=
    by 
      rw [monomCoeff]
      cases x==x₀ <;> rfl

def FormalSum.coords{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]: FormalSum R X → X → R
| [], _ =>  0
| h :: t, x₀ => monomCoeff R X x₀ h + coords t x₀

def FormalSum.support{R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]
        (s: FormalSum R X) : List X :=
              s.map <| fun (_, x) => x

open FormalSum



theorem nonzero_coord_in_support{R: Type}[Ring R][DecidableEq R]
    {X: Type}[DecidableEq X](s: FormalSum R X) :
        ∀ x: X, 0 ≠  s.coords x  → x ∈ s.support  := 
          match s with 
          | [] => fun x hyp => 
            by
              have d : coords [] x = (0 : R) := by rfl
              rw [d] at hyp
              contradiction
          | h :: t => 
            by
            intro x hyp
            let (a₀, x₀) := h
            have d : support ((a₀, x₀) :: t) =  
              x₀ :: (support t) := by rfl
            rw [d]
            match p:x₀ == x with
            | true => 
                have eqn : x₀ = x := of_decide_eq_true p
                rw [eqn]
                apply List.mem_of_elem_eq_true
                simp [List.elem]
            | false => 
                rw [coords, monomCoeff, p, zero_add] at hyp
                let step := nonzero_coord_in_support t x hyp
                apply List.mem_of_elem_eq_true
                simp [List.elem]
                have p' : (x == x₀) = false := 
                      by
                        have eqn := of_decide_eq_false p 
                        have eqn' : ¬ (x = x₀) := by
                            intro contra
                            let contra' := Eq.symm contra
                            contradiction
                        exact decide_eq_false eqn'                                      
                rw [p']
                apply List.elem_eq_true_of_mem
                exact step

def equalOnSupport{R: Type}[DecidableEq R]{X: Type}[DecidableEq X](l: List X)(f g : X → R) : Prop :=
  match l with
  | [] => true
  | h :: t =>
    (f h = g h) ∧ (equalOnSupport t f g)

theorem equal_on_support_of_equal{R: Type}[DecidableEq R]{X: Type}[DecidableEq X]
  (l: List X)(f g : X → R):
    f = g → equalOnSupport l f g := by
    intro hyp
    induction l with
    | nil =>
      rw [equalOnSupport]  
    | cons h t step => 
      rw [equalOnSupport]
      apply And.intro
      rw [hyp]
      exact step

theorem mem_of_equal_on_support{R: Type}[DecidableEq R]
  {X: Type}[DecidableEq X](l: List X)
    (f g : X → R)(x : X)(mhyp: x ∈ l) : 
      equalOnSupport l f g →  f x = g x :=
    match l with
    | [] => by contradiction
    | h :: t => by 
      intro hyp
      simp [equalOnSupport] at hyp
      cases mhyp 
      exact hyp.left
      have inTail : x ∈ t := by assumption
      have step := mem_of_equal_on_support t f g x inTail hyp.right
      exact step

def decideEqualOnSupport{R: Type}[DecidableEq R]
  {X: Type}[DecidableEq X](l: List X)(f g : X → R) :
      Decidable (equalOnSupport l f g) := 
  match l with
  | [] => 
    Decidable.isTrue (by simp [equalOnSupport])
  | h :: t => by 
    simp [equalOnSupport]
    cases (decideEqualOnSupport t f g) with
    | isTrue hs => 
        exact (
          if c:f h = g h then (Decidable.isTrue ⟨c, hs⟩) 
          else by
            apply Decidable.isFalse
            intro contra
            have contra' := contra.left 
            contradiction
        )        
    | isFalse hs => 
       apply Decidable.isFalse
       intro contra
       have contra' := contra.right
       contradiction

instance {X: Type}[DecidableEq X]{R: Type}[DecidableEq R]
  {l: List X}{f g : X → R} :
    Decidable (equalOnSupport l f g) := decideEqualOnSupport l f g

-- Setoid using coordinate equality
def eqlCoords(s₁ s₂ : FormalSum R X) : Prop :=
        s₁.coords = s₂.coords

namespace eqlCoords

theorem refl{R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]
  (s: FormalSum R X) :
      eqlCoords R X s s := by
        rfl

theorem symm{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{s₁ s₂ : FormalSum R X} : 
    eqlCoords R X s₁ s₂ → eqlCoords R X s₂ s₁ := by
    intro hyp
    apply funext
    intro x 
    apply Eq.symm
    exact congrFun hyp x

theorem trans{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{s₁ s₂ s₃ : FormalSum R X}:
    eqlCoords R X s₁ s₂ → eqlCoords R X s₂ s₃ → eqlCoords R X s₁ s₃ := by
    intro hyp₁ hyp₂
    apply funext
    intro x
    have l₁ := congrFun hyp₁ x
    have l₂ := congrFun hyp₂ x
    exact Eq.trans l₁ l₂

theorem is_equivalence{R: Type}[Ring R][DecidableEq R]
    {X: Type}[DecidableEq X] : 
      Equivalence (eqlCoords R X) := 
      {refl := refl, symm := symm, trans := trans}

end eqlCoords

instance formalSumSetoid:
    Setoid (FormalSum R X) := ⟨eqlCoords R X, eqlCoords.is_equivalence⟩

abbrev FreeModule := Quotient (formalSumSetoid R X)

notation "⟦" a "⟧" => Quotient.mk' a

def decideEqualQuotient{R: Type}[Ring R][DecidableEq R]
    {X: Type}[DecidableEq X](s₁ s₂ : FormalSum R X) : 
  Decidable ( ⟦ s₁ ⟧ = ⟦ s₂ ⟧ )  := 
        if ch₁ : equalOnSupport s₁.support s₁.coords s₂.coords then
          if ch₂ : equalOnSupport s₂.support s₁.coords s₂.coords then
            Decidable.isTrue ( 
              by
              apply Quotient.sound
              apply funext
              intro x
              exact 
                if  h₁:(0 = s₁.coords x) then 
                  if h₂:(0 = s₂.coords x) then
                    by rw [← h₁, h₂]
                  else by
                  have lem : x ∈ s₂.support := by 
                      apply nonzero_coord_in_support
                      assumption                      
                  let lem' :=   
                    mem_of_equal_on_support s₂.support s₁.coords s₂.coords x lem ch₂
                  exact lem'
                else by
                  have lem : x ∈ s₁.support := by 
                      apply nonzero_coord_in_support
                      assumption
                  let lem' :=   
                    mem_of_equal_on_support s₁.support s₁.coords s₂.coords x lem ch₁
                  exact lem'
              )
          else
            Decidable.isFalse (
              by
                intro contra
                let lem :=
                  equal_on_support_of_equal 
                    s₂.support s₁.coords s₂.coords (Quotient.exact contra) 
                contradiction
            )
        else
          Decidable.isFalse (
            by
              intro contra
              let lem :=
                  equal_on_support_of_equal 
                    s₁.support s₁.coords s₂.coords (Quotient.exact contra)
              contradiction
          )

instance {R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{s₁ s₂ : FormalSum R X} :  
    Decidable ( ⟦ s₁ ⟧ = ⟦ s₂ ⟧ ) := decideEqualQuotient s₁ s₂

def FreeModule.beq?{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]
    (x₁ x₂ : FreeModule R X) : Bool := by
    apply Quotient.lift₂ (fun (s₁ s₂ : FormalSum R X) => 
          decide ( ⟦ s₁ ⟧ = ⟦ s₂ ⟧))
    intro a₁ b₁ a₂ b₂ eqv₁ eqv₂
    let eq₁ : ⟦ a₁ ⟧ = ⟦ a₂ ⟧ := Quot.sound eqv₁
    let eq₂ : ⟦ b₁⟧ = ⟦ b₂ ⟧ := Quot.sound eqv₂
    simp [eq₁, eq₂]
    exact x₁
    exact x₂
    
def FreeModule.eq_of_beq_true
  {R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]:
    ∀ x₁ x₂ : FreeModule R X,  x₁.beq? x₂ = true → x₁ = x₂ := by
    let f := @Quotient.ind₂ (FormalSum R X) (FormalSum R X)
              (formalSumSetoid R X) (formalSumSetoid R X)
              (fun (x₁ x₂ : FreeModule R X) =>   x₁.beq? x₂ = true → x₁ = x₂)
    apply f
    intro s₁ s₂ eqv
    let eql := of_decide_eq_true eqv
    assumption

def FreeModule.neq_of_beq_false
  {R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]:
    ∀ x₁ x₂ : FreeModule R X,  x₁.beq? x₂ = false → Not (x₁ = x₂) := by
    let f := @Quotient.ind₂ (FormalSum R X) (FormalSum R X)
              (formalSumSetoid R X) (formalSumSetoid R X)
              (fun (x₁ x₂ : FreeModule R X) =>   x₁.beq? x₂ = false →
                Not (x₁ = x₂))
    apply f
    intro s₁ s₂ neqv
    let neql := of_decide_eq_false neqv
    assumption

def FreeModule.decEq{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]
    (x₁ x₂ : FreeModule R X) : Decidable (x₁ = x₂) := by
    match p:x₁.beq? x₂ with
    | true => 
      apply Decidable.isTrue
      apply FreeModule.eq_of_beq_true
      assumption
    | false => 
      apply Decidable.isFalse
      apply FreeModule.neq_of_beq_false
      assumption

instance {X: Type}[DecidableEq X]: DecidableEq (FreeModule R X) :=
  fun x₁ x₂ => x₁.decEq x₂

/- Ring structure -/


def FormalSum.scmul{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X] : R → FormalSum R X → FormalSum R X  
| _, [] => []
| r, (h::t) =>
    let (a₀, x₀) := h
    (r * a₀, x₀) :: (scmul r t)

theorem scmul_coords{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X](r: R)(s : FormalSum R X)(x₀ : X):
    (r * s.coords x₀) =  (s.scmul r ).coords x₀ := by 
    induction s with
    | nil =>
      simp [coords] 
    | cons h t ih => 
      simp [scmul, coords, monom_coords_mul, left_distrib, ih] 

def FreeModule.scmul{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X] : R → FreeModule R X → FreeModule R X := by
    intro r
    let f : FormalSum R X → FreeModule R X := fun s => ⟦ s.scmul r ⟧
    apply Quotient.lift f
    intro s₁ s₂
    simp
    intro hypeq
    apply Quotient.sound 
    apply funext
    intro x₀
    have l₁ := scmul_coords r s₁ x₀
    have l₂ := scmul_coords r s₂ x₀
    rw [← l₁, ← l₂]
    rw [hypeq]

theorem append_coords{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X](s₁ s₂ : FormalSum R X)(x₀ : X):
    (s₁.coords x₀) + (s₂.coords x₀) = (s₁ ++ s₂).coords x₀ := by 
    induction s₁ with
    | nil =>
      simp [coords] 
    | cons h t ih => 
      simp [coords, ← ih, add_assoc]    

def FreeModule.add{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X] : FreeModule R X → FreeModule R X → FreeModule R X := by
    let f : FormalSum R X → FormalSum R X → FreeModule R X := 
      fun s₁ s₂ => ⟦ s₁ ++ s₂ ⟧
    apply Quotient.lift₂ f
    intro a₁ b₁ a₂ b₂
    simp
    intro eq₁ eq₂ 
    apply Quotient.sound 
    apply funext
    intro x₀
    have l₁ := append_coords a₁ b₁ x₀
    have l₂ := append_coords a₂ b₂ x₀
    rw [← l₁, ← l₂]
    rw [eq₁, eq₂]

/- Relation via moves and equivalence to "equal coordsicients"-/
inductive BasicRel : FormalSum R X  → FormalSum R X   →  Prop where
| zeroCoeff (tail: FormalSum R X)(x: X)(a : R)(h: a = 0):  
        BasicRel  ((a, x):: tail) tail 
| addCoeffs (a b: R)(x: X)(tail: FormalSum R X):  
        BasicRel  ((a, x) :: (b, x) :: tail) ((a + b, x) :: tail)
| cons (a: R)(x: X)(s₁ s₂ : FormalSum R X):
        BasicRel  s₁ s₂ → BasicRel ((a, x) :: s₁) ((a, x) ::  s₂)
| swap (a₁ a₂: R)(x₁ x₂: X)(tail : FormalSum R X):
        BasicRel  ((a₁, x₁) :: (a₂, x₂) :: tail) 
                    ((a₂, x₂) :: (a₁, x₁) :: tail)

def FreeNatModuleAux := Quot (BasicRel R X)
namespace FormalSum

def sum {R: Type}[Ring R][DecidableEq R]{X: Type} [DecidableEq X] 
  (s: FormalSum R X): FreeNatModuleAux R X :=
      Quot.mk (BasicRel R X) s

def equiv {R: Type}[Ring R][DecidableEq R]{X: Type} [DecidableEq X] (s₁ s₂: FormalSum R X): Prop :=
      s₁.sum = s₂.sum

end FormalSum

infix:65 " ≃ " => FormalSum.equiv

open FormalSum

theorem coords_move_invariant (x₀ : X)
  (s₁ s₂: FormalSum R X)(h: BasicRel R X s₁ s₂):
        coords s₁ x₀  = coords s₂ x₀ := by
          induction h with
          | zeroCoeff tail x a hyp => simp [coords, hyp, monom_coords_at_zero]
          | addCoeffs a b x tail => 
            simp [coords, monom_coords_at_zero, ← add_assoc, monom_coords_hom]
          | cons a x s₁ s₂ r step => 
            simp [coords, step]
          | swap a₁ a₂ x₁ x₂ tail => 
            simp [coords, ← add_assoc, add_comm]

def FreeNatModuleAux.coeff (x₀ : X) : FreeNatModuleAux R X → R := 
      Quot.lift (fun s => s.coords  x₀) (coords_move_invariant R X x₀)

theorem coeff_factors (x: X)(s: FormalSum R X):
      FreeNatModuleAux.coeff R X x (sum s) = s.coords x  := by
      simp [FreeNatModuleAux.coeff]
      apply @Quot.liftBeta (r := BasicRel R X) (f:= fun s => s.coords  x)
      apply coords_move_invariant

theorem coords_well_defined{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X] (x: X)(s₁ s₂: FormalSum R X):
      s₁ ≃ s₂ → s₁.coords x = s₂.coords x := by
        intro hyp
        have l : FreeNatModuleAux.coeff R X x (sum s₂) = s₂.coords x :=
          by simp [coeff_factors, hyp]
        rw [← l]
        rw [← coeff_factors]        
        rw [hyp]

theorem cons_equiv_of_equiv{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X] (s₁ s₂ : FormalSum R X) (a: R) (x: X):
      s₁ ≃ s₂ → (a, x) :: s₁ ≃ (a, x) :: s₂  := by
        intro h
        let f : FormalSum R X → FreeNatModuleAux R X := 
            fun s => sum <| (a, x) :: s
        let wit : (s₁ s₂ : FormalSum R X) → (BasicRel R X s₁ s₂) → f s₁ = f s₂ :=
            by
            intro s₁ s₂ hyp
            apply Quot.sound
            apply BasicRel.cons
            assumption
        let g := Quot.lift f wit
        let factorizes : 
            (s : FormalSum R X) → g (s.sum) = 
              sum ((a, x) :: s) := Quot.liftBeta f wit
        rw[equiv]
        rw [← factorizes]
        rw [← factorizes]
        rw [h]

theorem nonzero_coeff_has_complement{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X] (x₀ : X)(s : FormalSum R X) :
        0 ≠  s.coords x₀  → 
          (∃ ys: FormalSum R X, 
            (((s.coords x₀, x₀) :: ys) ≃ s) ∧ 
            (List.length ys < s.length))  := by 
            induction s with 
            | nil =>
              intro contra
              contradiction
            | cons head tail hyp => 
              let (a, x) := head
              intro pos
              cases c:x == x₀ with
              | true => 
                let k := FormalSum.coords tail x₀ 
                have lem : a + k = 
                      coords ((a, x) :: tail) x₀ := 
                        by rw [coords, monomCoeff, c]
                have c'' : x = x₀ := 
                        of_decide_eq_true c
                rw [c'']
                rw [c''] at lem
                exact if c':(0 = k) 
                then by
                  have lIneq : tail.length < List.length ((a, x) :: tail) := 
                    by 
                      simp [List.length_cons]
                  rw [← c', add_zero] at lem
                  rw [← lem]   
                  exact ⟨tail, rfl, lIneq⟩
                else by
                  let ⟨ys, eqnStep, lIneqStep⟩ := hyp c'
                  have eqn₁ : 
                    (a, x₀) :: (k, x₀) :: ys ≃ (a + k, x₀) :: ys := by
                    apply Quot.sound 
                    apply BasicRel.addCoeffs 
                  have eqn₂ : 
                  (a, x₀) :: (k, x₀) :: ys ≃ (a, x₀) :: tail := 
                    by 
                      apply cons_equiv_of_equiv
                      assumption
                  have eqn : (a + k, x₀) :: ys ≃ 
                          (a, x₀) :: tail :=
                      Eq.trans (Eq.symm eqn₁) eqn₂    
                  rw [← lem]
                  have lIneq : ys.length < List.length ((a, x₀) :: tail) :=
                    by
                    apply Nat.le_trans lIneqStep 
                    simp [List.length_cons, Nat.le_succ]
                  exact ⟨ys, eqn, lIneq⟩
              | false =>
                let k := coords tail x₀
                have lem : k = 
                      coords ((a, x) :: tail) x₀ := 
                        by 
                          simp [coords, monomCoeff, c, zero_add]
                rw [← lem] at pos          
                let ⟨ys', eqnStep, lIneqStep⟩ := hyp pos   
                rw [← lem]
                let ys := (a, x) :: ys'      
                have lIneq : ys.length < ((a, x) :: tail).length := 
                  by 
                    simp [List.length_cons]
                    apply Nat.succ_lt_succ
                    exact lIneqStep
                have eqn₁ : 
                  (k, x₀) :: ys ≃ (a, x) :: (k, x₀) :: ys' := by
                    apply Quot.sound 
                    apply BasicRel.swap
                have eqn₂ : 
                  (a, x) :: (k, x₀) :: ys' ≃ (a, x) :: tail := 
                    by 
                      apply cons_equiv_of_equiv
                      assumption 
                have eqn : (k, x₀) :: ys ≃ (a, x) :: tail := by 
                    exact Eq.trans eqn₁ eqn₂
                exact ⟨ys, eqn, lIneq⟩


theorem equiv_e_of_zero_coeffs
  {R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]
    (s: FormalSum R X)
               (hyp :∀ x: X, s.coords x = 0) : s ≃ [] := 
               let canc : IsAddLeftCancel R :=
                ⟨fun a b c h => by 
                      rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]⟩
               match mt:s with 
               | [] => rfl
               | h :: t => by
                let (a₀, x₀) := h
                let hyp₀ := hyp x₀
                rw [coords] at hyp₀
                have c₀ : monomCoeff R X x₀ (a₀, x₀) = a₀ := by
                    simp [monomCoeff]                     
                rw [c₀] at hyp₀
                exact if hz: a₀ = 0 then by 
                  rw [hz] at hyp₀
                  rw [zero_add]at hyp₀
                  have tail_coeffs: ∀ x: X, 
                    coords t x = 0 := 
                      by 
                        intro x
                        simp [coords]
                        exact if c:(x₀ = x) then
                        by
                          rw [← c] 
                          assumption
                        else 
                        by
                          let hx := hyp x
                          simp [coords, monomCoeff] at hx
                          have lf : (x₀ == x) = false := 
                            decide_eq_false c 
                          rw [lf] at hx
                          simp [zero_add] at hx
                          assumption
                  have dec : t.length <  (h :: t).length  := by
                    simp [List.length_cons] 
                  let step : t ≃ [] := by 
                    apply equiv_e_of_zero_coeffs 
                    exact tail_coeffs
                  rw [hz]
                  have ls : (0, x₀) :: t ≃ t := by
                    apply Quot.sound
                    apply BasicRel.zeroCoeff
                    rfl
                  exact Eq.trans ls step
                else by
                  have non_zero : 0 ≠ coords t x₀ := by 
                    intro contra'
                    let contra := Eq.symm contra'
                    rw [contra, add_zero] at hyp₀
                    contradiction              
                  let ⟨ys, eqnStep, lIneqStep⟩ := 
                    nonzero_coeff_has_complement x₀ t non_zero
                  have tail_coeffs: ∀ x: X, 
                    coords ys x = 0 := 
                      by 
                        intro x
                        simp [coords]
                        exact if c:(x₀ = x) then
                        by
                          rw [← c] 
                          let ceq := coords_well_defined x₀ _ _  eqnStep
                          simp [coords, monomCoeff] at ceq
                          let pad : 
                            coords t x₀ = coords t x₀ + 0 := by simp [add_zero]
                          let ceq' := Eq.trans ceq pad
                          let ceq'' := add_left_cancel ceq'
                          assumption
                        else 
                        by
                          let hx := hyp x
                          simp [coords, monomCoeff] at hx
                          have lf : (x₀ == x) = false := 
                            decide_eq_false c 
                          rw [lf] at hx
                          simp [zero_add] at hx
                          let ceq := coords_well_defined x _ _  eqnStep
                          simp [coords, monomCoeff, lf] at ceq 
                          rw [hx] at ceq
                          exact ceq
                  have d : ys.length < (h :: t).length := 
                    by 
                      simp [List.length_cons]
                      apply Nat.le_trans lIneqStep
                      apply Nat.le_succ
                  let step : ys ≃ [] := by  
                    apply equiv_e_of_zero_coeffs 
                    exact tail_coeffs
                  let eqn₁ := cons_equiv_of_equiv _ _ (coords t x₀) x₀ step
                  let eqn₂ : t ≃ (coords t x₀, x₀) :: [] := Eq.trans ( Eq.symm eqnStep) eqn₁
                  let eqn₃ := cons_equiv_of_equiv _ _ a₀ x₀ eqn₂
                  apply Eq.trans eqn₃
                  have eqn₄ : sum [(a₀, x₀), (coords t x₀, x₀)] =
                      sum [(a₀ + coords t x₀, x₀)] := by
                        apply Quot.sound
                        apply BasicRel.addCoeffs
                  apply Eq.trans eqn₄
                  rw [hyp₀]
                  apply Quot.sound
                  apply BasicRel.zeroCoeff
                  rfl
termination_by _ R X s h => s.length
decreasing_by assumption

theorem equiv_of_equal_coeffs{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X](s₁ s₂: FormalSum R X)
               (hyp :∀ x: X, s₁.coords x = s₂.coords x) : s₁ ≃ s₂ := 
               let canc : IsAddLeftCancel R :=
                ⟨fun a b c h => by 
                      rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]⟩
               match mt:s₁ with 
               | [] => 
                have coeffs : ∀ x: X, s₂.coords x = 0 := by
                  intro x
                  let h := hyp x
                  rw [← h]
                  rfl
                let zl := equiv_e_of_zero_coeffs s₂ coeffs
                Eq.symm zl
               | h :: t => 
                  let (a₀, x₀):= h
                  by 
                  exact if p:0 = a₀
                  then by
                    have eq₁ : (a₀, x₀) :: t ≃ t := by 
                        apply Quot.sound
                        apply BasicRel.zeroCoeff
                        apply Eq.symm
                        assumption
                    have dec : t.length <  (h :: t).length  := by
                      simp [List.length_cons] 
                    have eq₂ : t ≃ s₂ := by 
                      apply equiv_of_equal_coeffs t s₂
                      intro x
                      let ceq := coords_well_defined  x ((a₀, x₀) :: t) t eq₁
                      simp [← ceq, hyp]
                    exact Eq.trans eq₁ eq₂
                  else by
                    let a₁ := coords t x₀                     
                    exact if p₁:0 = a₁  
                    then by
                        have cf₂ : s₂.coords x₀ = a₀ := by
                          rw [← hyp]
                          simp [coords, ← p₁, Nat.add_zero, monomCoeff]
                        let ⟨ys, eqn, ineqn⟩ := 
                          nonzero_coeff_has_complement x₀ s₂ (by 
                            rw [cf₂]
                            assumption)
                        let cfs := fun x => 
                          coords_well_defined  x _ _ eqn
                        rw [cf₂] at cfs
                        let cfs' := fun (x: X) =>
                          Eq.trans (hyp x) (Eq.symm (cfs x))
                        simp [coords] at cfs'
                        have dec : t.length <  (h :: t).length  := by
                         simp [List.length_cons] 
                        let step := 
                          equiv_of_equal_coeffs t ys cfs'
                        let step' := cons_equiv_of_equiv t ys a₀ x₀ step 
                        rw [cf₂] at eqn
                        exact Eq.trans step' eqn  
                    else by
                        let ⟨ys, eqn, ineqn⟩ := 
                          nonzero_coeff_has_complement  x₀ t p₁
                        let s₃ := (a₀ + a₁, x₀) :: ys
                        have eq₁ : (a₀, x₀) :: (a₁ , x₀) :: ys ≃ s₃ := by 
                          apply Quot.sound
                          let lem := BasicRel.addCoeffs a₀ a₁ x₀ ys
                          exact lem
                        have eq₂ : (a₀, x₀) :: (a₁ , x₀) :: ys ≃ 
                            (a₀, x₀) :: t := by 
                              apply cons_equiv_of_equiv
                              assumption
                        have eq₃ : s₃ ≃ s₂ := by 
                          have bd : ys.length + 1 < t.length + 1 := 
                            by
                              apply Nat.succ_lt_succ
                              exact ineqn
                          apply equiv_of_equal_coeffs
                          intro x
                          rw [← hyp x]
                          simp [coords]
                          let d := coords_well_defined  x _ _ eqn
                          rw [coords] at d
                          rw [← d]
                          simp [monom_coords_hom, coords, add_assoc]
                        apply Eq.trans (Eq.trans (Eq.symm eq₂) eq₁) eq₃ 
termination_by _ R X s _ _  => s.length
decreasing_by assumption

theorem func_eql_of_move_equiv{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{β : Sort u}
  (f : FormalSum R X → β):
  (∀ s₁ s₂ : FormalSum R X, ∀ mv : BasicRel R X s₁ s₂, f s₁ = f s₂) → 
  (∀ s₁ s₂ : FormalSum R X, s₁ ≈ s₂ →  f s₁ = f s₂) := by
  intro hyp
  let fbar : FreeNatModuleAux R X → β :=
      Quot.lift f hyp
  let fct : ∀ s : FormalSum R X, f s = fbar (sum s) := by
      apply Quot.liftBeta
      apply hyp
  intro s₁ s₂ sim
  have ec : eqlCoords R X s₁ s₂ := sim
  rw [eqlCoords] at ec
  have pullback: sum s₁ = sum s₂ := by
    apply equiv_of_equal_coeffs
    intro x
    exact congrFun ec x
  simp [fct, pullback]
