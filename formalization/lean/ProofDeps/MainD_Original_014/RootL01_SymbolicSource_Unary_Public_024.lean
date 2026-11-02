module

public import RootL01_SymbolicSource_Unary_Resources_023

/-! The local unary cost explicitly includes the PRODUCED value.  It is
not a polynomial binary-Nat conversion theorem.  The original structural
caller must pay the published Word-domain bound and derive its input. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.Unary

open Turing
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

variable {C : Type*}

def localScale (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) : Nat :=
  mass frame context memory digits amount+evaluate digits amount+1

theorem resource_poly (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) :
    time digits amount ≤ 8*(localScale frame context memory digits amount)^2 ∧
    scale frame context memory digits amount ≤ 17*(localScale frame context memory digits amount)^2 ∧
    6*(scale frame context memory digits amount+3)+1 ≤ 121*(localScale frame context memory digits amount)^2 := by
  let K := localScale frame context memory digits amount
  have positive : 1 ≤ K := by dsimp [K,localScale]; omega
  have square : K ≤ K^2 := by nlinarith
  have squarePos : 1 ≤ K^2 := one_le_pow₀ positive
  have digitMass := RatInput.Encoder.point_mass (entry frame context memory digits amount).stk (3 : Stack)
  change digits.length ≤ mass frame context memory digits amount at digitMass
  have D : digits.length ≤ K := by dsimp [K,localScale]; omega
  have F : 3*evaluate digits amount+3 ≤ 3*K := by dsimp [K,localScale]; omega
  have M : mass frame context memory digits amount ≤ K^2 := by
    have linear : mass frame context memory digits amount ≤ K := by dsimp [K,localScale]; omega
    exact linear.trans square
  have product := Nat.mul_le_mul F D
  have run := time_le digits amount
  have T : time digits amount ≤ 8*K^2 := by nlinarith
  have B : scale frame context memory digits amount ≤ 17*K^2 := by
    dsimp only [scale]
    omega
  refine ⟨T,B,?_⟩
  change 6*(scale frame context memory digits amount+3)+1 ≤ 121*K^2
  omega

theorem charge_poly {frame : Bank} {context : C} {memory : Registers} {digits : List Bool} {amount : Nat}
    {trace : List (State C)} (facts : Facts frame context memory digits amount trace) :
    charge trace ≤ 1024*(localScale frame context memory digits amount)^4 := by
  have caps := resource_poly frame context memory digits amount
  calc
    charge trace ≤ time digits amount*(6*(scale frame context memory digits amount+3)+1) :=
      charge_le frame context memory digits amount trace facts
    _ ≤ (8*(localScale frame context memory digits amount)^2)*(121*(localScale frame context memory digits amount)^2) :=
      Nat.mul_le_mul caps.1 caps.2.2
    _ = 968*(localScale frame context memory digits amount)^4 := by ring
    _ ≤ 1024*(localScale frame context memory digits amount)^4 := Nat.mul_le_mul_right _ (by decide)

namespace Public

theorem actual (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat) :
    ∃ trace : List (State C),Facts frame context memory digits amount trace ∧
      charge trace ≤ 1024*(localScale frame context memory digits amount)^4 := by
  obtain ⟨trace,facts⟩ := actual_bounded frame context memory digits amount
  exact ⟨trace,facts,charge_poly facts⟩

theorem final_stacks (frame : Bank) (context : C) (digits : List Bool) (amount : Nat) :
    (final frame context digits amount).stk = cells frame [] (unary (evaluate digits amount)) [] ∧
    (final frame context digits amount).var = (context,(false,false)) ∧
    (final frame context digits amount).l = some .done := ⟨rfl,rfl,rfl⟩

theorem canonical_final (frame : Bank) (context : C) (value : Nat) :
    (final frame context (PSTRTMNatValue017.rawPayload value).reverse 0).stk =
      cells frame [] (unary value) [] := by
  change cells frame [] (unary (evaluate (PSTRTMNatValue017.rawPayload value).reverse 0)) [] = _
  rw [evaluate_canonical]

theorem canonical (frame : Bank) (context : C) (memory : Registers) (value : Nat) :
    ∃ trace : List (State C),Facts frame context memory (PSTRTMNatValue017.rawPayload value).reverse 0 trace ∧
      charge trace ≤ 1024*(mass frame context memory (PSTRTMNatValue017.rawPayload value).reverse 0+value+1)^4 := by
  obtain ⟨trace,facts,cost⟩ := actual frame context memory (PSTRTMNatValue017.rawPayload value).reverse 0
  exact ⟨trace,facts,by simpa only [localScale,evaluate_canonical] using cost⟩

theorem fixed_source (C : Type*) [Finite C] :
    ∃ (source : Label → Statement C) (allowed : Finset Label),
      source=program .halt ∧ source .done=.halt ∧ TM2.Supports source allowed ∧ Finite (Store C) ∧
      ∀ (frame : Bank) (context : C) (memory : Registers) (digits : List Bool) (amount : Nat),
        ∃ trace : List (State C),Facts frame context memory digits amount trace ∧
          charge trace ≤ 1024*(localScale frame context memory digits amount)^4 :=
  ⟨program .halt,support,rfl,by rfl,supports,finiteStore,actual⟩

end Public
end RootL01.SymbolicSource.Unary
