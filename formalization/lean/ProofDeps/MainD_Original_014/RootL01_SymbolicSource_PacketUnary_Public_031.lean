module
public import RootL01_SymbolicSource_PacketUnary_Resources_030

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootL01.SymbolicSource.PacketUnary
open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation
variable {C : Type*}

def localScale (frame : Bank) (value : Nat) (tail : List Bool) : Nat := mass frame value tail+value+1

theorem actual_digit_mass (frame : Bank) (value : Nat) (tail : List Bool) :
    (PSTRTMNatValue017.rawPayload value).length ≤ mass frame value tail := by
  have bound := RatInput.Encoder.point_mass (entryBank frame value tail) (15 : RatInput.Stack)
  change (L01_3_5_TABLE_FourRecord011.packet value++tail).length ≤ mass frame value tail at bound
  simp only [L01_3_5_TABLE_FourRecord011.packet,List.length_append,RatOutput.flagged_length,
    List.length_cons,List.length_nil] at bound
  omega

theorem resource_poly (frame : Bank) (value : Nat) (tail : List Bool) :
    time value ≤ 32*(localScale frame value tail)^2 ∧
    scale frame value tail ≤ 225*(localScale frame value tail)^2 ∧
    18*(scale frame value tail+8)+1 ≤ 4195*(localScale frame value tail)^2 := by
  let K := localScale frame value tail
  have positive : 1 ≤ K := by dsimp [K,localScale]; omega
  have square : K ≤ K^2 := by nlinarith
  have squarePos : 1 ≤ K^2 := one_le_pow₀ positive
  have D : (PSTRTMNatValue017.rawPayload value).length ≤ K :=
    (actual_digit_mass frame value tail).trans (by dsimp [K,localScale]; omega)
  have coefficient : 3*value+6 ≤ 6*K := by dsimp [K,localScale]; omega
  have product := Nat.mul_le_mul coefficient D
  have sub := Unary.canonical_time_le value
  have T : time value ≤ 32*K^2 := by dsimp only [time]; nlinarith
  have M : mass frame value tail ≤ K^2 :=
    (show mass frame value tail ≤ K by dsimp [K,localScale]; omega).trans square
  have B : scale frame value tail ≤ 225*K^2 := by dsimp only [scale]; omega
  refine ⟨T,B,?_⟩
  change 18*(scale frame value tail+8)+1 ≤ 4195*K^2
  omega

theorem charged_poly {frame : Bank} {context : C} {registers : Unary.Registers} {rat : RatInput.Store}
    {value : Nat} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts frame context registers rat value tail trace final) :
    charge trace ≤ 262144*(localScale frame value tail)^4 := by
  have caps := resource_poly frame value tail
  calc
    charge trace ≤ time value*(18*(scale frame value tail+8)+1) := charge_le facts
    _ ≤ (32*(localScale frame value tail)^2)*(4195*(localScale frame value tail)^2) :=
      Nat.mul_le_mul caps.1 caps.2.2
    _ = 134240*(localScale frame value tail)^4 := by ring
    _ ≤ 262144*(localScale frame value tail)^4 := Nat.mul_le_mul_right _ (by decide)

namespace Public

theorem actual (frame : Bank) (context : C) (registers : Unary.Registers) (rat : RatInput.Store)
    (value : Nat) (tail : List Bool) :
    ∃ trace final,Facts frame context registers rat value tail trace final ∧
      charge trace ≤ 262144*(localScale frame value tail)^4 := by
  obtain ⟨trace,final,facts⟩ := actual_bounded frame context registers rat value tail
  exact ⟨trace,final,facts,charged_poly facts⟩

theorem final_stacks {frame : Bank} {context : C} {registers : Unary.Registers} {rat : RatInput.Store}
    {value : Nat} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts frame context registers rat value tail trace final) :
    final.stk 15=L01_3_5_TABLE_FourRecord011.packet value++tail ∧ final.stk 7=frame 7 ∧
      final.stk 3=[] ∧ final.stk 5=Unary.unary value ∧ final.stk 6=[] ∧
      ∀ slot,slot ≠ 3 → slot ≠ 5 → slot ≠ 6 → slot ≠ 15 → final.stk slot=frame slot := by
  rw [facts.contents]
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro slot a b c d
  simp only [Function.update_of_ne b,entryBank,a,c,d,ite_false,b,or_self]

theorem fixed_source (C : Type*) [Finite C] :
    ∃ (source : Label → Statement C) (allowed : Finset Label),
      source=program .halt ∧ source .done=.halt ∧ TM2.Supports source allowed ∧ Finite (Store C) ∧
      ∀ (frame : Bank) (context : C) (registers : Unary.Registers) (rat : RatInput.Store)
        (value : Nat) (tail : List Bool),
        ∃ trace final,Facts frame context registers rat value tail trace final ∧
          charge trace ≤ 262144*(localScale frame value tail)^4 :=
  ⟨program .halt,support,rfl,rfl,supports,finiteStore,actual⟩

theorem consume_state (before : State C) (value : Nat) (tail : List Bool)
    (active : before.l=some (.collect 0))
    (packet : before.stk 15=L01_3_5_TABLE_FourRecord011.packet value++tail)
    (empty3 : before.stk 3=[]) (empty5 : before.stk 5=[]) (empty6 : before.stk 6=[]) :
    ∃ trace final,Facts before.stk before.var.1.1 before.var.1.2 before.var.2 value tail trace final ∧
      trace.head?=some before ∧ charge trace ≤ 262144*(RatInput.occupied before.stk+value+1)^4 := by
  have bank : entryBank before.stk value tail=before.stk := by
    funext slot
    fin_cases slot <;> simp [entryBank,packet,empty3,empty5,empty6]
  have whole : entry before.stk before.var.1.1 before.var.1.2 before.var.2 value tail=before := by
    unfold entry
    rw [bank,←active]
  obtain ⟨trace,final,facts,cost⟩ := actual before.stk before.var.1.1 before.var.1.2 before.var.2 value tail
  refine ⟨trace,final,facts,facts.first.trans (congrArg some whole),?_⟩
  simpa only [localScale,mass,bank] using cost

end Public
end RootL01.SymbolicSource.PacketUnary
