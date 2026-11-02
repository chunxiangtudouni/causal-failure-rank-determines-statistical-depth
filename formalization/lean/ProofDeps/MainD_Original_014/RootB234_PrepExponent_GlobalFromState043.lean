module

public import RootB234_PrepExponent_GlobalResources042

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def Owned (slot : Stack) : Prop :=
  slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=10 ∨ slot=11 ∨ slot=12 ∨ slot=13 ∨ slot=14

instance (slot : Stack) : Decidable (Owned slot) := by unfold Owned;infer_instance

theorem entry_bank (before : State C) (budget : Rat)
    (packet : before.stk 15=RatInput.Encoder.packet budget [])
    (empty : ∀ slot,Owned slot→before.stk slot=[]) :
    QLoop.bank before.stk (before.stk 7) [] (RatInput.Encoder.packet budget []) []=before.stk := by
  funext slot
  fin_cases slot
  all_goals first | rfl | exact (empty _ (by decide)).symm | exact packet.symm

theorem entry_state (before : State C) (budget : Rat) (active : before.l=some default)
    (packet : before.stk 15=RatInput.Encoder.packet budget [])
    (empty : ∀ slot,Owned slot→before.stk slot=[]) :
    state default before.var (QLoop.bank before.stk (before.stk 7) [] (RatInput.Encoder.packet budget []) [])=before := by
  cases before with
  | mk position memory contents =>
    change position=some default at active
    subst position
    unfold state
    rw [entry_bank _ budget packet empty]

/-- Current physical bank to full original E execution. All empty-bank
and packet facts are caller-produced representation invariants. In
particular,11 must really be cleared before entry; stash preserves it. -/
theorem from_state (caller : Statement C) (before : State C) (budget : Rat) (number : Nat)
    (positive : 0<budget) (active : before.l=some default)
    (input : before.stk 8=B23_4_RatWordPrep.NatField.packet number [])
    (packet : before.stk 15=RatInput.Encoder.packet budget [])
    (empty : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (afterMemory : Store C) (part : Segment caller before
      (state .done afterMemory
        (bank before.stk (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget (before.stk 7)))
          (B23_4_RatWordPrep.NatField.packet (BinaryExperiment.quotaExponent budget number) [])
          (RatInput.Encoder.packet budget []) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext before.var ∧ afterMemory.2=(false,false) ∧
      part.trace.length≤totalCost before.stk (before.stk 7) budget number := by
  obtain ⟨afterMemory,part,context,flags,count⟩ :=
    actual_original caller before.stk before.var (before.stk 7) budget number positive input
  have initial := entry_state before budget active packet empty
  exact ⟨afterMemory,⟨part.trace,part.first.trans (congrArg some initial),part.chain,part.last⟩,context,flags,count⟩

theorem from_state_resources (before : State C) (budget : Rat) (number : Nat)
    (positive : 0<budget) (active : before.l=some default)
    (input : before.stk 8=B23_4_RatWordPrep.NatField.packet number [])
    (packet : before.stk 15=RatInput.Encoder.packet budget [])
    (empty : ∀ slot,Owned slot→before.stk slot=[])
    (coefficient degree : Nat) (degreePositive : 1≤degree)
    (cost : totalCost before.stk (before.stk 7) budget number≤
      coefficient*(resourceScale before.stk (before.stk 7) budget number)^degree) :
    ∃ (afterMemory : Store C) (part : Segment .halt before
      (state .done afterMemory
        (bank before.stk (RatInput.Encoder.packet (qValue number) (RatInput.Encoder.packet budget (before.stk 7)))
          (B23_4_RatWordPrep.NatField.packet (BinaryExperiment.quotaExponent budget number) [])
          (RatInput.Encoder.packet budget []) [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext before.var ∧ afterMemory.2=(false,false) ∧
      PolynomialBounds coefficient degree (resourceScale before.stk (before.stk 7) budget number) part.trace := by
  obtain ⟨afterMemory,part,context,flags,count⟩ := from_state .halt before budget number positive active input packet empty
  have initial : ∀ slot,(before.stk slot).length≤8*resourceScale before.stk (before.stk 7) budget number := by
    intro slot
    have mass := RatInput.Encoder.point_mass before.stk slot
    unfold resourceScale
    omega
  exact ⟨afterMemory,part,context,flags,
    resources_of_cap _ _ part coefficient degree _ (resourceScale_positive _ _ _ _) degreePositive initial (count.trans cost)⟩

theorem caller_scale (before : State C) (budget : Rat) (number : Nat)
    (packet : before.stk 15=RatInput.Encoder.packet budget []) :
    resourceScale before.stk (before.stk 7) budget number≤
      3*(RatInput.occupied before.stk+number+targetExponent budget number+1) := by
  have cache := RatInput.Encoder.point_mass before.stk 7
  have input := RatInput.Encoder.point_mass before.stk 15
  rw [packet,RatInput.Encoder.packet_length] at input
  simp only [List.length_nil] at input
  unfold resourceScale
  omega

end RootB234.PrepExponent.Global
