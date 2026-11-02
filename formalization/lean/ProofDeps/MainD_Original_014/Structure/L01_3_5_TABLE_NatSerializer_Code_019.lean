module

public import Structure.L01_3_5_TABLE_Trace_005
public import Structure.L01_3_5_TABLE_FourRecord_Code_011
public import Common.PSTR_WordBool_RatInputAPI_093

/-! Read one actual self-delimited natural packet with the frozen field
collector and owned-sentinel restorer. The original15/old7 are restored;
the reversed raw payload in3 is the real formatter's next input. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_NatSerializer019

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation
open L01_3_5_TABLE_Trace005

abbrev Label := RatInput.Label
abbrev Memory (C : Type*) := RatInput.Memory C
abbrev State (C : Type*) := RatInput.State C
abbrev Bank := RatInput.Stack → List Bool

def collectProgram {C : Type*} (label : Label) : RatInput.Statement C :=
  if label = 0 then .push 7 (fun _ => true) (.goto (fun _ => 1)) else
  if label = 2 then .goto (fun _ => 3) else RatInput.program .halt label

theorem prepare_step {C : Type*} (background : Bank) (context : C) (memory : RatInput.Store)
    (source scratch numerator denominator raw : List Bool) :
    TM2.step collectProgram (RatInput.state background 0 context memory source scratch numerator denominator raw) =
      some (RatInput.state background 1 context memory source (true :: scratch) numerator denominator raw) := by
  simp [collectProgram,RatInput.state,TM2.step,TM2.stepAux,
    RatInput.scratch_at,RatInput.update_scratch]

theorem return_step {C : Type*} (background : Bank) (context : C) (memory : RatInput.Store)
    (source scratch numerator denominator raw : List Bool) :
    TM2.step collectProgram (RatInput.state background 2 context memory source scratch numerator denominator raw) =
      some (RatInput.state background 3 context memory source scratch numerator denominator raw) := rfl

theorem field_proper {C : Type*} (background : Bank) (context : C) (mode : Bool)
    (digits : List Bool) (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    ∀ current ∈ (RatInput.fieldTrace false background context mode digits bit flag copied
      source scratch numerator denominator raw).dropLast, current.l = some 1 := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil =>
      intro current present
      simp only [RatInput.fieldTrace,Bool.false_eq_true,ite_false,List.dropLast_cons_cons,
        List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at present
      subst current
      rfl
  | cons digit later ih =>
      intro current present
      rw [RatInput.fieldTrace] at present
      simp only [Bool.false_eq_true,ite_false] at present
      rw [List.dropLast_cons_of_ne_nil (RatInput.field_nonempty false background context
        mode later digit true (digit :: true :: copied) source scratch (digit :: numerator) denominator raw)] at present
      rcases List.mem_cons.mp present with same | remaining
      · subst current
        rfl
      · exact ih digit true (digit :: true :: copied) (digit :: numerator) denominator current remaining

theorem field_lift {C : Type*} (background : Bank) (context : C) (mode : Bool)
    (digits : List Bool) (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    (RatInput.fieldTrace false background context mode digits bit flag copied
      source scratch numerator denominator raw).IsChain
      (fun before after => TM2.step collectProgram before = some after) := by
  apply chain_on (RatInput.program .halt) collectProgram _
    (RatInput.field_chain .halt false background context mode digits bit flag copied source scratch numerator denominator raw)
  intro current present label position
  have one := field_proper background context mode digits bit flag copied source scratch numerator denominator raw current present
  have same : label = 1 := Option.some.inj (position.symm.trans one)
  subst label
  rfl

theorem restore_lift {C : Type*} (background : Bank) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    (RatInput.restoreTrace background context bit flag mode copied source scratch numerator denominator raw).IsChain
      (fun before after => TM2.step collectProgram before = some after) := by
  apply chain_on (RatInput.program .halt) collectProgram _
    (RatInput.restore_chain .halt background context bit flag mode copied source scratch numerator denominator raw)
  intro current present point position
  have member := List.mem_of_mem_dropLast present
  obtain ⟨mapped,mappedMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨small,smallMember,rfl⟩ := List.mem_map.mp mappedMember
  have labels := PSTRSymbolicRatExport.old_restore_labels context bit flag mode copied source scratch (background 1)
    (RatInput.restoreBackground background numerator denominator raw) small smallMember
  rcases labels with inside | done
  · have same : point = 3 := by
      change small.l.map PSTRSymbolicRatExport.restoreLabel = some point at position
      rw [inside] at position
      exact (Option.some.inj position).symm
    subst point
    rfl
  · have same : point = 4 := by
      change small.l.map PSTRSymbolicRatExport.restoreLabel = some point at position
      rw [done] at position
      cases mode <;> exact (Option.some.inj position).symm
    subst point
    rfl

end PaperProofs.Common.Native.L01_3_5_TABLE_NatSerializer019
