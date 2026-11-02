module

public import PSTR_WordBool_RatPair_Fields_001

/-! One real087 restore for the entire backed double packet. No source
cell, old15 suffix or old7 cell is synthesized by a host operation. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem restore_labels (background : Stack → List Bool) (context : C) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    ∀ current∈RatInput.restoreTrace background context bit flag mode copied source scratch numerator denominator raw,
      current.l=some 3 ∨ current.l=some 4 := by
  intro current member
  obtain ⟨mapped,mappedMember,rfl⟩:=List.mem_map.mp member
  obtain ⟨small,smallMember,rfl⟩:=List.mem_map.mp mappedMember
  have labels:=PSTRSymbolicRatExport.old_restore_labels context bit flag mode copied source scratch
    (background 1) (RatInput.restoreBackground background numerator denominator raw) small smallMember
  rcases labels with inside|done
  · left
    change small.l.map PSTRSymbolicRatExport.restoreLabel=some 3
    rw [inside]
    rfl
  · right
    change small.l.map PSTRSymbolicRatExport.restoreLabel=some 4
    rw [done]
    cases mode <;> rfl

theorem program_restore (caller : Statement C) :
    program caller (restoreLabel 3)=restoreBody := rfl

theorem restore_path (caller : Statement C) (background : Stack → List Bool)
    (context : C) (sx sy : Bool) (formatter : WordNatIO.Store) (bit flag mode : Bool)
    (copied source scratch numerator denominator raw : List Bool) :
    let old:=RatInput.restoreTrace background ((context,sx,sy),formatter) bit flag mode
      copied source scratch numerator denominator raw
    (old.map restoreConfiguration).head?=some (restoreConfiguration
      (RatInput.state background 3 ((context,sx,sy),formatter) (bit,flag,mode) source
        (PSTRSymbolicNaturalExport.backups copied++true::scratch) numerator denominator raw)) ∧
    (old.map restoreConfiguration).IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
    (old.map restoreConfiguration).getLast?=some (restoreConfiguration
      (RatInput.state background 4 ((context,sx,sy),formatter)
        (PSTRSymbolicNaturalExport.finalBit copied bit,true,mode)
        (copied.reverse++source) scratch numerator denominator raw)) ∧
    (old.map restoreConfiguration).length=copied.length+2 := by
  let old:=RatInput.restoreTrace background ((context,sx,sy),formatter) bit flag mode
    copied source scratch numerator denominator raw
  let exchange:=RatInput.Encoder.exchange (C × Bool × Bool)
  let sourceProgram:=RatInput.program (C:=(C × Bool × Bool) × WordNatIO.Store) .halt
  let storeProgram:=StoreIso.machine exchange sourceProgram
  have chain:=RatInput.restore_chain .halt background ((context,sx,sy),formatter) bit flag mode
    copied source scratch numerator denominator raw
  have last:=RatInput.restore_last background ((context,sx,sy),formatter) bit flag mode
    copied source scratch numerator denominator raw
  have proper:=NativeMulLink.no_early_halt_port sourceProgram 4 rfl old _ chain last rfl
  have storeChain:=StoreIso.chain_configuration_on exchange sourceProgram storeProgram old chain
    (by intro current member point selected;rfl)
  have mapped:=LabelMap.chain_configuration_on restoreLabel storeProgram (program caller)
    (old.map (StoreIso.configuration exchange)) storeChain (by
      intro current member point selected
      rw [←List.map_dropLast] at member
      obtain ⟨small,smallMember,rfl⟩:=List.mem_map.mp member
      change small.l=some point at selected
      have labels:=restore_labels background ((context,sx,sy),formatter) bit flag mode
        copied source scratch numerator denominator raw small (List.mem_of_mem_dropLast smallMember)
      have atThree : point=3 := by
        rcases labels with inside|done
        · exact Option.some.inj (selected.symm.trans inside)
        · have atFour : point=4:=Option.some.inj (selected.symm.trans done)
          subst point
          exact False.elim (proper small smallMember selected)
      subst point
      exact program_restore caller)
  have maps : (old.map (StoreIso.configuration exchange)).map (LabelMap.configuration restoreLabel)=
      old.map restoreConfiguration := by
    rw [List.map_map]
    rfl
  rw [maps] at mapped
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.head?_map,RatInput.restore_head,Option.map_some]
  · exact mapped
  · rw [List.getLast?_map,RatInput.restore_last,Option.map_some]
  · rw [List.length_map,RatInput.restore_length]

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector
