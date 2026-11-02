module

public import RootB234_PrepExponent_GlobalInitial036
public import RootB234_PrepExponent_GlobalDecision037

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def clearCfg (site : ClearSite) (before : Cells.State (PacketUnary.Store (Arithmetic.Aux×C))) : State C :=
  LabelMap.configuration (clearLabel site) (StackIso.configuration QLoop.clearRoles before)

theorem clear_initial (site : ClearSite) (background : Stack → List Bool) (memory : Store C)
    (cache exponent input trash : List Bool) :
    clearCfg site (Cells.initial .clear0 memory
      (StackIso.slots QLoop.clearRoles.symm (bank background cache exponent input trash [] [])))=
      state (.clear site 0) memory (bank background cache exponent input trash [] []) := by
  unfold clearCfg Cells.initial LabelMap.configuration StackIso.configuration state
  change (⟨some (.clear site 0),memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_final (site : ClearSite) (background : Stack → List Bool)
    (context : PacketUnary.Store (Arithmetic.Aux×C)) (cache exponent input trash : List Bool) :
    clearCfg site (Cells.result .clear0 context
      (StackIso.slots QLoop.clearRoles.symm (bank background cache exponent input trash [] [])))=
      state (clearNext site) (context,false,false) (bank background cache exponent input [] [] []) := by
  unfold clearCfg Cells.result Cells.output LabelMap.configuration StackIso.configuration state
  change (⟨some (clearNext site),(context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_actual (caller : Statement C) (site : ClearSite) (background : Stack → List Bool) (memory : Store C)
    (cache exponent input trash : List Bool) :
    ∃ part : Segment caller
      (state (.clear site 0) memory (bank background cache exponent input trash [] []))
      (state (clearNext site) (memory.1,false,false) (bank background cache exponent input [] [] [])),
      part.trace.length=trash.length+2 := by
  let before := StackIso.slots QLoop.clearRoles.symm (bank background cache exponent input trash [] [])
  let run := Cells.trace .clear0 memory before
  let changed : Cells.Label → Cells.Statement (PacketUnary.Store (Arithmetic.Aux×C)) :=
    fun point => StackIso.statement QLoop.clearRoles (Cells.Public.clear0 point)
  have stacked := StackIso.chain_configuration_on QLoop.clearRoles Cells.Public.clear0 changed run
    (Cells.trace_chain .clear0 .halt memory before) (by intro current member point selected;rfl)
  have first : (run.map (StackIso.configuration QLoop.clearRoles)).head?=
      some (StackIso.configuration QLoop.clearRoles (Cells.initial .clear0 memory before)) := by
    rw [List.head?_map,Cells.trace_head,Option.map_some]
  have last : (run.map (StackIso.configuration QLoop.clearRoles)).getLast?=
      some (StackIso.configuration QLoop.clearRoles (Cells.result .clear0 memory.1 before)) := by
    rw [List.getLast?_map,Cells.trace_last,Option.map_some]
  have path := label_path (clearLabel site) changed caller 6 rfl _ _ _ first stacked last rfl
    (by intro point different;simp only [clearLabel,different,ite_false,program];rfl)
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map (clearCfg site)).head?=some (clearCfg site (Cells.initial .clear0 memory before)) := path.1
  have last' : (run.map (clearCfg site)).getLast?=some (clearCfg site (Cells.result .clear0 memory.1 before)) := path.2.2
  dsimp only [before] at first' last'
  rw [clear_initial] at first'
  rw [clear_final] at last'
  exact ⟨⟨run.map (clearCfg site),first',path.2.1,last'⟩,by rw [List.length_map,Cells.trace_length];rfl⟩

def compareCost (background : Stack → List Bool) (tail exponent : List Bool) (right left : Rat) : Nat :=
  let cache := RatInput.Encoder.packet left (RatInput.Encoder.packet right tail)
  RatBinary.time RatAddSub.addSubCoefficient (QLoop.rawBackground background cache exponent) right left [] cache+
    9*RatInput.Encoder.fieldSize left+3*RatInput.Encoder.fieldSize right+
    RatInput.Encoder.fieldSize (right-left)+63

/-- Actual R<=Y test: four real packet calls, real subtraction, actual
reader of the result, and physical pop/branch of the produced Bool. -/
theorem compare_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail exponent : List Bool) (right left : Rat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.packet .compareCopyY 0) memory
        (bank background (RatInput.Encoder.packet left (RatInput.Encoder.packet right tail)) exponent [] [] [] []))
      (state (if right≤left then .packet .stopDropY 0 else .packet .repeatCopyY 0) afterMemory
        (bank background (RatInput.Encoder.packet left (RatInput.Encoder.packet right tail)) exponent [] [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=(true,decide (right≤left)) ∧
      part.trace.length ≤ compareCost background tail exponent right left := by
  let rtail := RatInput.Encoder.packet right tail
  let cache := RatInput.Encoder.packet left rtail
  obtain ⟨copyY,copyYCount⟩ := copy7_actual caller .compareCopyY rfl rfl background memory rtail exponent [] [] [] left
  obtain ⟨pullY,pullYCount⟩ := pull12_actual caller .compareParkY rfl rfl background (memory.1,false,false)
    rtail exponent (RatInput.Encoder.packet left []) [] left
  obtain ⟨copyR,copyRCount⟩ := copy7_actual caller .compareCopyR rfl rfl background (memory.1,false,false)
    tail exponent (RatInput.Encoder.packet left []) (RatInput.Encoder.packet left []) [] right
  obtain ⟨restoreY,restoreYCount⟩ := restore12_actual caller .compareRestoreY rfl rfl background (memory.1,false,false)
    rtail exponent (RatInput.Encoder.packet right (RatInput.Encoder.packet left [])) [] left
  let restored : Segment caller
      (state (.packet .compareRestoreY 0) (memory.1,false,false)
        (bank background rtail exponent (RatInput.Encoder.packet right (RatInput.Encoder.packet left []))
          (RatInput.Encoder.packet left []) [] []))
      (state (.subtract default) (memory.1,false,false) (bank background cache exponent (RatPair.input right left []) [] [] [])) :=
    ⟨restoreY.trace,restoreY.first,restoreY.chain,restoreY.last.trans (congrArg some (by rw [pair_packets right left []];rfl))⟩
  obtain ⟨subMemory,subPart,subContext,subCount⟩ := sub_actual caller background (memory.1,false,false) cache exponent right left []
  obtain ⟨readMemory,readPart,readContext,_readFlags,readCount⟩ := reader_compare_actual caller background subMemory cache exponent right left
  have branch : TM2.step (program caller)
      (state .branch readMemory (bank background cache exponent [] [] [] [decide (right≤left)]))=
      some (state (if right≤left then .packet .stopDropY 0 else .packet .repeatCopyY 0)
        (readMemory.1,true,decide (right≤left)) (bank background cache exponent [] [] [] [])) := by
    simpa only [decide_eq_true_eq] using branch_step caller background readMemory cache exponent [] (decide (right≤left))
  let branchPart := Segment.edge branch
  let j1 := copyY.append pullY
  let j2 := j1.append copyR
  let j3 := j2.append restored
  let j4 := j3.append subPart
  let j5 := j4.append readPart
  let whole := j5.append branchPart
  refine ⟨(readMemory.1,true,decide (right≤left)),whole,readContext.trans subContext,rfl,?_⟩
  have restoredCount : restored.trace.length ≤ 3*RatInput.Encoder.fieldSize left+14 := restoreYCount
  have branchCount : branchPart.trace.length=2 := rfl
  have c1 : j1.trace.length ≤ copyY.trace.length+pullY.trace.length := copyY.append_length pullY
  have c2 : j2.trace.length ≤ j1.trace.length+copyR.trace.length := j1.append_length copyR
  have c3 : j3.trace.length ≤ j2.trace.length+restored.trace.length := j2.append_length restored
  have c4 : j4.trace.length ≤ j3.trace.length+subPart.trace.length := j3.append_length subPart
  have c5 : j5.trace.length ≤ j4.trace.length+readPart.trace.length := j4.append_length readPart
  have c6 : whole.trace.length ≤ j5.trace.length+branchPart.trace.length := j5.append_length branchPart
  unfold compareCost
  change whole.trace.length ≤ RatBinary.time RatAddSub.addSubCoefficient
    (QLoop.rawBackground background cache exponent) right left [] cache+
    9*RatInput.Encoder.fieldSize left+3*RatInput.Encoder.fieldSize right+RatInput.Encoder.fieldSize (right-left)+63
  omega

end RootB234.PrepExponent.Global
