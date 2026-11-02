module

public import RootB234_PrepExponent_QLoopPaths022

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

theorem copy_state (background : Stack → List Bool) (counter : List Bool)
    (point : RatPacketTransport.Label) (memory : Store C) (source target : List Bool) :
    LabelMap.configuration copyLabel
      (RatPacketTransport.atState copyRoles (bank background [] counter [] []) point memory.1 memory.2 source [] target)=
      state (copyLabel point) memory (bank background source counter target []) := by
  unfold LabelMap.configuration RatPacketTransport.atState state
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem discard_state (background : Stack → List Bool) (counter input : List Bool)
    (point : RatPacketTransport.Label) (memory : Store C) (source target : List Bool) :
    LabelMap.configuration discardLabel
      (RatPacketTransport.atState discardRoles (bank background [] counter input []) point memory.1 memory.2 source [] target)=
      state (discardLabel point) memory (bank background source counter input target) := by
  unfold LabelMap.configuration RatPacketTransport.atState state
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem park_state (mapping : RatPacketTransport.Label → Label) (background : Stack → List Bool) (counter : List Bool)
    (point : RatPacketTransport.Label) (memory : Store C) (source target : List Bool) :
    LabelMap.configuration mapping
      (RatPacketTransport.atState parkRoles (bank background [] counter [] []) point memory.1 memory.2 source [] target)=
      state (mapping point) memory (bank background target counter source []) := by
  unfold LabelMap.configuration RatPacketTransport.atState state
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem copy_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (counter tail : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.copyQ 0) memory (bank background (RatInput.Encoder.packet value tail) counter [] []))
      (state .literalTwo (memory.1,false,false)
        (bank background (RatInput.Encoder.packet value tail) counter (RatInput.Encoder.packet value []) [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨part,count⟩ := packet_actual caller copyRoles true copyLabel
    (by intro point different;simp only [copyLabel,different,ite_false,program,RatPacketTransport.atProgram])
    (bank background [] counter [] []) memory.1 memory.2 value tail []
  refine ⟨⟨part.trace,?_,part.chain,?_⟩,count⟩
  · simpa only [copy_state,copyLabel,show (0 : RatPacketTransport.Label)≠4 from by decide,ite_false] using part.first
  · exact part.last.trans (congrArg some (copy_state background counter 4 (memory.1,false,false)
      (RatInput.Encoder.packet value tail) (RatInput.Encoder.packet value [])))

theorem discard_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (counter input tail : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.discardOld 0) memory (bank background (RatInput.Encoder.packet value tail) counter input []))
      (state (.clearOld 0) (memory.1,false,false)
        (bank background tail counter input (RatInput.Encoder.packet value []))),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨part,count⟩ := packet_actual caller discardRoles false discardLabel
    (by intro point different;simp only [discardLabel,different,ite_false,program,RatPacketTransport.atProgram])
    (bank background [] counter input []) memory.1 memory.2 value tail []
  refine ⟨⟨part.trace,?_,part.chain,?_⟩,count⟩
  · simpa only [discard_state,discardLabel,show (0 : RatPacketTransport.Label)≠4 from by decide,ite_false] using part.first
  · exact part.last.trans (congrArg some (discard_state background counter input 4 (memory.1,false,false)
      tail (RatInput.Encoder.packet value [])))

theorem park_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (counter tail : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.parkNew 0) memory (bank background tail counter (RatInput.Encoder.packet value []) []))
      (state .take (memory.1,false,false) (bank background (RatInput.Encoder.packet value tail) counter [] [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨part,count⟩ := packet_actual caller parkRoles false parkLabel
    (by intro point different;simp only [parkLabel,different,ite_false,program,RatPacketTransport.atProgram])
    (bank background [] counter [] []) memory.1 memory.2 value [] tail
  refine ⟨⟨part.trace,?_,part.chain,?_⟩,count⟩
  · simpa only [park_state,parkLabel,show (0 : RatPacketTransport.Label)≠4 from by decide,ite_false] using part.first
  · exact part.last.trans (congrArg some (park_state parkLabel background counter 4 (memory.1,false,false)
      [] (RatInput.Encoder.packet value tail)))

theorem budget_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (value : Rat) :
    ∃ part : Segment caller
      (state (.budget 0) memory (bank background tail [] (RatInput.Encoder.packet value []) []))
      (state .literalQ (memory.1,false,false) (bank background (RatInput.Encoder.packet value tail) [] [] [])),
      part.trace.length ≤ 3*RatInput.Encoder.fieldSize value+14 := by
  obtain ⟨part,count⟩ := packet_actual caller parkRoles false budgetLabel
    (by intro point different;simp only [budgetLabel,different,ite_false,program,RatPacketTransport.atProgram])
    (bank background [] [] [] []) memory.1 memory.2 value [] tail
  refine ⟨⟨part.trace,?_,part.chain,?_⟩,count⟩
  · simpa only [park_state,budgetLabel,show (0 : RatPacketTransport.Label)≠4 from by decide,ite_false] using part.first
  · exact part.last.trans (congrArg some (park_state budgetLabel background [] 4 (memory.1,false,false)
      [] (RatInput.Encoder.packet value tail)))

def clearCfg (before : Cells.State (PacketUnary.Store (Arithmetic.Aux×C))) : State C :=
  LabelMap.configuration clearLabel (StackIso.configuration clearRoles before)

theorem clear_initial (background : Stack → List Bool) (memory : Store C) (cache counter input trash : List Bool) :
    clearCfg (Cells.initial .clear0 memory
      (StackIso.slots clearRoles.symm (bank background cache counter input trash)))=
      state (.clearOld 0) memory (bank background cache counter input trash) := by
  unfold clearCfg Cells.initial LabelMap.configuration StackIso.configuration state
  change (⟨some (.clearOld 0),memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_final (background : Stack → List Bool) (context : PacketUnary.Store (Arithmetic.Aux×C))
    (cache counter input trash : List Bool) :
    clearCfg (Cells.result .clear0 context
      (StackIso.slots clearRoles.symm (bank background cache counter input trash)))=
      state (.parkNew 0) (context,false,false) (bank background cache counter input []) := by
  unfold clearCfg Cells.result Cells.output LabelMap.configuration StackIso.configuration state
  change (⟨some (.parkNew 0),(context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache counter input trash : List Bool) :
    ∃ part : Segment caller (state (.clearOld 0) memory (bank background cache counter input trash))
      (state (.parkNew 0) (memory.1,false,false) (bank background cache counter input [])),
      part.trace.length=trash.length+2 := by
  let before := StackIso.slots clearRoles.symm (bank background cache counter input trash)
  let run := Cells.trace .clear0 memory before
  let changed : Cells.Label → Cells.Statement (PacketUnary.Store (Arithmetic.Aux×C)) :=
    fun point => StackIso.statement clearRoles (Cells.Public.clear0 point)
  have stacked := StackIso.chain_configuration_on clearRoles Cells.Public.clear0 changed run
    (Cells.trace_chain .clear0 .halt memory before) (by intro current member point selected;rfl)
  have first : (run.map (StackIso.configuration clearRoles)).head?=
      some (StackIso.configuration clearRoles (Cells.initial .clear0 memory before)) := by
    rw [List.head?_map,Cells.trace_head,Option.map_some]
  have last : (run.map (StackIso.configuration clearRoles)).getLast?=
      some (StackIso.configuration clearRoles (Cells.result .clear0 memory.1 before)) := by
    rw [List.getLast?_map,Cells.trace_last,Option.map_some]
  have path := label_path clearLabel changed caller 6 rfl _ _ _ first stacked last rfl
    (by intro point different;simp only [clearLabel,different,ite_false,program];rfl)
  simp only [List.map_map,Function.comp_def] at path
  have first' : (run.map clearCfg).head?=some (clearCfg (Cells.initial .clear0 memory before)) := path.1
  have last' : (run.map clearCfg).getLast?=some (clearCfg (Cells.result .clear0 memory.1 before)) := path.2.2
  dsimp only [before] at first' last'
  rw [clear_initial] at first'
  rw [clear_final] at last'
  refine ⟨⟨run.map clearCfg,first',path.2.1,last'⟩,?_⟩
  rw [List.length_map,Cells.trace_length]
  rfl

end RootB234.PrepExponent.QLoop
