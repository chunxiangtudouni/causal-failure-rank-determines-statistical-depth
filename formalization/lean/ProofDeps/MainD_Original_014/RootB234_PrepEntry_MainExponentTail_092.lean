module

public import RootB234_PrepEntry_MainExponentRun_091

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open PaperProofs.Common PaperProofs.Statistics
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*}

def movedBank (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack→List Bool :=
  Function.update (Function.update (exponentBank bits stages tools budget) 11 []) 5
    (NatField.packet (BinaryExperiment.quotaExponent budget stages) [])

def stageBank (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack→List Bool :=
  Function.update (metadataBank bits stages tools budget) 5 (NatField.packet (BinaryExperiment.quotaExponent budget stages) [])

def naturalCfg (before : NatPacket.State (ExponentCore C)) : State C :=
  LabelMap.configuration naturalLabel (StoreIso.configuration (exponentIso C) (StackIso.configuration naturalRoles before))

def naturalBackground (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack→List Bool :=
  StackIso.slots naturalRoles.symm (exponentBank bits stages tools budget)

theorem natural_entry (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (memory : Global.Store (ExponentContext C)) :
    naturalCfg (NatPacket.entry (naturalBackground bits stages tools budget) memory.1 memory.2
      (BinaryExperiment.quotaExponent budget stages) [] [])=
      state (.natural default) (exponentIso C memory) (exponentBank bits stages tools budget) := by
  change (⟨some (.natural default),exponentIso C memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem natural_final (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (context : ExponentCore C) :
    naturalCfg (NatPacket.finalState false (naturalBackground bits stages tools budget) context
      (BinaryExperiment.quotaExponent budget stages) [] [])=
      state (.clear 0) (exponentIso C (context,false,false)) (movedBank bits stages tools budget) := by
  change (⟨some (.clear 0),exponentIso C (context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem natural_actual (caller : Statement C) (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (memory : Global.Store (ExponentContext C)) :
    ∃ part : Segment caller
      (state (.natural default) (exponentIso C memory) (exponentBank bits stages tools budget))
      (state (.clear 0) (exponentIso C (memory.1,false,false)) (movedBank bits stages tools budget)),
      part.trace.length≤NatPacket.coefficient*(RatInput.occupied (exponentBank bits stages tools budget)+1) := by
  let background:=naturalBackground bits stages tools budget
  let number:=BinaryExperiment.quotaExponent budget stages
  obtain ⟨run,facts⟩:=NatPacket.actual_polynomial false background memory.1 memory.2 number [] []
  let old : NatPacket.Label → NatPacket.Statement (ExponentCore C) := NatPacket.program false .halt
  let changed : NatPacket.Label → NatPacket.Statement (ExponentCore C) := fun point => StackIso.statement naturalRoles (old point)
  have stackChain:=StackIso.chain_configuration_on naturalRoles old changed run facts.chain
    (by intro current member point selected;rfl)
  have stackFirst : (run.map (StackIso.configuration naturalRoles)).head?=
      some (StackIso.configuration naturalRoles (NatPacket.entry background memory.1 memory.2 number [] [])) := by
    rw [List.head?_map,facts.first,Option.map_some]
  have stackLast : (run.map (StackIso.configuration naturalRoles)).getLast?=
      some (StackIso.configuration naturalRoles (NatPacket.finalState false background memory.1 number [] [])) := by
    rw [List.getLast?_map,facts.last,Option.map_some]
  have path:=store_label_path (exponentIso C) naturalLabel changed caller .done rfl _ _ _
    stackFirst stackChain stackLast rfl
    (by intro point different;simp only [naturalLabel,different,ite_false,program];rfl)
  simp only [List.map_map,Function.comp_def] at path
  have first : (run.map naturalCfg).head?=some (naturalCfg (NatPacket.entry background memory.1 memory.2 number [] [])):=path.1
  have last : (run.map naturalCfg).getLast?=some (naturalCfg (NatPacket.finalState false background memory.1 number [] [])):=path.2.2
  dsimp only [background,number] at first last
  rw [natural_entry] at first
  rw [natural_final] at last
  have occupied : NatPacket.mass background memory.1 memory.2 number [] []=
      RatInput.occupied (exponentBank bits stages tools budget) := by
    have sameBanks:=congrArg (fun current : State C => current.stk) (natural_entry bits stages tools budget memory)
    have equality:=congrArg RatInput.occupied sameBanks
    change RatInput.occupied (StackIso.slots naturalRoles
      (NatPacket.entry background memory.1 memory.2 number [] []).stk)=_ at equality
    have permutation : RatInput.occupied (StackIso.slots naturalRoles
        (NatPacket.entry background memory.1 memory.2 number [] []).stk)=
        RatInput.occupied (NatPacket.entry background memory.1 memory.2 number [] []).stk :=
      StackIso.occupied_sum naturalRoles _
    exact permutation.symm.trans equality
  refine ⟨⟨run.map naturalCfg,first,path.2.1,last⟩,?_⟩
  simpa only [List.length_map,NatPacket.scale,occupied] using facts.time

def clearCfg (before : Cells.State (ExponentCore C)) : State C :=
  LabelMap.configuration clearLabel (StoreIso.configuration (exponentIso C) (StackIso.configuration clearRoles before))

def clearBackground (bits : List Bool) (stages tools : Nat) (budget : Rat) : RatInput.Stack→List Bool :=
  StackIso.slots clearRoles.symm (movedBank bits stages tools budget)

theorem clear_entry (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (memory : Global.Store (ExponentContext C)) :
    clearCfg (Cells.initial .clear0 memory (clearBackground bits stages tools budget))=
      state (.clear 0) (exponentIso C memory) (movedBank bits stages tools budget) := by
  change (⟨some (.clear 0),exponentIso C memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_final (bits : List Bool) (stages tools : Nat) (budget : Rat) (context : ExponentCore C) :
    clearCfg (Cells.result .clear0 context (clearBackground bits stages tools budget))=
      state (.channels default) (exponentIso C (context,false,false)) (stageBank bits stages tools budget) := by
  change (⟨some (.channels default),exponentIso C (context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_actual (caller : Statement C) (bits : List Bool) (stages tools : Nat) (budget : Rat)
    (memory : Global.Store (ExponentContext C)) :
    ∃ part : Segment caller
      (state (.clear 0) (exponentIso C memory) (movedBank bits stages tools budget))
      (state (.channels default) (exponentIso C (memory.1,false,false)) (stageBank bits stages tools budget)),
      part.trace.length=(movedBank bits stages tools budget 7).length+2 := by
  let background:=clearBackground bits stages tools budget
  let run:=Cells.trace .clear0 memory background
  let old : Cells.Label → Cells.Statement (ExponentCore C) := Cells.Public.clear0
  let changed : Cells.Label → Cells.Statement (ExponentCore C) := fun point => StackIso.statement clearRoles (old point)
  have stackChain:=StackIso.chain_configuration_on clearRoles old changed run (Cells.trace_chain .clear0 .halt memory background)
    (by intro current member point selected;rfl)
  have stackFirst : (run.map (StackIso.configuration clearRoles)).head?=
      some (StackIso.configuration clearRoles (Cells.initial .clear0 memory background)) := by
    rw [List.head?_map,Cells.trace_head,Option.map_some]
  have stackLast : (run.map (StackIso.configuration clearRoles)).getLast?=
      some (StackIso.configuration clearRoles (Cells.result .clear0 memory.1 background)) := by
    rw [List.getLast?_map,Cells.trace_last,Option.map_some]
  have path:=store_label_path (exponentIso C) clearLabel changed caller 6 rfl _ _ _
    stackFirst stackChain stackLast rfl
    (by intro point different;simp only [clearLabel,different,ite_false,program];rfl)
  simp only [List.map_map,Function.comp_def] at path
  have first : (run.map clearCfg).head?=some (clearCfg (Cells.initial .clear0 memory background)):=path.1
  have last : (run.map clearCfg).getLast?=some (clearCfg (Cells.result .clear0 memory.1 background)):=path.2.2
  dsimp only [background] at first last
  rw [clear_entry] at first
  rw [clear_final] at last
  exact ⟨⟨run.map clearCfg,first,path.2.1,last⟩,by rw [List.length_map,Cells.trace_length];rfl⟩

end RootB234.PrepEntry.MainExponent
