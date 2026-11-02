module

public import RootB234_PrepExponent_NCountPaths016

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NCount
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

theorem reverse_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input backup output counter target : List Bool) :
    ∃ part : Segment caller (state background (.reverse 3) memory input backup output counter target)
        (state background (.unary (.collect 0)) (memory.1,false,false) input [] output counter (backup.reverse++target)),
      part.trace.length=backup.length+2 := by
  let before := StackIso.slots reverseRoles.symm (bank background input backup output counter target)
  let run := Cells.trace .reverse3To2 memory before
  have path := cells_path caller .reverse3To2 reverseRoles reverseLabel memory before rfl
  have first : (run.map reverseCfg).head?=some (reverseCfg (Cells.initial .reverse3To2 memory before)) := path.1
  have last : (run.map reverseCfg).getLast?=some (reverseCfg (Cells.result .reverse3To2 memory.1 before)) := path.2.2
  dsimp only [before] at first last
  rw [reverse_initial] at first
  rw [reverse_final] at last
  exact ⟨⟨run.map reverseCfg,first,path.2.1,last⟩,by rw [List.length_map,Cells.trace_length];rfl⟩

theorem move_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input backup output counter target : List Bool) :
    ∃ part : Segment caller (state background (.move 3) memory input backup output counter target)
        (state background (.clear 0) (memory.1,false,false) input backup [] (output.reverse++counter) target),
      part.trace.length=output.length+2 := by
  let before := StackIso.slots moveRoles.symm (bank background input backup output counter target)
  let run := Cells.trace .reverse3To2 memory before
  have path := cells_path caller .reverse3To2 moveRoles moveLabel memory before rfl
  have first : (run.map moveCfg).head?=some (moveCfg (Cells.initial .reverse3To2 memory before)) := path.1
  have last : (run.map moveCfg).getLast?=some (moveCfg (Cells.result .reverse3To2 memory.1 before)) := path.2.2
  dsimp only [before] at first last
  rw [move_initial] at first
  rw [move_final] at last
  exact ⟨⟨run.map moveCfg,first,path.2.1,last⟩,by rw [List.length_map,Cells.trace_length];rfl⟩

theorem clear_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input backup output counter target : List Bool) :
    ∃ part : Segment caller (state background (.clear 0) memory input backup output counter target)
        (state background .done (memory.1,false,false) input backup output counter []),
      part.trace.length=target.length+2 := by
  let before := StackIso.slots clearRoles.symm (bank background input backup output counter target)
  let run := Cells.trace .clear0 memory before
  have path := cells_path caller .clear0 clearRoles clearLabel memory before rfl
  have first : (run.map clearCfg).head?=some (clearCfg (Cells.initial .clear0 memory before)) := path.1
  have last : (run.map clearCfg).getLast?=some (clearCfg (Cells.result .clear0 memory.1 before)) := path.2.2
  dsimp only [before] at first last
  rw [clear_initial] at first
  rw [clear_final] at last
  exact ⟨⟨run.map clearCfg,first,path.2.1,last⟩,by rw [List.length_map,Cells.trace_length];rfl⟩

theorem unary_path (caller : Statement C) (run : List (PacketUnary.State (C×RatOutput.Store)))
    (before final : PacketUnary.State (C×RatOutput.Store))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (PacketUnary.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map unaryCfg).head?=some (unaryCfg before) ∧
    (run.map unaryCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map unaryCfg).getLast?=some (unaryCfg final) := by
  let old := PacketUnary.program (C:=C×RatOutput.Store) .halt
  let changed := StoreIso.machine (unaryIso C) old
  have storePath := StoreIso.actual_path_on (unaryIso C) old changed run before final first chain last
    (by intro current member point selected;rfl)
  have proper := NativeMulLink.no_early_halt_port changed .done rfl _ _ storePath.2.1 storePath.2.2.1 active
  have linked := LabelMap.actual_path_on unaryLabel changed (program caller)
    _ _ _ storePath.1 storePath.2.1 storePath.2.2.1 (by
      intro current member point selected
      have different : point≠.done := by intro same;subst point;exact proper current member selected
      simp only [unaryLabel,different,ite_false,program]
      rfl)
  simp only [List.map_map,Function.comp_def] at linked
  exact ⟨linked.1,linked.2.1,linked.2.2.1⟩

theorem unary_actual (caller : Statement C) (background : Stack → List Bool) (context : C)
    (registers : Unary.Registers) (rat : RatInput.Store) (flags : RatOutput.Store) (number : Nat) :
    ∃ (memory : Store C) (part : Segment caller
      (state background (.unary (.collect 0)) (((context,registers),rat),flags)
        (B23_4_RatWordPrep.NatField.packet number []) [] [] [] (B23_4_RatWordPrep.NatField.packet number []))
      (state background (.move 3) memory (B23_4_RatWordPrep.NatField.packet number []) []
        (Unary.unary number) [] (B23_4_RatWordPrep.NatField.packet number []))),
      memory.1.1.1=context ∧ part.trace.length ≤ PacketUnary.time number := by
  let input := B23_4_RatWordPrep.NatField.packet number []
  let frame := bank background input [] [] [] input
  obtain ⟨run,final,facts⟩ := PacketUnary.actual_bounded frame (context,flags) registers rat number []
  have path := unary_path caller run _ _ facts.first facts.chain facts.last facts.active
  have actualBank : PacketUnary.entryBank frame number []=frame := by
    funext slot
    fin_cases slot <;> simp [PacketUnary.entryBank,frame,bank,input,packet_equal]
  have firstState : unaryCfg (PacketUnary.entry frame (context,flags) registers rat number [])=
      state background (.unary (.collect 0)) (((context,registers),rat),flags) input [] [] [] input := by
    unfold unaryCfg PacketUnary.entry LabelMap.configuration StoreIso.configuration
    rw [actualBank]
    rfl
  have finalBank : Function.update (PacketUnary.entryBank frame number []) 5 (Unary.unary number)=
      bank background input [] (Unary.unary number) [] input := by
    rw [actualBank]
    funext slot
    fin_cases slot <;> rfl
  have lastState : unaryCfg final=state background (.move 3) (unaryIso C final.var)
      input [] (Unary.unary number) [] input := by
    unfold unaryCfg LabelMap.configuration StoreIso.configuration state
    rw [facts.active,facts.contents,finalBank]
    rfl
  refine ⟨unaryIso C final.var,⟨run.map unaryCfg,path.1.trans (congrArg some firstState),path.2.1,
    path.2.2.trans (congrArg some lastState)⟩,?_,?_⟩
  · change final.var.1.1.1=context
    exact congrArg Prod.fst facts.context_eq
  · simpa only [List.length_map] using facts.count

theorem actual (caller : Statement C) (background : Stack → List Bool) (context : C)
    (registers : Unary.Registers) (rat : RatInput.Store) (flags : RatOutput.Store) (number : Nat) :
    ∃ (memory : PacketUnary.Store C) (run : List (State C)),memory.1.1=context ∧
      run.head?=some (state background (.copy .boot) (((context,registers),rat),flags)
        (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []) ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      run.getLast?=some (state background .done (memory,false,false)
        (B23_4_RatWordPrep.NatField.packet number []) [] [] (Unary.unary number) []) ∧
      run.length ≤ 4*(B23_4_RatWordPrep.NatField.packet number []).length+number+PacketUnary.time number+10 := by
  let input := B23_4_RatWordPrep.NatField.packet number []
  obtain ⟨front,frontCount⟩ := copy_actual caller background (((context,registers),rat),flags) input
  obtain ⟨rawReverse,reverseCount⟩ := reverse_actual caller background (((context,registers),rat),true,true)
    input input.reverse [] [] []
  let reversed : Segment caller _ (state background (.unary (.collect 0))
      (((context,registers),rat),false,false) input [] [] [] input) :=
    ⟨rawReverse.trace,rawReverse.first,rawReverse.chain,by simpa only [List.reverse_reverse,List.append_nil] using rawReverse.last⟩
  obtain ⟨afterUnary,converted,sameContext,convertCount⟩ := unary_actual caller background context registers rat (false,false) number
  obtain ⟨rawMove,moveCount⟩ := move_actual caller background afterUnary input [] (Unary.unary number) [] input
  let moved : Segment caller _ (state background (.clear 0) (afterUnary.1,false,false)
      input [] [] (Unary.unary number) input) :=
    ⟨rawMove.trace,rawMove.first,rawMove.chain,by simpa only [Unary.unary,List.reverse_replicate,List.append_nil] using rawMove.last⟩
  obtain ⟨cleaned,cleanCount⟩ := clear_actual caller background (afterUnary.1,false,false) input [] [] (Unary.unary number) input
  let whole := (((front.append reversed).append converted).append moved).append cleaned
  refine ⟨afterUnary.1,whole.trace,sameContext,whole.first,whole.chain,whole.last,?_⟩
  have a := Segment.append_length front reversed
  have b := Segment.append_length (front.append reversed) converted
  have c := Segment.append_length ((front.append reversed).append converted) moved
  have d := Segment.append_length (((front.append reversed).append converted).append moved) cleaned
  have r : reversed.trace.length=input.length+2 := by
    change rawReverse.trace.length=input.length+2
    simpa only [List.length_reverse] using reverseCount
  have m : moved.trace.length=number+2 := by
    change rawMove.trace.length=number+2
    simpa only [Unary.unary,List.length_replicate] using moveCount
  change whole.trace.length ≤ 4*input.length+number+PacketUnary.time number+10
  dsimp only [whole]
  omega

end RootB234.PrepExponent.NCount
