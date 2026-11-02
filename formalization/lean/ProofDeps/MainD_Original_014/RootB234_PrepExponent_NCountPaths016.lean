module

public import RootB234_PrepExponent_NCountCode015

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

theorem transport_path {Λ : Type*} (roles : Stack ≃ Stack) (rename : Λ → Label)
    (old : Λ → TM2.Stmt RatInput.Alphabet Λ (Store C)) (caller : Statement C)
    (allowed : Λ → Prop) (run : List (TM2.Cfg RatInput.Alphabet Λ (Store C)))
    (before final : TM2.Cfg RatInput.Alphabet Λ (Store C))
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step old a=some b))
    (last : run.getLast?=some final)
    (proper : ∀ current∈run.dropLast,∀ point,current.l=some point→allowed point)
    (same : ∀ point,allowed point→program caller (rename point)=
      LabelMap.statement rename (StackIso.statement roles (old point))) :
    let mapCfg := fun current => LabelMap.configuration rename (StackIso.configuration roles current)
    (run.map mapCfg).head?=some (mapCfg before) ∧
    (run.map mapCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map mapCfg).getLast?=some (mapCfg final) := by
  let changed := fun point => StackIso.statement roles (old point)
  have mappedChain := StackIso.chain_configuration_on roles old changed run chain
    (by intro current member point selected; rfl)
  have mappedFirst : (run.map (StackIso.configuration roles)).head?=
      some (StackIso.configuration roles before) := by
    rw [List.head?_map,first,Option.map_some]
  have mappedLast : (run.map (StackIso.configuration roles)).getLast?=
      some (StackIso.configuration roles final) := by
    rw [List.getLast?_map,last,Option.map_some]
  have linked := LabelMap.actual_path_on rename changed (program caller)
    _ _ _ mappedFirst mappedChain mappedLast (by
      intro current member point selected
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact same point (proper original present point selected))
  simp only [List.map_map,Function.comp_def] at linked
  exact ⟨linked.1,linked.2.1,linked.2.2.1⟩

structure Segment (caller : Statement C) (before final : State C) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final

def Segment.edge {caller : Statement C} {before final : State C}
    (step : TM2.step (program caller) before=some final) : Segment caller before final :=
  ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨step,List.isChain_singleton _⟩,rfl⟩

def Segment.append {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    Segment caller before final := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)

theorem Segment.append_length {caller : Statement C} {before middle final : State C}
    (front : Segment caller before middle) (back : Segment caller middle final) :
    (front.append back).trace.length ≤ front.trace.length+back.trace.length := by
  change (front.trace++back.trace.tail).length ≤ _
  simp only [List.length_append,List.length_tail]
  omega


theorem copy_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input : List Bool) :
    ∃ part : Segment caller (state background (.copy .boot) memory input [] [] [] [])
        (state background (.reverse 3) (memory.1,true,true) input input.reverse [] [] []),
      part.trace.length=2*input.length+4 := by
  let oldBackground := StackIso.slots copyRoles.symm (bank background [] [] [] [] [])
  obtain ⟨run,facts⟩ := B23_4_RatWordPrep.WholeCopy.actual_bounded oldBackground memory input [] (background 4)
  have path := transport_path copyRoles copyLabel (B23_4_RatWordPrep.WholeCopy.program .halt) caller
    (fun point => point≠.done) run _ _ facts.first facts.chain facts.last
    (by intro current member point selected same;subst point;exact (facts.proper current member).1 selected)
    (by intro point different;simp only [copyLabel,different,ite_false,program])
  have first : (run.map copyCfg).head?=some (copyCfg
      (B23_4_RatWordPrep.WholeCopy.state oldBackground .boot memory input [] (background 4))) := path.1
  have last : (run.map copyCfg).getLast?=some (copyCfg
      (B23_4_RatWordPrep.WholeCopy.state oldBackground .done (memory.1,true,true) input (input.reverse++[]) (background 4))) := path.2.2
  dsimp only [oldBackground] at first last
  rw [copy_state] at first last
  simp only [copyLabel,ite_true,List.append_nil] at last
  have boot : copyLabel .boot=.copy .boot := rfl
  rw [boot] at first
  exact ⟨⟨run.map copyCfg,first,path.2.1,last⟩,by rw [List.length_map,facts.count]⟩

theorem cells_path (caller : Statement C) (op : Cells.Operation) (roles : Stack ≃ Stack)
    (mapping : Cells.Label → Label) (memory : Store C) (before : Stack → List Bool)
    (agrees : program caller (mapping (Cells.entry op))=
      LabelMap.statement mapping (StackIso.statement roles (Cells.body op))) :
    let run := Cells.trace op memory before
    let cfg := fun current => LabelMap.configuration mapping (StackIso.configuration roles current)
    (run.map cfg).head?=some (cfg (Cells.initial op memory before)) ∧
    (run.map cfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map cfg).getLast?=some (cfg (Cells.result op memory.1 before)) := by
  apply transport_path roles mapping (Cells.program op .halt) caller (fun point => point=Cells.entry op)
    _ _ _ (Cells.trace_head _ _ _) (Cells.trace_chain _ .halt _ _) (Cells.trace_last _ _ _)
  · intro current member point selected
    exact Option.some.inj (selected.symm.trans (Cells.trace_proper op memory before current member))
  · intro point equal
    subst point
    simpa only [Cells.program,ite_true] using agrees

theorem reverse_initial (background : Stack → List Bool) (memory : Store C)
    (input backup output counter target : List Bool) :
    reverseCfg (Cells.initial .reverse3To2 memory
      (StackIso.slots reverseRoles.symm (bank background input backup output counter target)))=
      state background (.reverse 3) memory input backup output counter target := by
  unfold reverseCfg Cells.initial LabelMap.configuration StackIso.configuration
  change (⟨some (.reverse 3),memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem reverse_final (background : Stack → List Bool) (context : PacketUnary.Store C)
    (input backup output counter target : List Bool) :
    reverseCfg (Cells.result .reverse3To2 context
      (StackIso.slots reverseRoles.symm (bank background input backup output counter target)))=
      state background (.unary (.collect 0)) (context,false,false) input [] output counter (backup.reverse++target) := by
  unfold reverseCfg Cells.result Cells.output LabelMap.configuration StackIso.configuration
  change (⟨some (.unary (.collect 0)),(context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem move_initial (background : Stack → List Bool) (memory : Store C)
    (input backup output counter target : List Bool) :
    moveCfg (Cells.initial .reverse3To2 memory
      (StackIso.slots moveRoles.symm (bank background input backup output counter target)))=
      state background (.move 3) memory input backup output counter target := by
  unfold moveCfg Cells.initial LabelMap.configuration StackIso.configuration
  change (⟨some (.move 3),memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem move_final (background : Stack → List Bool) (context : PacketUnary.Store C)
    (input backup output counter target : List Bool) :
    moveCfg (Cells.result .reverse3To2 context
      (StackIso.slots moveRoles.symm (bank background input backup output counter target)))=
      state background (.clear 0) (context,false,false) input backup [] (output.reverse++counter) target := by
  unfold moveCfg Cells.result Cells.output LabelMap.configuration StackIso.configuration
  change (⟨some (.clear 0),(context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_initial (background : Stack → List Bool) (memory : Store C)
    (input backup output counter target : List Bool) :
    clearCfg (Cells.initial .clear0 memory
      (StackIso.slots clearRoles.symm (bank background input backup output counter target)))=
      state background (.clear 0) memory input backup output counter target := by
  unfold clearCfg Cells.initial LabelMap.configuration StackIso.configuration
  change (⟨some (.clear 0),memory,_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem clear_final (background : Stack → List Bool) (context : PacketUnary.Store C)
    (input backup output counter target : List Bool) :
    clearCfg (Cells.result .clear0 context
      (StackIso.slots clearRoles.symm (bank background input backup output counter target)))=
      state background .done (context,false,false) input backup output counter [] := by
  unfold clearCfg Cells.result Cells.output LabelMap.configuration StackIso.configuration
  change (⟨some .done,(context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl


end RootB234.PrepExponent.NCount
