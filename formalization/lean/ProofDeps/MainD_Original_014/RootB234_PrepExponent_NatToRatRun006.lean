module

public import RootB234_PrepExponent_NatToRat005

/-! The real WholeCopy and Cells paths are linked at their actual active
ports. The denominator/header are literal paid pushes. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatToRat
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
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
    (input target : List Bool) :
    ∃ part : Segment caller
        (state background (.copy .boot) memory input [] [] target)
        (state background (.reverse 3) (memory.1,true,true) input [] input.reverse target),
      part.trace.length=2*input.length+4 := by
  let oldBackground := StackIso.slots copyRoles.symm (Function.update background 15 target)
  obtain ⟨run,facts⟩ := B23_4_RatWordPrep.WholeCopy.actual_bounded oldBackground memory input [] []
  have linked := transport_path copyRoles copyLabel (B23_4_RatWordPrep.WholeCopy.program .halt)
    caller (fun point => point≠.done) run _ _ facts.first facts.chain facts.last
    (by
      intro current member point selected equal
      subst point
      exact (facts.proper current member).1 selected)
    (by
      intro point different
      simp only [copyLabel,different,ite_false,program])
  change (run.map copyCfg).head?=_ ∧ _ ∧ _ at linked
  have first := linked.1
  have last := linked.2.2
  change (run.map copyCfg).head?=some (copyCfg
    (B23_4_RatWordPrep.WholeCopy.state oldBackground .boot memory input [] [])) at first
  change (run.map copyCfg).getLast?=some (copyCfg
    (B23_4_RatWordPrep.WholeCopy.state oldBackground .done (memory.1,true,true) input (input.reverse++[]) [])) at last
  dsimp only [oldBackground] at first last
  rw [copy_state] at first last
  simp only [copyLabel,ite_true,List.append_nil] at last
  have boot : copyLabel .boot=.copy .boot := rfl
  rw [boot] at first
  exact ⟨⟨run.map copyCfg,first,linked.2.1,last⟩,by rw [List.length_map,facts.count]⟩

theorem reverse_initial (background : Stack → List Bool) (memory : Store C)
    (input scratch backup target : List Bool) :
    reverseCfg (Cells.initial .reverse3To2 memory
      (StackIso.slots reverseRoles.symm (bank background input scratch backup target)))=
      state background (.reverse 3) memory input scratch backup target := by
  unfold reverseCfg Cells.initial LabelMap.configuration StackIso.configuration
  change (⟨some (.reverse 3),memory,_⟩ : State C)=_
  congr 1
  funext slot
  simp only [StackIso.slots,Equiv.symm_symm,Equiv.apply_symm_apply]

theorem reverse_final (background : Stack → List Bool) (context : C)
    (input scratch backup target : List Bool) :
    reverseCfg (Cells.result .reverse3To2 context
      (StackIso.slots reverseRoles.symm (bank background input scratch backup target)))=
      state background .header (context,false,false) input scratch [] (backup.reverse++target) := by
  unfold reverseCfg Cells.result Cells.output LabelMap.configuration StackIso.configuration
  change (⟨some .header,(context,false,false),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem reverse_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input scratch backup target : List Bool) :
    ∃ part : Segment caller
        (state background (.reverse 3) memory input scratch backup target)
        (state background .header (memory.1,false,false) input scratch [] (backup.reverse++target)),
      part.trace.length=backup.length+2 := by
  let oldBefore := StackIso.slots reverseRoles.symm (bank background input scratch backup target)
  let run := Cells.trace .reverse3To2 memory oldBefore
  have linked := transport_path reverseRoles reverseLabel Cells.Public.reverse3To2 caller
    (fun point => point=3) run _ _ (Cells.trace_head _ _ _) (Cells.trace_chain _ .halt _ _)
    (Cells.trace_last _ _ _)
    (by
      intro current member point selected
      exact Option.some.inj (selected.symm.trans (Cells.trace_proper _ _ _ current member)))
    (by
      intro point equal
      subst point
      rfl)
  change (run.map reverseCfg).head?=_ ∧ _ ∧ _ at linked
  have first := linked.1
  have last := linked.2.2
  change (run.map reverseCfg).head?=some (reverseCfg (Cells.initial .reverse3To2 memory oldBefore)) at first
  change (run.map reverseCfg).getLast?=some (reverseCfg (Cells.result .reverse3To2 memory.1 oldBefore)) at last
  dsimp only [oldBefore] at first last
  rw [reverse_initial] at first
  rw [reverse_final] at last
  refine ⟨⟨run.map reverseCfg,first,linked.2.1,last⟩,?_⟩
  rw [List.length_map,Cells.trace_length]
  rfl

theorem actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (number : Nat) (tail : List Bool) :
    ∃ run : List (State C),
      run.head?=some (state background .prepare memory (B23_4_RatWordPrep.NatField.packet number []) [] [] tail) ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      run.getLast?=some (state background .done (memory.1,false,false)
        (B23_4_RatWordPrep.NatField.packet number []) [] [] (RatInput.Encoder.packet (number : Rat) tail)) ∧
      run.length ≤ 3*(B23_4_RatWordPrep.NatField.packet number []).length+10 := by
  let input := B23_4_RatWordPrep.NatField.packet number []
  let target := true::true::false::false::tail
  let prep := Segment.edge (step_prepare caller background memory input [] [] tail)
  obtain ⟨copyPart,copyCount⟩ := copy_actual caller background memory input target
  obtain ⟨reversePart,reverseCount⟩ := reverse_actual caller background (memory.1,true,true) input [] input.reverse target
  let finish := Segment.edge (step_header caller background (memory.1,false,false) input [] [] (input.reverse.reverse++target))
  let whole := ((prep.append copyPart).append reversePart).append finish
  have output : true::false::(input.reverse.reverse++target)=RatInput.Encoder.packet (number : Rat) tail := by
    simpa only [List.reverse_reverse] using integer_packet number tail
  refine ⟨whole.trace,whole.first,whole.chain,?_,?_⟩
  · simpa only [output] using whole.last
  · have firstBound := Segment.append_length prep copyPart
    have secondBound := Segment.append_length (prep.append copyPart) reversePart
    have thirdBound := Segment.append_length ((prep.append copyPart).append reversePart) finish
    have prepCount : prep.trace.length=2 := rfl
    have finishCount : finish.trace.length=2 := rfl
    dsimp only [whole]
    change (((prep.append copyPart).append reversePart).append finish).trace.length ≤ 3*input.length+10
    rw [List.length_reverse] at reverseCount
    omega

end RootB234.PrepExponent.NatToRat
