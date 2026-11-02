module

public import RootB234_PrepEntry_ScalarPacketCode_099

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.ScalarPacket
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep PSTRTMRawNat010
open PA17TMRatArithmeticParse002
variable {C : Type*}

structure Path (caller : Statement C) (before final : State C) (bound : Nat) where
  trace : List (State C)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤bound

def Path.append {caller : Statement C} {before middle final : State C} {a b : Nat}
    (front : Path caller before middle a) (back : Path caller middle final b) : Path caller before final (a+b) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.first
    rw [same];rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first];rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have first:=front.count
    have second:=back.count
    simp only [List.length_append,List.length_tail]
    omega

private theorem old_state (mapping : RatDrop.Label→Label) (background : RatInput.Stack→List Bool)
    (point : RatDrop.Label) (context : C) (memory : RatOutput.Store) (source : List Bool) :
    LabelMap.configuration mapping (RatDrop.state background point context memory source (background 3))=
      state (mapping point) context memory background source := by
  change (⟨some (mapping point),(context,memory),_⟩ : State C)=_
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem field_proper (background : RatInput.Stack→List Bool) (context : C) (point next : RatDrop.Label)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    ∀ current∈(RatDrop.fieldTrace false background context point next digits memory source parked).dropLast,
      current.l=some point := by
  induction digits generalizing memory parked with
  | nil =>
    intro current member
    simp only [RatDrop.fieldTrace,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    subst current;rfl
  | cons digit later ih =>
    intro current member
    rw [RatDrop.fieldTrace,List.dropLast_cons_of_ne_nil (RatDrop.field_nonempty false _ _ _ _ _ _ _ _)] at member
    rcases List.mem_cons.mp member with rfl|inside
    · rfl
    · exact ih (true,digit) parked current inside

private theorem field_actual (caller : Statement C) (mapping : RatDrop.Label→Label)
    (point next : RatDrop.Label) (code : RatDrop.program (C:=C) .halt point=RatDrop.fieldBody false point next)
    (same : program caller (mapping point)=LabelMap.statement mapping (RatDrop.program .halt point))
    (background : RatInput.Stack→List Bool) (context : C) (memory : RatOutput.Store) (digits tail : List Bool) :
    ∃ _part : Path caller (state (mapping point) context memory background (leftBlocks digits++false::false::tail))
      (state (mapping next) context (true,false) background tail) (digits.length+2),True := by
  let run:=RatDrop.fieldTrace false background context point next digits memory tail (background 3)
  have first:=RatDrop.field_head false background context point next digits memory tail (background 3)
  have last:=RatDrop.field_last false background context point next digits memory tail (background 3)
  have chain:=RatDrop.field_chain (.halt : RatDrop.Statement C) false background context point next code digits memory tail (background 3)
  have path:=LabelMap.actual_path_on mapping (RatDrop.program .halt) (program caller) run _ _ first chain last
    (by
      intro current member selected active
      have atField:=field_proper background context point next digits memory tail (background 3) current member
      have equal : selected=point:=Option.some.inj (active.symm.trans atField)
      subst selected;exact same)
  have first' : (run.map (LabelMap.configuration mapping)).head?=
      some (state (mapping point) context memory background (leftBlocks digits++false::false::tail)) :=
    path.1.trans (congrArg some (old_state mapping background point context memory _))
  have last' : (run.map (LabelMap.configuration mapping)).getLast?=
      some (state (mapping next) context (true,false) background tail) := by
    simpa only [RatDrop.fieldCopied,Bool.false_eq_true,ite_false,old_state] using path.2.2.1
  refine ⟨⟨run.map (LabelMap.configuration mapping),first',path.2.1,last',?_⟩,trivial⟩
  simpa only [List.length_map,run,RatDrop.field_length] using Nat.le_refl (digits.length+2)

theorem natural_actual (caller : Statement C) (background : RatInput.Stack→List Bool) (context : C)
    (memory : RatOutput.Store) (number : Nat) (tail : List Bool) :
    ∃ _part : Path caller (state .natural context memory background (NatField.packet number tail))
      (state .done context (true,false) background tail) ((PSTRTMNatValue017.rawPayload number).length+4),True := by
  let digits:=PSTRTMNatValue017.rawPayload number
  have boot : TM2.step (program caller) (state .natural context memory background (NatField.packet number tail))=
      some (state (.field true) context memory background (NatField.packet number tail)) := rfl
  let front : Path caller (state .natural context memory background (NatField.packet number tail))
      (state (.field true) context memory background (NatField.packet number tail)) 2 :=
    ⟨[_,_],rfl,List.isChain_cons_cons.mpr ⟨boot,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨back,_⟩:=field_actual caller (fieldLabel true) 4 5 rfl rfl background context memory digits tail
  let whole:=front.append back
  refine ⟨⟨whole.trace,whole.first,whole.chain,whole.last,?_⟩,trivial⟩
  have count:=whole.count
  dsimp only [digits] at count
  omega

theorem rational_actual (caller : Statement C) (background : RatInput.Stack→List Bool) (context : C)
    (memory : RatOutput.Store) (value : Rat) (tail : List Bool) :
    ∃ _part : Path caller (state .rational context memory background (RatInput.Encoder.packet value tail))
      (state .done context (true,false) background tail) (RatInput.Encoder.fieldSize value+6),True := by
  let num:=numeratorDigits value
  let den:=denominatorDigits value
  let middle:=leftBlocks den++false::false::tail
  let before:=RatDrop.state background 3 context memory (RatInput.Encoder.packet value tail) (background 3)
  let after:=RatDrop.state background 4 context (true,sign value) (leftBlocks num++false::false::middle) (background 3)
  have header : TM2.step (RatDrop.program (.halt : RatDrop.Statement C)) before=some after :=
    RatDrop.header_step .halt false 3 4 rfl background context memory (sign value) _ (background 3)
  have transported:=LabelMap.step_configuration_on headerLabel (RatDrop.program .halt) (program caller) before
    (by intro point active;have equal : point=3:=Option.some.inj active.symm;subst point;rfl)
  rw [header,Option.map_some] at transported
  have hFirst : LabelMap.configuration headerLabel before=state .rational context memory background (RatInput.Encoder.packet value tail) :=
    old_state _ _ _ _ _ _
  have hLast : LabelMap.configuration headerLabel after=state (.field false) context (true,sign value) background (leftBlocks num++false::false::middle) :=
    old_state _ _ _ _ _ _
  rw [hFirst,hLast] at transported
  let front : Path caller (state .rational context memory background (RatInput.Encoder.packet value tail))
      (state (.field false) context (true,sign value) background (leftBlocks num++false::false::middle)) 2 :=
    ⟨[_,_],rfl,List.isChain_cons_cons.mpr ⟨transported,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨numerator,_⟩:=field_actual caller (fieldLabel false) 4 5 rfl rfl background context (true,sign value) num middle
  obtain ⟨denominator,_⟩:=field_actual caller denominatorLabel 5 6 rfl rfl background context (true,false) den tail
  let whole:=(front.append numerator).append denominator
  refine ⟨⟨whole.trace,whole.first,whole.chain,whole.last,?_⟩,trivial⟩
  have count:=whole.count
  change whole.trace.length≤num.length+den.length+6
  omega

theorem sign_actual (caller : Statement C) (background : RatInput.Stack→List Bool) (context : C)
    (memory : RatOutput.Store) (value : Rat) (tail : List Bool) :
    ∃ _part : Path caller (state .sign context memory background (RatInput.Encoder.packet value tail))
      (state .done context (true,sign value) background (RatInput.Encoder.packet value tail)) 2,True := by
  have edge : TM2.step (program caller) (state .sign context memory background (RatInput.Encoder.packet value tail))=
      some (state .done context (true,sign value) background (RatInput.Encoder.packet value tail)) := by
    simp only [TM2.step,program,state,TM2.stepAux,bank,Function.update_self,RatInput.Encoder.packet,
      PSTRSymbolicRatExport.packet,RatDrop.capture,List.head?_cons,List.tail_cons]
    congr 2
    funext slot
    fin_cases slot <;> simp [Function.update]
  exact ⟨⟨[_,_],rfl,List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩,trivial⟩

end RootB234.PrepEntry.ScalarPacket
