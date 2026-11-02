module

public import PSTR_WordBool_WordOutput_Contexts_001

/-! Same actual final serializer trace and linear field-size resources,
with callerC and both Bool registers readonly even at internal nodes. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+32) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C)
    (background : Stack → List Bool) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frames : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,
      (∀ slot,(current.stk slot).length≤bound+32*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have equal : firstState=before:=Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      refine ⟨?_,frames⟩
      intro slot
      exact (bounded slot).trans (by simp)
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources before next bound edge bounded
      have nextFrames : ∀ slot,¬Work slot→next.stk slot=background slot :=
        fun slot untouched=>(step.2 slot untouched).trans (frames slot untouched)
      intro current member
      rcases List.mem_cons.mp member with same|later
      · subst current
        exact ⟨fun slot=>(bounded slot).trans (Nat.le_add_right _ _),frames⟩
      · have tail:=ih next (bound+32) rfl tailChain step.1 nextFrames current later
        refine ⟨?_,tail.2⟩
        intro slot
        have perSlot:=tail.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+32) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤64*(bound+33) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched node member
  · have clock:=ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
      (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

theorem chain_caller (caller : Statement C) (trace : List (State C))
    (chain : trace.IsChain (fun a b=>TM2.step (program .halt) a=some b))
    (proper : ∀ current∈trace.dropLast,current.l≠some .done) :
    trace.IsChain (fun a b=>TM2.step (program caller) a=some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons before rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      refine List.isChain_cons_cons.mpr ⟨?_,ih tailChain ?_⟩
      · have beforeProper:=proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self)
        cases before with
        | mk position memory contents =>
          cases position with
          | none => cases edge
          | some point =>
            have notDone : point≠.done:=by intro same;subst point;exact beforeProper rfl
            change some (TM2.stepAux (program caller point) memory contents)=some next
            rw [program_proper caller point notDone]
            exact edge
      · intro current member
        apply proper current
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ member

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    after.var.1.1=before.var.1.1 := by
  cases before with
  | mk position memory contents=>
    cases position with
    | none=>cases edge
    | some point=>
      have same : after=TM2.stepAux (program .halt point) memory contents:=(Option.some.inj edge).symm
      subst after
      exact nodes_readonly _ (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b=>TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,current.var.1.1=before.var.1.1 := by
  induction trace generalizing before with
  | nil=>simp
  | cons firstState rest ih=>
    have same : firstState=before:=Option.some.inj first
    subst firstState
    cases rest with
    | nil=>intro current member;have same:=List.mem_singleton.mp member;subst current;rfl
    | cons next rest=>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)

theorem actual_output (caller : Statement C) (background : Stack → List Bool) (context : C) (hit map : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (r : Rat) (tail scratch : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry background context hit map memory formatter r tail scratch) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧ final.var.1.1=(context,hit,map) ∧
      final.stk=RatInput.Encoder.bank background (RatInput.Encoder.packet r tail) scratch [] [] [] []
        (encode [.rational r,boolDatum hit,boolDatum map]) [] [] ∧
      trace.length≤8*fieldSize r+40 ∧
      (∀ current∈trace,current.var.1.1=(context,hit,map) ∧
        (∀ slot,(current.stk slot).length≤space background r tail scratch) ∧
        RatInput.occupied current.stk≤16*space background r tail scratch ∧
        ∀ slot,¬Work slot→current.stk slot=background slot) ∧
      (∀ current∈trace.dropLast,current.l≠some .done ∧
        ∀ point,current.l=some point→
          (∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,
            node.1.1.1=(context,hit,map) ∧
            (∀ slot,(node.2 slot).length≤space background r tail scratch+32) ∧
            ∀ slot,¬Work slot→node.2 slot=background slot) ∧
          ScannerStatement.clock (program caller point) current.var current.stk≤64*(space background r tail scratch+33)) := by
  obtain ⟨trace,first,chain,last,count⟩:=actual_fields .halt background context hit map memory formatter
    (PA17TMRatArithmeticParse002.sign r) (PA17TMRatArithmeticParse002.numeratorDigits r)
    (PA17TMRatArithmeticParse002.denominatorDigits r) tail scratch
  let final : State C:=⟨some .done,
    (((context,hit,map),(PSTRSymbolicNaturalExport.finalBit
      (RatOutput.outputLeft (PA17TMRatArithmeticParse002.sign r) (PA17TMRatArithmeticParse002.numeratorDigits r)
        (PA17TMRatArithmeticParse002.denominatorDigits r)) false,true,PA17TMRatArithmeticParse002.sign r)),(false,false)),
    RatInput.Encoder.bank background (RatInput.Encoder.packet r tail) scratch [] [] [] []
      (output (PA17TMRatArithmeticParse002.sign r) (PA17TMRatArithmeticParse002.numeratorDigits r)
        (PA17TMRatArithmeticParse002.denominatorDigits r) hit map) [] []⟩
  have proper:=NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last rfl
  let before:=entry background context hit map memory formatter r tail scratch
  have mass : RatInput.occupied before.stk=RatInput.Encoder.outside background+
      (RatInput.Encoder.packet r tail).length+scratch.length := by
    dsimp only [before,entry]
    rw [RatInput.Encoder.occupied_bank]
    simp only [List.length_nil,Nat.add_zero]
  have bounds:=trace_resources trace before background (RatInput.occupied before.stk) first chain
    (RatInput.Encoder.point_mass before.stk)
    (by intro slot untouched;exact RatInput.Encoder.bank_frame _ _ _ _ _ _ _ _ _ _ slot untouched)
  have contexts:=trace_context trace before first chain
  have linear : RatInput.occupied before.stk+32*trace.length≤space background r tail scratch := by
    rw [mass,RatInput.Encoder.packet_length]
    change trace.length≤8*fieldSize r+40 at count
    dsimp only [space,fieldSize] at count ⊢
    omega
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤space background r tail scratch :=
    fun current member slot=>((bounds current member).1 slot).trans linear
  refine ⟨trace,final,first,chain_caller caller trace chain proper,last,rfl,rfl,?_,count,?_,?_⟩
  · change RatInput.Encoder.bank _ _ _ _ _ _ _ _ _ _= _
    rw [output_original]
  · intro current member
    exact ⟨contexts current member,bounded current member,
      RatInput.Encoder.occupied_bound current.stk _ (bounded current member),(bounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have notDone : point≠.done:=by intro same;subst point;exact proper current member selected
    rw [program_proper caller point notDone]
    have nodes:=internal_resources current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,nodes.2⟩
    intro node nodeMember
    have nodeFacts:=nodes.1 node nodeMember
    refine ⟨?_,nodeFacts.1,?_⟩
    · exact (nodes_readonly _ (program_readonly point) current.var current.stk node nodeMember).trans
        (contexts current (List.mem_of_mem_dropLast member))
    · intro slot untouched
      exact (nodeFacts.2 slot untouched).trans ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
