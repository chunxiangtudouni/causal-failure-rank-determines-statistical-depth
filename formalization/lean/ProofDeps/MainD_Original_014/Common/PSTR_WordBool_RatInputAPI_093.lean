module

public import Common.PSTR_WordBool_RatInputResources_092

/-! Uniform exact original-pair encoder. All resource facts concern the
same actual trace. Its workspace is linear in the two finite field lengths,
with no dependence on the time of an enclosing word/controller loop. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def packet (p : Rat) (tail : List Bool) : List Bool :=
  PSTRSymbolicRatExport.packet (PA17TMRatArithmeticParse002.sign p)
    (PA17TMRatArithmeticParse002.numeratorDigits p) (PA17TMRatArithmeticParse002.denominatorDigits p) tail

def fieldSize (p : Rat) : Nat := (PA17TMRatArithmeticParse002.numeratorDigits p).length+
  (PA17TMRatArithmeticParse002.denominatorDigits p).length

def space (background : RatInput.Stack→List Bool) (p : Rat) (tail scratch : List Bool) : Nat :=
  outside background+tail.length+scratch.length+122*fieldSize p+516

def entry (background : RatInput.Stack→List Bool) (context : C) (memory : RatInput.Store)
    (formatter : WordNatIO.Store) (p : Rat) (tail scratch : List Bool) : State C :=
  ⟨some (.collect 0),((context,memory),formatter),bank background (packet p tail) scratch [] [] [] [] [] [] []⟩

theorem packet_length (p : Rat) (tail : List Bool) : (packet p tail).length=2*fieldSize p+6+tail.length := by
  simp only [packet,PSTRSymbolicRatExport.packet,List.length_cons,List.length_append,RatOutput.flagged_length,
    fieldSize]
  omega

theorem bank_frame (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool)
    (slot : RatInput.Stack) (untouched : ¬Work slot) :
    bank background source scratch numRev denRev numerator denominator raw left counter slot=background slot := by
  simp only [Work,not_or] at untouched
  rcases untouched with ⟨n3,n4,n5,n6,n7,n12,n13,n14,n15⟩
  simp only [bank,n3,n4,n5,n6,n7,n12,n13,n14,n15,ite_false]

theorem program_proper (caller : Statement C) (point : Label) (proper : point≠.done) :
    program caller point=program .halt point := by
  cases point <;> first | rfl | exact False.elim (proper rfl)

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

theorem actual_pair (caller : Statement C) (background : RatInput.Stack→List Bool)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store) (p : Rat) (tail scratch : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry background context memory formatter p tail scratch) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧ final.var.1.1=context ∧
      final.stk=bank background (packet p tail) scratch [] [] [] [] (encode [.rational 1,.rational p]) [] [] ∧
      trace.length≤8*fieldSize p+34 ∧
      (∀ current∈trace,
        (∀ slot,(current.stk slot).length≤space background p tail scratch) ∧
        RatInput.occupied current.stk≤16*space background p tail scratch ∧
        ∀ slot,¬Work slot→current.stk slot=background slot) ∧
      (∀ current∈trace.dropLast, current.l≠some .done ∧
        ∀ point,current.l=some point→
          (∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,
            (∀ slot,(node.2 slot).length≤space background p tail scratch+15) ∧
            ∀ slot,¬Work slot→node.2 slot=background slot) ∧
          ScannerStatement.clock (program caller point) current.var current.stk≤30*(space background p tail scratch+16)) := by
  obtain ⟨trace,first,chain,final,last,active,contextFinal,contentsFinal,count⟩:=
    actual_encode_pair .halt background context memory formatter p tail scratch
  have proper:=NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active
  let before:=entry background context memory formatter p tail scratch
  have head : trace.head?=some before:=first
  have mass : RatInput.occupied before.stk=outside background+(packet p tail).length+scratch.length := by
    dsimp only [before,entry]
    rw [occupied_bank]
    simp only [List.length_nil,Nat.add_zero]
  have bounds:=trace_resources trace before background (RatInput.occupied before.stk) head chain
    (point_mass before.stk) (by intro slot untouched;exact bank_frame _ _ _ _ _ _ _ _ _ _ slot untouched)
  have linear : RatInput.occupied before.stk+15*trace.length≤space background p tail scratch := by
    rw [mass,packet_length]
    change trace.length≤8*fieldSize p+34 at count
    dsimp only [space]
    omega
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤space background p tail scratch :=
    fun current member slot=>((bounds current member).1 slot).trans linear
  refine ⟨trace,final,first,chain_caller caller trace chain proper,last,active,contextFinal,contentsFinal,count,?_,?_⟩
  · intro current member
    exact ⟨bounded current member,occupied_bound current.stk _ (bounded current member),(bounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have notDone : point≠.done:=by intro same;subst point;exact proper current member selected
    rw [program_proper caller point notDone]
    have nodes:=internal_resources current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,nodes.2⟩
    intro node nodeMember
    have nodeFacts:=nodes.1 node nodeMember
    refine ⟨nodeFacts.1,?_⟩
    intro slot untouched
    exact (nodeFacts.2 slot untouched).trans ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

