module

public import B23_4_RatWordPrep_SeqCmp_LookupPackets_093
public import B23_4_RatWordPrep_SeqCmp_PacketLists_090

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def peekState (before : State C) (cell : Bool) : State C :=
  ⟨some (if cell then .restoreMove 0 else .unmark),WordFields.capture before.var (some cell),before.stk⟩

theorem peek_step (truth : Bool) (caller : Statement C) (before : State C) (cell : Bool) (rest : List Bool)
    (active : before.l=some .restore) (head : before.stk 15=cell::rest) :
    TM2.step (program truth caller) before=some (peekState before cell) := by
  cases before with
  | mk point memory slots =>
    change point=some .restore at active
    subst point
    change slots 15=cell::rest at head
    cases cell <;> simp [TM2.step,TM2.stepAux,program,peekState,WordFields.capture,bit,head]

def unmarkState (before : State C) (tail : List Bool) : State C :=
  ⟨some (.selected 0),WordFields.capture before.var (some false),Function.update before.stk 15 tail⟩

theorem unmark_step (truth : Bool) (caller : Statement C) (before : State C) (tail : List Bool)
    (active : before.l=some .unmark) (head : before.stk 15=false::tail) :
    TM2.step (program truth caller) before=some (unmarkState before tail) := by
  cases before with
  | mk point memory slots =>
    change point=some .unmark at active
    subst point
    change slots 15=false::tail at head
    simp only [TM2.step,program,TM2.stepAux,head,List.head?_cons,List.tail_cons,unmarkState]

def RestoreFrame (slot : RatInput.Stack) : Prop := slot≠2 ∧ slot≠4 ∧ slot≠15

theorem actual_restore (truth : Bool) (caller : Statement C) (values : List Rat) (before : State C)
    (tail : List Bool) (active : before.l=some .restore) (scratch : before.stk 4=[])
    (archive : before.stk 15=PacketLists.rats values (false::tail)) :
    ∃ (final : State C) (_run : Segment truth caller before final),
      final.l=some (.selected 0) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 15=tail ∧
      final.stk 2=PacketLists.rats values.reverse (before.stk 2) ∧ final.stk 4=[] ∧
      ∀ slot,RestoreFrame slot→final.stk slot=before.stk slot := by
  induction values generalizing before with
  | nil =>
    have head : before.stk 15=false::tail := archive
    let middle := peekState before false
    let peek : Segment truth caller before middle :=
      ⟨[before,middle],rfl,List.isChain_cons_cons.mpr ⟨peek_step truth caller before false tail active head,.singleton _⟩,rfl⟩
    let final := unmarkState middle tail
    let pop : Segment truth caller middle final :=
      ⟨[middle,final],rfl,List.isChain_cons_cons.mpr ⟨unmark_step truth caller middle tail rfl head,.singleton _⟩,rfl⟩
    let whole := peek.append pop
    refine ⟨final,whole,rfl,rfl,?_,?_,?_,?_⟩
    · rfl
    · rfl
    · change before.stk 4=[]
      exact scratch
    · intro slot safe
      change Function.update before.stk 15 tail slot=before.stk slot
      exact Function.update_of_ne safe.2.2 _ _
  | cons x values ih =>
    let rest := PacketLists.rats values (false::tail)
    have source : before.stk 15=RatInput.Encoder.packet x rest := archive
    have head : before.stk 15=true::(RatInput.Encoder.packet x rest).tail := by
      rw [source]
      rfl
    let middle := peekState before true
    let peek : Segment truth caller before middle :=
      ⟨[before,middle],rfl,List.isChain_cons_cons.mpr ⟨peek_step truth caller before true _ active head,.singleton _⟩,rfl⟩
    obtain ⟨next,moveRun,port,context,contents,_time⟩ := actual_packet truth caller restoreLabel
      RootB234.RatPacketTransport.Public.move15To2Roles false middle x rest rfl source scratch
      (by intro point different; simp only [restoreLabel,different,ite_false,program]; rfl)
    have nextArchive : next.stk 15=PacketLists.rats values (false::tail) := by rw [contents]; rfl
    have nextScratch : next.stk 4=[] := by rw [contents]; rfl
    have nextTable : next.stk 2=RatInput.Encoder.packet x (before.stk 2) := by rw [contents]; rfl
    have nextFrame (slot : RatInput.Stack) (n2 : slot≠2) (n4 : slot≠4) (n15 : slot≠15) :
        next.stk slot=before.stk slot := by
      rw [contents]
      change (if slot=15 then _ else if slot=4 then _ else if slot=2 then _ else before.stk slot)=_
      simp only [n2,n4,n15,ite_false]
    obtain ⟨final,tailRun,finalPort,tailContext,finalArchive,finalTable,finalScratch,finalFrame⟩ :=
      ih next port nextScratch nextArchive
    let whole := (peek.append moveRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,finalArchive,?_,finalScratch,?_⟩
    · rw [finalTable,nextTable,List.reverse_cons,PacketLists.rats_append]
      rfl
    · intro slot safe
      exact (finalFrame slot safe).trans (nextFrame slot safe.1 safe.2.1 safe.2.2)

end B23_4_RatWordPrep.Lookup
