module

public import B23_4_RatWordPrep_SeqCmp_LookupCountCalls_173
public import B23_4_RatWordPrep_SeqCmp_PacketLists_090

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def restoreWork (values : List Rat) : Nat := (values.map (fun x => 3*RatInput.Encoder.fieldSize x+16)).sum+4

theorem actual_restore (truth : Bool) (caller : Statement C) (values : List Rat) (before : State C)
    (tail : List Bool) (active : before.l=some .restore) (scratch : before.stk 4=[])
    (archive : before.stk 15=PacketLists.rats values (false::tail)) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some (.selected 0) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 15=tail ∧
      final.stk 2=PacketLists.rats values.reverse (before.stk 2) ∧ final.stk 4=[] ∧
      (∀ slot,RestoreFrame slot→final.stk slot=before.stk slot) ∧ run.trace.length≤restoreWork values := by
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
    refine ⟨final,whole,rfl,rfl,?_,?_,?_,?_,by exact (by decide : 3≤4)⟩
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
    obtain ⟨next,moveRun,port,context,contents,moveTime⟩ := actual_packet truth caller restoreLabel
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
    obtain ⟨final,tailRun,finalPort,tailContext,finalArchive,finalTable,finalScratch,finalFrame,tailTime⟩ :=
      ih next port nextScratch nextArchive
    let whole := (peek.append moveRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,finalArchive,?_,finalScratch,?_,?_⟩
    · rw [finalTable,nextTable,List.reverse_cons,PacketLists.rats_append]
      rfl
    · intro slot safe
      exact (finalFrame slot safe).trans (nextFrame slot safe.1 safe.2.1 safe.2.2)
    · have j2 := append_length_le peek moveRun
      have j3 := append_length_le (peek.append moveRun) tailRun
      have peekTime : peek.trace.length=2 := rfl
      change ((peek.append moveRun).append tailRun).trace.length≤_
      simp only [restoreWork,List.map_cons,List.sum_cons] at tailTime ⊢
      omega

end B23_4_RatWordPrep.Lookup.Count
