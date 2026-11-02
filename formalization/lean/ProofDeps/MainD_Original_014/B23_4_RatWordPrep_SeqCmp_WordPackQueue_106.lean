module

public import B23_4_RatWordPrep_SeqCmp_WordPackCalls_104
public import B23_4_RatWordPrep_SeqCmp_PacketLists_090

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def checkSource (wordMode : Bool) : RatInput.Stack := if wordMode then 3 else 2
def checkLabel (wordMode : Bool) : Label := if wordMode then .wordCheck else .tableCheck
def checkYes (wordMode : Bool) : Label := if wordMode then .wordMove 2 else .tableMove 0
def checkNo (wordMode : Bool) : Label := if wordMode then .tableCheck else .reverse13 3

def checked (wordMode : Bool) (before : State C) : State C :=
  ⟨some (if (before.stk (checkSource wordMode)).head?.isSome then checkYes wordMode else checkNo wordMode),
    WordFields.capture before.var (before.stk (checkSource wordMode)).head?,before.stk⟩

theorem check_step (caller : Statement C) (wordMode : Bool) (before : State C)
    (active : before.l=some (checkLabel wordMode)) :
    TM2.step (program caller) before=some (checked wordMode before) := by
  cases before with
  | mk point memory slots =>
    change point=some (checkLabel wordMode) at active
    subst point
    cases wordMode <;> simp [checkLabel,checkSource,checkYes,checkNo,checked,program,
      TM2.step,TM2.stepAux,WordFields.capture,WordFields.present] <;> split_ifs <;> rfl

theorem natural_packet_nonempty (number : Nat) (tail : List Bool) : NatField.packet number tail≠[] := by
  intro empty
  have length := congrArg List.length empty
  simp only [NatField.packet,List.length_append,List.length_cons,List.length_nil,
    PSTRSymbolicRatExport.flagged_length] at length
  omega

theorem check_present (cells : List Bool) (nonempty : cells≠[]) : cells.head?.isSome=true := by
  cases cells with
  | nil => exact (nonempty rfl).elim
  | cons bit rest => rfl

def WordFrame (slot : RatInput.Stack) : Prop := slot≠0 ∧ slot≠3 ∧ slot≠4

/-- Packet-by-packet reversal restores original symbol order without
reversing data bits within any field. Termination reads real finite EOF. -/
theorem actual_word_queue (caller : Statement C) (values : List Nat) (before : State C)
    (active : before.l=some .wordCheck) (scratch : before.stk 4=[])
    (queue : before.stk 3=PacketLists.naturals values []) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some .tableCheck ∧ final.var.2.2=before.var.2.2 ∧ final.stk 3=[] ∧
      final.stk 0=PacketLists.naturals values.reverse (before.stk 0) ∧ final.stk 4=[] ∧
      ∀ slot,WordFrame slot→final.stk slot=before.stk slot := by
  induction values generalizing before with
  | nil =>
    let final := checked true before
    let run : Segment caller before final :=
      ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨check_step caller true before active,.singleton _⟩,rfl⟩
    have empty : before.stk 3=[] := queue
    refine ⟨final,run,?_,rfl,empty,rfl,scratch,?_⟩
    · change some (if (before.stk 3).head?.isSome then _ else _)=_
      rw [empty]
      rfl
    · intro slot safe
      rfl
  | cons number values ih =>
    let middle := checked true before
    let checkRun : Segment caller before middle :=
      ⟨[before,middle],rfl,List.isChain_cons_cons.mpr ⟨check_step caller true before active,.singleton _⟩,rfl⟩
    have source : before.stk 3=NatField.packet number (PacketLists.naturals values []) := queue
    have hasCell : (before.stk 3).head?.isSome=true := by
      rw [source]
      exact check_present _ (natural_packet_nonempty _ _)
    have moveActive : middle.l=some (.wordMove 2) := by
      change some (if (before.stk 3).head?.isSome then _ else _)=_
      rw [hasCell]
      rfl
    obtain ⟨next,moveRun,port,context,contents,_time⟩ := actual_natural caller wordLabel wordRoles middle number
      (PacketLists.naturals values []) moveActive source scratch
        (by intro point different; simp only [wordLabel,different,ite_false,program])
    have nextQueue : next.stk 3=PacketLists.naturals values [] := by rw [contents]; rfl
    have nextScratch : next.stk 4=[] := by rw [contents]; rfl
    have nextTarget : next.stk 0=NatField.packet number (before.stk 0) := by rw [contents]; rfl
    have moveFrame (slot : RatInput.Stack) (n0 : slot≠0) (n3 : slot≠3) (n4 : slot≠4) : next.stk slot=before.stk slot := by
      rw [contents]
      change (if slot=3 then _ else if slot=4 then _ else if slot=0 then _ else before.stk slot)=_
      simp only [n0,n3,n4,ite_false]
    obtain ⟨final,tailRun,finalPort,tailContext,empty,output,temp,frame⟩ := ih next port nextScratch nextQueue
    let whole := (checkRun.append moveRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,empty,?_,temp,?_⟩
    · rw [output,nextTarget,List.reverse_cons,PacketLists.naturals_append]
      rfl
    · intro slot safe
      exact (frame slot safe).trans (moveFrame slot safe.1 safe.2.1 safe.2.2)

end B23_4_RatWordPrep.WordPack
