module

public import B23_4_RatWordPrep_SeqCmp_WordPackQueue_106
public import B23_4_RatWordPrep_SeqCmp_WordPackTable_107
public import B23_4_RatWordPrep_SeqCmp_WordPackMetadata_105

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def naturalWork (values : List Nat) : Nat := (values.map (fun n => 3*(PSTRTMNatValue017.rawPayload n).length+8)).sum+2
def rationalWork (values : List Rat) : Nat := (values.map (fun x => 3*RatInput.Encoder.fieldSize x+16)).sum+2

theorem actual_word_queue (caller : Statement C) (values : List Nat) (before : State C)
    (active : before.l=some .wordCheck) (scratch : before.stk 4=[])
    (queue : before.stk 3=PacketLists.naturals values []) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .tableCheck ∧ final.var.2.2=before.var.2.2 ∧ final.stk 3=[] ∧
      final.stk 0=PacketLists.naturals values.reverse (before.stk 0) ∧ final.stk 4=[] ∧
      (∀ slot,WordFrame slot→final.stk slot=before.stk slot) ∧ run.trace.length≤naturalWork values := by
  induction values generalizing before with
  | nil =>
    let final := checked true before
    let run : Segment caller before final :=
      ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨check_step caller true before active,.singleton _⟩,rfl⟩
    have empty : before.stk 3=[] := queue
    refine ⟨final,run,?_,rfl,empty,rfl,scratch,?_,Nat.le_refl 2⟩
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
    obtain ⟨next,moveRun,port,context,contents,moveTime⟩ := actual_natural caller wordLabel wordRoles middle number
      (PacketLists.naturals values []) moveActive source scratch
        (by intro point different; simp only [wordLabel,different,ite_false,program])
    have nextQueue : next.stk 3=PacketLists.naturals values [] := by rw [contents]; rfl
    have nextScratch : next.stk 4=[] := by rw [contents]; rfl
    have nextTarget : next.stk 0=NatField.packet number (before.stk 0) := by rw [contents]; rfl
    have moveFrame (slot : RatInput.Stack) (n0 : slot≠0) (n3 : slot≠3) (n4 : slot≠4) : next.stk slot=before.stk slot := by
      rw [contents]
      change (if slot=3 then _ else if slot=4 then _ else if slot=0 then _ else before.stk slot)=_
      simp only [n0,n3,n4,ite_false]
    obtain ⟨final,tailRun,finalPort,tailContext,empty,output,temp,frame,tailTime⟩ := ih next port nextScratch nextQueue
    let whole := (checkRun.append moveRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,empty,?_,temp,?_,?_⟩
    · rw [output,nextTarget,List.reverse_cons,PacketLists.naturals_append]
      rfl
    · intro slot safe
      exact (frame slot safe).trans (moveFrame slot safe.1 safe.2.1 safe.2.2)
    · have firstJoin := checkRun.append_length_le moveRun
      have lastJoin := (checkRun.append moveRun).append_length_le tailRun
      have checkTime : checkRun.trace.length=2 := rfl
      change ((checkRun.append moveRun).append tailRun).trace.length≤_
      simp only [naturalWork,List.map_cons,List.sum_cons] at tailTime ⊢
      omega

theorem actual_table_queue (caller : Statement C) (values : List Rat) (before : State C)
    (active : before.l=some .tableCheck) (scratch : before.stk 4=[])
    (queue : before.stk 2=PacketLists.rats values []) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.reverse13 3) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=[] ∧
      final.stk 13=PacketLists.rats values.reverse (before.stk 13) ∧ final.stk 4=[] ∧
      (∀ slot,TableFrame slot→final.stk slot=before.stk slot) ∧ run.trace.length≤rationalWork values := by
  induction values generalizing before with
  | nil =>
    let final := checked false before
    let run : Segment caller before final :=
      ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨check_step caller false before active,.singleton _⟩,rfl⟩
    have empty : before.stk 2=[] := queue
    refine ⟨final,run,?_,rfl,empty,rfl,scratch,?_,Nat.le_refl 2⟩
    · change some (if (before.stk 2).head?.isSome then _ else _)=_
      rw [empty]
      rfl
    · intro slot safe
      rfl
  | cons number values ih =>
    let middle := checked false before
    let checkRun : Segment caller before middle :=
      ⟨[before,middle],rfl,List.isChain_cons_cons.mpr ⟨check_step caller false before active,.singleton _⟩,rfl⟩
    have source : before.stk 2=RatInput.Encoder.packet number (PacketLists.rats values []) := queue
    have hasCell : (before.stk 2).head?.isSome=true := by
      rw [source]
      exact check_present _ (rat_packet_nonempty _ _)
    have moveActive : middle.l=some (.tableMove 0) := by
      change some (if (before.stk 2).head?.isSome then _ else _)=_
      rw [hasCell]
      rfl
    obtain ⟨next,moveRun,port,context,contents,moveTime⟩ := actual_packet caller tableLabel RootB234.RatPacketTransport.Public.copy2To13Roles false middle number
      (PacketLists.rats values []) moveActive source scratch
        (by intro point different; simp only [tableLabel,different,ite_false,program])
    have nextQueue : next.stk 2=PacketLists.rats values [] := by rw [contents]; rfl
    have nextScratch : next.stk 4=[] := by rw [contents]; rfl
    have nextTarget : next.stk 13=RatInput.Encoder.packet number (before.stk 13) := by rw [contents]; rfl
    have moveFrame (slot : RatInput.Stack) (n0 : slot≠13) (n3 : slot≠2) (n4 : slot≠4) : next.stk slot=before.stk slot := by
      rw [contents]
      change (if slot=2 then _ else if slot=4 then _ else if slot=13 then _ else before.stk slot)=_
      simp only [n0,n3,n4,ite_false]
    obtain ⟨final,tailRun,finalPort,tailContext,empty,output,temp,frame,tailTime⟩ := ih next port nextScratch nextQueue
    let whole := (checkRun.append moveRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,empty,?_,temp,?_,?_⟩
    · rw [output,nextTarget,List.reverse_cons,PacketLists.rats_append]
      rfl
    · intro slot safe
      exact (frame slot safe).trans (moveFrame slot safe.1 safe.2.1 safe.2.2)
    · have firstJoin := checkRun.append_length_le moveRun
      have lastJoin := (checkRun.append moveRun).append_length_le tailRun
      have checkTime : checkRun.trace.length=2 := rfl
      change ((checkRun.append moveRun).append tailRun).trace.length≤_
      simp only [rationalWork,List.map_cons,List.sum_cons] at tailTime ⊢
      omega

end B23_4_RatWordPrep.WordPack.Count
