module

public import B23_4_RatWordPrep_SeqCmp_WordPackQueue_106
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

theorem rat_packet_nonempty (value : Rat) (tail : List Bool) : RatInput.Encoder.packet value tail≠[] := by
  intro empty
  have impossible := congrArg List.head? empty
  change some true=none at impossible
  cases impossible

def TableFrame (slot : RatInput.Stack) : Prop := slot≠13 ∧ slot≠2 ∧ slot≠4

/-- Packet-by-packet reversal restores original channel order without
reversing data bits within any field. Termination reads real finite EOF. -/
theorem actual_table_queue (caller : Statement C) (values : List Rat) (before : State C)
    (active : before.l=some .tableCheck) (scratch : before.stk 4=[])
    (queue : before.stk 2=PacketLists.rats values []) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some (.reverse13 3) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=[] ∧
      final.stk 13=PacketLists.rats values.reverse (before.stk 13) ∧ final.stk 4=[] ∧
      ∀ slot,TableFrame slot→final.stk slot=before.stk slot := by
  induction values generalizing before with
  | nil =>
    let final := checked false before
    let run : Segment caller before final :=
      ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨check_step caller false before active,.singleton _⟩,rfl⟩
    have empty : before.stk 2=[] := queue
    refine ⟨final,run,?_,rfl,empty,rfl,scratch,?_⟩
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
    obtain ⟨next,moveRun,port,context,contents,_time⟩ := actual_packet caller tableLabel RootB234.RatPacketTransport.Public.copy2To13Roles false middle number
      (PacketLists.rats values []) moveActive source scratch
        (by intro point different; simp only [tableLabel,different,ite_false,program])
    have nextQueue : next.stk 2=PacketLists.rats values [] := by rw [contents]; rfl
    have nextScratch : next.stk 4=[] := by rw [contents]; rfl
    have nextTarget : next.stk 13=RatInput.Encoder.packet number (before.stk 13) := by rw [contents]; rfl
    have moveFrame (slot : RatInput.Stack) (n0 : slot≠13) (n3 : slot≠2) (n4 : slot≠4) : next.stk slot=before.stk slot := by
      rw [contents]
      change (if slot=2 then _ else if slot=4 then _ else if slot=13 then _ else before.stk slot)=_
      simp only [n0,n3,n4,ite_false]
    obtain ⟨final,tailRun,finalPort,tailContext,empty,output,temp,frame⟩ := ih next port nextScratch nextQueue
    let whole := (checkRun.append moveRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,empty,?_,temp,?_⟩
    · rw [output,nextTarget,List.reverse_cons,PacketLists.rats_append]
      rfl
    · intro slot safe
      exact (frame slot safe).trans (moveFrame slot safe.1 safe.2.1 safe.2.2)

end B23_4_RatWordPrep.WordPack
