module

public import B23_4_RatWordPrep_SeqCmp_WordFoldStep_122

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def checked (before : State C) : State C :=
  ⟨some (if (before.stk 0).head?.isSome then .falseLookup .boot else .done),
    capture before.var (before.stk 0).head?,before.stk⟩

theorem check_step (caller : Statement C) (before : State C) (active : before.l=some .check) :
    TM2.step (program caller) before=some (checked before) := by
  cases before with
  | mk point memory slots =>
    change point=some .check at active
    subst point
    simp [checked,program,TM2.step,TM2.stepAux,capture,present,WordFields.capture,WordFields.present]
    split_ifs <;> rfl

def value (E : BinaryExperiment) (symbols : List (Fin E.alphabetSize)) (odds : Rat) : Rat :=
  symbols.foldl (stepOdds E) odds

/-- The only runtime loop test is physical query0 EOF. Each actual symbol
step consumes one actual natural packet, and the same fixed source
produces the normalized odds fold. The list is proof-side stream data. -/
theorem actual_loop (caller : Statement C) (E : BinaryExperiment) (symbols : List (Fin E.alphabetSize))
    (before : State C) (odds : Rat) (metadataTail : List Bool)
    (active : before.l=some .check)
    (query : before.stk 0=PacketLists.naturals (symbols.map Fin.val) [])
    (metadata : before.stk 1=NatField.packet E.alphabetSize metadataTail)
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some .done ∧ final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=[] ∧
      final.stk 1=before.stk 1 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet (value E symbols odds) [] ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) := by
  induction symbols generalizing before odds with
  | nil =>
    let final := checked before
    let run : Segment caller before final :=
      ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨check_step caller before active,.singleton _⟩,rfl⟩
    have empty : before.stk 0=[] := query
    refine ⟨final,run,?_,rfl,empty,rfl,rfl,packet,rfl,owned⟩
    change some (if (before.stk 0).head?.isSome then _ else _)=_
    rw [empty]
    rfl
  | cons symbol symbols ih =>
    let middle := checked before
    let checkRun : Segment caller before middle :=
      ⟨[before,middle],rfl,List.isChain_cons_cons.mpr ⟨check_step caller before active,.singleton _⟩,rfl⟩
    let rest := PacketLists.naturals (symbols.map Fin.val) []
    have source : before.stk 0=NatField.packet symbol.val rest := query
    have hasCell : (before.stk 0).head?.isSome=true := by
      rw [source]
      exact WordPack.check_present _ (WordPack.natural_packet_nonempty _ _)
    have atLookup : middle.l=some (.falseLookup .boot) := by
      change some (if (before.stk 0).head?.isSome then _ else _)=_
      rw [hasCell]
      rfl
    obtain ⟨next,symbolRun,atCheck,context,nextQuery,nextMeta,nextTable,nextPacket,scratch,nextOwned⟩ :=
      actual_symbol caller E symbol middle odds rest metadataTail atLookup source metadata table packet owned
    obtain ⟨final,tailRun,finalPort,tailContext,empty,finalMeta,finalTable,finalPacket,finalScratch,finalOwned⟩ :=
      ih next (stepOdds E odds symbol) atCheck nextQuery (nextMeta.trans metadata) (nextTable.trans table) nextPacket nextOwned
    let whole := (checkRun.append symbolRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,empty,
      finalMeta.trans nextMeta,finalTable.trans nextTable,finalPacket,finalScratch.trans scratch,finalOwned⟩

end B23_4_RatWordPrep.WordFold
