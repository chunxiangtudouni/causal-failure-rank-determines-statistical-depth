module

public import B23_4_RatWordPrep_SeqCmp_WordFoldCountSymbol_184
public import B23_4_RatWordPrep_SeqCmp_WordFoldLoop_123

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def loopBudget (caller : Statement C) (number bound count : Nat) : Nat :=
  2+count*(symbolBudget caller number bound+2)

/-- The only runtime loop test is physical query0 EOF. Each actual symbol
step consumes one actual natural packet, and the same fixed source
produces the normalized odds fold. The list is proof-side stream data. -/
theorem actual_loop (caller : Statement C) (E : BinaryExperiment) (symbols : List (Fin E.alphabetSize))
    (target : Rat) (word : E.StoppedWord) (before : State C) (odds : Rat)
    (active : before.l=some .check)
    (query : before.stk 0=PacketLists.naturals (symbols.map Fin.val) [])
    (metadata : before.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []))
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) [])
    (packet : before.stk 15=RatInput.Encoder.packet odds [])
    (owned : ∀ slot,Owned slot→before.stk slot=[])
    (count : symbols.length≤(wordInput E target word).length)
    (width : potential E symbols odds≤8*((wordInput E target word).length+1)^2)
    (safe : CounterSafe (wordInput E target word).length before.stk) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .done ∧ final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=[] ∧
      final.stk 1=before.stk 1 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet (value E symbols odds) [] ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      CounterSafe (wordInput E target word).length final.stk ∧
      run.trace.length≤loopBudget caller E.alphabetSize (wordInput E target word).length symbols.length := by
  induction symbols generalizing before odds with
  | nil =>
    let final := checked before
    let run : Segment caller before final :=
      ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨check_step caller before active,.singleton _⟩,rfl⟩
    have empty : before.stk 0=[] := query
    refine ⟨final,run,?_,rfl,empty,rfl,rfl,packet,rfl,owned,safe,by
      change 2≤loopBudget caller E.alphabetSize (wordInput E target word).length 0
      simp [loopBudget]⟩
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
    have oddsWidth : RatInput.Encoder.fieldSize odds≤8*((wordInput E target word).length+1)^2 := by
      unfold potential at width
      omega
    have currentMass := canonical_mass E target word (symbol::symbols) before odds count query metadata table packet owned safe oddsWidth
    obtain ⟨next,symbolRun,atCheck,context,nextQuery,nextMeta,nextTable,nextPacket,scratch,nextOwned,nextSafe,symbolTime⟩ :=
      actual_symbol caller E symbol target word middle odds rest (RatInput.Encoder.packet target []) atLookup source metadata table packet owned safe currentMass oddsWidth
    obtain ⟨final,tailRun,finalPort,tailContext,empty,finalMeta,finalTable,finalPacket,finalScratch,finalOwned,finalSafe,tailTime⟩ :=
      ih next (stepOdds E odds symbol) atCheck nextQuery (nextMeta.trans metadata) (nextTable.trans table) nextPacket nextOwned
        (by simp only [List.length_cons] at count; omega) ((potential_step E symbol symbols odds).trans width) nextSafe
    let whole := (checkRun.append symbolRun).append tailRun
    refine ⟨final,whole,finalPort,tailContext.trans context,empty,
      finalMeta.trans nextMeta,finalTable.trans nextTable,finalPacket,finalScratch.trans scratch,finalOwned,finalSafe,?_⟩
    have j2 := checkRun.append_length_le symbolRun
    have j3 := (checkRun.append symbolRun).append_length_le tailRun
    have checkTime : checkRun.trace.length=2 := rfl
    change ((checkRun.append symbolRun).append tailRun).trace.length≤_
    simp only [loopBudget,List.length_cons] at tailTime ⊢
    nlinarith

end B23_4_RatWordPrep.WordFold.Count
