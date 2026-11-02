module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeProgram_027a
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeEntry_020e
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeFootprint_028a
public import PaperProofs.Structure.PSTR_HD_CountRefines_049
public import PaperProofs.Structure.PSTR_CountCost_067

/-! The fixed positive-query array executes its actual encoded final HALT.
The one raw-entry witness supplies the original callback reply, every prefix
frame and the original full DynamicRunCorrect certificate, with real ROM and
allocation/code footprint. Arbitrary incoming registers are still permitted. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeProgram027

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeEntry020

theorem original_literal_room {q : Nat} (full : List (Finset (Fin q))) :
    Fits (wordBits full) 8192 := by
  apply PA17PackingBounds043.polynomial_fits
  have hp := (PA17PackingBounds043.powers_le_six full.length q).1
  omega

theorem code_length : (packingCode program).length = 6705 := by
  rw [packingCode_length, program_length]

private theorem terminal_fetch {bits : Nat} (state : WordState bits)
    (words : WordsFit bits (packingCode program)) (pcfit : Fits bits (5 * program.length))
    (pc : state.pc = BitVec.ofNat bits (5 * program.length)) :
    RawTreePreprocessingClaims.fetch program state = haltWords := by
  have hp : state.pc.toNat = 5 * program.length := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcfit]
  change physicalFetch bits (packingCode program) state.pc.toNat = haltWords
  rw [hp, physicalFetch_eq bits _ _ words]
  exact natFetch_halt program

structure HaltedQueryPost {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (initial : WordState (wordBits full)) (countSteps : Nat) : Prop where
  raw : RawQueryPost full command configuration stage hq program initial countSteps
  halt_eq : packingRun (callInput q full command) program
      (queryClock countSteps q (treeSize q full) + 1) initial =
    { packingRun (callInput q full command) program (queryClock countSteps q (treeSize q full)) initial with halted := true }
  halted : (packingRun (callInput q full command) program
    (queryClock countSteps q (treeSize q full) + 1) initial).halted = true
  correct : ReplyCorrect q (callback q full stage configuration.used)
    (replyState q (capacity full) (packingRun (callInput q full command) program
      (queryClock countSteps q (treeSize q full) + 1) initial))
  prefix_legal : ∀ clock < queryClock countSteps q (treeSize q full) + 1,
    let state := packingRun (callInput q full command) program clock initial
    state.halted = false ∧ state.pc.toNat + 4 < (packingCode program).length ∧
      match PackingOp.decode (RawTreePreprocessingClaims.fetch program state) with
      | none => RawTreePreprocessingClaims.fetch program state = haltWords
      | some op => packingAccessFits (callInput q full command) (allocatedWords full) state op
  represents : ∀ clock ≤ queryClock countSteps q (treeSize q full) + 1,
    HeapRepresents q full (capacity full) configuration (packingRun (callInput q full command) program clock initial).heap
  capacityBound : ∀ clock ≤ queryClock countSteps q (treeSize q full) + 1,
    CapacityPrefixBounded q (capacity full)
      (logicalHeap q (capacity full) (packingRun (callInput q full command) program clock initial).heap)
  low : ∀ clock ≤ queryClock countSteps q (treeSize q full) + 1, ∀ physical,
    Fits (wordBits full) physical → physical < workspace full →
      (packingRun (callInput q full command) program clock initial).heap (BitVec.ofNat (wordBits full) physical) =
        initial.heap (BitVec.ofNat (wordBits full) physical)
  high : ∀ clock ≤ queryClock countSteps q (treeSize q full) + 1, ∀ physical,
    Fits (wordBits full) physical → PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical →
      (packingRun (callInput q full command) program clock initial).heap (BitVec.ofNat (wordBits full) physical) =
        initial.heap (BitVec.ofNat (wordBits full) physical)
  table : ∀ clock ≤ queryClock countSteps q (treeSize q full) + 1, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q (capacity full) (packingRun (callInput q full command) program clock initial).heap address =
      logicalHeap q (capacity full) initial.heap address
  trace_eq : packingDynamicTrace (callInput q full command) program
      (queryClock countSteps q (treeSize q full) + 1) initial =
    packingDynamicTrace (callInput q full command) program (queryClock countSteps q (treeSize q full)) initial ++
      haltTrace.map Sum.inl
  trace : (packingDynamicTrace (callInput q full command) program
      (queryClock countSteps q (treeSize q full) + 1) initial).length ≤
    12 * (8 * CapacityBits.width q + 148 + 501 * treeSize q full + PA17A19RuntimeQuery026.tailClock q (treeSize q full)) + 6

theorem halted_of_raw {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (initial : WordState (wordBits full)) (countSteps : Nat)
    (raw : RawQueryPost full command configuration stage hq program initial countSteps) :
    HaltedQueryPost full command configuration stage hq initial countSteps := by
  let rom := callInput q full command
  let T := queryClock countSteps q (treeSize q full)
  let final := packingRun rom program T initial
  have room := original_literal_room full
  have words := code_fit room
  have pcfit := pc_fit room
  have pc : final.pc = BitVec.ofNat (wordBits full) (5 * program.length) := by
    rw [program_length]
    exact raw.pc
  have halt := PSTRCountKernel.halt_at_exit rom program T initial words pcfit raw.active pc
  have fetched := terminal_fetch final words pcfit pc
  have hp : final.pc.toNat = 5 * program.length := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcfit]
  have heaps (clock : Nat) (hc : clock ≤ T + 1) :
      (packingRun rom program clock initial).heap = (packingRun rom program (min clock T) initial).heap := by
    by_cases he : clock ≤ T
    · rw [Nat.min_eq_left he]
    · have heq : clock = T + 1 := by omega
      subst clock
      rw [Nat.min_eq_right (by omega : T ≤ T + 1), halt]
  have trace_eq : packingDynamicTrace rom program (T + 1) initial =
      packingDynamicTrace rom program T initial ++ haltTrace.map Sum.inl := by
    rw [dynamicTrace_succ_right, stepEvents_halt rom program final words hp raw.active]
  refine ⟨raw, halt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trace_eq, ?_⟩
  · exact congrArg WordState.halted halt
  · rw [halt]
    exact raw.correct
  · intro clock hc
    dsimp only
    by_cases he : clock < T
    · rcases raw.safe clock he with ⟨active, inCode, op, decoded, access⟩
      exact ⟨active, inCode, by rw [decoded]; exact access⟩
    · have heq : clock = T := by omega
      subst clock
      refine ⟨raw.active, ?_, ?_⟩
      · change final.pc.toNat + 4 < (packingCode program).length
        rw [hp, packingCode_length]
        omega
      · change match PackingOp.decode (RawTreePreprocessingClaims.fetch program final) with
          | none => RawTreePreprocessingClaims.fetch program final = haltWords
          | some op => packingAccessFits rom (allocatedWords full) final op
        rw [fetched, decode_halt]
  · intro clock hc
    rw [heaps clock hc]
    exact raw.represents (min clock T) (Nat.min_le_right _ _)
  · intro clock hc
    rw [heaps clock hc]
    exact raw.capacityBound (min clock T) (Nat.min_le_right _ _)
  · intro clock hc physical hfit hphysical
    rw [heaps clock hc]
    exact raw.low (min clock T) (Nat.min_le_right _ _) physical hfit hphysical
  · intro clock hc physical hfit hphysical
    rw [heaps clock hc]
    exact raw.high (min clock T) (Nat.min_le_right _ _) physical hfit hphysical
  · intro clock hc address ha
    rw [heaps clock hc]
    exact raw.table (min clock T) (Nat.min_le_right _ _) address ha
  · rw [trace_eq, List.length_append, List.length_map, haltTrace_length]
    exact Nat.add_le_add_right raw.trace 6

theorem actual_halted_query {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (hq : 0 < q) (hl : LaminarSchedule full) (initial : WordState (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat (wordBits full) 0) (ha : initial.halted = false) :
    ∃ countSteps, HaltedQueryPost full command configuration (cursor full configuration command allowed) hq initial countSteps := by
  have room := original_literal_room full
  obtain ⟨countSteps, raw⟩ := actual_raw_query full command configuration allowed program
    contains_bootstrap contains_counts (embedded_header room) (embedded_tests room) (embedded_ranks room)
    (embedded_selector room) (embedded_footer room) hq hl initial rep hp ha
  exact ⟨countSteps, halted_of_raw full command configuration _ hq initial countSteps raw⟩

theorem dynamic_of_halted {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (heap : BitVec (wordBits full) → BitVec (wordBits full)) (countSteps : Nat)
    (post : HaltedQueryPost full command configuration stage hq (packingInitial heap) countSteps) :
    RawTreePreprocessingClaims.DynamicRunCorrect (allocatedWords full) (callInput q full command) program
      (queryClock countSteps q (treeSize q full) + 1) heap := by
  refine ⟨code_fit (original_literal_room full), PA17A19RuntimeFootprint028.callInput_words_fit full command,
    ?_, post.halted, post.prefix_legal⟩
  rw [code_length]
  exact PA17A19RuntimeFootprint028.call_footprint_8192 full command

theorem actual_dynamic_query {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ countSteps,
      RawTreePreprocessingClaims.DynamicRunCorrect (allocatedWords full) (callInput q full command) program
        (queryClock countSteps q (treeSize q full) + 1) heap ∧
      HaltedQueryPost full command configuration (cursor full configuration command allowed) hq (packingInitial heap) countSteps := by
  obtain ⟨countSteps, post⟩ := actual_halted_query full command configuration allowed hq hl (packingInitial heap) rep rfl rfl
  exact ⟨countSteps, dynamic_of_halted full command configuration _ hq heap countSteps post, post⟩

theorem halted_steps_bound {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (initial : WordState (wordBits full)) (countSteps : Nat)
    (post : HaltedQueryPost full command configuration stage hq initial countSteps) :
    queryClock countSteps q (treeSize q full) + 1 ≤ 1786 * liveWork q (treeSize q full) := by
  have ht := PSTRWidthOriginal.positive_tree_size full hq
  have hwork : 1 ≤ liveWork q (treeSize q full) := by
    simp only [liveWork, ne_of_gt hq, ite_false, queryWork]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) ht)
  have hcount : countSteps ≤ 575 * liveWork q (treeSize q full) :=
    post.raw.entry.upper.trans (PSTRCountCost.active_bound_work full hq)
  have htail : PA17A19RuntimeQuery026.tailClock q (treeSize q full) ≤ 1128 * liveWork q (treeSize q full) := by
    simpa only [liveWork, ne_of_gt hq, ite_false, queryWork] using
      PA17A19RuntimeQuery026.tailClock_bound q (treeSize q full) ht
  unfold queryClock
  omega

theorem halted_call_cost {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (heap : BitVec (wordBits full) → BitVec (wordBits full)) (countSteps : Nat)
    (post : HaltedQueryPost full command configuration stage hq (packingInitial heap) countSteps) :
    callCost q full program command (queryClock countSteps q (treeSize q full) + 1) heap ≤
      32768 * liveWork q (treeSize q full) := by
  have hs := halted_steps_bound full command configuration stage hq (packingInitial heap) countSteps post
  have ht := packingDynamicTrace_length_le (callInput q full command) program
    (queryClock countSteps q (treeSize q full) + 1) (packingInitial heap)
  have hwork : 1 ≤ liveWork q (treeSize q full) := by
    have ht := PSTRWidthOriginal.positive_tree_size full hq
    simp only [liveWork, ne_of_gt hq, ite_false, queryWork]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) ht)
  unfold callCost
  rw [code_length]
  omega

theorem query_call_claims_of_halted {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (allowed : Allowed full configuration .query) (hq : 0 < q)
    (heap : BitVec (wordBits full) → BitVec (wordBits full)) (countSteps : Nat)
    (post : HaltedQueryPost full .query configuration (cursor full configuration .query allowed) hq
      (packingInitial heap) countSteps) :
    CallClaims 32768 q full (capacity full) (allocatedWords full) program configuration .query
      (queryClock countSteps q (treeSize q full) + 1) heap := by
  refine ⟨dynamic_of_halted full .query configuration _ hq heap countSteps post,
    halted_call_cost full .query configuration _ hq heap countSteps post, ?_, ?_, ?_, ?_⟩
  · exact post.represents _ le_rfl
  · intro address ha _
    exact post.table _ le_rfl address ha
  · intro clock hc _
    exact post.capacityBound clock hc
  · intro h
    have he : (⟨configuration.stage, h⟩ : Fin (full.length + 1)) = cursor full configuration .query allowed := by
      apply Fin.ext
      rfl
    rw [he]
    exact post.correct

theorem actual_query_call_claims {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (allowed : Allowed full configuration .query)
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ steps, CallClaims 32768 q full (capacity full) (allocatedWords full) program configuration .query steps heap := by
  obtain ⟨countSteps, _, post⟩ := actual_dynamic_query full .query configuration allowed hq hl heap rep
  exact ⟨queryClock countSteps q (treeSize q full) + 1,
    query_call_claims_of_halted full configuration allowed hq heap countSteps post⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeProgram027
