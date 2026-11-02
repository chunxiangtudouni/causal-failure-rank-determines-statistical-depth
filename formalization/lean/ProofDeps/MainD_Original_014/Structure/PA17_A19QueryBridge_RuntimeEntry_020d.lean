module

public import Structure.PA17_A19QueryBridge_RuntimeEntry_020c
public import Structure.PSTR_ArbitrarySafe_101

/-! The SAME arbitrary-register count witness supplies all persistent data
and every actual decoded/access-safe prefix through the82-op Header.
No second existential count run, scratch oracle, or free register reset is used. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

abbrev allocatedWords {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  physicalHeaderWords + packedCapacityWords q (capacity full) (wordBits full) +
    8192 * (full.length + q + treeSize q full + 1)

private theorem packing_access_mono {bits : Nat} (rom : PhysicalROM) (small large : Nat)
    (hroom : small ≤ large) (state : WordState bits) (op : PackingOp)
    (safe : packingAccessFits rom small state op) : packingAccessFits rom large state op := by
  cases op with
  | base operation =>
    cases operation with
    | subtract target first second => trivial
    | base instruction =>
      cases instruction with
      | loadROM region target pointer => exact safe
      | loadHeap target pointer => exact lt_of_lt_of_le safe hroom
      | storeHeap pointer source => exact lt_of_lt_of_le safe hroom
      | constant target value => trivial
      | add target first second => trivial
      | minimum target first second => trivial
      | select target condition first second => trivial
  | arithmetic operation target first second => trivial
  | jumpIfZero condition target => trivial

private theorem at_safe_mono {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (small large : Nat) (hroom : small ≤ large) (state : WordState bits)
    (safe : PSTRCountKernel.AtSafe rom whole small state) :
    PSTRCountKernel.AtSafe rom whole large state := by
  rcases safe with ⟨active, inCode, op, decoded, access⟩
  exact ⟨active, inCode, op, decoded, packing_access_mono rom small large hroom state op access⟩

theorem actual_raw_header_safe {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (co : PSTROuterCountCode.Contains whole 61)
    (em : PA17A19RuntimeHeader011.Embedded (wordBits full) 539 whole)
    (hq : 0 < q) (hl : LaminarSchedule full) (initial : WordState (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat (wordBits full) 0) (ha : initial.halted = false) :
    ∃ countSteps,
      RawHeaderPost full command configuration (cursor full configuration command allowed) hq whole initial countSteps ∧
      (∀ clock < countSteps + 82,
        PSTRCountKernel.AtSafe (callInput q full command) whole (allocatedWords full)
          (packingRun (callInput q full command) whole clock initial)) := by
  let rom := callInput q full command
  let stage := cursor full configuration command allowed
  obtain ⟨steps, lower, upper, complete, frames, _, table, safe⟩ := PSTRArbitrarySafe.actual_complete full command
    configuration whole cb co em.words em.pcfit hq hl initial rep hp ha
  let counted := packingRun rom whole steps initial
  have hh := from_counts full command configuration stage hq hl whole em counted complete rfl
  have hbase : PSTRCountWorkspace.base q full (capacity full) (wordBits full) = workspace full :=
    PSTRCountWorkspace.base_metadata_end q full hq (capacity full) (wordBits full)
  have lowhigh (clock : Nat) (hc : clock ≤ steps) (physical : Nat) (hfit : Fits (wordBits full) physical)
      (hposition : physical < workspace full ∨ PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q ≤ physical) :
      (packingRun rom whole clock initial).heap (BitVec.ofNat (wordBits full) physical) =
        initial.heap (BitVec.ofNat (wordBits full) physical) := by
    apply (frames clock hc).2 physical hfit
    rw [hbase]
    simpa only [treeSize, ne_of_gt hq, ite_false] using hposition
  have prefixRep (clock : Nat) (hc : clock ≤ steps + 82) :
      HeapRepresents q full (capacity full) configuration (packingRun rom whole clock initial).heap := by
    by_cases he : clock ≤ steps
    · exact (frames clock he).1
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
      rw [PSTRWordSegments.run_add]
      exact (header_prefix_fields full command configuration stage hq hl whole em counted complete extra (by omega)).1
  refine ⟨steps, ?_, ?_⟩
  · refine ⟨lower, upper, complete, ?_, prefixRep, ?_, ?_, ?_, ?_⟩
    · rw [PSTRWordSegments.run_add]
      exact hh
    · intro clock hc
      exact PSTRArbitraryOutside.represents_capacity full configuration _ _ hq (prefixRep clock hc)
    · intro clock hc physical hfit hphysical
      by_cases he : clock ≤ steps
      · exact lowhigh clock he physical hfit (Or.inl hphysical)
      · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
        rw [PSTRWordSegments.run_add]
        exact ((header_prefix_fields full command configuration stage hq hl whole em counted complete extra
          (by omega)).2.1 physical hphysical).trans (lowhigh steps le_rfl physical hfit (Or.inl hphysical))
    · intro clock hc physical hfit hphysical
      by_cases he : clock ≤ steps
      · exact lowhigh clock he physical hfit (Or.inr hphysical)
      · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
        rw [PSTRWordSegments.run_add]
        exact ((header_prefix_fields full command configuration stage hq hl whole em counted complete extra
          (by omega)).2.2.1 physical hfit hphysical).trans (lowhigh steps le_rfl physical hfit (Or.inr hphysical))
    · intro clock hc address haddress
      by_cases he : clock ≤ steps
      · exact table clock he address haddress
      · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
        rw [PSTRWordSegments.run_add]
        exact ((header_prefix_fields full command configuration stage hq hl whole em counted complete extra
          (by omega)).2.2.2 address haddress).trans (table steps le_rfl address haddress)
  · intro clock hc
    by_cases he : clock < steps
    · have current := safe clock he
      rw [hbase] at current
      have current' : PSTRCountKernel.AtSafe rom whole
          (PSTRQueryLayout.endpoint (workspace full) (treeSize q full) q)
          (packingRun rom whole clock initial) := by
        simpa only [treeSize, ne_of_gt hq, ite_false] using current
      exact at_safe_mono rom whole _ (allocatedWords full)
        (PSTRQueryLayout.endpoint_index_factor full (capacity full) (wordBits full) 8192 hq hl (by decide)) _ current'
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show steps ≤ clock by omega)
      rw [PSTRWordSegments.run_add]
      have room := PA17A19RuntimeHeader011.original_numeric_room full stage 8192 8192 hq hl
        (by decide) (by decide) (by decide)
      have hp' : counted.pc = BitVec.ofNat (wordBits full) (5 * 539) := by simpa using complete.pc
      have hs : configuration.stage ≤ full.length := by
        have hh : stage.val < full.length + 1 := stage.isLt
        change configuration.stage < full.length + 1 at hh
        omega
      rcases PA17A19RuntimeHeader011.actual_prefix_decoded em full command configuration (capacity full)
        (allocatedWords full) counted (PA17A19QueryBridgeNumeric006b.bits_eight full.length q) hq
        complete.rep hs room.2.2.2.2.2.1 hp' complete.active extra (by omega) with
        ⟨active, _, inCode, op, decoded, access⟩
      exact ⟨active, inCode, op, decoded, access⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeEntry020
