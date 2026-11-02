module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeHeader_011c

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap PSTRWordSegments
open RawTreePreprocessingClaims

theorem readStage_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : physicalHeaderWords + packedCapacityWords q capWords bits < heapWords) :
    ∀ count (hc : count < readStage.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (readStage.take count) state) readStage[count] := by
  have hp := (headers full configuration capWords state.heap rep).2.2.1
  have h2 : 2 % 2 ^ bits < heapWords := (Nat.mod_le _ _).trans_lt (by unfold physicalHeaderWords at hroom; omega)
  have h4 : (4 + packedCapacityWords q capWords bits) % 2 ^ bits < heapWords :=
    (Nat.mod_le _ _).trans_lt (by simpa only [physicalHeaderWords] using hroom)
  intro count hc
  change count < 5 at hc
  interval_cases count <;>
    simp +decide [readStage, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, hp, h2, BitVec.ofNat_add_ofNat, Nat.add_comm, h4]

theorem stageGetter_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hi : state.register .index = BitVec.ofNat bits position)
    (hroom : metadataAddress q capWords bits (offset q full 7 + position) < heapWords) :
    ∀ count (hc : count < (PSTRStaticFields.program ⟨7, by decide⟩).length),
      packingAccessFits (callInput q full command) heapWords
        (executeOps (callInput q full command) ((PSTRStaticFields.program ⟨7, by decide⟩).take count) state)
        (PSTRStaticFields.program ⟨7, by decide⟩)[count] := by
  have hh : 3 ≤ heapWords := by unfold metadataAddress physicalHeaderWords at hroom; omega
  intro count hc
  by_cases h1 : count = 1
  · subst count
    change (BitVec.ofNat bits 0).toNat < heapWords
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  by_cases h3 : count = 3
  · subst count
    change (BitVec.ofNat bits 2).toNat < heapWords
    exact (Nat.mod_le 2 (2 ^ bits)).trans_lt (by omega)
  by_cases h6 : count = 6
  · subst count
    have hpack := (headers full configuration capWords state.heap rep).2.2.1
    change ((executeOps (callInput q full command) ((PSTRStaticFields.program ⟨7, by decide⟩).take 6) state).register .address).toNat < heapWords
    have hptr : (executeOps (callInput q full command) ((PSTRStaticFields.program ⟨7, by decide⟩).take 6) state).register .address =
        BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 := by
      simp +decide [PSTRStaticFields.program, executeOps, packingExecuteOp, wordOp, wordInstruction, hpack]
    rw [hptr, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    apply (Nat.mod_le _ _).trans_lt
    simp only [offset, metadataAddress, physicalHeaderWords] at hroom
    omega
  by_cases h17 : count = 17
  · subst count
    change (BitVec.ofNat bits 0).toNat < (callInput q full command).input.length
    simp [callInput, rawIncidenceROM]
  by_cases h21 : count = 21
  · subst count
    have result := (execute_stage_address full command configuration capWords state position hb hq rep hi).1
    have hptr : (executeOps (callInput q full command) ((PSTRStaticFields.program ⟨7, by decide⟩).take 21) state).register .address =
        BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 7 + position)) := result
    change ((executeOps (callInput q full command) ((PSTRStaticFields.program ⟨7, by decide⟩).take 21) state).register .address).toNat < heapWords
    rw [hptr, BitVec.toNat_ofNat]
    exact (Nat.mod_le _ _).trans_lt hroom
  change count < 22 at hc
  interval_cases count <;> simp_all +decide [PSTRStaticFields.program, packingAccessFits, AccessFits]

theorem prepareRow_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heapWords : Nat) (state : WordState bits) (hb : 8 ≤ bits) (hh : 0 < heapWords) :
    ∀ count (hc : count < prepareRow.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (prepareRow.take count) state) prepareRow[count] := by
  have hpow : 256 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  intro count hc
  change count < 19 at hc
  interval_cases count <;>
    simp +decide [prepareRow, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words, callInput, rawIncidenceROM, h1, hh]

theorem locate_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords) :
    ∀ count (hc : count < locate.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (locate.take count) state) locate[count] := by
  exact PA17A19RuntimeRead007.access_append _ _ _ _ state
    (PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep
      (by rw [PSTRCountWorkspace.base_metadata_end q full hq capWords bits]; exact hroom) hb)
    (PA17A19RuntimeRead007.headerFinish_access _ _ _ (by omega))

theorem writeHeader_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat)
    (state : WordState bits) (ha : state.register .address = BitVec.ofNat bits header)
    (hroom : header + 3 < heapWords) :
    ∀ count (hc : count < writeHeader.length), packingAccessFits rom heapWords
      (executeOps rom (writeHeader.take count) state) writeHeader[count] := by
  have hp (i : Nat) (hi : i ≤ 3) : (header + i) % 2 ^ bits < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have hzero : header % 2 ^ bits < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  intro count hc
  change count < 10 at hc
  interval_cases count <;>
    simp +decide [writeHeader, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, ha, BitVec.ofNat_add_ofNat, Nat.add_assoc, hp, hzero]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011
