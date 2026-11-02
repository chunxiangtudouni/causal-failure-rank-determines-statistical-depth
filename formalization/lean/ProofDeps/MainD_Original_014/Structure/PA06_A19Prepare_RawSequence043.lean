module

public import Structure.PA06_A19Prepare_RawHeader039Ord
public import Structure.PA06_A19Prepare_BankData042_Ordinal
public import Structure.PA06_A19Prepare_BankData042_ExtraFields

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawSequence043

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PrepareRuntimeLayout026 (sequence sequenceClock)
open PA06A19PrepareRuntimeSequence041
open PA06A19PrepareBankData042
open PA06A19PrepareRawHeader039Body (headerProgram headerClock heapWords wordRun_add)

def suffix (tail : List PackingOp) : List PackingOp := sequence 1310 ++ tail

def program (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareRawHeader039Entry.program (suffix tail)

def front (tail : List PackingOp) : List PackingOp :=
  PA06A19PrepareRawHeader039Entry.front (suffix tail) ++
    headerProgram PA06A19PrepareRawHeader039Entry.headerStart

theorem front_length (tail : List PackingOp) : (front tail).length = 1310 := by
  simp only [front, List.length_append, PA06A19PrepareRawHeader039Entry.front_length,
    PA06A19PrepareHeaderScratch024.program_length, PA06A19PrepareRawHeader039Entry.headerStart,
    PA06A19PrepareCompactCandidates007.inputStart, PA06A19PrepareCompactCandidates007.parentStart_eq]

theorem program_layout (tail : List PackingOp) :
    front tail ++ sequence (front tail).length ++ tail = program tail := by
  have layout := PA06A19PrepareRawHeader039Entry.program_layout (suffix tail)
  rw [PA06A19PrepareRawHeader039Entry.front_length] at layout
  rw [front_length]
  simpa only [program, front, suffix, List.append_assoc] using layout

theorem program_length (tail : List PackingOp) : (program tail).length = 1444 + tail.length := by
  simp only [program, PA06A19PrepareRawHeader039Entry.program_length, suffix, List.length_append,
    PA06A19PrepareRuntimeLayout026.sequence_length]
  omega

/-! The original input establishes all intermediate bank/cache premises.
The full containing program is unchanged at the 1206,1310,1444 boundaries. -/

theorem raw_sequence_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (used : Finset (Fin q)) (hq : 0 < q) (hl : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ clock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full +
        headerClock full.length q + sequenceClock full.length q,
      let bits := indexWidth 32 full.length q
      let t := treeSize q full
      let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
      let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
      let rom := controllerInput q full used
      let after := packingRun rom (program tail) clock (natInitial.toWord bits)
      PA06A19PrepareRuntimePacked016.Header q after.heap ∧
        PA06A19PrepareFiniteInit032.BankData q full after ∧
        PA06A19PrepareInitialUsed037.BankData q full after ∧
        (after.heap (BitVec.ofNat bits (CB + 3))).toNat = PA06A19PreparePackedView013.oldCapacity full.length q t ∧
        (after.heap (BitVec.ofNat bits (CB + 6))).toNat = 4 + P ∧
        PA06A19PrepareChildrenCache023.InputData q full CB (PA06A19PrepareRuntimeHeader019.natView after) ∧
        CopiedOrdData q full CB after ∧
        after.pc.toNat = 5 * 1444 ∧ after.halted = false ∧
        ∀ count < clock,
          let current := packingRun rom (program tail) count (natInitial.toWord bits)
          current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
              packingAccessFits rom (heapWords full.length q t) current op := by
  let bits := indexWidth 32 full.length q
  let M := full.length + q + 1
  let t := treeSize q full
  let rom := controllerInput q full used
  let initial := natInitial.toWord bits
  obtain ⟨parentClock, parentBound, previous⟩ :=
    PA06A19PrepareRawHeader039Ord.raw_header_entry q full (suffix tail) used hq hl hend hcode
  dsimp only at previous
  obtain ⟨parents, _rawOrd, middleOrd, headerPC, headerActive, header, frame, previousSafe⟩ := previous
  let raw := packingRun rom (program tail) parentClock initial
  let middle := packingRun rom (program tail) (parentClock + headerClock full.length q) initial
  have hcodeSeq : WordsFit bits (packingCode (front tail ++ sequence (front tail).length ++ tail)) := by
    rw [program_layout]
    exact hcode
  have hendSeq : Fits bits (5 * (front tail ++ sequence (front tail).length ++ tail).length) := by
    rw [program_layout]
    exact hend
  have hpc : middle.pc.toNat = 5 * (front tail).length := by
    rw [front_length]
    exact headerPC
  have sourceFit (address : Nat) (ha : address < PA06A19PrepareCompactWord008.linearLimit full.length q) :
      Fits bits address := ha.trans (PA06A19PrepareCompactArrays018.linearLimit_fits full.length q)
  have sourceFrame (address : Nat) (h16 : 16 ≤ address)
      (ha : address < PA06A19PrepareCompactWord008.linearLimit full.length q) :
      middle.heap (BitVec.ofNat bits address) = raw.heap (BitVec.ofNat bits address) := by
    apply frame
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sourceFit address ha)]
    exact h16
  have small16 : 16 < PA06A19PrepareCompactWord008.linearLimit full.length q := by
    unfold PA06A19PrepareCompactWord008.linearLimit
    omega
  have nodeBound : 20 + 4 * M < PA06A19PrepareCompactWord008.linearLimit full.length q := by
    dsimp only [M, PA06A19PrepareCompactWord008.linearLimit]
    omega
  have hM : (middle.heap (BitVec.ofNat bits 16)).toNat = full.length + q + 1 := by
    rw [sourceFrame 16 (by decide) small16]
    exact parents.2.2.2.1
  have htree : t = (prepareNormalization q full).indexed.nodes.size := by
    dsimp only [t, treeSize]
    rw [ite_eq_right (Nat.ne_of_gt hq)]
  have nodeAddress : RawCandidateParentRAM.nodeCountAddress 16 M = 20 + 4 * M := by
    unfold RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
    omega
  have ht : (middle.heap (BitVec.ofNat bits (20 + 4 * M))).toNat = t := by
    rw [sourceFrame _ (by omega) nodeBound]
    rw [← nodeAddress]
    exact parents.2.2.2.2.1.trans htree.symm
  have data := embedded_sequence_data q full used hq (front tail) tail middle hpc headerActive hM ht header hcodeSeq hendSeq
  have bank := embedded_bankData_pair q full used hq (front tail) tail middle hpc headerActive hM ht header hcodeSeq hendSeq
  have extra := embedded_extra_bankData q full used hq (front tail) tail middle hpc headerActive hM ht header hcodeSeq hendSeq
  have children := embedded_children_input q full used hq (front tail) tail raw middle
    parents frame hpc headerActive header hcodeSeq hendSeq
  have copiedOrd := embedded_copied_ord q full used hq (front tail) tail middle middleOrd
    hpc headerActive hM ht header hcodeSeq hendSeq
  have finalHeader := embedded_sequence_header q full used hq (front tail) tail middle
    hpc headerActive hM ht header hcodeSeq hendSeq
  have totalRun : packingRun rom (program tail)
      (parentClock + headerClock full.length q + sequenceClock full.length q) initial =
      packingRun rom (front tail ++ sequence (front tail).length ++ tail) (sequenceClock full.length q) middle := by
    rw [wordRun_add, program_layout]
  refine ⟨parentClock + headerClock full.length q + sequenceClock full.length q, by omega, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [totalRun]
    exact finalHeader
  · rw [totalRun]
    exact bank.1
  · rw [totalRun]
    exact bank.2
  · rw [totalRun]
    exact extra.1
  · rw [totalRun]
    exact extra.2
  · rw [totalRun]
    exact children
  · rw [totalRun]
    exact copiedOrd
  · rw [totalRun, data.2.1, front_length]
  · rw [totalRun]
    exact data.1
  · intro count hc
    by_cases early : count < parentClock + headerClock full.length q
    · have safe := previousSafe count early
      have htree' : treeSize q full = (prepareNormalization q full).indexed.nodes.size := htree
      simpa only [program, htree'] using safe
    · have split : count = parentClock + headerClock full.length q +
          (count - (parentClock + headerClock full.length q)) := by omega
      have safe := embedded_sequence_prefix_access q full used hq (front tail) tail middle
        hpc headerActive hM ht header hcodeSeq hendSeq
        (count - (parentClock + headerClock full.length q)) (by omega)
      rw [program_layout] at safe
      rw [split, wordRun_add]
      exact safe

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawSequence043
