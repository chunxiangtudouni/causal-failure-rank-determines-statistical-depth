module

public import PaperProofs.Structure.PSTR_QueryLayout_041
public import PaperProofs.Structure.PSTR_HD_WordSegments_014
public import PaperProofs.Structure.PackedCapacityRAM

/-! Fixed actual reply reload after selector scratch has clobbered registers.
The ranks are read from real H4/H5, the selected tool from real c+t+2, and
active/selection masks from H2/H7. No free register restoration or output
answer is an instruction input. -/

@[expose] public section
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReply016

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def program : List PackingOp :=
  [.base (.base (.constant .index 1)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .flag 2)), .base (.base (.add .total .total .flag)),
   .base (.base (.constant .index 4)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index)), .base (.base (.constant .flag 1)),
   .base (.base (.add .index .index .flag)), .base (.base (.loadHeap .fresh .index)),
   .base (.base (.add .value .fresh .flag)), .base (.base (.minimum .value .old .value)),
   .base (.base (.constant .index 2)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .flag .index)), .base (.base (.select .old .flag .old .total)),
   .base (.base (.select .value .flag .value .total)), .base (.base (.constant .index 0)),
   .base (.base (.select .fresh .flag .fresh .index)), .base (.base (.constant .flag 0)),
   .base (.base (.loadHeap .flag .flag)), .base (.base (.add .index .total .total)),
   .base (.base (.add .index .index .flag)), .base (.base (.constant .flag 18)),
   .base (.base (.add .index .index .flag)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.constant .flag 7)),
   .base (.base (.add .flag .address .flag)), .base (.base (.loadHeap .flag .flag)),
   .base (.base (.constant .total 0)), .base (.base (.select .index .flag .index .total))]

theorem program_length : program.length = 32 := rfl

theorem program_straight : StraightProgram program := by
  simp [program, StraightProgram, StraightOp]

theorem program_noStore : ∀ op ∈ program, HeapPreservingOp op := by
  simp [program, HeapPreservingOp]

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (program.take count) state).heap = state.heap :=
  executeOps_heap_of_no_store rom _ state (by
    intro op ho
    exact program_noStore op (List.mem_of_mem_take ho))

theorem execute_result {bits : Nat} (rom : PhysicalROM)
    (workspace size q good bad : Nat) (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.endpoint workspace size q))
    (hq : (rom.words .input).getD 1 0 = q)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hgood : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 4)) =
      BitVec.ofNat bits good)
    (hbad : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 5)) =
      BitVec.ofNat bits bad)
    (hg : good ≤ q + 2) (hb : bad ≤ q + 2) :
    let header := PSTRQueryLayout.header workspace size
    let active := (state.heap (BitVec.ofNat bits (header + 2))).toNat
    let enabled := (state.heap (BitVec.ofNat bits (header + 7))).toNat
    let after := executeOps rom program state
    after.register .address = BitVec.ofNat bits header ∧
    after.register .old = BitVec.ofNat bits (if active = 0 then q + 2 else good) ∧
    after.register .fresh = BitVec.ofNat bits (if active = 0 then 0 else bad) ∧
    after.register .value = BitVec.ofNat bits
      (if active = 0 then q + 2 else min good (bad + 1)) ∧
    after.register .index = (if enabled = 0 then BitVec.ofNat bits 0 else
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + size + 2))) ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  let header := PSTRQueryLayout.header workspace size
  have hq3 : q + 3 ≤ PSTRQueryLayout.endpoint workspace size q := by
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags
      PSTRQueryLayout.goodFlags
    omega
  have h1 : Fits bits 1 := (show 1 ≤ q + 3 by omega).trans_lt (hq3.trans_lt hroom)
  have hgoodFit : Fits bits good := (hg.trans (by omega : q + 2 ≤ q + 3)).trans_lt (hq3.trans_lt hroom)
  have hbad1Fit : Fits bits (bad + 1) := (show bad + 1 ≤ q + 3 by omega).trans_lt (hq3.trans_lt hroom)
  have hsizeWord : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) hsize
  have htool : header + (q + 2 + (q + 2) + size + 18) =
      PSTRQueryLayout.childBase workspace size q + size + 2 := by
    unfold PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    dsimp only [header]
    omega
  have htool' : header + (q + 2 + (q + 2 + (size + 18))) =
      PSTRQueryLayout.childBase workspace size q + size + 2 := by
    simpa only [Nat.add_assoc] using htool
  simp only [Nat.add_assoc] at htool'
  dsimp only [header] at htool'
  dsimp only
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    hq, hgood, hbad, hsizeWord, BitVec.ofNat_add_ofNat, Nat.add_assoc,
    Nat.mod_eq_of_lt hgoodFit, Nat.mod_eq_of_lt hbad1Fit,
    htool', min_def]
  all_goals split_ifs <;> simp only [true_and]

theorem inline_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (state : WordState bits) :
    (packingDynamicTrace rom containing 32 state).length ≤ 384 :=
  packingDynamicTrace_length_le rom containing 32 state

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReply016
