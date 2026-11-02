module

public import PaperProofs.Structure.RawCandidateSerializedInputWordPieces

/-! Remaining serializer pieces, with runtime register/address bounds.
The original cache macros recover B on every call, including after output
has overwritten heap cell eight. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordDataPieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedInputRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge workspaceBase_fits candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits workspace_address_fits)
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateOrderingWord (MacroSafe single_safe constant_safe loadCell_safe storeCell_safe jump_safe)
open RawCandidateSerializedInputWordCache (base_safe loadCache_safe storeCache_safe setCache_safe incrementCache_safe)
open RawCandidateSerializedInputWordPieces (loadCache_heap loadNodeCount_safe readOrd_safe testBranch_safe)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

theorem write_space (N q node tool raw : Nat) (hn : node ≤ candidateCount N q) (ht : tool ≤ q) (hr : raw ≤ N * q) :
    6 + raw + node * q + tool < workspaceBase N q := by
  have hm : 1 ≤ candidateCount N q := by unfold candidateCount; omega
  have hq : q ≤ candidateCount N q * q := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right q hm
  have hNq : N * q ≤ candidateCount N q * q := Nat.mul_le_mul_right q (by unfold candidateCount; omega)
  have hnq := Nat.mul_le_mul_right q hn
  simp only [workspaceBase, Nat.mul_assoc]
  omega

theorem raw_product_fits (N q : Nat) : Fits (indexWidth 16 N q) (N * q) := by
  have hspace := write_space N q 0 0 (N * q) (by omega) (by omega) le_rfl
  exact lt_trans (by omega) (workspaceBase_fits N q)

theorem arguments_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnode : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hsource : Fits (indexWidth 16 full.length q)
      (state.heap (ordAddress full.length q (state.heap (workspaceBase full.length q + 1)))))
    (htool : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + 2))) :
    MacroSafe q full arguments state := by
  have first := readOrd_safe q full state hf hnode hsource
  let read := runOps (rawIncidenceROM q full) readOrd state
  have hh : read.heap = state.heap := (readOrd_values q full state).2.1
  have second := loadCache_safe q full .fresh 2 (by omega) read first.full (by rw [hh]; exact htool)
  exact first.append second

theorem rowTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hinc : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + 1) + 1))
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) : MacroSafe q full (rowTail start) state := by
  have first := incrementCache_safe q full 1 (by omega) state hf hinc
  exact first.append (jump_safe q full (start + 200) _ first.full (lt_of_le_of_lt (by omega) hend))

def writeMid : List PackingOp :=
  [.arithmetic .multiply .old .old .flag, .base (.base (.add .old .old .fresh))]

def writeSuffix : List PackingOp :=
  [.base (.base (.add .old .old .fresh)), .base (.base (.constant .address 6)),
    .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))]

theorem writeMid_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hprod : Fits (indexWidth 16 full.length q) (state.register .old * state.register .flag))
    (hsum : Fits (indexWidth 16 full.length q) (state.register .old * state.register .flag + state.register .fresh)) :
    MacroSafe q full writeMid state := by
  let rom := rawIncidenceROM q full
  let firstCode : List PackingOp := [.arithmetic .multiply .old .old .flag]
  have first : MacroSafe q full firstCode state := by
    apply single_safe q full (.arithmetic .multiply .old .old .flag) state hf
    · exact fits_update hf .old _ hprod
    · trivial
  let multiplied := runOps rom firstCode state
  have second : MacroSafe q full [.base (.base (.add .old .old .fresh))] multiplied := by
    apply single_safe q full (.base (.base (.add .old .old .fresh))) multiplied first.full
    · apply fits_update first.full
      simpa [multiplied, firstCode, runOps, natExecuteOp, natArithmetic] using hsum
    · trivial
  exact first.append second

theorem writeSuffix_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hspace : 6 + state.register .old + state.register .fresh < workspaceBase full.length q) :
    MacroSafe q full writeSuffix state := by
  have hlimit := workspaceLimit_fits full.length q
  have hb := workspaceBase_ge full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 4 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 4 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by change count < 4; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (writeSuffix[count]'(by change count < 4; exact hlt)) _)
      interval_cases count <;>
        simp only [writeSuffix, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals apply lt_of_le_of_lt _ hlimit
      all_goals unfold workspaceLimit
      all_goals omega
  · intro count hc
    have hc' : count < 4 := hc
    interval_cases count <;>
      simp [writeSuffix, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    unfold workspaceLimit
    omega

theorem writeNode_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnode : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (htool : state.register .fresh ≤ q) (hraw : state.heap (workspaceBase full.length q + 3) ≤ full.length * q) :
    MacroSafe q full writeNode state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  have space := write_space full.length q (state.heap (B + 1)) (state.register .fresh) (state.heap (B + 3)) hnode htool hraw
  have first := loadCache_safe q full .old 1 (by omega) state hf (hnode.trans_lt (candidateCount_fits _ _))
  let one := runOps rom (loadCache .old 1) state
  have oneEq : one = loaded full.length q .old 1 state := loadCache_runOps q full .old 1 state
  have oneHeap : one.heap = state.heap := loadCache_heap q full .old 1 state
  have oo : one.register .old = state.heap (B + 1) := by rw [oneEq]; simp [loaded, recovered, B]
  have oflag : one.register .flag = q := by rw [oneEq]; simp [loaded, recovered]
  have ofresh : one.register .fresh = state.register .fresh := by rw [oneEq]; simp [loaded, recovered]
  have mid := writeMid_safe q full one first.full
    (by rw [oo, oflag]; exact lt_trans (by omega) (workspaceBase_fits _ _))
    (by rw [oo, oflag, ofresh]; exact lt_trans (by omega) (workspaceBase_fits _ _))
  let two := runOps rom writeMid one
  have twoHeap : two.heap = state.heap := by
    simpa [two, writeMid, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute] using oneHeap
  have twoOld : two.register .old = state.heap (B + 1) * q + state.register .fresh := by
    simp [two, writeMid, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, oo, oflag, ofresh]
  have third := loadCache_safe q full .fresh 3 (by omega) two mid.full
    (by rw [twoHeap]; exact hraw.trans_lt (raw_product_fits _ _))
  let three := runOps rom (loadCache .fresh 3) two
  have threeEq : three = loaded full.length q .fresh 3 two := loadCache_runOps q full .fresh 3 two
  have thirdOld : three.register .old = state.heap (B + 1) * q + state.register .fresh := by
    rw [threeEq]
    simpa [loaded, recovered] using twoOld
  have tf : three.register .fresh = state.heap (B + 3) := by rw [threeEq]; simp [loaded, recovered, twoHeap, B]
  have last := writeSuffix_safe q full three third.full (by rw [thirdOld, tf]; omega)
  have allSafe := first.append (mid.append (third.append last))
  simpa only [writeNode, writeMid, writeSuffix, List.append_assoc] using allSafe

theorem toolTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnode : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (htool : state.register .fresh ≤ q) (hraw : state.heap (workspaceBase full.length q + 3) ≤ full.length * q)
    (hcounter : state.heap (workspaceBase full.length q + 2) ≤ q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) : MacroSafe q full (toolTail start) state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  have first := writeNode_safe q full state hf hnode htool hraw
  let written := runOps rom writeNode state
  have hh := writeNode_heap q full state
  have space := write_space full.length q (state.heap (B + 1)) (state.register .fresh) (state.heap (B + 3)) hnode htool hraw
  dsimp only [B] at space
  have ch : written.heap (workspaceBase full.length q + 2) = state.heap (workspaceBase full.length q + 2) := by
    change (runOps rom writeNode state).heap (workspaceBase full.length q + 2) = _
    rw [hh, Function.update_of_ne (by omega)]
  have second := incrementCache_safe q full 2 (by omega) written first.full
    (by rw [ch]; apply lt_of_le_of_lt _ (candidateCount_fits full.length q); unfold candidateCount; omega)
  have last := jump_safe q full (start + 236) _ second.full (lt_of_le_of_lt (by omega) hend)
  simpa only [toolTail, List.append_assoc] using first.append (second.append last)

theorem incidence_getD_le_one (q : Nat) (full : List (Finset (Fin q))) (offset : Nat) :
    (incidence full).getD offset 0 ≤ 1 := by
  have each (value : Nat) (hv : value ∈ incidence full) : value ≤ 1 := by
    obtain ⟨eligible, _heligible, hvalue⟩ := List.mem_flatMap.mp hv
    obtain ⟨tool, _htool, rfl⟩ := List.mem_map.mp hvalue
    unfold bit
    split <;> omega
  by_cases hi : offset < (incidence full).length
  · rw [List.getD_eq_getElem _ 0 hi]
    exact each _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ 0 (by omega)]
    omega

theorem raw_source_le_one (q : Nat) (full : List (Finset (Fin q))) (offset : Nat) :
    (rawIncidenceROM q full).semantic.read .input (2 + offset) ≤ 1 := by
  change ([full.length, q] ++ incidence full).getD (2 + offset) 0 ≤ 1
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
  exact incidence_getD_le_one q full offset

def rawReadSuffix : List PackingOp :=
  [.base (.base (.constant .index 2)), .base (.base (.add .index .index .old)),
    .base (.base (.loadROM .input .value .index)), .base (.base (.constant .address 6)),
    .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))]

theorem rawReadSuffix_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hOld : state.register .old = offset)
    (hoffset : offset < full.length * q) : MacroSafe q full rawReadSuffix state := by
  have hb := workspaceBase_ge full.length q
  have hbase := workspaceBase_fits full.length q
  have hspace := prefixLength_lt_base q full
  unfold prefixLength at hspace
  have hread : Fits (indexWidth 16 full.length q) ((rawIncidenceROM q full).semantic.read .input (2 + offset)) :=
    (raw_source_le_one q full offset).trans_lt (lt_of_le_of_lt (by omega) hbase)
  constructor
  · intro count hc
    have hc' : count ≤ 6 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 6 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by change count < 6; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (rawReadSuffix[count]'(by change count < 6; exact hlt)) _)
      interval_cases count <;>
        simp only [rawReadSuffix, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals apply lt_of_le_of_lt _ hbase
      all_goals omega
  · intro count hc
    have hc' : count < 6 := hc
    interval_cases count <;>
      simp [rawReadSuffix, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits,
        hOld, raw_input_length]
    all_goals first | exact hoffset | (unfold workspaceLimit; omega)

theorem rawBody_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hcursor : state.heap (workspaceBase full.length q + 1) < full.length * q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) : MacroSafe q full (rawBody start) state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let offset := state.heap (B + 1)
  have hspace := prefixLength_lt_base q full
  unfold prefixLength at hspace
  have hb := workspaceBase_ge full.length q
  have first := loadCache_safe q full .old 1 (by omega) state hf (hcursor.le.trans_lt (raw_product_fits _ _))
  let loadedState := runOps rom (loadCache .old 1) state
  have lr : loadedState = loaded full.length q .old 1 state := loadCache_runOps q full .old 1 state
  have lh : loadedState.heap = state.heap := loadCache_heap q full .old 1 state
  have lo : loadedState.register .old = offset := by rw [lr]; simp [loaded, recovered, offset, B]
  have read := rawReadSuffix_safe q full offset loadedState first.full lo hcursor
  let copied := runOps rom rawReadSuffix loadedState
  have cc : copied.heap (B + 1) = state.heap (B + 1) := by
    have hne : B + 1 ≠ 6 + offset := by dsimp [B, offset]; omega
    simp [copied, rawReadSuffix, runOps, natExecuteOp, Op.execute, Instruction.execute, lo, lh, hne]
  have inc := incrementCache_safe q full 1 (by omega) copied read.full
    (by rw [cc]; exact (Nat.succ_le_of_lt hcursor).trans_lt (raw_product_fits _ _))
  have jump := jump_safe q full (start + 95) _ inc.full (lt_of_le_of_lt (by omega) hend)
  have allSafe := first.append (read.append (inc.append jump))
  simpa only [rawBody, rawReadSuffix, List.append_assoc] using allSafe

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordDataPieces
