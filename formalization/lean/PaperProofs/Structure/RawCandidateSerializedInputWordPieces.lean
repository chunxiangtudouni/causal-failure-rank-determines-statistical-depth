module

public import PaperProofs.Structure.RawCandidateSerializedInputWordChunks
public import PaperProofs.Structure.RawCandidateSerializedInputWordCache
public import PaperProofs.Structure.RawCandidateSerializedInputRun

/-! Actual prefix bounds for serializer pieces.  Every cache access
executes the original Base12 program; mutable heap cell eight is arbitrary.
Source-cell bounds are numerical handoffs of preceding real phases. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordPieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedInputRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits workspace_address_fits)
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateOrderingWord (MacroSafe single_safe constant_safe loadCell_safe storeCell_safe jump_safe)
open RawCandidateSerializedInputWordCache (base_safe loadCache_safe storeCache_safe setCache_safe incrementCache_safe)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

private theorem small_fits (N q value : Nat) (hv : value ≤ 4 * candidateCount N q + 32) :
    Fits (indexWidth 16 N q) value := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

def nodeCountSuffix : List PackingOp :=
  [.base (.base (.constant .index 4)), .arithmetic .multiply .index .total .index,
    .base (.base (.add .address .address .index)), .base (.base (.constant .index 4)),
    .base (.base (.add .address .address .index)), .base (.base (.loadHeap .value .address))]

def ordSuffix : List PackingOp :=
  [.base (.base (.constant .index 2)), .arithmetic .multiply .index .total .index,
    .base (.base (.add .address .address .index)), .base (.base (.constant .index 4)),
    .base (.base (.add .address .address .index)), .base (.base (.add .address .address .old)),
    .base (.base (.loadHeap .old .address))]

theorem nodeCountSuffix_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hM : state.register .total = candidateCount full.length q)
    (hB : state.register .address = workspaceBase full.length q)
    (hsource : Fits (indexWidth 16 full.length q) (state.heap (nodeCountAddress full.length q))) :
    MacroSafe q full nodeCountSuffix state := by
  have hlimit := workspaceLimit_fits full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 6 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 6 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by change count < 6; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (nodeCountSuffix[count]'(by change count < 6; exact hlt)) _)
      interval_cases count <;>
        simp only [nodeCountSuffix, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
      all_goals apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
      all_goals first
        | (simpa only [nodeCountAddress, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_comm] using hsource)
        | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; omega)
  · intro count hc
    have hc' : count < 6 := hc
    interval_cases count <;>
      simp [nodeCountSuffix, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits, hM, hB]
    unfold workspaceLimit
    omega

theorem ordSuffix_safe (q : Nat) (full : List (Finset (Fin q))) (node : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hM : state.register .total = candidateCount full.length q)
    (hB : state.register .address = workspaceBase full.length q)
    (hnode : state.register .old = node) (hn : node ≤ candidateCount full.length q)
    (hsource : Fits (indexWidth 16 full.length q) (state.heap (ordAddress full.length q node))) :
    MacroSafe q full ordSuffix state := by
  have hlimit := workspaceLimit_fits full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 7 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 7 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by change count < 7; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (ordSuffix[count]'(by change count < 7; exact hlt)) _)
      interval_cases count <;>
        simp only [ordSuffix, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
      all_goals apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
      all_goals first
        | (simpa only [ordAddress, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_comm] using hsource)
        | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; omega)
  · intro count hc
    have hc' : count < 7 := hc
    interval_cases count <;>
      simp [ordSuffix, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits, hM, hB, hnode]
    unfold workspaceLimit
    omega

theorem loadNodeCount_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hsource : Fits (indexWidth 16 full.length q) (state.heap (nodeCountAddress full.length q))) :
    MacroSafe q full loadNodeCount state := by
  have base := base_safe q full state hf
  let recoveredState := runOps (rawIncidenceROM q full) RawCandidateWorkspaceBaseRAM.program state
  have hr : recoveredState = recovered full.length q state := base_runOps q full state
  have tail := nodeCountSuffix_safe q full recoveredState base.full (by rw [hr]; rfl) (by rw [hr]; rfl)
    (by simpa only [hr, recovered] using hsource)
  exact base.append tail

theorem loadCache_heap (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat) (state : NatState) :
    (runOps (rawIncidenceROM q full) (loadCache target offset) state).heap = state.heap := by
  calc
    _ = (loaded full.length q target offset state).heap := congrArg NatState.heap (loadCache_runOps q full target offset state)
    _ = state.heap := rfl

theorem readOrd_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnode : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hsource : Fits (indexWidth 16 full.length q)
      (state.heap (ordAddress full.length q (state.heap (workspaceBase full.length q + 1))))) :
    MacroSafe q full readOrd state := by
  let rom := rawIncidenceROM q full
  have first := loadCache_safe q full .old 1 (by omega) state hf (small_fits _ _ _ (hnode.trans (by omega)))
  let loadedState := runOps rom (loadCache .old 1) state
  have lr := loadCache_runOps q full .old 1 state
  have lh : loadedState.heap = state.heap := loadCache_heap q full .old 1 state
  have lo : loadedState.register .old = state.heap (workspaceBase full.length q + 1) := by
    change (runOps rom (loadCache .old 1) state).register .old = _
    rw [lr]
    simp [loaded]
  have base := base_safe q full loadedState first.full
  let recoveredState := runOps rom RawCandidateWorkspaceBaseRAM.program loadedState
  have hr : recoveredState = recovered full.length q loadedState := base_runOps q full loadedState
  have tail := ordSuffix_safe q full (state.heap (workspaceBase full.length q + 1)) recoveredState base.full
    (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; exact lo) hnode
    (by simpa only [hr, recovered, lh] using hsource)
  have allSafe := first.append (base.append tail)
  simpa only [readOrd, ordSuffix, List.append_assoc] using allSafe

def testBranch (left right : Register) (exit : Nat) : List PackingOp :=
  [.base (.subtract .flag left right), .base (.base (.constant .index (5 * exit))), .jumpIfZero .flag .index]

theorem testBranch_safe (q : Nat) (full : List (Finset (Fin q))) (left right : Register) (exit : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hexit : Fits (indexWidth 16 full.length q) (5 * exit)) : MacroSafe q full (testBranch left right exit) state := by
  let rom := rawIncidenceROM q full
  let subtractCode : List PackingOp := [.base (.subtract .flag left right)]
  have first : MacroSafe q full subtractCode state := by
    apply single_safe q full (.base (.subtract .flag left right)) state hf
    · exact fits_update hf .flag _ ((Nat.sub_le _ _).trans_lt (hf left))
    · trivial
  let subtracted := runOps rom subtractCode state
  let constantCode : List PackingOp := [.base (.base (.constant .index (5 * exit)))]
  have second := constant_safe q full .index (5 * exit) subtracted first.full hexit
  let constantState := runOps rom constantCode subtracted
  have third : MacroSafe q full [.jumpIfZero .flag .index] constantState := by
    apply single_safe q full (.jumpIfZero .flag .index) constantState second.full
    · exact second.full
    · trivial
  exact first.append (second.append third)

theorem rawTest_safe (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hcursor : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + 1)))
    (hraw : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + 3)))
    (hexit : Fits (indexWidth 16 full.length q) (5 * exit)) : MacroSafe q full (rawTest exit) state := by
  let rom := rawIncidenceROM q full
  have first := loadCache_safe q full .old 1 (by omega) state hf hcursor
  let cursorState := runOps rom (loadCache .old 1) state
  have ch : cursorState.heap = state.heap := loadCache_heap q full .old 1 state
  have second := loadCache_safe q full .total 3 (by omega) cursorState first.full (by rw [ch]; exact hraw)
  have third := testBranch_safe q full .total .old exit _ second.full hexit
  simpa only [rawTest, testBranch, List.append_assoc] using first.append (second.append third)

theorem boundedTest_safe (q : Nat) (full : List (Finset (Fin q))) (counter header exit : Nat)
    (hcounter : counter ≤ 3) (hheader : header ≤ 8) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hc : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + counter)))
    (hh : Fits (indexWidth 16 full.length q) (state.heap header))
    (hexit : Fits (indexWidth 16 full.length q) (5 * exit)) : MacroSafe q full (boundedTest counter header exit) state := by
  let rom := rawIncidenceROM q full
  have first := loadCache_safe q full .total counter hcounter state hf hc
  let counted := runOps rom (loadCache .total counter) state
  have ch : counted.heap = state.heap := loadCache_heap q full .total counter state
  have second := loadCell_safe q full .old header hheader counted first.full (by rw [ch]; exact hh)
  have third := testBranch_safe q full .old .total exit _ second.full hexit
  simpa only [boundedTest, testBranch, List.append_assoc] using first.append (second.append third)

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordPieces
