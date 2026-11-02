module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCardsNumeric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED concrete leaf/tool numeric blocks. Only actual control words
and incoming registers are bounded. No arbitrary heap bound is supplied.
The two private heads are exact slices of the existing46-op writer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (preparedSize mass highCacheEnd loadRel storeRel incrementRel)

theorem scanArguments_numeric (rom : PhysicalROM) (B H CB M node tool : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hn : state.heap (CB + 19) = node) (ht : state.heap (CB + 20) = tool)
    (hnM : node ≤ M) (htM : tool ≤ M) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom scanArguments state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 6 at hc
    interval_cases count <;> cases reg <;>
      simp_all [scanArguments, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 6 at hc
    interval_cases count <;>
      simp_all [scanArguments, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem cacheLeafArguments_numeric (rom : PhysicalROM) (B H CB M : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom cacheLeafArguments state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 6 at hc
    interval_cases count <;> cases reg <;>
      simp_all [cacheLeafArguments, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 6 at hc
    interval_cases count <;>
      simp_all [cacheLeafArguments, storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

private def scanSingletonLeafHead : List PackingOp :=
  loadRel .old 19 ++ loadRel .value 20 ++
    [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))]

private def scanSingletonToolHead : List PackingOp :=
  loadRel .old 20 ++ loadRel .value 19 ++
    [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))]

private theorem scanSingleton_split : recordSingleton =
    (scanSingletonLeafHead ++ storeField .leaf) ++ scanSingletonToolHead ++ storeField .tool := rfl

theorem recordSingleton_numeric (rom : PhysicalROM) (B H CB P N q t node tool : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hbase : state.heap (CB + 6) = 4 + P) (ht : state.heap (CB + 2) = t)
    (hN : state.heap (CB + 0) = N) (hn : state.heap (CB + 19) = node)
    (htool : state.heap (CB + 20) = tool) (hnode : node < t) (htoolBound : tool < q)
    (htM : t ≤ N + q + 1) (hlayout : CB = 4 + P + 4096 * (N + q + 1 + t))
    (hroom : highCacheEnd CB (N + q + 1) < H) (hH : H ≤ B) :
    NumericSafe B H rom recordSingleton state := by
  have controlRoom : CB + 6 < H := by unfold highCacheEnd at hroom; omega
  have leafBelow : fieldAddress P N t .leaf node < CB := by
    change 6 + P + 5 * t + node < CB
    omega
  have firstSafe : NumericSafe B H rom scanSingletonLeafHead state := by
    constructor
    · intro count hc reg
      have hreg := hr reg
      change count ≤ 8 at hc
      interval_cases count <;> cases reg <;>
        simp_all [scanSingletonLeafHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 8 at hc
      interval_cases count <;>
        simp_all [scanSingletonLeafHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  let first := runOps rom scanSingletonLeafHead state
  have firstEffect : first.register .address = CB ∧ first.register .old = node ∧
      first.heap = state.heap := by
    simp [first, scanSingletonLeafHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, hn]
  have firstStore := storeField_numeric rom B H CB P N q t node .leaf first
    (firstSafe.final _ _ _ _ _) firstEffect.1 hbase ht hN firstEffect.2.1 hnode hlayout controlRoom hH
  let stored := runOps rom (storeField .leaf) first
  have storedEffect := storeField_effect rom CB P N t node .leaf first
    firstEffect.1 hbase ht hN firstEffect.2.1
  have storedHeap : stored.heap = Function.update state.heap (fieldAddress P N t .leaf node)
      (first.register .value) := by rw [storedEffect.2.2.2.2, firstEffect.2.2]
  have storedCB : stored.register .address = CB := storedEffect.1
  have storedNode : stored.heap (CB + 19) = node := by
    rw [storedHeap, Function.update_of_ne (by omega)]; exact hn
  have storedTool : stored.heap (CB + 20) = tool := by
    rw [storedHeap, Function.update_of_ne (by omega)]; exact htool
  have storedBase : stored.heap (CB + 6) = 4 + P := by
    rw [storedHeap, Function.update_of_ne (by omega)]; exact hbase
  have storedT : stored.heap (CB + 2) = t := by
    rw [storedHeap, Function.update_of_ne (by omega)]; exact ht
  have storedN : stored.heap (CB + 0) = N := by
    rw [storedHeap, Function.update_of_ne (by omega)]; exact hN
  have storedRegs : RegistersLE B stored := firstStore.final _ _ _ _ _
  have secondSafe : NumericSafe B H rom scanSingletonToolHead stored := by
    constructor
    · intro count hc reg
      have hreg := storedRegs reg
      change count ≤ 8 at hc
      interval_cases count <;> cases reg <;>
        simp_all [scanSingletonToolHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals unfold highCacheEnd at hroom; omega
    · intro count hc
      change count < 8 at hc
      interval_cases count <;>
        simp_all [scanSingletonToolHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
      all_goals unfold highCacheEnd at hroom; omega
  let second := runOps rom scanSingletonToolHead stored
  have secondEffect : second.register .address = CB ∧ second.register .old = tool ∧
      second.heap = stored.heap := by
    simp [second, scanSingletonToolHead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, storedCB, storedTool]
  have secondStore := storeField_numeric rom B H CB P N q t tool .tool second
    (secondSafe.final _ _ _ _ _) secondEffect.1 storedBase storedT storedN secondEffect.2.1
    htoolBound hlayout controlRoom hH
  have firstPart := NumericSafe.append B H rom scanSingletonLeafHead (storeField .leaf) state firstSafe firstStore
  have nextPart := NumericSafe.append B H rom (scanSingletonLeafHead ++ storeField .leaf)
    scanSingletonToolHead state firstPart (by rw [runOps_append]; exact secondSafe)
  rw [scanSingleton_split]
  exact NumericSafe.append B H rom ((scanSingletonLeafHead ++ storeField .leaf) ++ scanSingletonToolHead)
    (storeField .tool) state nextPart (by rw [runOps_append, runOps_append]; exact secondStore)

theorem scanBoundedTest_numeric (rom : PhysicalROM) (B H CB M size upto bound counter exit : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hs : state.heap (CB + bound) = size) (hu : state.heap (CB + counter) = upto)
    (hbound : bound ≤ 24) (hcounter : counter ≤ 24) (hsM : size ≤ M) (huM : upto ≤ M)
    (hexit : 5 * exit ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (scanBoundedTest bound counter exit) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 9 at hc
    interval_cases count <;> cases reg <;>
      simp_all [scanBoundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp_all [scanBoundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem scanScore_numeric (rom : PhysicalROM) (B H CB M card skip : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hc : state.heap (CB + 21) = card) (hcard : card ≤ M)
    (hskip : 5 * skip ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (scanScore skip) state := by
  constructor
  · intro count hcount reg
    have hreg := hr reg
    change count ≤ 11 at hcount
    interval_cases count <;> cases reg <;>
      simp_all [scanScore, scanScoreLead, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom
    all_goals first | omega | (split_ifs <;> omega)
  · intro count hcount
    change count < 11 at hcount
    interval_cases count <;>
      simp_all [scanScore, scanScoreLead, loadRel, runOps, natExecuteOp,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

theorem scanInnerTail_numeric (rom : PhysicalROM) (B H CB M tool start : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (ht : state.heap (CB + 20) = tool) (htM : tool + 1 ≤ M)
    (hjump : 5 * (start + 51) ≤ B) (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom (scanInnerTail start) state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 11 at hc
    interval_cases count <;> cases reg <;>
      simp_all [scanInnerTail, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 11 at hc
    interval_cases count <;>
      simp_all [scanInnerTail, incrementRel, loadRel, storeRel, jumpTo, runOps, natExecuteOp,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
