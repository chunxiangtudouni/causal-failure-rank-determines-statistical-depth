module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Exact stage-only ordinary output footprint and three nested-loop states.
The current equality flag is an actual Boolean word, never a supplied
stage-map result. Existing leaf/tool outputs are outside this footprint. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel incrementRel)

def StageAllowed (q : Nat) (full : List (Finset (Fin q))) (CB P address : Nat) : Prop :=
  address = CB + 19 ∨ address = CB + 20 ∨ address = CB + 22 ∨ address = CB + 23 ∨ address = CB + 24 ∨
    (fieldAddress P full.length (preparedSize q full) .stage 0 ≤ address ∧
      address < fieldAddress P full.length (preparedSize q full) .stage 0 + full.length)

def StageFrame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (before after : NatState) : Prop :=
  ∀ address, ¬ StageAllowed q full CB P address → after.heap address = before.heap address

theorem StageFrame.refl (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (state : NatState) :
    StageFrame q full CB P state state := fun _ _ => rfl

theorem StageFrame.trans {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat} {a b c : NatState}
    (hab : StageFrame q full CB P a b) (hbc : StageFrame q full CB P b c) : StageFrame q full CB P a c :=
  fun address hn => (hbc address hn).trans (hab address hn)

theorem stage_region_below_control (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    fieldAddress P full.length (preparedSize q full) .stage 0 + full.length ≤ CB := by
  simp only [fieldAddress, fieldFactor, fieldExtra, mass] at *
  omega

theorem ScanInput.of_stageFrame {q : Nat} {full : List (Finset (Fin q))} {CB P : Nat}
    {before after : NatState} (input : ScanInput q full CB P before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (frame : StageFrame q full CB P before after) (hCB : after.register .address = CB) : ScanInput q full CB P after := by
  have below := stage_region_below_control q full CB P hlayout
  have preserve (address : Nat) (ha : CB ≤ address)
      (h19 : address ≠ CB + 19) (h20 : address ≠ CB + 20) (h22 : address ≠ CB + 22)
      (h23 : address ≠ CB + 23) (h24 : address ≠ CB + 24) : after.heap address = before.heap address := by
    apply frame
    unfold StageAllowed
    omega
  refine ⟨hCB, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [preserve _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact input.raw.mass_cell
    · intro candidate
      rw [preserve _ (by unfold rawCardAddress; omega) (by unfold rawCardAddress; omega)
        (by unfold rawCardAddress; omega) (by unfold rawCardAddress; omega)
        (by unfold rawCardAddress; omega) (by unfold rawCardAddress; omega)]
      exact input.raw.cards candidate
    · intro node
      obtain ⟨candidate, hord, hsupport⟩ := input.raw.ordered node
      refine ⟨candidate, ?_, hsupport⟩
      rw [preserve _ (by unfold rawOrdAddress; omega) (by unfold rawOrdAddress; omega)
        (by unfold rawOrdAddress; omega) (by unfold rawOrdAddress; omega)
        (by unfold rawOrdAddress; omega) (by unfold rawOrdAddress; omega)]
      exact hord
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact input.stages
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact input.tools
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact input.nodes
  · rw [preserve _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact input.base

def stageTarget (q : Nat) (full : List (Finset (Fin q))) (reference : NatState) (CB : Nat) (stage : Nat) : Nat :=
  stageScan (rawIncidenceROM q full) reference.heap CB (mass q full) (preparedSize q full) q stage

structure StageOuterReady (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (row pc : Nat) (state : NatState) : Prop where
  input : ScanInput q full CB P state
  stage_cell : state.heap (CB + 22) = row
  stages : ∀ stage : Fin full.length, stage.val < row →
    state.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val) = stageTarget q full reference CB stage.val
  pc : state.pc = pc
  active : state.halted = false

structure StageNodeReady (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (stage : Fin full.length) (upto pc : Nat) (state : NatState) : Prop where
  input : ScanInput q full CB P state
  stage_cell : state.heap (CB + 22) = stage.val
  node_cell : state.heap (CB + 19) = upto
  current_stage : state.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val) =
    scanWinner (fun node => stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage.val node q) upto
  stages : ∀ earlier : Fin full.length, earlier.val < stage.val →
    state.heap (fieldAddress P full.length (preparedSize q full) .stage earlier.val) = stageTarget q full reference CB earlier.val
  pc : state.pc = pc
  active : state.halted = false

structure StageToolReady (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (upto pc : Nat) (state : NatState) : Prop where
  input : ScanInput q full CB P state
  stage_cell : state.heap (CB + 22) = stage.val
  node_cell : state.heap (CB + 19) = node.val
  tool_cell : state.heap (CB + 20) = upto
  match_cell : state.heap (CB + 23) = bit (stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage.val node.val upto)
  current_stage : state.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val) =
    scanWinner (fun next => stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage.val next q) node.val
  stages : ∀ earlier : Fin full.length, earlier.val < stage.val →
    state.heap (fieldAddress P full.length (preparedSize q full) .stage earlier.val) = stageTarget q full reference CB earlier.val
  pc : state.pc = pc
  active : state.halted = false

theorem stage_control_frame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) {offset value : Nat}
    (before after : NatState) (hoffset : offset = 19 ∨ offset = 20 ∨ offset = 22 ∨ offset = 23 ∨ offset = 24)
    (hh : after.heap = Function.update before.heap (CB + offset) value) : StageFrame q full CB P before after := by
  intro address hn
  have hne : address ≠ CB + offset := by
    unfold StageAllowed at hn
    rcases hoffset with h | h | h | h | h <;> subst offset <;> omega
  rw [hh, Function.update_of_ne hne]

theorem bit_and_comparison (value : Bool) (left right : Nat) :
    (if right = left then bit value else 0) = bit (value && decide (left = right)) := by
  cases value <;> by_cases h : left = right <;> simp [bit, h, eq_comm]

theorem stageNodeWriteTest_pc (rom : PhysicalROM) (CB flag skip : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hflag : state.heap (CB + 23) = flag) :
    (runOps rom (stageNodeWriteTest skip) state).pc = if flag = 0 then 5 * skip else state.pc + 25 := by
  simp [stageNodeWriteTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, hflag]

theorem stageRecord_effect (rom : PhysicalROM) (CB P N t stage node : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hbase : state.heap (CB + 6) = 4 + P)
    (ht : state.heap (CB + 2) = t)
    (hs : state.heap (CB + 22) = stage) (hn : state.heap (CB + 19) = node) :
    let after := runOps rom stageRecord state
    after.register .address = CB ∧
      after.heap = Function.update state.heap (fieldAddress P N t .stage stage) (node + 1) := by
  simp [stageRecord, loadRel, storeField, fieldPointer, fieldPointerLead, fieldPointerExtra,
    fieldAddress, fieldFactor, fieldExtra, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, hCB, hbase, ht, hs, hn, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  congr 1
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
