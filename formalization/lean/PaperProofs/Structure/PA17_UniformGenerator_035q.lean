module

public import PaperProofs.Structure.PA17_UniformGenerator_035k
public import PaperProofs.Structure.PA17_UniformGenerator_035l

/-! Every actual prefix of the runtime length-measurement controls.
Unrelated heap words remain unrestricted. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035q

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035k
  PA17UniformGenerator035j PA17UniformGenerator035l

theorem snapshot_numeric (rom : PhysicalROM) (B heapWords cursor saved : Nat)
    (hc : cursor ≤ B) (hca : cursor < heapWords) (hs : saved ≤ B) (hsa : saved < heapWords)
    (state : NatState) (hr : RegistersLE B state) (hcount : state.heap cursor ≤ B) :
    NumericSafe B heapWords rom (snapshot cursor saved) state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 4 at hn
    interval_cases count <;> cases register <;>
      simp [snapshot, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 4 at hn
    interval_cases count <;>
      simp [snapshot, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hca, hsa]

theorem patch_numeric (rom : PhysicalROM) (B heapWords cursor saved outputBase : Nat)
    (hc : cursor ≤ B) (hca : cursor < heapWords) (hs : saved ≤ B) (hsa : saved < heapWords)
    (ho : outputBase ≤ B) (hone : 1 ≤ B) (state : NatState) (hr : RegistersLE B state)
    (hcount : state.heap cursor ≤ B) (hsaved : state.heap saved ≤ B)
    (haddress : outputBase + state.heap saved ≤ B) (haccess : outputBase + state.heap saved < heapWords) :
    NumericSafe B heapWords rom (patch cursor saved outputBase) state := by
  constructor
  · intro count hn register
    have hh := hr register
    change count ≤ 10 at hn
    interval_cases count <;> cases register <;>
      simp [patch, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hn
    change count < 10 at hn
    interval_cases count <;>
      simp [patch, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hca, hsa, haccess]

theorem wrapperHead_numeric (rom : PhysicalROM) (B heapWords stack cursor saved outputBase : Nat)
    (hstack : stack + 1 ≤ B) (hstackA : stack + 1 ≤ heapWords)
    (hc : cursor < stack) (hca : cursor < heapWords) (hs : saved ≤ B) (hsa : saved < heapWords)
    (hne : cursor ≠ saved) (ho : outputBase ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hcount : state.heap cursor + 1 ≤ B)
    (haddress : outputBase + state.heap cursor ≤ B) (haccess : outputBase + state.heap cursor < heapWords) :
    NumericSafe B heapWords rom (wrapperHead stack cursor saved outputBase) state := by
  have hfirst := snapshot_numeric rom B heapWords cursor saved (by omega) hca hs hsa state hr (by omega)
  have hf : (runOps rom (snapshot cursor saved) state).heap cursor = state.heap cursor := by
    rw [snapshot_heap, Function.update_of_ne hne]
  have hlater := emitWord_numeric (.constant 0) rom B heapWords stack cursor outputBase (by trivial)
    hstack hstackA hc hca ho _ (hfirst.final _ _ _ _ _) (Nat.zero_le B)
    (by rw [hf]; exact hcount) (by rw [hf]; exact haddress) (by rw [hf]; exact haccess)
  rw [PA17UniformGenerator035k.wrapperHead]
  exact NumericSafe.append _ _ _ _ _ _ hfirst hlater

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035q
