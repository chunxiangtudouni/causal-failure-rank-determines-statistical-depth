module

public import Structure.PSTR_UniformBootstrapCode_105
public import Structure.PSTR_BootstrapStoreAccess_098

/-! Actual fetch/access for NEW park23/locator26/init45. Original straight
execution and concrete memory access predicates are reused, with genuine
new literal slices/PCs. No old61 Contains premise is silently substituted. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformStoreAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRCountKernel PSTRCountWorkspace PSTRQueryLayout PSTROuterStoreAccess PSTRBootstrapStoreAccess

theorem park_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (zeroTarget : Nat) (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (heapWords : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 115) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 3) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have slice := PSTRUniformBootstrapCode.park_contains whole zeroTarget cb
  have safe : PrefixOK rom heapWords (fun _ => False) PSTRCountInit.park state := by
    apply access_only
    intro count hc
    change count < 3 at hc
    interval_cases count <;> trivial
  exact (straight_prefix_safe rom whole PSTRCountInit.park heapWords 23 (fun _ => False) slice.bound slice.code
    PSTRCountInit.park_straight hw hpcfit state hp ha safe clock hclock).1

theorem workspace_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (whole : List PackingOp) (zeroTarget : Nat) (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hb : 8 ≤ bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits < heapWords)
    (hp : state.pc = BitVec.ofNat bits 130) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 19) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  have slice := PSTRUniformBootstrapCode.workspace_contains whole zeroTarget cb
  exact (straight_prefix_safe (callInput q full command) whole PSTRCountWorkspace.program heapWords 26 (fun _ => False)
    slice.bound slice.code PSTRCountWorkspace.program_straight hw hpcfit state hp ha
    (access_only _ _ _ state (PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep hroom hb))
    clock hclock).1

theorem init_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords heapWords : Nat) (state : WordState bits)
    (whole : List PackingOp) (zeroTarget : Nat) (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (haddress : state.register .address = BitVec.ofNat bits (base q full capWords bits))
    (hroom : base q full capWords bits + 15 < heapWords)
    (hp : state.pc = BitVec.ofNat bits 225) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 18) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  have slice := PSTRUniformBootstrapCode.init_contains whole zeroTarget cb
  exact (straight_prefix_safe (callInput q full command) whole PSTRCountInit.program heapWords 45 (fun _ => False)
    slice.bound slice.code PSTRCountInit.program_straight hw hpcfit state hp ha
    (init_prefixOK _ _ _ state haddress hroom) clock hclock).1


end PaperProofs.Structure.LaminarTree.PSTRUniformStoreAccess
