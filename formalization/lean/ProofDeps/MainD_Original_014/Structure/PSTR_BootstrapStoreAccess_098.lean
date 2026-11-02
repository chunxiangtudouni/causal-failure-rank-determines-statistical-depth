module

public import Structure.PSTR_WidthAccess_097
public import Structure.PSTR_LiveHeaderSafety_004

/-! Real bootstrap memory accesses: raw header, actual W locator, actual
four-slot initialization and actual parent sentinel. These certificates do
not provide or assume initialized scratch contents. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBootstrapStoreAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRCountKernel PSTRCountWorkspace PSTRQueryLayout PSTROuterStoreAccess

theorem spill_access {bits : Nat} (rom : PhysicalROM) (base heapWords : Nat) (state : WordState bits)
    (hf : state.register .flag = BitVec.ofNat bits base) (hroom : base + 3 < heapWords)
    (count : Nat) (hc : count < PSTRReplySpill.spillProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRReplySpill.spillProgram.take count) state)
      PSTRReplySpill.spillProgram[count] := by
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  change count < 8 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRReplySpill.spillProgram, List.take_succ_cons, List.take_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, hf, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, h2, h3]
    apply (Nat.mod_le _ _).trans_lt
    omega

theorem init_prefixOK {bits : Nat} (rom : PhysicalROM) (workspace heapWords : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) (hroom : workspace + 15 < heapWords) :
    PrefixOK rom heapWords (fun _ => False) PSTRCountInit.program state := by
  let headed := executeOps rom PSTRCountInit.head state
  let spilled := executeOps rom PSTRReplySpill.spillProgram headed
  have head : PrefixOK rom heapWords (fun _ => False) PSTRCountInit.head state := by
    apply access_only
    intro count hc
    change count < 7 at hc
    interval_cases count <;> trivial
  have spill := access_only rom heapWords PSTRReplySpill.spillProgram headed
    (spill_access rom (workspace + 12) heapWords headed
      (PSTRCountInit.head_registers rom workspace state ha).2.2.2.2.1 (by omega))
  have tail : PrefixOK rom heapWords (fun _ => False) PSTRCountInit.tail spilled := by
    apply access_only
    intro count hc
    change count < 3 at hc
    interval_cases count <;> trivial
  have joined := prefixOK_append rom heapWords (fun _ => False) PSTRCountInit.head
    (PSTRReplySpill.spillProgram ++ PSTRCountInit.tail) state head
    (prefixOK_append rom heapWords (fun _ => False) PSTRReplySpill.spillProgram PSTRCountInit.tail headed spill tail)
  simpa only [PSTRCountInit.program, List.append_assoc] using joined

theorem sentinel_access {bits : Nat} (rom : PhysicalROM) (workspace size heapWords : Nat) (state : WordState bits)
    (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hroom : parentsBase workspace size < heapWords)
    (count : Nat) (hc : count < PSTRParentSentinel.program.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRParentSentinel.program.take count) state)
      PSTRParentSentinel.program[count] := by
  change count < 5 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRParentSentinel.program, List.take_succ_cons, List.take_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, hb, ht, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.zero_mod]
    first | exact (Nat.mod_le _ _).trans_lt hroom | unfold parentsBase countsBase at hroom; omega

theorem header_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (heapWords : Nat) (state : WordState bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hq : Fits bits q) (hpos : Fits bits (2 + full.length * q))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 8) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  have slice := PSTRBootstrapPrefix.header_at whole cb
  exact (straight_prefix_safe (callInput q full command) whole PSTRLiveHeader.program heapWords 0 (fun _ => False)
    slice.bound slice.code PSTRLiveHeader.program_straight hw hpcfit state hp ha
    (access_only _ _ _ state (PSTRLiveHeaderSafety.access_prefix full command heapWords state hb hN hq hpos)) clock hclock).1

theorem park_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (heapWords : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 105) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 3) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  have slice := PSTRBootstrapPrefix.park_at whole cb
  have safe : PrefixOK rom heapWords (fun _ => False) PSTRCountInit.park state := by
    apply access_only
    intro count hc
    change count < 3 at hc
    interval_cases count <;> trivial
  exact (straight_prefix_safe rom whole PSTRCountInit.park heapWords 21 (fun _ => False) slice.bound slice.code
    PSTRCountInit.park_straight hw hpcfit state hp ha safe clock hclock).1

theorem workspace_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hb : 8 ≤ bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits < heapWords)
    (hp : state.pc = BitVec.ofNat bits 120) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 19) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  have slice := PSTRBootstrapPrefix.workspace_at whole cb
  exact (straight_prefix_safe (callInput q full command) whole PSTRCountWorkspace.program heapWords 24 (fun _ => False)
    slice.bound slice.code PSTRCountWorkspace.program_straight hw hpcfit state hp ha
    (access_only _ _ _ state (PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep hroom hb))
    clock hclock).1

theorem init_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords heapWords : Nat) (state : WordState bits)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (haddress : state.register .address = BitVec.ofNat bits (base q full capWords bits))
    (hroom : base q full capWords bits + 15 < heapWords)
    (hp : state.pc = BitVec.ofNat bits 215) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 18) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  have slice := PSTRBootstrapPrefix.init_at whole cb
  exact (straight_prefix_safe (callInput q full command) whole PSTRCountInit.program heapWords 43 (fun _ => False)
    slice.bound slice.code PSTRCountInit.program_straight hw hpcfit state hp ha
    (init_prefixOK _ _ _ state haddress hroom) clock hclock).1

theorem sentinel_safe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (origin workspace size heapWords : Nat)
    (slice : PSTROuterCountCode.BlockAt whole origin PSTRParentSentinel.program)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : state.register .old = BitVec.ofNat bits (countsBase workspace))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hroom : parentsBase workspace size < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 5) :
    AtSafe rom whole heapWords (packingRun rom whole clock state) := by
  exact (straight_prefix_safe rom whole PSTRParentSentinel.program heapWords origin (fun _ => False)
    slice.bound slice.code PSTRParentSentinel.program_straight hw hpcfit state hp ha
    (access_only _ _ _ state (sentinel_access rom workspace size heapWords state hb ht hroom)) clock hclock).1

end PaperProofs.Structure.LaminarTree.PSTRBootstrapStoreAccess
