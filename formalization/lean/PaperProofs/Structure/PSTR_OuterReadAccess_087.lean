module

public import PaperProofs.Structure.PSTR_ArbitraryOutside_086

/-! Actual straight-prefix accesses for leaf preparation and saved-slot
reload. Original cached field reads and the real W locator are reused;
the runtime pointers are never supplied as an extra original input. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTROuterReadAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRCountKernel PSTRCountWorkspace PSTRQueryLayout

theorem park_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < PSTRLeafPrepare.parkAddress.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRLeafPrepare.parkAddress.take count) state)
      PSTRLeafPrepare.parkAddress[count] := by
  change count < 2 at hc
  interval_cases count <;> trivial

theorem width_access {bits : Nat} (rom : PhysicalROM) (workspace heapWords : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) (hroom : workspace + 13 < heapWords)
    (count : Nat) (hc : count < PSTRLeafPrepare.loadWidth.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRLeafPrepare.loadWidth.take count) state)
      PSTRLeafPrepare.loadWidth[count] := by
  change count < 8 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRLeafPrepare.loadWidth, List.take_succ_cons, List.take_zero,
      List.getElem_cons_zero, List.getElem_cons_succ, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, ha, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    apply (Nat.mod_le _ _).trans_lt
    omega

theorem reload_access {bits : Nat} (rom : PhysicalROM) (workspace heapWords : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) (hroom : workspace + 15 < heapWords)
    (count : Nat) (hc : count < PSTRCountRestore.restore.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRCountRestore.restore.take count) state)
      PSTRCountRestore.restore[count] := by
  change count < 7 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRCountRestore.restore, List.take_succ_cons, List.take_zero,
      List.getElem_cons_zero, List.getElem_cons_succ, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, ha, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    apply (Nat.mod_le _ _).trans_lt
    omega

theorem prepare_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : base q full capWords bits + 15 < heapWords) :
    PrefixOK (callInput q full command) heapWords (fun _ => True) PSTRLeafPrepare.program state := by
  let rom := callInput q full command
  let region := fun _ : Nat => True
  let field : Fin 9 := ⟨6, by decide⟩
  let read := executeOps rom (PSTRStaticFields.program field) state
  let parked := executeOps rom PSTRLeafPrepare.parkAddress read
  let located := executeOps rom PSTRCountWorkspace.program parked
  have pfield := fields_prefixOK full command configuration capWords 0 0 heapWords state field node.val hb hq rep hN
    (by simp [field, PSTRStaticLayout.chunks]) hi (by omega)
  have p0 : PrefixOK rom heapWords region (PSTRStaticFields.program field) state :=
    readOnly_prefixOK rom heapWords region _ state (fields_readOnly field) pfield.access
  have p1 : PrefixOK rom heapWords region PSTRLeafPrepare.parkAddress read := by
    apply readOnly_prefixOK
    · simp [PSTRLeafPrepare.parkAddress, ReadOnly]
    · exact park_access rom heapWords read
  have reading := PSTRStaticFields.execute_field full command configuration capWords state field node.val hb hq rep hN
    (by simp [field, PSTRStaticLayout.chunks]) hi
  have parking := PSTRLeafPrepare.park_registers rom read
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by
    rw [parking.2.2, reading.2.2.2]
    exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked hb hq parked_rep
  have p2 : PrefixOK rom heapWords region PSTRCountWorkspace.program parked := by
    apply readOnly_prefixOK _ _ _ _ _ locator_readOnly
    exact PSTRCountWorkspace.prefix_access full command configuration capWords heapWords parked parked_rep (by omega) hb
  have p3 : PrefixOK rom heapWords region PSTRLeafPrepare.loadWidth located := by
    apply readOnly_prefixOK
    · simp [PSTRLeafPrepare.loadWidth, ReadOnly]
    · exact width_access rom (base q full capWords bits) heapWords located locating.1 (by omega)
  have joined := prefixOK_append rom heapWords region (PSTRStaticFields.program field)
    (PSTRLeafPrepare.parkAddress ++ (PSTRCountWorkspace.program ++ PSTRLeafPrepare.loadWidth)) state p0
    (prefixOK_append rom heapWords region PSTRLeafPrepare.parkAddress
      (PSTRCountWorkspace.program ++ PSTRLeafPrepare.loadWidth) read p1
      (prefixOK_append rom heapWords region PSTRCountWorkspace.program PSTRLeafPrepare.loadWidth parked p2 p3))
  simpa only [PSTRLeafPrepare.program, List.append_assoc] using joined

theorem restore_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits + 15 < heapWords) :
    PrefixOK (callInput q full command) heapWords (fun _ => True) PSTRCountRestore.program state := by
  let rom := callInput q full command
  let region := fun _ : Nat => True
  let located := executeOps rom PSTRCountWorkspace.program state
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have p0 : PrefixOK rom heapWords region PSTRCountWorkspace.program state := by
    apply readOnly_prefixOK _ _ _ _ _ locator_readOnly
    exact PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep (by omega) hb
  have p1 : PrefixOK rom heapWords region PSTRCountRestore.restore located := by
    apply readOnly_prefixOK
    · simp [PSTRCountRestore.restore, ReadOnly]
    · exact reload_access rom (base q full capWords bits) heapWords located locating.1 hroom
  exact prefixOK_append rom heapWords region PSTRCountWorkspace.program PSTRCountRestore.restore state p0 p1

theorem prepare_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (whole : List PackingOp) (start : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start PSTRLeafPrepare.program)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : base q full capWords bits + 15 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 51) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  exact (straight_prefix_safe (callInput q full command) whole PSTRLeafPrepare.program heapWords start (fun _ => True)
    slice.bound slice.code PSTRLeafPrepare.program_straight hwords hpcfit state hp ha
    (prepare_prefixOK full command configuration capWords heapWords state node hb hq rep hN hi hroom) clock hclock).1

theorem restore_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (whole : List PackingOp) (start : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start PSTRCountRestore.program)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : base q full capWords bits + 15 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 26) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  exact (straight_prefix_safe (callInput q full command) whole PSTRCountRestore.program heapWords start (fun _ => True)
    slice.bound slice.code PSTRCountRestore.program_straight hwords hpcfit state hp ha
    (restore_prefixOK full command configuration capWords heapWords state hb hq rep hroom) clock hclock).1

end PaperProofs.Structure.LaminarTree.PSTROuterReadAccess
