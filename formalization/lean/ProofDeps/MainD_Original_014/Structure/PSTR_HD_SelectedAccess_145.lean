module

public import Structure.PSTR_HD_SelectedFrame_144
public import Structure.PSTR_LeafUsedAccess_089

/-! Every actual memory/ROM access of selected-error102. The42-op entry
is checked at its actual saved-state, then repair21 and restore10 at their
actual cursor/header states. No all-clock safety premise is assumed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRReplySpill PSTRCountKernel

theorem access_append {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (left right : List PackingOp) (state : WordState bits)
    (hl : ∀ count (hc : count < left.length), packingAccessFits rom heapWords (executeOps rom (left.take count) state) left[count])
    (hr : ∀ count (hc : count < right.length), packingAccessFits rom heapWords
      (executeOps rom (right.take count) (executeOps rom left state)) right[count]) :
    ∀ count (hc : count < (left ++ right).length),
      packingAccessFits rom heapWords (executeOps rom ((left ++ right).take count) state) (left ++ right)[count] := by
  have first : PrefixOK rom heapWords (fun _ => False) left state := ⟨hl, by intro _ _ _ _ h; exact False.elim h⟩
  have second : PrefixOK rom heapWords (fun _ => False) right (executeOps rom left state) :=
    ⟨hr, by intro _ _ _ _ h; exact False.elim h⟩
  exact (prefixOK_append rom heapWords (fun _ => False) left right state first second).access

theorem cursor_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < cursorProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (cursorProgram.take count) state) cursorProgram[count] := by
  change count < 2 at hc
  interval_cases count <;> exact True.intro

theorem prepare_access {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords heapWords : Nat) (state : WordState bits) (room : Rooms full capWords bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (heapRoom : PSTRCountWorkspace.base q full capWords bits + 12 < heapWords) :
    ∀ count (hc : count < prepareProgram.length),
      packingAccessFits (callInput q full .error) heapWords
        (executeOps (callInput q full .error) (prepareProgram.take count) state) prepareProgram[count] :=
  access_append (callInput q full .error) heapWords PSTRCountWorkspace.program cursorProgram state
    (PSTRCountWorkspace.prefix_access full .error configuration capWords heapWords state rep (by omega) room.bits_eight)
    (cursor_access (callInput q full .error) heapWords _)

theorem controls_access {bits : Nat} (rom : PhysicalROM) (heapWords workspace : Nat) (state : WordState bits)
    (room : Fits bits (workspace + 12)) (heapRoom : workspace + 12 < heapWords)
    (address : state.register .address = BitVec.ofNat bits workspace)
    (count : Nat) (hc : count < PSTRRepairEntry.loadControls.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRRepairEntry.loadControls.take count) state) PSTRRepairEntry.loadControls[count] := by
  have hw11 : Fits bits (workspace + 11) := (show workspace + 11 ≤ workspace + 12 by omega).trans_lt room
  have h12 : workspace + 11 + 1 = workspace + 12 := by omega
  change count < 7 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRRepairEntry.loadControls, List.take_succ_cons, List.take_zero,
      List.getElem_cons_zero, List.getElem_cons_succ, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, address, BitVec.ofNat_add_ofNat, h12, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hw11, Nat.mod_eq_of_lt room]
    omega

theorem entry_access {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords heapWords : Nat) (state : WordState bits) (hq : 0 < q) (room : Rooms full capWords bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (heapRoom : PSTRCountWorkspace.base q full capWords bits + 12 < heapWords) :
    ∀ count (hc : count < PSTRRepairEntry.program.length),
      packingAccessFits (callInput q full .error) heapWords
        (executeOps (callInput q full .error) (PSTRRepairEntry.program.take count) state) PSTRRepairEntry.program[count] := by
  let rom := callInput q full .error
  let located := executeOps rom PSTRCountWorkspace.program state
  have locating := PSTRCountWorkspace.execute_base full .error configuration capWords state room.bits_eight hq rep
  have first := access_append rom heapWords PSTRCountWorkspace.program PSTRRepairEntry.loadControls state
    (PSTRCountWorkspace.prefix_access full .error configuration capWords heapWords state rep (by omega) room.bits_eight)
    (controls_access rom heapWords _ located room.workspace heapRoom locating.1)
  have hinput : 1 < rom.input.length := by
    simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hheap : 0 < heapWords := by omega
  have second := access_append rom heapWords (PSTRCountWorkspace.program ++ PSTRRepairEntry.loadControls)
    PSTRLeafUsed.setup state first (PSTRLeafUsedAccess.setup_access rom heapWords _ hinput hheap)
  simpa only [PSTRRepairEntry.program, List.append_assoc] using second

theorem prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords heapWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q capWords state))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (heapRoom : PSTRCountWorkspace.base q full capWords bits + 12 < heapWords) :
    ∀ count (hc : count < program.length),
      packingAccessFits (callInput q full .error) heapWords
        (executeOps (callInput q full .error) (program.take count) state) program[count] := by
  let rom := callInput q full .error
  let workspace := PSTRCountWorkspace.base q full capWords bits
  have prep := prepare_values full .error configuration capWords state room.bits_eight hq rep
  have data := execute_entry_data full configuration capWords state tool hq allowed choose room rep reply savedWidth
  have geometry := entry_geometry full configuration capWords state tool hq room data
  have spRep : HeapRepresents q full capWords configuration (savedState rom state).heap := by
    rw [← entry_heap rom state]
    exact data.represented
  have first := access_append rom heapWords prepareProgram spillProgram state
    (prepare_access full configuration capWords heapWords state room rep heapRoom)
    (PSTRReplySafety.spill_access rom _ (workspace + 8) heapWords prep.1
      ((show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room.workspace) (by omega))
  have second := access_append rom heapWords (prepareProgram ++ spillProgram) PSTRRepairEntry.program state first
    (by simpa only [executeOps_append, savedState] using
      (entry_access full configuration capWords heapWords (savedState rom state) hq room spRep heapRoom))
  have hws := workspace_exact full capWords bits hq
  have hg := geometry.2.2.1
  change ((entryState rom state).register .address).toNat * CapacityBits.width q / bits < packedCapacityWords q capWords bits at hg
  have repairAccess := PSTRRepairSafety.repair_access rom (entryState rom state) heapWords (packedCapacityWords q capWords bits)
    room.bits_eight room.width data.width data.represented.2.2.2.1 data.represented.2.2.1 geometry.2.1 geometry.2.2.2
    (by omega) (Rooms.metadata full capWords bits room hq 0 (by omega)) (by omega)
  have third := access_append rom heapWords ((prepareProgram ++ spillProgram) ++ PSTRRepairEntry.program)
    PSTRRuntimeRepair.program state second
    (by simpa only [executeOps_append, entryState, savedState] using repairAccess)
  have cursor : (repairState rom state).register .flag = BitVec.ofNat bits (workspace + 8 + 3) := by
    rw [repairState, repair_cursor]
    exact data.cursor
  have restoreAccess := PSTRReplySafety.restore_access rom (repairState rom state) (workspace + 8) heapWords cursor
    ((show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room.workspace) (by omega)
  have fourth := access_append rom heapWords (((prepareProgram ++ spillProgram) ++ PSTRRepairEntry.program) ++ PSTRRuntimeRepair.program)
    restoreProgram state third
    (by simpa only [executeOps_append, repairState, entryState, savedState] using restoreAccess)
  exact fourth

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
