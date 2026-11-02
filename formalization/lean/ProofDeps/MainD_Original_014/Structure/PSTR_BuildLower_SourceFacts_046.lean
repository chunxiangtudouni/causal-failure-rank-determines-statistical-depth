module

public import Structure.PSTR_BuildLower_SourceInput_044
public import Structure.PSTR_BuildLower_ROMUse_020
public import PaperProofs.Structure.PA17_FullBuildWord_036c

/-! Facts about the ORIGINAL executed source program, obtained from its proved
numeric and capacity invariants. These discharge internal port obligations;
no source safety, successful execution or performance oracle is a caller field. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceFacts
open IndexedRAM IndexedClosureRAM AlgorithmClaims

abbrev size (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  (prepareNormalization q full).indexed.nodes.size

abbrev program (q : Nat) (full : List (Finset (Fin q))) : List Op :=
  PA17TableBuild005.buildProgram full.length q (size q full)

abbrev before (q : Nat) (full : List (Finset (Fin q))) (count : Nat) : State :=
  IndexedClosureRAM.execute (givenTreeROM q full).semantic ((program q full).take count) (initial (fun _ => 0))

theorem before_next (q : Nat) (full : List (Finset (Fin q))) (count : Nat)
    (hc : count < (program q full).length) :
    before q full (count + 1) = ((program q full)[count]).execute (givenTreeROM q full).semantic (before q full count) := by
  simp only [before, List.take_succ_eq_append_getElem hc, IndexedClosureRAM.execute_append,
    IndexedClosureRAM.execute]

theorem register_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (count : Nat) (hc : count ≤ (program q full).length) (reg : Register) :
    Fits (indexWidth 32 full.length q) ((before q full count).register reg) := by
  apply PA17WordBounds023.cubic_fits
  exact (PA17FullBuildWord036c.prepared_program_numeric q full hq hlaminar).1 count hc reg

theorem access (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (count : Nat) (hc : count < (program q full).length) :
    AccessFits (givenTreeROM q full) (PA17QueryLayout014.heapWords full.length q (size q full))
      (before q full count) (program q full)[count] :=
  (PA17FullBuildWord036c.prepared_program_numeric q full hq hlaminar).2 count hc

theorem capacity (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (count : Nat) (hc : count ≤ (program q full).length) :
    CapacityPrefixBounded q (PA17CellLayout003.capacityWords full.length q (size q full)) (before q full count).heap :=
  PA17BuildCapacity007.prepared_build_capacityThroughout q full hq hlaminar count hc

theorem packed_store_value (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (count : Nat) (hc : count < (program q full).length)
    (pointer source : Register) (hop : (program q full)[count] = .base (.storeHeap pointer source))
    (hp : (before q full count).register pointer < PA17CellLayout003.capacityWords full.length q (size q full)) :
    (before q full count).register source ≤ q := by
  have hb := capacity q full hq hlaminar (count + 1) (by omega) ((before q full count).register pointer) hp
  rw [before_next q full count hc, hop] at hb
  simpa only [Op.execute, Instruction.execute, Function.update_self] using hb

theorem store_address (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (count : Nat) (hc : count < (program q full).length)
    (pointer source : Register) (hop : (program q full)[count] = .base (.storeHeap pointer source)) :
    (before q full count).register pointer < PA17QueryLayout014.heapWords full.length q (size q full) := by
  have hh := access q full hq hlaminar count hc
  simpa only [hop, AccessFits] using hh

theorem input_lower (q : Nat) (full : List (Finset (Fin q))) (count : Nat)
    (hc : count < (program q full).length) (target pointer : Register)
    (hop : (program q full)[count] = .base (.loadROM .input target pointer)) :
    3 ≤ (before q full count).register pointer := by
  have hh := SourceInput.fullBuild_input_lower full.length q (size q full) (fun _ => 0)
    (givenTreeROM q full) (initial (fun _ => 0)) count hc
  simpa only [hop, SourceInput.stepLower] using hh

theorem input_upper (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (count : Nat) (hc : count < (program q full).length)
    (target pointer : Register) (hop : (program q full)[count] = .base (.loadROM .input target pointer)) :
    (before q full count).register pointer < (givenTreeROM q full).input.length := by
  have hh := access q full hq hlaminar count hc
  simpa only [hop, AccessFits, PhysicalROM.words] using hh

theorem no_children (q : Nat) (full : List (Finset (Fin q))) (count : Nat)
    (hc : count < (program q full).length) : plainReadsChildren (program q full)[count] = false :=
  original_buildProgram_no_children full.length q (size q full) _ (List.getElem_mem hc)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceFacts
