module

public import PaperProofs.Structure.RawTreePreprocessingA06Closure
public import PaperProofs.Structure.CompactControllerClaims

set_option autoImplicit false
set_option warningAsError true

/-! Actual ROM-tail insensitivity of the original fixed A06 constructor.
The small prefix relation concerns physical ROM words only; it does not
contain an execution, safety, output, policy or complexity conclusion.
The A06 applications below discharge every actual-load condition from the
already proved original all-clock prefix invariant. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareROM001

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceScanSafety RawIncidenceLaminarRAM

/-- The new input is an actual list extension of every old ROM region. -/
def ROMPrefix (old new : PhysicalROM) : Prop :=
  ∀ region, ∃ tail : List Nat, new.words region = old.words region ++ tail

/-- Only the input region changes, by appending the supplied actual words. -/
def inputTail (rom : PhysicalROM) (tail : List Nat) : PhysicalROM :=
  { rom with input := rom.input ++ tail }

theorem inputTail_prefix (rom : PhysicalROM) (tail : List Nat) :
    ROMPrefix rom (inputTail rom tail) := by
  intro region
  cases region with
  | input => exact ⟨tail, rfl⟩
  | internal => exact ⟨[], by simp only [inputTail, PhysicalROM.words, List.append_nil]⟩
  | children => exact ⟨[], by simp only [inputTail, PhysicalROM.words, List.append_nil]⟩

theorem ROMPrefix.length_le {old new : PhysicalROM} (hprefix : ROMPrefix old new)
    (region : Region) : (old.words region).length ≤ (new.words region).length := by
  obtain ⟨tail, htail⟩ := hprefix region
  rw [htail, List.length_append]
  omega

theorem ROMPrefix.read_eq {old new : PhysicalROM} (hprefix : ROMPrefix old new)
    (region : Region) (address : Nat) (ha : address < (old.words region).length) :
    new.semantic.read region address = old.semantic.read region address := by
  obtain ⟨tail, htail⟩ := hprefix region
  change (new.words region).getD address 0 = (old.words region).getD address 0
  rw [htail]
  exact List.getD_append _ _ _ _ ha

/-- Every old legal memory access remains legal under the ROM extension.
No writable-memory enlargement or word-width change is hidden here. -/
theorem accessFits_of_romPrefix {old new : PhysicalROM} (hprefix : ROMPrefix old new)
    (heapWords : Nat) (state : State) (op : Op) (hfit : AccessFits old heapWords state op) :
    AccessFits new heapWords state op := by
  cases op with
  | subtract target left right => exact hfit
  | base instruction =>
    cases instruction with
    | loadROM region target pointer =>
      exact hfit.trans_le (hprefix.length_le region)
    | constant target value => exact hfit
    | add target left right => exact hfit
    | minimum target left right => exact hfit
    | select target condition whenTrue whenFalse => exact hfit
    | loadHeap target pointer => exact hfit
    | storeHeap pointer source => exact hfit

/-- One actual ordinary operation observes the same old in-range words. -/
theorem natExecuteOp_eq_of_romPrefix {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (heapWords : Nat) (state : NatState) (op : PackingOp)
    (hfit : NatAccessFits old heapWords state op) :
    natExecuteOp new op state = natExecuteOp old op state := by
  cases op with
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl
  | base op =>
    cases op with
    | subtract target left right => rfl
    | base instruction =>
      cases instruction <;> try rfl
      case loadROM region target pointer =>
        have ha : state.register pointer < (old.words region).length := hfit
        simp only [natExecuteOp, Op.execute, Instruction.execute,
          hprefix.read_eq region (state.register pointer) ha]

/-- Same code is fetched; only an actual active ROM load requires its old
in-range certificate. Decoding and the HALT path do not read data ROM. -/
theorem natStep_eq_of_romPrefix {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (heapWords : Nat) (program : List PackingOp)
    (state : NatState)
    (hfit : state.halted = false → ∀ op,
      PackingOp.decode (natFetch program state.pc) = some op →
        NatAccessFits old heapWords state op) :
    natStep new program state = natStep old program state := by
  cases hh : state.halted with
  | true => simp only [natStep, hh, ite_true]
  | false =>
    cases hd : PackingOp.decode (natFetch program state.pc) with
    | none => simp only [natStep, hh, Bool.false_eq_true, ite_false, hd]
    | some op =>
      simp only [natStep, hh, Bool.false_eq_true, ite_false, hd]
      exact natExecuteOp_eq_of_romPrefix hprefix heapWords state op (hfit hh op hd)

/-- Generic induction on the actual old run. The only per-prefix hypothesis
is the ordinary old access condition, never equality of runs or outputs. -/
theorem natRun_eq_of_romPrefix {old new : PhysicalROM}
    (hprefix : ROMPrefix old new) (heapWords : Nat) (program : List PackingOp)
    (initial : NatState) (count : Nat) :
    (∀ clock < count,
      (natRun old program clock initial).halted = false → ∀ op,
        PackingOp.decode (natFetch program (natRun old program clock initial).pc) = some op →
          NatAccessFits old heapWords (natRun old program clock initial) op) →
    natRun new program count initial = natRun old program count initial := by
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
    intro hfit
    have before := ih (fun clock hc => hfit clock (by omega))
    rw [natRun_succ, natRun_succ, before]
    exact natStep_eq_of_romPrefix hprefix heapWords program _ (hfit count (by omega))

/-- Unconditional on runtime safety or laminarity: the proved old A06
invariant supplies every actual read bound for the entire fixed program. -/
theorem raw_natRun_inputTail (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (tail : List Nat) (count : Nat) :
    natRun (inputTail (rawIncidenceROM q full) tail) RawTreePreprocessingNat.program count natInitial =
      natRun (rawIncidenceROM q full) RawTreePreprocessingNat.program count natInitial := by
  apply natRun_eq_of_romPrefix (inputTail_prefix _ _) (RawTreePreprocessingCostBounds.heapWords full.length q)
  intro clock hc hactive op hd
  have hs := RawTreePreprocessingA06Closure.all_prefix_safe q full hq count clock hc
  obtain ⟨_registers, _index, _indexBound, _pc, access⟩ := hs
  simpa only [hd] using access hactive

/-- The actual native-width executions also agree at every clock. Extra
ROM words are not required to fit because this equality proves they are
never read; eligibility of a later complete controller must still check
its full ROM/code/heap footprint separately. -/
theorem raw_wordRun_inputTail (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (tail : List Nat) (count : Nat) :
    let bits := indexWidth 16 full.length q
    let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
    packingRun (inputTail (rawIncidenceROM q full) tail) RawTreePreprocessingNat.program count initial =
      packingRun (rawIncidenceROM q full) RawTreePreprocessingNat.program count initial := by
  let bits := indexWidth 16 full.length q
  have point (clock : Nat) :
      RawTreePreprocessingWordInterface.SafePoint q full
        (natRun (rawIncidenceROM q full) RawTreePreprocessingNat.program clock natInitial) :=
    RawTreePreprocessingA06Closure.all_prefix_safe q full hq (clock + 1) clock (by omega)
  have hcode : WordsFit bits (packingCode RawTreePreprocessingNat.program) :=
    RawTreePreprocessingCostBounds.code_wordsFit full.length q
  have hold := natRun_toWord (rawIncidenceROM q full) RawTreePreprocessingNat.program natInitial count hcode
    (fun clock _hc => ⟨(point clock).1, RawTreePreprocessingWordInterface.safePoint_pcFit q full _ (point clock)⟩)
  have hnew := natRun_toWord (inputTail (rawIncidenceROM q full) tail)
    RawTreePreprocessingNat.program natInitial count hcode (by
      intro clock _hc
      rw [raw_natRun_inputTail q full hq tail clock]
      exact ⟨(point clock).1, RawTreePreprocessingWordInterface.safePoint_pcFit q full _ (point clock)⟩)
  change packingRun _ _ _ (natInitial.toWord bits) = packingRun _ _ _ (natInitial.toWord bits)
  exact hnew.trans ((congrArg (NatState.toWord bits) (raw_natRun_inputTail q full hq tail count)).trans hold.symm)

/-- Actual A19 initial-input tail, with arbitrary original initial used set. -/
theorem controllerInput_natRun_eq_raw (q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (count : Nat) :
    natRun (CompactControllerClaims.controllerInput q full initialUsed)
        RawTreePreprocessingNat.program count natInitial =
      natRun (rawIncidenceROM q full) RawTreePreprocessingNat.program count natInitial :=
  raw_natRun_inputTail q full hq
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed)))) count

theorem controllerInput_wordRun_eq_raw (q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (count : Nat) :
    let bits := indexWidth 16 full.length q
    let initial := packingInitial (fun _ => BitVec.ofNat bits 0)
    packingRun (CompactControllerClaims.controllerInput q full initialUsed)
        RawTreePreprocessingNat.program count initial =
      packingRun (rawIncidenceROM q full) RawTreePreprocessingNat.program count initial :=
  raw_wordRun_inputTail q full hq
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed)))) count

/-- The original raw constructor's precise actual Nat output is transported
unchanged to the genuine A19 input. This is not HeapRepresents or a complete
A19 preprocessor: no ROM reinterpretation, compact-space or free restart is
inferred from the equality. -/
theorem controllerInput_raw_preprocessing (q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (hq : 0 < q) :
    ∃ steps ≤ 16384 * treeWork full.length q,
      let result := natRun (CompactControllerClaims.controllerInput q full initialUsed)
        RawTreePreprocessingNat.program steps natInitial
      result.halted = true ∧ result.register .value ≤ 1 ∧
        (result.register .value = 1 ↔ LaminarSchedule full) ∧
        (LaminarSchedule full → RawTreePreprocessingNat.Output q full result) := by
  obtain ⟨steps, hsteps, result⟩ := RawTreePreprocessingNat.raw_preprocessing q full hq
  refine ⟨steps, hsteps, ?_⟩
  rw [controllerInput_natRun_eq_raw q full initialUsed hq steps]
  exact result

end PaperProofs.Structure.LaminarTree.PA06A19PrepareROM001
