module

public import Structure.PA06_A19Prepare_InitializedFront086
public import Structure.PA06_A19Prepare_ROM_001

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED physical transport of ONE actual initialized front.
The original controller ROM tail is appended by the proved ROMPrefix
transport at every same clock. All082 code/PC premises are internal. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims

theorem word_prefix_of_points (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (clock : Nat) (points : PrefixSafe (Point q full) (rawIncidenceROM q full) program natInitial clock) :
    (∀ count ≤ clock,
      packingRun (controllerInput q full used) program count (natInitial.toWord (bits q full)) =
        (natRun (rawIncidenceROM q full) program count natInitial).toWord (bits q full)) ∧
      ∀ count < clock, PA06A19PrepareInitialUsed037.Fetched (allocation q full)
        (controllerInput q full used) program
        (packingRun (controllerInput q full used) program count (natInitial.toWord (bits q full))) := by
  let rom := controllerInput q full used
  have hprefix : PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full) rom :=
    PA06A19PrepareROM001.inputTail_prefix (rawIncidenceROM q full)
      ((List.finRange q).map (fun tool => bit (decide (tool ∈ used))))
  have words := PA06A19PrepareAllQCode082.selected_encoded_words_fit full.length q
  have rawEq (count : Nat) (bound : count ≤ clock) :
      natRun rom program count natInitial = natRun (rawIncidenceROM q full) program count natInitial := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix hprefix (allocation q full)
    intro step hs _active op decoded
    obtain ⟨_registers, _pcFit, _a, index, hi, pc, access⟩ := points step (by omega)
    rw [pc, natFetch_body program index hi, decode_encode] at decoded
    have sameOp : program[index] = op := Option.some.inj decoded
    rw [← sameOp]
    exact access
  have refined (count : Nat) (bound : count ≤ clock) :
      packingRun rom program count (natInitial.toWord (bits q full)) =
        (natRun (rawIncidenceROM q full) program count natInitial).toWord (bits q full) := by
    have actual := natRun_toWord rom program natInitial count words (by
      intro step hs
      rw [rawEq step (by omega)]
      have point := points step (by omega)
      exact ⟨point.1, point.2.1⟩)
    exact actual.trans (congrArg (NatState.toWord (bits q full)) (rawEq count bound))
  refine ⟨refined, ?_⟩
  intro count bound
  obtain ⟨registers, pcFit, active, index, hi, pc, access⟩ := points count bound
  have wordPC : ((natRun (rawIncidenceROM q full) program count natInitial).toWord (bits q full)).pc.toNat =
      (natRun (rawIncidenceROM q full) program count natInitial).pc := by
    change (BitVec.ofNat (bits q full) _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit]
  rw [refined count bound.le]
  refine ⟨active, ?_, program[index], ?_, ?_⟩
  · rw [wordPC, pc, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch (bits q full) (packingCode program)
      ((natRun (rawIncidenceROM q full) program count natInitial).toWord (bits q full)).pc.toNat) = some (program[index])
    rw [wordPC, pc, physicalFetch_eq _ _ _ words]
    change PackingOp.decode (natFetch program (5 * index)) = some program[index]
    rw [natFetch_body program index hi, decode_encode]
  · apply physical_access_of_nat rom (allocation q full) _ _ registers
    cases shape : program[index] with
    | base instruction =>
      exact PA06A19PrepareROM001.accessFits_of_romPrefix hprefix (allocation q full) _ instruction
        (by simpa only [NatAccessFits, shape] using access)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

/-- ONE selected checker boundary is extended by its actual2+16 steps.
The output Nat witness really starts at natInitial; the Word endpoint and
every fetched proper prefix use the SAME frontClock and ONE082.program. -/
theorem initialized_front (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (laminar : LaminarSchedule full) :
    ∃ clock ≤ checkerSteps full.length q + 17,
      let before := natRun (rawIncidenceROM q full) program clock natInitial
      let actual := packingRun (controllerInput q full used) program clock (natInitial.toWord (bits q full))
      PA06A19PrepareAfterGate081.Initialized q full before ∧ actual = before.toWord (bits q full) ∧
        (∀ count ≤ clock,
          packingRun (controllerInput q full used) program count (natInitial.toWord (bits q full)) =
            (natRun (rawIncidenceROM q full) program count natInitial).toWord (bits q full)) ∧
        ∀ count < clock, PA06A19PrepareInitialUsed037.Fetched (allocation q full)
          (controllerInput q full used) program
          (packingRun (controllerInput q full used) program count (natInitial.toWord (bits q full))) := by
  obtain ⟨clock, bound, entry, points⟩ := initialized_front_nat q full hq laminar
  have bridge := word_prefix_of_points q full used clock points
  exact ⟨clock, bound, entry, bridge.1 clock le_rfl, bridge.1, bridge.2⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086
