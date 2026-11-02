module

public import PaperProofs.Structure.PA17_PackedTranslator_034h

/-! Whole-body induction for the concrete packed translator. The hypotheses
are the original logical program's actual prefix certificates. No macro
simulation or safety contract is assumed. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

theorem translateBody_correct {bits : Nat} (q capWords indexWords spillBase heapWords : Nat)
    (body : List Op) (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical)
    (hregister : ∀ count ≤ body.length, ∀ register,
      Fits bits ((execute rom.semantic (body.take count) logical).register register))
    (haccess : ∀ count (hc : count < body.length),
      AccessFits rom (capWords + indexWords)
        (execute rom.semantic (body.take count) logical) body[count])
    (hcapacity : CapacityThroughout q capWords rom body logical) :
    PackedAccessSafe heapWords rom (body.flatMap (translateOp q bits capWords spillBase)) physical ∧
      PA17PackedStore042b.CapacitySafe q capWords rom
        (body.flatMap (translateOp q bits capWords spillBase)) physical ∧
      SpillSim q capWords indexWords spillBase (execute rom.semantic body logical)
        (executeOps rom (body.flatMap (translateOp q bits capWords spillBase)) physical) := by
  induction body generalizing logical physical with
  | nil =>
    refine ⟨PackedAccessSafe.nil heapWords rom physical, ?_, hs⟩
    intro count hc
    have hz : count = 0 := by simp at hc; omega
    subst count
    exact hs.capacity (hcapacity 0 (by simp))
  | cons op later ih =>
    have hone := translateOp_correct q capWords indexWords spillBase heapWords op rom logical physical hl hs
      (haccess 0 (by simp))
      (hregister 1 (by simp)) (hcapacity 0 (by simp)) (hcapacity 1 (by simp))
    have hr : ∀ count ≤ later.length, ∀ register,
        Fits bits ((execute rom.semantic (later.take count) (op.execute rom.semantic logical)).register register) := by
      intro count hc register
      exact hregister (count + 1) (by simp only [List.length_cons]; omega) register
    have ha : ∀ count (hc : count < later.length),
        AccessFits rom (capWords + indexWords)
          (execute rom.semantic (later.take count) (op.execute rom.semantic logical)) later[count] := by
      intro count hc
      exact haccess (count + 1) (by simp only [List.length_cons]; omega)
    have hb : CapacityThroughout q capWords rom later (op.execute rom.semantic logical) := by
      intro count hc
      exact hcapacity (count + 1) (by simp only [List.length_cons]; omega)
    have htail := ih (op.execute rom.semantic logical)
      (executeOps rom (translateOp q bits capWords spillBase op) physical) hone.2.2 hr ha hb
    rw [List.flatMap_cons, executeOps_append]
    exact ⟨PackedAccessSafe.append heapWords rom _ _ physical hone.1 htail.1,
      PA17PackedStore042b.CapacitySafe.append q capWords rom _ _ physical hone.2.1 htail.2.1,
      htail.2.2⟩

theorem translateBody_correct_of_finiteSafe {bits : Nat} (q capWords indexWords spillBase heapWords : Nat)
    (body : List Op) (rom : PhysicalROM) (logical : State) (physical : WordState bits)
    (hl : PA17PackedStore042b.Layout q capWords indexWords spillBase heapWords bits)
    (hs : SpillSim q capWords indexWords spillBase logical physical)
    (hfinite : FiniteSafe bits (capWords + indexWords) rom body logical)
    (hcapacity : CapacityThroughout q capWords rom body logical) :
    PackedAccessSafe heapWords rom (body.flatMap (translateOp q bits capWords spillBase)) physical ∧
      PA17PackedStore042b.CapacitySafe q capWords rom
        (body.flatMap (translateOp q bits capWords spillBase)) physical ∧
      SpillSim q capWords indexWords spillBase (execute rom.semantic body logical)
        (executeOps rom (body.flatMap (translateOp q bits capWords spillBase)) physical) := by
  exact translateBody_correct q capWords indexWords spillBase heapWords body rom logical physical hl hs
    (fun count hc => (hfinite.2.2.2.1 count hc).2.1) hfinite.2.2.2.2 hcapacity

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
