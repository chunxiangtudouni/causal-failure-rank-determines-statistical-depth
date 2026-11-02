module

public import PaperProofs.Structure.PA17_PackedPhase_045b

/-! The original PackedPhaseRefines target for the actual translator, from
the original body's explicit execution certificates and literal layout. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedPhase045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034

theorem packedPhaseRefines (wordFactor N q t capWords indexWords : Nat)
    (body : List Op) (rom : PhysicalROM)
    (heap : BitVec (indexWidth wordFactor N q) → BitVec (indexWidth wordFactor N q))
    (ht : 0 < t)
    (hl : PA17PackedStore042b.Layout q capWords indexWords
      (physicalSpillBase q (indexWidth wordFactor N q) capWords indexWords)
      (packedCapacityWords q capWords (indexWidth wordFactor N q) + newIndexWords indexWords)
      (indexWidth wordFactor N q))
    (hrom : ∀ region, WordsFit (indexWidth wordFactor N q) (rom.words region))
    (hfoot : Fits (indexWidth wordFactor N q)
      (rom.size + (packedCapacityWords q capWords (indexWidth wordFactor N q) + newIndexWords indexWords) +
        (packingCode (packedProgram q (indexWidth wordFactor N q) capWords indexWords body)).length))
    (hregister : ∀ count ≤ body.length, ∀ register,
      Fits (indexWidth wordFactor N q) ((execute rom.semantic (body.take count)
        (execute rom.semantic (wipe (capWords + indexWords))
          (initial (unpackHeap q capWords (indexWidth wordFactor N q) heap)))).register register))
    (haccess : ∀ count (hc : count < body.length),
      AccessFits rom (capWords + indexWords)
        (execute rom.semantic (body.take count)
          (execute rom.semantic (wipe (capWords + indexWords))
            (initial (unpackHeap q capWords (indexWidth wordFactor N q) heap)))) body[count])
    (hcapacity : CapacityThroughout q capWords rom body
      (execute rom.semantic (wipe (capWords + indexWords))
        (initial (unpackHeap q capWords (indexWidth wordFactor N q) heap)))) :
    PackedPhaseRefines 512 wordFactor N q t capWords (newIndexWords indexWords) rom
      (logicalProgram (capWords + indexWords) body)
      (packedProgram q (indexWidth wordFactor N q) capWords indexWords body) heap := by
  let bits := indexWidth wordFactor N q
  let code := packedProgram q bits capWords indexWords body
  let words := packedCapacityWords q capWords bits + newIndexWords indexWords
  have hd := packedProgram_data_correct q capWords indexWords words body rom heap hl hregister haccess hcapacity
  have hc := packedProgram_codeFit q capWords indexWords words body rom _ hl hregister
  have hs : StraightProgram code := packedProgram_straight q bits capWords indexWords body
  have hp : Fits bits (5 * code.length) := by
    have hh := packingCode_length code
    change Fits bits (rom.size + words + (packingCode code).length) at hfoot
    unfold Fits at *
    omega
  have hrun (count : Nat) (hcount : count ≤ code.length) :=
    packingRun_eq_executeOps_take rom code (packingInitial heap) hs hc hp rfl rfl count hcount
  refine ⟨packingRunCorrect_of_straight words rom code heap hs hc hrom hfoot hd.1, ?_, ?_, ?_,
    packedProgram_cost_le q bits capWords indexWords (capWords + indexWords) body,
    packedPhysicalWords_bitBound q capWords (newIndexWords indexWords) bits, ht⟩
  · rw [hrun code.length le_rfl, List.take_length]
    exact hd.2.2.1
  · rw [hrun code.length le_rfl, List.take_length]
    exact hd.2.2.2
  · intro count hcount
    rw [hrun count hcount]
    exact hd.2.1 count hcount

end PaperProofs.Structure.LaminarTree.PA17PackedPhase045
