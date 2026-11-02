module

public import PaperProofs.Structure.PA17_PackedTranslator_034k

/-! Fetched-word correctness for actual straight packing programs. This
discharges every listed instruction fetch and the terminal HALT. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17PackedPhase045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034

theorem packingRunCorrect_of_straight {bits : Nat} (heapWords : Nat) (rom : PhysicalROM)
    (program : List PackingOp) (heap : BitVec bits → BitVec bits)
    (hstraight : StraightProgram program) (hcode : WordsFit bits (packingCode program))
    (hrom : ∀ region, WordsFit bits (rom.words region))
    (hfoot : Fits bits (rom.size + heapWords + (packingCode program).length))
    (haccess : PackedAccessSafe heapWords rom program (packingInitial heap)) :
    PackingRunCorrect bits heapWords rom program heap := by
  have hpcfit : Fits bits (5 * program.length) := by
    have hh := packingCode_length program
    unfold Fits at *
    omega
  have hrun (count : Nat) (hc : count ≤ program.length) :
      packingRun rom program count (packingInitial heap) =
        executeOps rom (program.take count) (packingInitial heap) :=
    packingRun_eq_executeOps_take rom program _ hstraight hcode hpcfit rfl rfl count hc
  have hpc (count : Nat) (hc : count ≤ program.length) :
      (executeOps rom (program.take count) (packingInitial heap)).pc.toNat = 5 * count := by
    rw [executeOps_pc rom _ _ (fun op ho => hstraight op (List.mem_of_mem_take ho))]
    change (BitVec.ofNat bits 0 + BitVec.ofNat bits (5 * (program.take count).length)).toNat = _
    rw [BitVec.zero_add, List.length_take_of_le hc, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hpcfit)]
  refine ⟨hcode, hrom, hfoot, ?_, ?_⟩
  · intro count hc
    dsimp only
    rw [hrun count hc.le]
    refine ⟨by rw [executeOps_halted]; rfl, hpc count hc.le, ?_, haccess count hc⟩
    change PackingOp.decode (physicalFetch bits (packingCode program)
      (executeOps rom (program.take count) (packingInitial heap)).pc.toNat) = _
    rw [physicalFetch_eq bits (packingCode program) _ hcode, hpc count hc.le]
    exact (congrArg PackingOp.decode (natFetch_body program count hc)).trans (decode_encode _)
  · dsimp only
    rw [hrun program.length le_rfl]
    refine ⟨by rw [executeOps_halted]; rfl, hpc program.length le_rfl, ?_, ?_⟩
    · change PackingOp.decode (physicalFetch bits (packingCode program)
        (executeOps rom (program.take program.length) (packingInitial heap)).pc.toNat) = none
      rw [physicalFetch_eq bits (packingCode program) _ hcode, hpc program.length le_rfl]
      exact (congrArg PackingOp.decode (natFetch_halt program)).trans decode_halt
    · rw [packingRun_executeOps_halt rom program _ hstraight hcode hpcfit rfl rfl]

end PaperProofs.Structure.LaminarTree.PA17PackedPhase045
