module

public import Paid.PDROC_D27Prepare_EndpointRun_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.EndpointRun

theorem guard_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (m : ℕ)
    (range : m ≤ P.certificate.M) (data : EndpointData P memory m)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory) :
    SequenceMemoryBounds Search.endpointTestCommands memory 64 (operandBudget P fee) := by
  let middle := memory.write 32 (.rational (1 + P.certificate.odds ^ m))
  have first := rational_eval memory .add 17 28 32 1 (P.certificate.odds ^ m)
    (1 + P.certificate.odds ^ m) data.ratOne data.power rfl
  have second := rational_eval middle .multiply 29 32 32 P.certificate.menuRatio
    (1 + P.certificate.odds ^ m) (P.certificate.menuRatio * (1 + P.certificate.odds ^ m))
    (Has.write_other memory 29 32 _ _ data.ratio (by decide)) (Has.write_same _ _ _) rfl
  have bits := endpoint_guard_intermediate_bits P fee m range
  have b1 := bounded.write 32 (.rational (1 + P.certificate.odds ^ m)) (by decide) bits.1
  have b2 : MemoryBounds 64 (operandBudget P fee) (guardMemory P memory m) :=
    b1.write 32 (.rational (P.certificate.menuRatio * (1 + P.certificate.odds ^ m))) (by decide) bits.2
  exact SequenceMemoryBounds.cons _ _ memory middle 64 _ bounded first
    (SequenceMemoryBounds.cons _ [] middle (guardMemory P memory m) 64 _ b1 second
      (SequenceMemoryBounds.nil _ _ _ b2))

theorem step_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (m : ℕ)
    (range : m < P.certificate.M) (data : EndpointData P memory m)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory) :
    SequenceMemoryBounds endpointStepCommands memory 64 (operandBudget P fee) := by
  let middle := memory.write 7 (.natural (m + 1))
  have first := natural_eval memory .add 7 14 7 m 1 (m + 1) data.counter data.one rfl
  have second := rational_eval middle .multiply 28 30 28 (P.certificate.odds ^ m) P.certificate.odds
    (P.certificate.odds ^ (m + 1))
    (Has.write_other memory 28 7 _ _ data.power (by decide))
    (Has.write_other memory 30 7 _ _ data.odds (by decide))
    (by simp only [RatOp.eval, Option.some.injEq]; exact (Search.endpoint_power_step P.certificate m).symm)
  have hM := (scalar_data_bounds P fee).2.2.1
  have counterBits := natural_small_bits P fee (m + 1) (by omega)
  have powerBits := odds_power_bits P fee (m + 1) (by omega)
  have b1 := bounded.write 7 (.natural (m + 1)) (by decide) counterBits
  have b2 : MemoryBounds 64 (operandBudget P fee) (stepMemory P memory m) :=
    b1.write 28 (.rational (P.certificate.odds ^ (m + 1))) (by decide) powerBits
  exact SequenceMemoryBounds.cons _ _ memory middle 64 _ bounded first
    (SequenceMemoryBounds.cons _ [] middle (stepMemory P memory m) 64 _ b1 second
      (SequenceMemoryBounds.nil _ _ _ b2))

end PDROC.D27Prepare.EndpointRun
