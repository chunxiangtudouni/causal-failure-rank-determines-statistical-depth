module

public import Paid.PDROC_D27Prepare_Search_006
public import Paid.PDROC_D27Prepare_Memory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid
open PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Search

open Program Memory

def currentMemory (state : State) : SlotMemory := ⟨state.heap, state.live⟩

theorem currentMemory_match (state : State) (fresh : state.register .fresh = .natural 0) :
    MemoryMatch state (currentMemory state) := ⟨rfl, rfl, fresh⟩

/-- Exact proof-memory update of the two literal majority-step macros. -/
theorem majorityStep_eval (D : CertificateInput) (j : ℕ) (memory : SlotMemory)
    (counter : Has memory 6 (.natural (2 * j + 1)))
    (two : Has memory 15 (.natural 2))
    (power : Has memory 28 (.rational (D.varianceBase ^ (2 * j + 1))))
    (varianceSquared : Has memory 26 (.rational (D.varianceBase ^ 2))) :
    slotSequenceEval majorityStepCommands memory = some
      ((memory.write 6 (.natural (2 * (j + 1) + 1))).write 28
        (.rational (D.varianceBase ^ (2 * (j + 1) + 1)))) := by
  let next := memory.write 6 (.natural (2 * (j + 1) + 1))
  apply sequence_cons (.natural .add 6 15 6) [.rational .multiply 28 26 28]
    memory next _
  · apply natural_eval _ .add 6 15 6 (2 * j + 1) 2 _ counter two
    simp only [NatOp.eval, Option.some.injEq]
    omega
  · have hp : Has next 28 (.rational (D.varianceBase ^ (2 * j + 1))) :=
      Has.write_other memory 28 6 _ _ power (by decide)
    have hv : Has next 26 (.rational (D.varianceBase ^ 2)) :=
      Has.write_other memory 26 6 _ _ varianceSquared (by decide)
    have calculated := rational_eval next .multiply 28 26 28 _ _
      (D.varianceBase ^ (2 * (j + 1) + 1)) hp hv
      (by simp only [RatOp.eval, Option.some.injEq]; exact (majority_power_step D j).symm)
    simp only [slotSequenceEval, calculated, Option.bind_some, next]

theorem endpointStep_eval (D : CertificateInput) (m : ℕ) (memory : SlotMemory)
    (counter : Has memory 7 (.natural m)) (one : Has memory 14 (.natural 1))
    (power : Has memory 28 (.rational (D.odds ^ m)))
    (odds : Has memory 30 (.rational D.odds)) :
    slotSequenceEval endpointStepCommands memory = some
      ((memory.write 7 (.natural (m + 1))).write 28 (.rational (D.odds ^ (m + 1)))) := by
  let next := memory.write 7 (.natural (m + 1))
  apply sequence_cons (.natural .add 7 14 7) [.rational .multiply 28 30 28]
    memory next _
  · exact natural_eval _ .add 7 14 7 m 1 _ counter one rfl
  · have hp : Has next 28 (.rational (D.odds ^ m)) :=
      Has.write_other memory 28 7 _ _ power (by decide)
    have ho : Has next 30 (.rational D.odds) :=
      Has.write_other memory 30 7 _ _ odds (by decide)
    have calculated := rational_eval next .multiply 28 30 28 _ _
      (D.odds ^ (m + 1)) hp ho
      (by simp only [RatOp.eval, Option.some.injEq]; exact (endpoint_power_step D m).symm)
    simp only [slotSequenceEval, calculated, Option.bind_some, next]

theorem exponentStep_eval (e : ℕ) (memory : SlotMemory)
    (counter : Has memory 8 (.natural e)) (one : Has memory 14 (.natural 1))
    (power : Has memory 28 (.rational ((1 / 2 : ℚ) ^ e)))
    (half : Has memory 21 (.rational (1 / 2))) :
    slotSequenceEval exponentStepCommands memory = some
      ((memory.write 8 (.natural (e + 1))).write 28 (.rational ((1 / 2 : ℚ) ^ (e + 1)))) := by
  let next := memory.write 8 (.natural (e + 1))
  apply sequence_cons (.natural .add 8 14 8) [.rational .multiply 28 21 28]
    memory next _
  · exact natural_eval _ .add 8 14 8 e 1 _ counter one rfl
  · have hp : Has next 28 (.rational ((1 / 2 : ℚ) ^ e)) :=
      Has.write_other memory 28 8 _ _ power (by decide)
    have hh : Has next 21 (.rational (1 / 2)) :=
      Has.write_other memory 21 8 _ _ half (by decide)
    have calculated := rational_eval next .multiply 28 21 28 _ _
      ((1 / 2 : ℚ) ^ (e + 1)) hp hh
      (by simp only [RatOp.eval, Option.some.injEq]; exact (exponent_power_step e).symm)
    simp only [slotSequenceEval, calculated, Option.bind_some, next]

def endpointTestCommands : List SlotCommand :=
  [.rational .add 17 28 32, .rational .multiply 29 32 32]

theorem endpointGuard_compiled : endpointGuard = slotSequenceCode endpointTestCommands ++
    ratCompareSlots .lessEqual 17 32 := rfl

theorem endpointTest_eval (D : CertificateInput) (m : ℕ) (memory : SlotMemory)
    (one : Has memory 17 (.rational 1))
    (power : Has memory 28 (.rational (D.odds ^ m)))
    (menuRatio : Has memory 29 (.rational D.menuRatio)) :
    slotSequenceEval endpointTestCommands memory = some
      ((memory.write 32 (.rational (1 + D.odds ^ m))).write 32
        (.rational (D.menuRatio * (1 + D.odds ^ m)))) := by
  let next := memory.write 32 (.rational (1 + D.odds ^ m))
  apply sequence_cons (.rational .add 17 28 32) [.rational .multiply 29 32 32]
    memory next _
  · exact rational_eval _ .add 17 28 32 1 (D.odds ^ m) _ one power rfl
  · have hr : Has next 29 (.rational D.menuRatio) :=
      Has.write_other memory 29 32 _ _ menuRatio (by decide)
    have hx : Has next 32 (.rational (1 + D.odds ^ m)) := Has.write_same _ _ _
    have calculated := rational_eval next .multiply 29 32 32 _ _ _ hr hx rfl
    simp only [slotSequenceEval, calculated, Option.bind_some, next]

end PDROC.D27Prepare.Search
