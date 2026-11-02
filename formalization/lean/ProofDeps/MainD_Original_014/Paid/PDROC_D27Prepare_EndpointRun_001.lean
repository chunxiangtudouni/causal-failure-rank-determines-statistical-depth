module

public import Paid.PDROC_D27Prepare_Search_007
public import Paid.PDROC_D27Prepare_J_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory

namespace PDROC.D27Prepare.EndpointRun

def region : Finset ℕ := {7, 23, 28, 29, 30, 32, 33, 34}

structure EndpointData (P : Parameters) (memory : SlotMemory) (m : ℕ) : Prop where
  counter : Has memory 7 (.natural m)
  one : Has memory 14 (.natural 1)
  ratOne : Has memory 17 (.rational 1)
  power : Has memory 28 (.rational (P.certificate.odds ^ m))
  odds : Has memory 30 (.rational P.certificate.odds)
  ratio : Has memory 29 (.rational P.certificate.menuRatio)

def stepMemory (P : Parameters) (memory : SlotMemory) (m : ℕ) : SlotMemory :=
  (memory.write 7 (.natural (m + 1))).write 28 (.rational (P.certificate.odds ^ (m + 1)))

def guardMemory (P : Parameters) (memory : SlotMemory) (m : ℕ) : SlotMemory :=
  (memory.write 32 (.rational (1 + P.certificate.odds ^ m))).write 32
    (.rational (P.certificate.menuRatio * (1 + P.certificate.odds ^ m)))

theorem step_data (P : Parameters) (memory : SlotMemory) (m : ℕ) (data : EndpointData P memory m) :
    EndpointData P (stepMemory P memory m) (m + 1) := by
  constructor
  · simp [stepMemory, Has, SlotMemory.write]
  · simpa [stepMemory, Has, SlotMemory.write] using data.one
  · simpa [stepMemory, Has, SlotMemory.write] using data.ratOne
  · simp [stepMemory, Has, SlotMemory.write]
  · simpa [stepMemory, Has, SlotMemory.write] using data.odds
  · simpa [stepMemory, Has, SlotMemory.write] using data.ratio

theorem guard_data (P : Parameters) (memory : SlotMemory) (m : ℕ) (data : EndpointData P memory m) :
    EndpointData P (guardMemory P memory m) m := by
  constructor
  · simpa [guardMemory, Has, SlotMemory.write] using data.counter
  · simpa [guardMemory, Has, SlotMemory.write] using data.one
  · simpa [guardMemory, Has, SlotMemory.write] using data.ratOne
  · simpa [guardMemory, Has, SlotMemory.write] using data.power
  · simpa [guardMemory, Has, SlotMemory.write] using data.odds
  · simpa [guardMemory, Has, SlotMemory.write] using data.ratio

def setupMemory (D : CertificateInput) (memory : SlotMemory) : SlotMemory :=
  let m1 := memory.write 23 (.rational D.t0)
  let m2 := m1.write 32 (.rational (4 * (D.stages : ℚ)))
  let m3 := m2.write 32 (.rational (4 * (D.stages : ℚ) * D.t0))
  let m4 := m3.write 29 (.rational D.menuRatio)
  let m5 := m4.write 32 (.rational (2 * D.gamma))
  let m6 := m5.write 33 (.rational (1 + 2 * D.gamma))
  let m7 := m6.write 34 (.rational (1 - 2 * D.gamma))
  let m8 := m7.write 30 (.rational D.odds)
  m8.write 28 (.rational 1)

theorem setup_eval (D : CertificateInput) (memory : SlotMemory)
    (t0 : Has memory 6 (.natural D.t0)) (ratN : Has memory 22 (.rational D.stages))
    (gamma : Has memory 2 (.rational D.gamma)) (risk : Has memory 3 (.rational D.risk))
    (one : Has memory 17 (.rational 1)) (two : Has memory 18 (.rational 2))
    (four : Has memory 20 (.rational 4)) :
    slotSequenceEval endpointSetupCommands memory = some (setupMemory D memory) := by
  have hn : (D.stages : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.stages_pos)
  have ht : (D.t0 : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.t0_pos)
  have denominator : (4 : ℚ) * D.stages * D.t0 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hn) ht
  simp [endpointSetupCommands, slotSequenceEval, SlotCommand.eval, SlotMemory.write,
    t0.1, t0.2, ratN.1, ratN.2, gamma.1, gamma.2, risk.1, risk.2,
    one.1, one.2, two.1, two.2, four.1, four.2, Cell.nat?, Cell.rat?, RatOp.eval,
    denominator, D.denominator_pos.ne', setupMemory, CertificateInput.menuRatio, CertificateInput.odds]

end PDROC.D27Prepare.EndpointRun
