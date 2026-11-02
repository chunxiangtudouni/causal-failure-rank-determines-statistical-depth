module

public import PaperProofs.Paid.PDROC_Simulator_022

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}
universe u
variable {SimSeed : Type u}

theorem simulatorStep_writeReport_marks
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (stage : I.Stage) (bit truth : Bool) (serial : ℕ)
    (hm : markedHistory cache.seen = markedHistory cache.shadow)
    (hactual : historyReport cache.seen stage = none) (hvirtual : historyReport cache.shadow stage = none) :
    let next := simulatorStep draw seed (simulatorStep draw seed cache (.wrote stage bit serial)) (.report stage truth serial)
    markedHistory next.seen = markedHistory next.shadow := by
  let record := simulatorDrawRecord (draw seed stage cache.shadow)
  let virtualBit := record.decision.getD bit
  let virtualSerial := (historyActions cache.shadow).length + record.observations.length
  have hseen : historyWritten (cache.seen ++ [.wrote stage bit serial]) stage = some bit := by
    simp only [historyWritten, historyWrite_append_wrote_same, Option.map_some]
  have hshadow : historyWritten ((cache.shadow ++ simulatorReviewPacket stage record) ++
      [.wrote stage virtualBit virtualSerial]) stage = some virtualBit := by
    simp only [historyWritten, historyWrite_append_wrote_same, Option.map_some]
  have hserial : historyWriteSerial ((cache.shadow ++ simulatorReviewPacket stage record) ++
      [.wrote stage virtualBit virtualSerial]) stage = virtualSerial := by
    simp only [historyWriteSerial, historyWrite_append_wrote_same, Option.map_some, Option.getD_some]
  have hdup : record.decision.getD virtualBit = virtualBit := by
    dsimp only [virtualBit]
    cases record.decision <;> rfl
  have hshadowEq : (simulatorStep draw seed (simulatorStep draw seed cache (.wrote stage bit serial)) (.report stage truth serial)).shadow =
      (((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) ++
        [.report stage (Bool.xor truth (Bool.xor virtualBit bit)) virtualSerial]) := by
    simp only [simulatorStep, simulatorAppend, Function.update_self, Option.getD_some]
    simp only [← List.append_assoc]
    change (((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) ++
      [.report stage (Bool.xor truth (Bool.xor (record.decision.getD
        ((historyWritten ((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) stage).getD false))
        ((historyWritten (cache.seen ++ [.wrote stage bit serial]) stage).getD false)))
        (historyWriteSerial ((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) stage)]) = _
    rw [hshadow, hseen, hserial]
    simp only [Option.getD_some, hdup]
  dsimp only
  rw [simulatorStep_seen, simulatorStep_seen, hshadowEq,
    markedHistory_append_writeReport cache.seen stage bit truth serial hactual,
    markedHistory_append_writeReport (cache.shadow ++ simulatorReviewPacket stage record) stage virtualBit
      (Bool.xor truth (Bool.xor virtualBit bit)) virtualSerial
      ((historyReport_append_simulatorReviews cache.shadow stage stage record).trans hvirtual),
    markedHistory_append_simulatorReviews, hm, coordinateFlip_error_flag bit virtualBit truth]

end PDROC
