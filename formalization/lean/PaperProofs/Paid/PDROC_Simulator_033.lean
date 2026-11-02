module

public import PaperProofs.Paid.PDROC_Simulator_032

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Full packet identity, retaining all observations and both exact virtual
serials, rather than only a record or marked-history projection. -/
theorem simulatorStep_writeReport_shadow {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    let record := simulatorDrawRecord (draw seed stage cache.shadow)
    let virtualBit := record.decision.getD bit
    let virtualSerial := (historyActions cache.shadow).length + record.observations.length
    (simulatorStep draw seed (simulatorStep draw seed cache (.wrote stage bit serial)) (.report stage truth serial)).shadow =
      (cache.shadow ++ simulatorReviewPacket stage record) ++
        [.wrote stage virtualBit virtualSerial,
          .report stage (Bool.xor truth (Bool.xor virtualBit bit)) virtualSerial] := by
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
  simp only [simulatorStep, simulatorAppend, Function.update_self, Option.getD_some]
  simp only [← List.append_assoc]
  change (((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) ++
    [.report stage (Bool.xor truth (Bool.xor (record.decision.getD
      ((historyWritten ((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) stage).getD false))
      ((historyWritten (cache.seen ++ [.wrote stage bit serial]) stage).getD false)))
      (historyWriteSerial ((cache.shadow ++ simulatorReviewPacket stage record) ++ [.wrote stage virtualBit virtualSerial]) stage)]) = _
  rw [hshadow, hseen, hserial]
  simp only [Option.getD_some, hdup, List.append_assoc, List.singleton_append]
  rfl

theorem simulatorReplay_writeReport_shadow {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    let shadow := (simulatorReplay draw seed history).shadow
    let record := simulatorDrawRecord (draw seed stage shadow)
    let virtualBit := record.decision.getD bit
    let virtualSerial := (historyActions shadow).length + record.observations.length
    (simulatorReplay draw seed (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow =
      (shadow ++ simulatorReviewPacket stage record) ++
        [.wrote stage virtualBit virtualSerial,
          .report stage (Bool.xor truth (Bool.xor virtualBit bit)) virtualSerial] := by
  have h := simulatorStep_writeReport_shadow draw seed (simulatorReplay draw seed history) stage bit truth serial
  simpa only [simulatorReplay, List.foldl_append, List.foldl_cons, List.foldl_nil] using h

end PDROC
