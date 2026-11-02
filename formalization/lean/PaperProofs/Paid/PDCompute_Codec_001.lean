module

public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem readAction_encode (action : MenuAction) (tail : List Cell) :
    readAction (encodeAction action ++ tail) = some (action, tail) := by
  cases action with
  | finish => rfl
  | abandon => rfl
  | test level bad => cases bad <;> rfl

theorem readEntry_encode (entry : MenuEntry) (tail : List Cell) :
    readEntry (encodeEntry entry ++ tail) = some (entry, tail) := by
  cases entry
  simp only [encodeEntry, List.append_assoc, readEntry, readAction_encode, readRat]
  rfl

theorem readMany_encode {α : Type} (read : List Cell → Option (α × List Cell))
    (encode : α → List Cell) (h : ∀ value tail, read (encode value ++ tail) = some (value, tail))
    (values : List α) (tail : List Cell) :
    readMany read values.length (values.flatMap encode ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany, h,
      Option.bind_eq_bind, Option.bind_some, ih]
    rfl

theorem readList_encode {α : Type} (read : List Cell → Option (α × List Cell))
    (encode : α → List Cell) (h : ∀ value tail, read (encode value ++ tail) = some (value, tail))
    (values : List α) (tail : List Cell) :
    readList read (encodeList encode values ++ tail) = some (values, tail) := by
  simpa only [readList, encodeList, List.cons_append, readNat, Option.bind_eq_bind, Option.bind_some] using
    readMany_encode read encode h values tail

theorem readRow_encode (row : MenuRow) (tail : List Cell) :
    readRow (encodeRow row ++ tail) = some (row, tail) := by
  simp only [readRow, encodeRow, readList_encode readEntry encodeEntry readEntry_encode,
    Option.bind_eq_bind, Option.bind_some, Array.toArray_toList]
  rfl

theorem readTable_encode (table : MenuTable) (tail : List Cell) :
    readTable (encodeTable table ++ tail) = some (table, tail) := by
  simp only [readTable, encodeTable, readList_encode readRow encodeRow readRow_encode,
    Option.bind_eq_bind, Option.bind_some, Array.toArray_toList]
  rfl

theorem readSolve_encode (solution : MultiplierSolve) (tail : List Cell) :
    readSolve (encodeSolve solution ++ tail) = some (solution, tail) := by
  cases solution
  simp only [readSolve, encodeSolve, List.cons_append, readRat, Option.bind_eq_bind, Option.bind_some, readTable_encode]
  rfl

theorem readState_encode (state : MultiplierState) (tail : List Cell) :
    readState (encodeState state ++ tail) = some (state, tail) := by
  cases state <;> simp only [readState, encodeState, List.cons_append, List.append_assoc,
    readNat, Option.bind_eq_bind, Option.bind_some, readSolve_encode] <;> rfl

theorem readEndpoint_encode (endpoint : EndpointConstant) (tail : List Cell) :
    readEndpoint (encodeEndpoint endpoint ++ tail) = some (endpoint, tail) := by
  cases endpoint
  rfl

theorem readCalibration_encode (calibration : CalibrationConstant) (tail : List Cell) :
    readCalibration (encodeCalibration calibration ++ tail) = some (calibration, tail) := by
  cases calibration
  rfl

theorem readFrontend_encode (frontend : CachedFrontend) (tail : List Cell) :
    readFrontend (encodeFrontend frontend ++ tail) = some (frontend, tail) := by
  cases frontend
  simp only [readFrontend, encodeFrontend, List.append_assoc,
    readList_encode readEndpoint encodeEndpoint readEndpoint_encode,
    readList_encode readCalibration encodeCalibration readCalibration_encode,
    readState_encode, Option.bind_eq_bind, Option.bind_some, Array.toArray_toList]
  rfl

theorem decodeFrontend_encode (frontend : CachedFrontend) :
    decodeFrontend (encodeFrontend frontend) = some frontend := by
  have h := readFrontend_encode frontend []
  simp only [List.append_nil] at h
  simp only [decodeFrontend, h, Option.bind_eq_bind, Option.bind_some, ite_true, pure]

theorem decodeArtifact_encode (artifact : Artifact) :
    decodeArtifact (encodeArtifact artifact) = some artifact := by
  cases artifact
  simp only [decodeArtifact, encodeArtifact, readFrontend_encode, Option.bind_eq_bind, Option.bind_some, readRat,
    ite_true, pure]

theorem encodeNatBits_length (value : ℕ) :
    (encodeNatBits value).length = 2 * natBits value + 1 := by
  simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.length_ofFn]
  omega

theorem encodeCellBits_length (cell : Cell) : (encodeCellBits cell).length ≤ 2 * cell.bits := by
  cases cell with
  | natural value =>
    simp only [encodeCellBits, List.length_cons, encodeNatBits_length, Cell.bits]
    omega
  | rational value =>
    simp only [encodeCellBits, List.length_append, List.length_cons, List.length_nil,
      encodeNatBits_length, Cell.bits, ratEncodingBits, ratNumBits, ratDenBits]
    omega

theorem codecClaims : CodecClaims :=
  ⟨decodeFrontend_encode, decodeArtifact_encode, 2, by norm_num, encodeCellBits_length⟩

end PDCompute


