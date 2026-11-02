module

public import Structure.PSTR_HD_HeadsBranches_063

/-! Literal slices of the fixed heads tail inside its SAME whole program.
All positions are compile-time offsets; none depends on runtime dimensions.
The getD transport avoids dependent-index rewriting across module boundaries. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem heads_tail_code (queryBody : List PackingOp) :
    ∀ i (hi : i < (tailAt queryBody.length).length),
      (headsProgram queryBody)[queryBody.length + i]'(by rw [headsProgram_length]; rw [tailAt_length] at hi; omega) =
        (tailAt queryBody.length)[i] := by
  intro i hi
  change (queryBody ++ tailAt queryBody.length)[queryBody.length + i]'(by simp only [List.length_append]; omega) = _
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem tail_slice (whole block : List PackingOp) (origin offset : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hsub : offset + block.length ≤ (tailAt origin).length)
    (hslice : ((tailAt origin).drop offset).take block.length = block) :
    ∀ i (hi : i < block.length), whole[(origin + offset) + i]'(by omega) = block[i] := by
  intro i hi
  have ht : i < ((tailAt origin).drop offset).length := by
    simp only [List.length_drop]
    omega
  have hg := congrArg (fun ops : List PackingOp => ops.getD i (.base (.base (.constant .value 0)))) hslice
  rw [List.getD_eq_getElem (n := i) (((tailAt origin).drop offset).take block.length)
      (.base (.base (.constant .value 0))) (by simp only [List.length_take]; omega),
    List.getD_eq_getElem (n := i) block (.base (.base (.constant .value 0))) hi] at hg
  simp only [List.getElem_take, List.getElem_drop] at hg
  have hc := hcode (offset + i) (by omega)
  simpa only [Nat.add_assoc] using hc.trans hg

theorem endpoint_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < endpointProgram.length), whole[origin + i]'(by rw [tailAt_length, endpointProgram_length] at *; omega) = endpointProgram[i] := by
  simpa only [Nat.add_zero] using tail_slice whole endpointProgram origin 0 hbound hcode (by change 0 + 31 ≤ 111; decide) rfl

theorem stageProbe_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < stageProbe.length), whole[(origin + 31) + i]'(by rw [tailAt_length, stageProbe_length] at *; omega) = stageProbe[i] :=
  tail_slice whole stageProbe origin 31 hbound hcode (by change 31 + 7 ≤ 111; decide) rfl

theorem terminalLead_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < (terminalLead origin).length), whole[(origin + 40) + i]'(by rw [tailAt_length, terminalLead_length] at *; omega) = (terminalLead origin)[i] :=
  tail_slice whole (terminalLead origin) origin 40 hbound hcode (by change 40 + 2 ≤ 111; decide) rfl

theorem finiteLead_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < (finiteLead origin).length), whole[(origin + 43) + i]'(by rw [tailAt_length, finiteLead_length] at *; omega) = (finiteLead origin)[i] :=
  tail_slice whole (finiteLead origin) origin 43 hbound hcode (by change 43 + 4 ≤ 111; decide) rfl

theorem guardLead_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < (guardLead origin).length), whole[(origin + 48) + i]'(by rw [tailAt_length, guardLead_length] at *; omega) = (guardLead origin)[i] :=
  tail_slice whole (guardLead origin) origin 48 hbound hcode (by change 48 + 7 ≤ 111; decide) rfl

theorem headsCorrect_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < headsCorrect.length), whole[(origin + 56) + i]'(by rw [tailAt_length, headsCorrect_length] at *; omega) = headsCorrect[i] :=
  tail_slice whole headsCorrect origin 56 hbound hcode (by change 56 + 8 ≤ 111; decide) rfl

theorem jumpBack_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < (jumpBack 0).length), whole[(origin + 64) + i]'(by rw [tailAt_length, jumpBack_length] at *; omega) = (jumpBack 0)[i] :=
  tail_slice whole (jumpBack 0) origin 64 hbound hcode (by change 64 + 3 ≤ 111; decide) rfl

theorem headsAppend_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < headsAppend.length), whole[(origin + 67) + i]'(by rw [tailAt_length, headsAppend_length] at *; omega) = headsAppend[i] :=
  tail_slice whole headsAppend origin 67 hbound hcode (by change 67 + 10 ≤ 111; decide) rfl

theorem headsInit_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < headsInit.length), whole[(origin + 80) + i]'(by rw [tailAt_length, headsInit_length] at *; omega) = headsInit[i] :=
  tail_slice whole headsInit origin 80 hbound hcode (by change 80 + 21 ≤ 111; decide) rfl

theorem headsFinish_tail_code (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i]) :
    ∀ i (hi : i < headsFinish.length), whole[(origin + 104) + i]'(by rw [tailAt_length, headsFinish_length] at *; omega) = headsFinish[i] :=
  tail_slice whole headsFinish origin 104 hbound hcode (by change 104 + 7 ≤ 111; decide) rfl

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
