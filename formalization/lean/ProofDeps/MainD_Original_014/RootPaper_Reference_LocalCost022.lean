module
public import RootPaper_Reference_ControlBits021

/-! Sum the actual call schedules and measured helper work. The only
structural multiplier comes from the already-realized DFS execution;
scalar, WORD, input formation and local work contain no F. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation PSTRWordBool
variable {I : Instance}

theorem kernel_current_width (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I)
    (B : Nat) (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (events : cache.events.length≤B) (risk : Rat) (actual : (kernel I available budget cache).current=some risk) :
    RatInput.Encoder.fieldSize risk≤8*B+4 := by
  have path : referenceBudgetPath (budget/2) cache.events=some risk :=
    (kernel_values available budget cache).2.1.symm.trans actual
  have bounded:=RootB236.RiskFold.original_path_width budget cache.events risk valid path
  have paid:=bounded.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 2 width) (Nat.mul_le_mul_left 6 events)) 4)
  omega

theorem controllerUnits_cap (I : Instance) (height B : Nat)
    (stages : I.stageCount≤B) (tools : I.toolCount≤B) (history : height≤B) :
    controllerUnits I height (I.stageCount+1)≤2048*(B+1)^3 := by
  let A:=B+1
  have positive : 1≤A := by dsimp only [A];omega
  have square : A≤A^2 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have cube : A^2≤A^3 := Nat.pow_le_pow_right positive (by decide : 2≤3)
  have one : 1≤A^3 := Nat.one_le_pow _ _ positive
  have one2 : 1≤A^2 := Nat.one_le_pow _ _ positive
  have first : (6*I.toolCount+120)*(3*height+1)≤360*A^2 := by
    have product:=Nat.mul_le_mul (by dsimp only [A];omega : 6*I.toolCount+120≤120*A)
      (by dsimp only [A];omega : 3*height+1≤3*A)
    nlinarith only [product]
  have second : (6*I.toolCount+12)*(I.toolCount+1)≤12*A^2 := by
    have product:=Nat.mul_le_mul (by dsimp only [A];omega : 6*I.toolCount+12≤12*A)
      (by dsimp only [A];omega : I.toolCount+1≤A)
    nlinarith only [product]
  have last : 9*I.toolCount+260≤260*A := by dsimp only [A];omega
  have step : stepUnits I height≤644*A^2 := by
    unfold stepUnits
    nlinarith only [first,second,last,square]
  have step' : stepUnits I height+8≤652*A^2 := by nlinarith only [step,one2]
  have replay : height*(stepUnits I height+8)≤652*A^3 := by
    have product:=Nat.mul_le_mul (by dsimp only [A];omega : height≤A) step'
    nlinarith only [product]
  have parse : (6*I.toolCount+128)*(3*height+1)≤384*A^2 := by
    have product:=Nat.mul_le_mul (by dsimp only [A];omega : 6*I.toolCount+128≤128*A)
      (by dsimp only [A];omega : 3*height+1≤3*A)
    nlinarith only [product]
  have decision : (3*I.toolCount+64)*(3*height+1)≤192*A^2 := by
    have product:=Nat.mul_le_mul (by dsimp only [A];omega : 3*I.toolCount+64≤64*A)
      (by dsimp only [A];omega : 3*height+1≤3*A)
    nlinarith only [product]
  have quota : I.stageCount+1≤A := by dsimp only [A];omega
  unfold controllerUnits parseUnits
  change _≤2048*A^3
  nlinarith only [replay,parse,decision,second,cube,square,quota,one]

theorem queryDataUnits_bound (I : Instance) (call : RankCall I) (B : Nat)
    (dimensions : I.stageCount+I.toolCount+2≤B+1) : queryDataUnits I call≤300*(B+1)^4 := by
  let S:=I.stageCount+I.toolCount+2
  have positive : 1≤S := by dsimp only [S];omega
  have one : 1≤S^2 := Nat.one_le_pow _ _ positive
  have mass:=query_mass I call.stage call.remaining
  change RootB236.Controller.DFSDriver.Machine.mass (queryBank I call.stage call.remaining)≤16*S^2 at mass
  have size : RootB236.Controller.DFSDriver.Machine.mass (queryBank I call.stage call.remaining)+1≤17*S^2 := by omega
  have power:=Nat.pow_le_pow_left size 2
  have linear : S≤S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤4)
  have extra : I.stageCount+I.toolCount+4≤3*S := by dsimp only [S];omega
  have actual : queryDataUnits I call≤300*S^4 := by
    unfold queryDataUnits
    nlinarith only [power,linear,extra]
  exact actual.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left dimensions 4))

theorem wordDataUnits_bound {input : StatisticalInput I} (call : WordCall input) (B : Nat)
    (size : (wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1≤100000*(B+1)^2) :
    wordDataUnits call≤100000^2*(B+1)^4 := by
  exact (Nat.pow_le_pow_left size 2).trans_eq (by rw [mul_pow,←pow_mul])

theorem marker_fee (call : ScalarCall I) (marker : ScalarMarker call) : RootPaper.TableCost.scalarFee call=0 := by
  cases call <;> first | rfl | cases marker

theorem calculation_scalar_fee (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (original : arithmeticScale input C budget≤B) (room : history.length≤B)
    (call : ScalarCall I) (member : call∈(controllerCalculation input available budget quota history).scalar) :
    RootPaper.TableCost.scalarFee call≤(RootPaper.TableCost.scalarRate*65536^10)*(B+1)^10 := by
  rcases controllerCalculation_callBound input available budget quota history valid call member with marker|bounded
  · rw [marker_fee call marker]
    exact Nat.zero_le _
  · have stages : I.stageCount≤B := by unfold arithmeticScale inputSize at original;omega
    have width : RatInput.Encoder.fieldSize budget≤B :=
      (RootPaper.Prep.input_rat_field I input C budget budget (by
        simp only [RootPaper.Prep.originalData,List.mem_append,List.mem_singleton];tauto)).trans original
    have larger : RootPaper.TableCost.CallBound (8*B+4) (B+1) call :=
      callBound_mono (by omega) (by omega) call bounded
    have paid:=RootPaper.TableCost.scalarFee_bound (8*B+4) (B+1) call larger
    have scale : 4096*(8*B+4+(B+1)+1)≤65536*(B+1) := by omega
    exact (paid.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scale 10))).trans_eq (by rw [mul_pow];ring)

theorem calculation_scalar_realized (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (valid : 0<budget ∧ budget≤1/2)
    (call : ScalarCall I) (member : call∈(controllerCalculation input available budget quota history).scalar)
    (arithmetic : ¬ScalarMarker call) : RootPaper.TableCost.ScalarRealized call := by
  rcases controllerCalculation_callBound input available budget quota history valid call member with marker|bounded
  · exact (arithmetic marker).elim
  · exact RootPaper.TableCost.scalar_realized _ _ call bounded

def dataCoefficient : Nat := 100000^2+2649
def localDegree (runtime : WordRuntime) : Nat := 2*runtime.degree+18
def localRate (runtime : WordRuntime) : Nat :=
  2*queryCoefficient+3*RootPaper.TableCost.scalarRate*65536^10+
    runtime.coefficient*100000^runtime.degree+dataCoefficient*unitRate

theorem localRate_positive (runtime : WordRuntime) : 0<localRate runtime := by
  have unit:=unitRate_positive
  unfold localRate dataCoefficient
  omega

theorem factor_positive (I : Instance) : 1≤generalStructureFactor I := by
  unfold generalStructureFactor
  exact Nat.succ_le_of_lt (by positivity)

theorem calculationCost_bound (runtime : WordRuntime) (input : StatisticalInput I) (C : Contract I)
    (available : Finset I.Tool) (budget : Rat) (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I))
    (B : Nat) (valid : 0<budget ∧ budget≤1/2) (original : arithmeticScale input C budget≤B)
    (room : history.length≤B) (getter : ∀ stage,(quota stage).2≤I.stageCount+1) :
    runningCost runtime B (controllerCalculation input available budget quota history)≤
      generalStructureFactor I*localRate runtime*(B+1)^localDegree runtime := by
  let result:=controllerCalculation input available budget quota history
  let A:=B+1
  have positive : 1≤A := by dsimp only [A];omega
  have dimensions : I.stageCount+I.toolCount+2≤A := by unfold arithmeticScale inputSize at original;dsimp only [A];omega
  have stages : I.stageCount≤B := by unfold arithmeticScale inputSize at original;omega
  have tools : I.toolCount≤B := by unfold arithmeticScale inputSize at original;omega
  have counted:=controllerCalculation_bounds input available budget quota history (I.stageCount+1) getter
  have queries : result.ranks.length≤2*A := by have count:=counted.queries;dsimp only [A,result];omega
  have scalar : result.scalar.length≤3*A^2 := counted.scalar.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [A];omega : history.length+1≤A) 2))
  have words : result.words.length≤1 := counted.words
  have admin : result.administration≤2048*A^3 := counted.administration.trans
    (controllerUnits_cap I history.length B stages tools room)
  have queryFeeBound : ∀ call∈result.ranks,queryFee I call≤queryCoefficient*A^8*generalStructureFactor I := by
    intro call _
    exact (queryFee_bound I call).trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left dimensions 8)))
  have q:=(RootPaper.TableCost.sum_cap (queryFee I) result.ranks _ queryFeeBound).trans
    (Nat.mul_le_mul_right _ queries)
  have q' : (result.ranks.map (queryFee I)).sum≤(2*queryCoefficient)*generalStructureFactor I*A^9 := by
    exact q.trans_eq (by ring)
  have scalarFeeBound : ∀ call∈result.scalar,RootPaper.TableCost.scalarFee call≤
      (RootPaper.TableCost.scalarRate*65536^10)*A^10 :=
    fun call member=>calculation_scalar_fee input C available budget quota history B valid original room call member
  have s:=(RootPaper.TableCost.sum_cap RootPaper.TableCost.scalarFee result.scalar _ scalarFeeBound).trans
    (Nat.mul_le_mul_right _ scalar)
  have s' : (result.scalar.map RootPaper.TableCost.scalarFee).sum≤
      (3*RootPaper.TableCost.scalarRate*65536^10)*A^12 := s.trans_eq (by ring)
  have wordSize : ∀ call∈result.words,
      (wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1≤100000*A^2 :=
    fun call member=>controllerCalculation_words input C available budget quota history B valid original room call member
  have wordFeeBound : ∀ call∈result.words,wordFeeFor runtime call≤
      (runtime.coefficient*100000^runtime.degree)*A^(2*runtime.degree) := by
    intro call member
    exact (Nat.mul_le_mul_left runtime.coefficient (Nat.pow_le_pow_left (wordSize call member) runtime.degree)).trans_eq
      (by rw [mul_pow,←pow_mul];ring)
  have w:=(RootPaper.TableCost.sum_cap (wordFeeFor runtime) result.words _ wordFeeBound).trans
    (Nat.mul_le_mul_right _ words)
  have w' : (result.words.map (wordFeeFor runtime)).sum≤
      (runtime.coefficient*100000^runtime.degree)*A^(2*runtime.degree) := by simpa only [Nat.one_mul] using w
  have qdata:=(RootPaper.TableCost.sum_cap (queryDataUnits I) result.ranks (300*A^4)
    (fun call _=>queryDataUnits_bound I call B dimensions)).trans (Nat.mul_le_mul_right _ queries)
  have qdata' : (result.ranks.map (queryDataUnits I)).sum≤600*A^5 := qdata.trans_eq (by ring)
  have wdata:=(RootPaper.TableCost.sum_cap wordDataUnits result.words (100000^2*A^4)
    (fun call member=>wordDataUnits_bound call B (wordSize call member))).trans (Nat.mul_le_mul_right _ words)
  have wdata' : (result.words.map wordDataUnits).sum≤100000^2*A^5 := by
    have power : A^4≤A^5:=Nat.pow_le_pow_right positive (by decide : 4≤5)
    have first : (result.words.map wordDataUnits).sum≤100000^2*A^4 := by simpa only [Nat.one_mul] using wdata
    exact first.trans (Nat.mul_le_mul_left _ power)
  have units : dataUnits result≤dataCoefficient*A^5 := by
    have power : A^3≤A^5:=Nat.pow_le_pow_right positive (by decide : 3≤5)
    have one : 1≤A^5:=Nat.one_le_pow _ _ positive
    dsimp only [dataUnits,dataCoefficient]
    nlinarith only [admin,qdata',wdata',power,one]
  have control : unitFee B*dataUnits result≤(dataCoefficient*unitRate)*A^13 :=
    (Nat.mul_le_mul_left (unitFee B) units).trans_eq (by dsimp only [unitFee,A];ring)
  have degree : 13≤localDegree runtime ∧ 12≤localDegree runtime ∧ 9≤localDegree runtime ∧ 2*runtime.degree≤localDegree runtime := by
    unfold localDegree;omega
  have reserve : A^localDegree runtime≤generalStructureFactor I*A^localDegree runtime := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (A^localDegree runtime) (factor_positive I)
  have qfinal:=q'.trans (Nat.mul_le_mul_left ((2*queryCoefficient)*generalStructureFactor I)
    (Nat.pow_le_pow_right positive degree.2.2.1))
  have sfinal:=(s'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive degree.2.1))).trans
    (Nat.mul_le_mul_left _ reserve)
  have wfinal:=(w'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive degree.2.2.2))).trans
    (Nat.mul_le_mul_left _ reserve)
  have cfinal:=(control.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive degree.1))).trans
    (Nat.mul_le_mul_left _ reserve)
  have paid:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add qfinal sfinal) wfinal) cfinal
  exact paid.trans_eq (by dsimp only [runningCost,localRate,result,A];ring)

end RootPaper.Reference.Charged
