module
public import RootPaper_TableCost_Coverage012
public import RootPaper_TableCost_Input011

/-! Actual closed fees summed over the candidate's own emitted schedules.
The bound below is an algebraic consumption lemma; all its operand bounds
are discharged from original input/history/produced archive by the ports. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open RationalControllerComputation PSTRWordBool
variable {I : Instance}
variable (runtime : WordCode)

def wordFeeFor {input : StatisticalInput I} (call : WordCall input) : Nat :=
  runtime.coefficient*((wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1)^runtime.degree

def historyFee (B : Nat) (read : HistoryRead) : Nat:=65536*read.visits*(B+1)^2

noncomputable def bitCost {input : StatisticalInput I} (B bits : Nat) (records : List Nat) (result : Computation input) : Nat :=
  (result.work.calls.map scalarFee).sum+(result.work.rationalTests.map rationalFee).sum+
    (result.work.naturalTests.map naturalFee).sum+(result.work.archiveReads.map (readDebit bits records)).sum+
    (result.work.historyReads.map (historyFee B)).sum+(result.words.map (wordFeeFor runtime)).sum+
    65536*(result.work.copied+result.work.localTicks+1)*(B+1)^2

noncomputable def runningDegree : Nat:=2*runtime.degree+10
noncomputable def runningRate : Nat:=65536^10*scalarRate+10^8*RootPaper.Prep.nativeRate+
  100000^runtime.degree*runtime.coefficient+65536*48+32840*9+20+65536

private theorem seven_bounds (a b c d e f g : Nat) :
    a≤a+b+c+d+e+f+g ∧ b≤a+b+c+d+e+f+g ∧ c≤a+b+c+d+e+f+g ∧
    d≤a+b+c+d+e+f+g ∧ e≤a+b+c+d+e+f+g ∧ f≤a+b+c+d+e+f+g ∧ g≤a+b+c+d+e+f+g := by omega

private theorem degree_bounds (d : Nat) : 10≤2*d+10 ∧ 2*d≤2*d+10 := by omega

theorem runningRate_pos : 0<(runningRate runtime) :=
  Nat.lt_of_lt_of_le (by decide : 0<(65536:Nat))
    (seven_bounds (65536^10*scalarRate) (10^8*RootPaper.Prep.nativeRate)
      (100000^runtime.degree*runtime.coefficient) (65536*48) (32840*9) 20 65536).2.2.2.2.2.2

/-- Generic arithmetic is proved before substituting large fixed machine
coefficients, to keep kernel reduction away from those constants. -/
theorem polynomial_cap (c k B e d degree rate size : Nat)
    (width : size≤k*(B+1)^e) (coefficient : k^d*c≤rate) (power : e*d≤degree) :
    c*size^d≤rate*(B+1)^degree := by
  have first:=Nat.mul_le_mul_left c (Nat.pow_le_pow_left width d)
  have same : c*(k*(B+1)^e)^d=(k^d*c)*(B+1)^(e*d) := by rw [mul_pow,←pow_mul];ring
  exact first.trans (same ▸ Nat.mul_le_mul coefficient (Nat.pow_le_pow_right (by omega) power))

theorem visits_bound (read : HistoryRead) : read.visits≤12*(read.length+1)^2 := by
  have positive : 1≤read.length+1:=by omega
  have square : read.length+1≤(read.length+1)^2:=by nlinarith
  unfold HistoryRead.visits
  cases read.helper <;> nlinarith

theorem historyFee_bound (B : Nat) (read : HistoryRead) (length : read.length≤2*B) :
    historyFee B read≤(65536*48)*(B+1)^4 := by
  have visits:read.visits≤48*(B+1)^2 := by
    have size:read.length+1≤2*(B+1):=by omega
    have power:=Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left size 2)
    exact (visits_bound read).trans (power.trans_eq (by ring))
  unfold historyFee
  exact (Nat.mul_le_mul_right ((B+1)^2) (Nat.mul_le_mul_left 65536 visits)).trans_eq (by ring)

theorem naturalFee_bound (B : Nat) (pair : Nat×Nat) (bound : NatPairBound B pair) :
    naturalFee pair≤(32840*9)*(B+1)^2 := by
  have positive : 1≤natBits pair.1+natBits pair.2+1:=by omega
  have square:natBits pair.1+natBits pair.2+1≤(natBits pair.1+natBits pair.2+1)^2:=by nlinarith
  have first:naturalFee pair≤32840*(natBits pair.1+natBits pair.2+1)^2:=by unfold naturalFee;nlinarith
  have width:natBits pair.1+natBits pair.2+1≤3*(B+1):=by dsimp only [NatPairBound] at bound;omega
  exact first.trans ((Nat.mul_le_mul_left 32840 (Nat.pow_le_pow_left width 2)).trans_eq (by ring))

theorem archiveFee_bound (B bits : Nat) (records : List Nat) (index : Nat)
    (length : records.length≤B) (width : bits≤B) :
    readDebit bits records index≤20*(B+1)^2 := by
  have first : records.length+10≤10*(B+1):=by omega
  have second : bits+records.length+2≤2*(B+1):=by omega
  exact (readDebit_bound bits records index).trans ((Nat.mul_le_mul first second).trans_eq (by ring))

theorem aggregate_bound {input : StatisticalInput I} (B bits : Nat) (records : List Nat)
    (result : Computation input)
    (calls : ∀ call∈result.work.calls,CallBound (8*B+4) B call)
    (control : WorkBounds B result.work) (length : records.length≤B) (width : bits≤B)
    (words : ∀ call∈result.words,(wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1≤100000*(B+1)^2) :
    bitCost runtime B bits records result≤(result.units+1)*(runningRate runtime)*(B+1)^(runningDegree runtime) := by
  let cap:=(runningRate runtime)*(B+1)^(runningDegree runtime)
  rcases seven_bounds (65536^10*scalarRate) (10^8*RootPaper.Prep.nativeRate)
      (100000^runtime.degree*runtime.coefficient) (65536*48) (32840*9) 20 65536 with
      ⟨sc,rc,wc,hc,nc,ac,adminC⟩
  have degree : 10≤(runningDegree runtime):=(degree_bounds runtime.degree).1
  have scalarBound : ∀ call∈result.work.calls,scalarFee call≤cap := by
    intro call member
    exact (scalarFee_bound (8*B+4) B call (calls call member)).trans
      (polynomial_cap scalarRate 65536 B 1 10 (runningDegree runtime) (runningRate runtime) _
        (by simp only [pow_one];omega) sc (by omega))
  have rationalBound : ∀ pair∈result.work.rationalTests,rationalFee pair≤cap := by
    intro pair member
    exact (rationalFee_bound pair (8*B+8) (control.1 pair member)).trans
      (polynomial_cap RootPaper.Prep.nativeRate 10 B 1 8 (runningDegree runtime) (runningRate runtime) _
        (by simp only [pow_one];omega) rc (by omega))
  have naturalBound : ∀ pair∈result.work.naturalTests,naturalFee pair≤cap := by
    intro pair member
    exact (naturalFee_bound B pair (control.2.1 pair member)).trans
      (Nat.mul_le_mul nc (Nat.pow_le_pow_right (by omega) (by omega : 2≤(runningDegree runtime))))
  have archiveBound : ∀ index∈result.work.archiveReads,readDebit bits records index≤cap := by
    intro index member
    exact (archiveFee_bound B bits records index length width).trans
      (Nat.mul_le_mul ac (Nat.pow_le_pow_right (by omega) (by omega : 2≤(runningDegree runtime))))
  have historyBound : ∀ read∈result.work.historyReads,historyFee B read≤cap := by
    intro read member
    exact (historyFee_bound B read (control.2.2 read member)).trans
      (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) (by omega : 4≤(runningDegree runtime))))
  have wordBound : ∀ call∈result.words,wordFeeFor runtime call≤cap := by
    intro call member
    exact polynomial_cap runtime.coefficient 100000 B 2 runtime.degree (runningDegree runtime) (runningRate runtime) _
      (words call member) wc (degree_bounds runtime.degree).2
  have a:=sum_cap scalarFee result.work.calls cap scalarBound
  have b:=sum_cap rationalFee result.work.rationalTests cap rationalBound
  have c:=sum_cap naturalFee result.work.naturalTests cap naturalBound
  have d:=sum_cap (readDebit bits records) result.work.archiveReads cap archiveBound
  have e:=sum_cap (historyFee B) result.work.historyReads cap historyBound
  have f:=sum_cap (wordFeeFor runtime) result.words cap wordBound
  have admin : 65536*(result.work.copied+result.work.localTicks+1)*(B+1)^2≤
      (result.work.copied+result.work.localTicks+1)*cap := by
    have one : 65536*(B+1)^2≤cap:=Nat.mul_le_mul adminC
      (Nat.pow_le_pow_right (by omega) (by omega : 2≤(runningDegree runtime)))
    have paid:=Nat.mul_le_mul_left (result.work.copied+result.work.localTicks+1) one
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using paid
  have all:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d) e) f) admin
  unfold bitCost
  exact all.trans_eq (by unfold Computation.units Execution.units cap;ring)

end RootPaper.TableCost
