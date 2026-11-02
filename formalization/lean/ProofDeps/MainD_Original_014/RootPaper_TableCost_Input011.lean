module
public import RootPaper_TableCost_Naturals010
public import RootPaper_TableCost_Fees009
public import Structure.RootB23_HistoryBits_Run_002
public import RootPaper_B23_QuotaView003

/-! Original input/history/physical-word size bounds. The original numeric
quota is read from the paid preparation rows. No computed width, quota or
future TABLE answer is supplied as an extra controller input. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open RationalControllerComputation PSTRWordBool
open scoped BigOperators
variable {I : Instance}

theorem sum_cap {α : Type*} (weight : α→Nat) (xs : List α) (cap : Nat)
    (each : ∀ x∈xs,weight x≤cap) : (xs.map weight).sum≤xs.length*cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have front:=each x List.mem_cons_self
      have later:=ih (fun y member=>each y (List.mem_cons_of_mem _ member))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem raw_length_material (data : List Datum) : data.length≤(data.flatMap encodeDatum).length := by
  induction data with
  | nil => rfl
  | cons datum later ih =>
      have positive:=PSTRTMLength004.datumBits_pos datum
      rw [←PSTRTMLength004.encodeDatum_length] at positive
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega

theorem encode_material_bound (data : List Datum) :
    (encode data).length≤3*(data.flatMap encodeDatum).length+4 := by
  have count:=raw_length_material data
  have header:=natBits_le_value data.length
  simp only [encode,List.length_append,PSTRTMLength004.encodeNat_length,List.length_cons,List.length_nil]
  omega

theorem history_length_material (history : List (VisibleEvent I)) : history.length≤historyMaterial history := by
  have count : history.length≤(history.flatMap encodeEvent).length := by
    induction history with
    | nil => rfl
    | cons event later ih =>
        have positive : 1≤(encodeEvent event).length := by cases event <;> simp [encodeEvent,encodeHandle]
        simp only [List.length_cons,List.flatMap_cons,List.length_append]
        omega
  exact count.trans (raw_length_material _)

theorem history_material_input (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (history : List (VisibleEvent I)) :
    historyMaterial history≤(controllerInput input C available budget history).length := by
  simp only [historyMaterial,controllerInput,encode,encodeHistory,List.flatMap_append,List.flatMap_cons,
    List.length_append,List.length_cons,List.length_nil]
  omega

theorem instance_material_input (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    instanceMaterial input≤arithmeticScale input C budget := by
  have material : instanceMaterial input≤(preparationInput input C budget).length := by
    simp only [instanceMaterial,preparationInput,encode,List.flatMap_append,List.length_append,
      List.length_cons,List.length_nil]
    omega
  exact material.trans (RootPaper.Prep.original_bits_le_scale I input C budget)

theorem word_input_size (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) (B : Nat)
    (material : ((rawExperiment E).flatMap encodeDatum).length≤B)
    (targetWidth : RatInput.Encoder.fieldSize target≤6144*(B+1))
    (alphabet : E.alphabetSize≤B) (length : word.1≤B) :
    (wordInput E target word).length+word.1+1≤100000*(B+1)^2 := by
  have symbols : ((((List.finRange word.1).map (fun k=>Datum.natural (word.2 k).val))).flatMap encodeDatum).length≤
      word.1*(2*B+4) := by
    simpa only [List.length_flatMap,List.map_map,Function.comp_def,List.length_finRange] using
      sum_cap (fun k : Fin word.1=>(encodeDatum (.natural (word.2 k).val)).length)
        (List.finRange word.1) (2*B+4) (by
          intro k member
          rw [PSTRTMLength004.encodeDatum_natural_length]
          have bits:=natBits_le_value (word.2 k).val
          have below: (word.2 k).val<E.alphabetSize:=(word.2 k).isLt
          omega)
  have count:=natBits_le_value word.1
  have wordMaterial : ((rawWord E word).flatMap encodeDatum).length≤(B+1)*(2*B+4) := by
    simp only [rawWord,List.flatMap_cons,List.length_append,PSTRTMLength004.encodeDatum_natural_length]
    have multiply:=Nat.mul_le_mul_right (2*B+4) length
    nlinarith
  have targetMaterial : (encodeDatum (.rational target)).length=2*RatInput.Encoder.fieldSize target+4 := by
    rw [PSTRTMLength004.encodeDatum_rational_length,RootB23.WordOddsBits.ratInput_fieldSize_eq]
    rfl
  have whole:=encode_material_bound (rawExperiment E++[.rational target]++rawWord E word)
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,targetMaterial] at whole
  change (wordInput E target word).length≤_ at whole
  nlinarith

def localSize (input : StatisticalInput I) (C : Contract I) (budget : Rat)
    (history : List (VisibleEvent I)) (records : List Nat) (bits : Nat) : Nat :=
  arithmeticScale input C budget+historyMaterial history+history.length+records.sum+records.length+bits+16

theorem physical_word_power (N q : Nat) :
    2^AlgorithmClaims.indexWidth 32 N q≤(2*(N+q+2))^32 := by
  let n:=N+q+2
  have low : n≤2^Nat.clog 2 n:=Nat.le_pow_clog (by decide) n
  have positive : 0<Nat.clog 2 n := by
    by_contra absent
    have zero:Nat.clog 2 n=0:=by omega
    rw [zero,pow_zero] at low
    dsimp only [n] at low
    omega
  have prior:2^(Nat.clog 2 n-1)<n:=Nat.pow_pred_clog_lt_self
    (show 1<(2:Nat) from by decide) (show 1<n from by dsimp only [n];omega)
  have next : 2^Nat.clog 2 n≤2*n := by
    have same:Nat.clog 2 n=(Nat.clog 2 n-1)+1:=by omega
    rw [same,pow_succ]
    nlinarith
  change 2^(32*Nat.clog 2 n)≤(2*n)^32
  rw [Nat.mul_comm 32,pow_mul]
  exact Nat.pow_le_pow_left next 32

theorem physical_word_width (N q : Nat) : AlgorithmClaims.indexWidth 32 N q≤32*(N+q+2) := by
  have digits : Nat.clog 2 (N+q+2)≤N+q+2 :=
    Nat.clog_le_of_le_pow (show N+q+2≤2^(N+q+2) from Nat.lt_two_pow_self.le)
  exact Nat.mul_le_mul_left 32 digits

def inputRate : Nat:=12*4^32+100000

theorem native_localSize (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : Rat) (policy : Policy input C .native accounting Unit)
    (sample : Unit×input.World) (clock : Nat) (records : List Nat)
    (early : clock≤4*arithmeticScale input C budget)
    (length : records.length≤4*(2*I.stageCount+1))
    (words : ∀ value∈records,value<2^AlgorithmClaims.indexWidth 32 I.stageCount I.toolCount) :
    localSize input C budget (run input C .native accounting policy.rule sample clock).history records
      (AlgorithmClaims.indexWidth 32 I.stageCount I.toolCount)≤ inputRate*(arithmeticScale input C budget)^33 := by
  let P:=arithmeticScale input C budget
  have positive : 1≤P := by dsimp only [P,arithmeticScale];omega
  have dimensions : I.stageCount+I.toolCount+1≤P := by dsimp only [P,arithmeticScale,inputSize];omega
  have rawInputBound : inputSize input C budget≤P := by dsimp only [P,arithmeticScale];omega
  have raw:=RootB23HistoryBits.run_controllerInput_length_le input C .native accounting policy.rule policy.legal sample clock available budget
  have size : inputSize input C budget+clock+1≤6*P := by omega
  have inputBits := raw.trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left size 3))
  have historyBits := (history_material_input input C available budget _).trans inputBits
  have historyLength:=(history_length_material (run input C .native accounting policy.rule sample clock).history).trans historyBits
  have wordWidth := physical_word_width I.stageCount I.toolCount
  have wordPower := (physical_word_power I.stageCount I.toolCount).trans
    (Nat.pow_le_pow_left (by omega : 2*(I.stageCount+I.toolCount+2)≤4*P) 32)
  have archiveSum:=sum_cap id records (2^AlgorithmClaims.indexWidth 32 I.stageCount I.toolCount)
    (fun value present=>(words value present).le)
  simp only [List.map_id_fun,id_eq] at archiveSum
  have sumBound : records.sum≤(12*4^32)*P^33 := by
    have count : records.length≤12*P:=by omega
    exact archiveSum.trans ((Nat.mul_le_mul count wordPower).trans_eq (by ring))
  have linear : P≤P^33:=by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤33)
  have cubic : P^3≤P^33:=Nat.pow_le_pow_right positive (by decide : 3≤33)
  have one : 1≤P^33:=Nat.one_le_pow _ _ positive
  have hist : historyMaterial (run input C .native accounting policy.rule sample clock).history≤27648*P^33 := by
    have scaled : historyMaterial (run input C .native accounting policy.rule sample clock).history≤27648*P^3 := by
      simpa only [mul_pow,←Nat.mul_assoc,show 128*(6:Nat)^3=27648 from by decide] using historyBits
    exact scaled.trans (Nat.mul_le_mul_left 27648 cubic)
  have histLength:=(history_length_material (run input C .native accounting policy.rule sample clock).history).trans hist
  unfold localSize inputRate
  change P+_+_+_+_+_+16≤_
  nlinarith only [hist,histLength,sumBound,linear,one,length,wordWidth,dimensions]

end RootPaper.TableCost
