module
public import Common.PSTR_TM_MulExpandRun_098
public import Common.PSTR_TM_MulResident_094
public import Common.PSTR_TM_AddCanonical_052

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMRawMulResident099
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMNatValue017
local notation "cols" => PSTRTMMulPassCode079.columns

def pairs (a b : Nat) : List (Bool×Bool) := PSTRTMPackCode036.digitPairs (rawPayload a) (rawPayload b)
def inputTriples (a b : Nat) : List PSTRTMMulPassCode079.Triple := PSTRTMMulExpandCode095.triples (pairs a b)
def outputTriples (a b : Nat) : List PSTRTMMulPassCode079.Triple := PSTRTMMulResident094.result (inputTriples a b)
def rawExpandMachine : Machine 456 := PSTRTMSeq005.seqMachine PSTRTMRawPack045.rawPackMachine PSTRTMMulExpandCode095.expandMachine
/-- ONE fixed721-label Bool program on ORIGINAL raw two-Nat input. All
zero extension/three-column expansion and binary multiplication are REAL.
The output still contains auxiliary A/B columns: canonical C-only original
encodeNat(a*b) projection/trim/inverse codec remain owed. -/
def rawMulResidentMachine : Machine 720 := PSTRTMSeq005.seqMachine rawExpandMachine PSTRTMMulLoopCode088.loopMachine
def expandTrace (a b : Nat) : List (MachineState 456) :=
  (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b)).map (PSTRTMSeq005.leftCfg (b:=111)) ++
    (PSTRTMMulExpandRun098.expandTrace (pairs a b)).map (PSTRTMSeq005.rightCfg (a:=344))
def expandFinal (a b : Nat) : MachineState 456 :=
  PSTRTMSeq005.rightCfg (a:=344) (PSTRTMMulExpandRun098.expandFinal (pairs a b))
def nativeTrace (a b : Nat) : List (MachineState 720) :=
  (expandTrace a b).map (PSTRTMSeq005.leftCfg (b:=263)) ++
    (PSTRTMMulResident094.residentTrace (inputTriples a b)).map (PSTRTMSeq005.rightCfg (a:=456))
def nativeFinal (a b : Nat) : MachineState 720 :=
  PSTRTMSeq005.rightCfg (a:=456) (PSTRTMMulResident094.residentFinal (inputTriples a b))

theorem expand_runs (a b : Nat) :
    Runs rawExpandMachine (encodeNat a++encodeNat b) (expandTrace a b) (expandFinal a b) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawPack045.rawPackMachine PSTRTMMulExpandCode095.expandMachine
    (encodeNat a++encodeNat b) (PSTRTMRawPack045.rawPackFinal (rawPayload a) (rawPayload b))
    (PSTRTMMulExpandRun098.expandFinal (pairs a b))
    (PSTRTMRawPack045.rawPackTrace (rawPayload a) (rawPayload b)) (PSTRTMMulExpandRun098.expandTrace (pairs a b))
  · simpa only [PSTRTMTwoRawOperands029.rawInput,rawPayload,List.length_ofFn,encodeNat,List.append_assoc,List.singleton_append] using
      PSTRTMRawPack045.rawPack_runs (rawPayload a) (rawPayload b)
  · have hr := PSTRTMMulExpandRun098.expand_runs (pairs a b)
    rw [PSTRTMRawPack045.rawPack_final_tape]
    exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem expand_final_tape (a b : Nat) : (expandFinal a b).Tape=Turing.Tape.mk₁ (cols (inputTriples a b)) :=
  PSTRTMMulExpandRun098.expand_final_tape (pairs a b)

theorem native_runs (a b : Nat) :
    Runs rawMulResidentMachine (encodeNat a++encodeNat b) (nativeTrace a b) (nativeFinal a b) := by
  apply PSTRTMSeq005.seq_runs rawExpandMachine PSTRTMMulLoopCode088.loopMachine
    (encodeNat a++encodeNat b) (expandFinal a b) (PSTRTMMulResident094.residentFinal (inputTriples a b))
    (expandTrace a b) (PSTRTMMulResident094.residentTrace (inputTriples a b)) (expand_runs a b)
  have hr := PSTRTMMulResident094.resident_runs (inputTriples a b)
  rw [expand_final_tape]
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

theorem native_final_tape (a b : Nat) : (nativeFinal a b).Tape=Turing.Tape.mk₁ (cols (outputTriples a b)) :=
  PSTRTMMulResident094.resident_final_tape (inputTriples a b)

theorem triple_values (ps : List (Bool×Bool)) :
    PSTRTMMulPassCode079.cValue (PSTRTMMulExpandCode095.triples ps)=0 ∧
    PSTRTMMulPassCode079.aValue (PSTRTMMulExpandCode095.triples ps)=PSTRTMBinaryAdd024.firstValue ps ∧
    PSTRTMMulPassCode079.bValue (PSTRTMMulExpandCode095.triples ps)=PSTRTMBinaryAdd024.secondValue ps := by
  induction ps with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit false (PSTRTMMulPassCode079.cValue (PSTRTMMulExpandCode095.triples later))=0 ∧
      Nat.bit a (PSTRTMMulPassCode079.aValue (PSTRTMMulExpandCode095.triples later))=Nat.bit a (PSTRTMBinaryAdd024.firstValue later) ∧
      Nat.bit b (PSTRTMMulPassCode079.bValue (PSTRTMMulExpandCode095.triples later))=Nat.bit b (PSTRTMBinaryAdd024.secondValue later)
    rw [ih.1,ih.2.1,ih.2.2]
    exact ⟨rfl,rfl,rfl⟩

theorem input_values (a b : Nat) : PSTRTMMulPassCode079.cValue (inputTriples a b)=0 ∧
    PSTRTMMulPassCode079.aValue (inputTriples a b)=a ∧ PSTRTMMulPassCode079.bValue (inputTriples a b)=b := by
  have ht := triple_values (pairs a b)
  have hp := PSTRTMAddCanonical052.digitPairs_values (rawPayload a) (rawPayload b)
  change PSTRTMBinaryAdd024.firstValue (pairs a b)=_ ∧ PSTRTMBinaryAdd024.secondValue (pairs a b)=_ at hp
  rw [valueDigits_rawPayload,valueDigits_rawPayload] at hp
  change PSTRTMMulPassCode079.cValue (inputTriples a b)=0 ∧
    PSTRTMMulPassCode079.aValue (inputTriples a b)=PSTRTMBinaryAdd024.firstValue (pairs a b) ∧
    PSTRTMMulPassCode079.bValue (inputTriples a b)=PSTRTMBinaryAdd024.secondValue (pairs a b) at ht
  rw [hp.1,hp.2] at ht
  exact ht

theorem exact_product (a b : Nat) : PSTRTMMulPassCode079.cValue (outputTriples a b)=a*b ∧
    PSTRTMMulPassCode079.bValue (outputTriples a b)=0 := by
  have hv := PSTRTMMulResident094.resident_result_values (inputTriples a b)
  have hi := input_values a b
  rw [hi.1,hi.2.1,hi.2.2,Nat.zero_add] at hv
  exact hv

private theorem payload_length (value : Nat) : (rawPayload value).length=natBits value := by
  simp only [rawPayload,List.length_ofFn]
theorem pairs_length_le (a b : Nat) : (pairs a b).length ≤ natBits a+natBits b := by
  simp only [pairs,PSTRTMPackCode036.digitPairs_length,payload_length]
  exact max_le (by omega) (by omega)
theorem input_length (a b : Nat) : (inputTriples a b).length=(pairs a b).length := by
  simp only [inputTriples,PSTRTMMulExpandCode095.triples,List.length_map]

theorem native_length_le (a b : Nat) :
    (nativeTrace a b).length ≤ 4096*(natBits a+natBits b+1)^2 := by
  have hr := PSTRTMRawPack045.rawPack_length_le (rawPayload a) (rawPayload b)
  simp only [payload_length] at hr
  have he := PSTRTMMulExpandRun098.expand_length_le (pairs a b)
  have hm := PSTRTMMulResident094.resident_length_le (inputTriples a b)
  rw [input_length] at hm
  have hp := pairs_length_le a b
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) 2
  simp only [nativeTrace,expandTrace,List.length_append,List.length_map]
  nlinarith

theorem native_visitedSpace_le (a b : Nat) :
    visitedSpace rawMulResidentMachine (encodeNat a++encodeNat b).length (nativeTrace a b) ≤
      16384*(natBits a+natBits b+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le rawMulResidentMachine (encodeNat a++encodeNat b).length (nativeTrace a b)
  have ht := native_length_le a b
  simp only [List.length_append,PSTRTMLength004.encodeNat_length] at hs ⊢
  nlinarith

/-- Exact original raw-input computation of resident product columns.
This contract intentionally exposes the remaining original output-codec
obligation; columns with auxiliary registers are NOT encodeNat(a*b). -/
theorem raw_product_columns_computes (a b : Nat) :
    computes rawMulResidentMachine (encodeNat a++encodeNat b) (cols (outputTriples a b))
      (4096*(natBits a+natBits b+1)^2) (16384*(natBits a+natBits b+1)^2) := by
  refine ⟨nativeTrace a b,nativeFinal a b,native_runs a b,?_,native_length_le a b,native_visitedSpace_le a b⟩
  rw [native_final_tape]
  simp [Turing.Tape.mk₁,Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMRawMulResident099
