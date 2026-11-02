module

public import Paid.PDCompute_SolverObjectiveCode_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem endpointPayload_length (values : List EndpointConstant) :
    (values.flatMap encodeEndpoint).length=2*values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.flatMap_cons,List.length_append,encodeEndpoint,List.length_cons,List.length_nil,ih]
    omega

theorem endpointPayload_error (values : List EndpointConstant) (index : ℕ) (inside : index < values.length) :
    (values.flatMap encodeEndpoint)[2*index]?=some (.rational values[index].error) := by
  induction values generalizing index with
  | nil => simp at inside
  | cons value values ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have hi : index < values.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
      have he : 2*(index+1)=2*index+1+1 := by omega
      simp only [List.flatMap_cons,encodeEndpoint,List.cons_append,List.nil_append,he,
        List.getElem?_cons_succ,List.getElem_cons_succ]
      exact ih index hi

theorem endpointPayload_charge (values : List EndpointConstant) (index : ℕ) (inside : index < values.length) :
    (values.flatMap encodeEndpoint)[2*index+1]?=some (.rational values[index].charge) := by
  induction values generalizing index with
  | nil => simp at inside
  | cons value values ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have hi : index < values.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
      have he : 2*(index+1)+1=(2*index+1)+1+1 := by omega
      simp only [List.flatMap_cons,encodeEndpoint,List.cons_append,List.nil_append,he,
        List.getElem?_cons_succ,List.getElem_cons_succ]
      exact ih index hi

def ReaderMode.HasCell (mode : ReaderMode) (input : List Cell) (state : State)
    (address : ℕ) (value : Cell) : Prop :=
  match mode with
  | .inputROM => input[address]?=some value
  | .liveHeap => address ∈ state.live ∧ state.heap address=value

theorem ReaderMode.read_execute (mode : ReaderMode) (input : List Cell) (before : State)
    (pointer target : Register) (address : ℕ) (value : Cell)
    (haddress : before.register pointer=.natural address)
    (hcell : mode.HasCell input before address value) :
    (mode.read target pointer).execute input before=
      some (({before with pc:=before.pc+1}).set target value) := by
  cases mode with
  | inputROM =>
    change input[address]?=some value at hcell
    simp [ReaderMode.read,Instruction.execute,haddress,Cell.nat?,hcell]
  | liveHeap => simp [ReaderMode.read,Instruction.execute,haddress,Cell.nat?,hcell.1,hcell.2]

/-- Exact original serialized endpoint cells, read directly from ROM or
from the core's live computed cache, not from an evaluation oracle. -/
theorem EndpointSource.error (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (source index : ℕ) (before : State) (hsource : EndpointSource mode input P source before)
    (hindex : index ≤ P.certificate.M) :
    mode.HasCell input before (source+(1+2*index))
      (.rational (P.cachedEndpoint P.endpointCache index).error) := by
  have hi : index < P.endpointCache.toList.length := by simp [Parameters.endpointCache]; omega
  have hh := endpointPayload_error P.endpointCache.toList index hi
  have hout : 1+2*index < (encodeList encodeEndpoint P.endpointCache.toList).length := by
    rw [encodeList,List.length_cons,endpointPayload_length]
    omega
  have hc : P.endpointCache.toList[index]=P.cachedEndpoint P.endpointCache index := by
    simp only [Array.getElem_toList,Parameters.cachedEndpoint]
    simp only [Array.length_toList] at hi
    simp only [dite_eq_left hi]
  rw [hc] at hh
  have he : (encodeList encodeEndpoint P.endpointCache.toList)[1+2*index]?=
      some (.rational (P.cachedEndpoint P.endpointCache index).error) := by
    simpa only [encodeList,Nat.add_comm 1,List.getElem?_cons_succ] using hh
  cases mode with
  | inputROM => exact (hsource (1+2*index) hout).trans he
  | liveHeap =>
    refine ⟨hsource.1 (1+2*index) hout,?_⟩
    have hv := PDLower.CalibrationCompute.HeapList.value hsource (1+2*index) hout
    have hev := (List.getElem?_eq_getElem hout).symm.trans he
    exact hv.trans (Option.some.inj hev)

theorem EndpointSource.charge (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (source index : ℕ) (before : State) (hsource : EndpointSource mode input P source before)
    (hindex : index ≤ P.certificate.M) :
    mode.HasCell input before (source+(1+2*index+1))
      (.rational (P.cachedEndpoint P.endpointCache index).charge) := by
  have hi : index < P.endpointCache.toList.length := by simp [Parameters.endpointCache]; omega
  have hh := endpointPayload_charge P.endpointCache.toList index hi
  have hout : 1+2*index+1 < (encodeList encodeEndpoint P.endpointCache.toList).length := by
    rw [encodeList,List.length_cons,endpointPayload_length]
    omega
  have hc : P.endpointCache.toList[index]=P.cachedEndpoint P.endpointCache index := by
    simp only [Array.getElem_toList,Parameters.cachedEndpoint]
    simp only [Array.length_toList] at hi
    simp only [dite_eq_left hi]
  rw [hc] at hh
  have he : (encodeList encodeEndpoint P.endpointCache.toList)[1+2*index+1]?=
      some (.rational (P.cachedEndpoint P.endpointCache index).charge) := by
    have hadd : 1+2*index+1=(2*index+1)+1 := by omega
    simpa only [encodeList,hadd,List.getElem?_cons_succ] using hh
  cases mode with
  | inputROM => exact (hsource (1+2*index+1) hout).trans he
  | liveHeap =>
    refine ⟨hsource.1 (1+2*index+1) hout,?_⟩
    have hv := PDLower.CalibrationCompute.HeapList.value hsource (1+2*index+1) hout
    have hev := (List.getElem?_eq_getElem hout).symm.trans he
    exact hv.trans (Option.some.inj hev)

end PDCompute.Solver
