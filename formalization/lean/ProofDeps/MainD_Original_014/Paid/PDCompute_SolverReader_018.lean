module

public import Paid.PDCompute_SolverArguments_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem EndpointSource.frame (mode : ReaderMode) (input : List Cell) (P : Parameters) (source base n k : ℕ)
    (before after : State) (hsource : EndpointSource mode input P source before)
    (hdisjoint : Disjoint before.live (workspace base n k)) (hframe : Frame before after base n k) :
    EndpointSource mode input P source after := by
  cases mode with
  | inputROM => exact hsource
  | liveHeap =>
      change PDLower.CalibrationCompute.HeapList _ _ _
      apply PDLower.CalibrationCompute.HeapList.of_values
      · intro index inside
        have hm := hsource.1 index inside
        have hout : source+index ∉ workspace base n k := by
          intro hw
          exact Finset.disjoint_left.mp hdisjoint hm hw
        exact (hframe.2 _ hout).mpr hm
      · intro index inside
        have hm := hsource.1 index inside
        have hout : source+index ∉ workspace base n k := by
          intro hw
          exact Finset.disjoint_left.mp hdisjoint hm hw
        rw [hframe.1 _ hout]
        exact PDLower.CalibrationCompute.HeapList.value hsource index inside

/-- Both real readers fetch the original encoded cache length, preserving
the original standalone O(NK) workspace and the core's already-paid cache. -/
theorem readEndpointCount_execute (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (source : ℕ) (before : State) (target : Register)
    (hsource : EndpointSource mode input P source before)
    (haddress : before.register .address=.natural source) :
    (mode.read target .address).execute input before =
      some (({before with pc:=before.pc+1}).set target (.natural (P.certificate.M+1))) := by
  have hsize : P.endpointCache.size=P.certificate.M+1 := by simp [Parameters.endpointCache]
  have hlength : 0 < (encodeList encodeEndpoint P.endpointCache.toList).length := by simp [encodeList]
  cases mode with
  | inputROM =>
      have h := hsource 0 hlength
      have hf : input[source]?=some (.natural (P.certificate.M+1)) := by
        simpa only [Nat.add_zero,encodeList,List.getElem?_cons_zero,Array.length_toList,hsize] using h
      simp [ReaderMode.read,Instruction.execute,haddress,Cell.nat?,hf]
  | liveHeap =>
      have hlive : source ∈ before.live := by simpa only [Nat.add_zero] using hsource.1 0 hlength
      have h := PDLower.CalibrationCompute.HeapList.value hsource 0 hlength
      have hv : before.heap source=.natural (P.certificate.M+1) := by
        simpa only [Nat.add_zero,encodeList,List.getElem_cons_zero,Array.length_toList,hsize] using h
      simp [ReaderMode.read,Instruction.execute,haddress,Cell.nat?,hlive,hv]

end PDCompute.Solver
