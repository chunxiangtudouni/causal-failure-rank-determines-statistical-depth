module

public import Paid.PDLower_CalibrationCompute_Weight_033
public import Paid.PDLower_CalibrationCompute_Gates_030
public import Paid.PDLower_CalibrationCompute_CacheLookup_038
public import Paid.PDLower_CalibrationCompute_CalibrationValue_039

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The actual heap endpoint read, actual denominator branch, legal
division or zero branch, and actual jump to emit. No supplied weight or
successful weight-computation witness appears in the hypotheses. -/
theorem weightPhase (origin : ℕ) (input : List Cell) (P : Parameters) (base : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .weight)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (cache : HeapList before header.endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (positive : 0<header.level) (bounded : header.level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after 400 ∧
      after.pc=labelAddress origin .emit ∧ header.At after base ∧
      after.register .fresh=.natural base ∧
      after.register .value=.rational (computedWeight (P.endpointConstant (header.level-1)).error header.q) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let error := (P.endpointConstant (header.level-1)).error
  let middle := weightResult before base header.endpoints header.level error header.q
  have endpoint := represented.lookup (offset:=1) (value:=.natural header.endpoints) rfl
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have q := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have actualError := endpointHeap_error cache positive bounded
  have literal := weight_execute input before base header.endpoints header.level error header.q fresh
    endpoint.2 endpoint.1 level.2 level.1 q.2 q.1 actualError.1 actualError.2
  have gate := segment_branch origin .weight .divide .zeroWeight input before middle
    ((1/2-header.q : ℚ)=0) position literal rfl (by simp [middle,weightResult])
  by_cases zero : (1/2-header.q : ℚ)=0
  · let branch : State := {middle with pc:=labelAddress origin .zeroWeight}
    let completed := ({branch with pc:=branch.pc+1}).set .value (.rational 0)
    let after : State := {completed with pc:=labelAddress origin .emit}
    have budget : 15*((basicBlock .weight).body.length+1)+15=330 := by decide
    have branchRun : Segment origin input before branch 330 := by simpa only [ite_eq_left zero,budget] using gate
    have finish : Segment origin input branch after 45 :=
      segment_go origin .zeroWeight .emit input branch completed rfl (zeroWeight_execute input branch) rfl
    refine ⟨after,(branchRun.trans finish).mono (by decide),rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · exact represented
    · simpa [after,completed,branch,middle,weightResult,weightLoaded,loadSlotResult,State.set] using fresh
    · simp only [after,completed,State.set,Function.update_self,computedWeight,ite_eq_left zero]
  · let branch : State := {middle with pc:=labelAddress origin .divide}
    let completed := divideResult branch (1/2-error) (1/2-header.q)
    let after : State := {completed with pc:=labelAddress origin .emit}
    have budget : 15*((basicBlock .weight).body.length+1)+15=330 := by decide
    have branchRun : Segment origin input before branch 330 := by simpa only [ite_eq_right zero,budget] using gate
    have total : branch.register .total=.rational (1/2-error) := by
      simp [branch,middle,weightResult,weightLoaded,loadSlotResult]
    have value : branch.register .value=.rational (1/2-header.q) := by simp [branch,middle,weightResult]
    have finish : Segment origin input branch after 45 :=
      segment_go origin .divide .emit input branch completed rfl
        (divide_execute input branch (1/2-error) (1/2-header.q) total value zero) rfl
    refine ⟨after,(branchRun.trans finish).mono (by decide),rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · exact represented
    · simpa [after,completed,branch,middle,divideResult,weightResult,weightLoaded,loadSlotResult] using fresh
    · simp only [after,completed,divideResult,Function.update_self,computedWeight,ite_eq_right zero,error]

end PDLower.CalibrationCompute
