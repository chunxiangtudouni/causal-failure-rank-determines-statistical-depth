module

public import Paid.PDLower_CalibrationCompute_OuterStep_078

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

def OuterDone (P : Parameters) (base returnPC count : ℕ) (before after : State) (extra : List Cell) : Prop :=
  after.pc=returnPC ∧ after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
    after.register .address=.natural (resultBase base P.certificate.M) ∧
    after.register .index=.natural (rowWidth P.certificate.M) ∧
    HeapList after (resultBase base P.certificate.M)
      (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) ∧
    after.output=before.output++extra ∧
    calibrationPrefix P count++extra=encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
    Frame before after base P.certificate.M

/-- All original M+1 levels, followed by the actual terminating test and
indirect return. The result cache and appended output are the original
full encoded calibration list; no successful callee is a hypothesis. -/
theorem outerLoop (P : Parameters) (origin base endpoints returnPC count : ℕ) (input : List Cell)
    (before : State) (header : Header) (ready : OuterReady P base endpoints returnPC count header before)
    (position : before.pc=labelAddress origin .levelGate) (bounded : count≤P.certificate.M+1)
    (separate : ∀ index<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+index∉workspace base P.certificate.M) :
    ∃ (after : State) (extra : List Cell),
      Segment origin input before after (13000*(P.certificate.Q+1)*(P.certificate.M+2)*(P.certificate.M+1-count)+420) ∧
      OuterDone P base returnPC count before after extra := by
  let perLevel := 13000*(P.certificate.Q+1)*(P.certificate.M+2)
  have go (remaining : ℕ) : ∀ (count : ℕ) (before : State) (header : Header),
      P.certificate.M+1-count=remaining → count≤P.certificate.M+1 →
      OuterReady P base endpoints returnPC count header before → before.pc=labelAddress origin .levelGate →
      ∃ (after : State) (extra : List Cell),Segment origin input before after (perLevel*(P.certificate.M+1-count)+420) ∧
        OuterDone P base returnPC count before after extra := by
    induction remaining with
    | zero =>
      intro count before header distance bounded ready position
      have equal : count=P.certificate.M+1 := by omega
      obtain ⟨after,actual,pc,fresh,old,address,index,heap,live,output⟩ :=
        levelGate_finish origin input base before header position ready.represented ready.fresh
          (by rw [ready.M,ready.level,equal]; omega)
      have cache : HeapList after (resultBase base P.certificate.M)
          (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) := by
        simpa only [HeapList,heapSegment,heap,live,equal,calibrationPrefix_full] using ready.cache
      refine ⟨after,[],actual.mono (by rw [distance]; omega),?_,?_,?_,?_,?_,cache,?_,?_,?_⟩
      · exact pc.trans ready.returnAddress
      · exact fresh
      · simpa only [ready.returnAddress] using old
      · simpa only [ready.M] using address
      · simpa only [ready.M] using index
      · simpa only [List.append_nil] using output
      · simp only [equal,List.append_nil,calibrationPrefix_full]
      · exact ⟨fun query _outside => congrFun heap query,fun query _outside => by rw [live]⟩
    | succ remaining ih =>
      intro count before header distance bounded ready position
      have inside : count<P.certificate.M+1 := by omega
      obtain ⟨next,nextHeader,stepRun,nextPC,nextReady,stepOutput,stepFrame⟩ :=
        outerStep P origin base endpoints returnPC count input before header ready position inside separate
      obtain ⟨after,extra,restRun,pc,fresh,old,address,index,cache,output,completion,restFrame⟩ :=
        ih (count+1) next nextHeader (by omega) (by omega) nextReady nextPC
      have cost : 13000*(P.certificate.Q+1)*(count+2)≤perLevel :=
        Nat.mul_le_mul_left (13000*(P.certificate.Q+1)) (by omega)
      have distanceStep : P.certificate.M+1-count=(P.certificate.M+1-(count+1))+1 := by omega
      have joined := (stepRun.mono cost).trans restRun
      have budget : perLevel+(perLevel*(P.certificate.M+1-(count+1))+420)=
          perLevel*(P.certificate.M+1-count)+420 := by
        rw [distanceStep]
        ring
      refine ⟨after,encodeCalibration ((P.calibrationWeightCache P.endpointCache)[count]'(by simpa using inside))++extra,
        budget ▸ joined,pc,fresh,old,address,index,cache,?_,?_,stepFrame.trans restFrame⟩
      · rw [output,stepOutput,List.append_assoc]
      · rw [←List.append_assoc,←calibrationPrefix_succ P count inside]
        exact completion
  exact go (P.certificate.M+1-count) count before header rfl bounded ready position

end PDLower.CalibrationCompute
