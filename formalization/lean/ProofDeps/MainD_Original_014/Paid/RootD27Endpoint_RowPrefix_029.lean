module

public import Paid.RootD27Endpoint_RowFrame_015
public import Paid.RootD27Endpoint_PairPrefix_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def endpointRowRegion (base E m : ℕ) : Finset ℕ := cellRegion base headerWords ∪ pairWriteRegion E m

/-- One entire original row: actual cast, scalar arithmetic, both cache
stores, updated power/counter and the real backwards jump. -/
theorem rowBody_actual_region (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base E testPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hE : values 0=.natural E) (hm : values 8=.natural m)
    (hone : values 13=.rational 1) (htwo : values 14=.rational 2)
    (hpower : values 7=.rational (powerRecurrence P.certificate.odds m))
    (hodds : values 6=.rational P.certificate.odds)
    (hfee : values 4=.rational P.reviewFee) (hden : values 12=.rational (2*P.certificate.gamma))
    (separated : base+48≤E) (hfetch : FetchesCode program before.pc (rowBodyCode testPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2235 ∧ after.pc=testPC ∧ after.register .fresh=.natural base ∧
      Header after base (bodyValues P values m) ∧
      E+1+2*m∈after.live ∧ E+2+2*m∈after.live ∧
      after.heap (E+1+2*m)=.rational (P.endpointConstant m).error ∧
      after.heap (E+2+2*m)=.rational (P.endpointConstant m).charge ∧
      (∀ address, address<base ∨ base+48≤address →
        address≠E+1+2*m → address≠E+2+2*m → after.heap address=before.heap address) ∧
      after.live=insert (E+2+2*m) (insert (E+1+2*m) before.live) ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (endpointRowRegion base E m)) := by
  let casted:=Function.update values 18 (.rational (m:ℚ))
  let scalar:=rowValues casted P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m
  have layout : rowBodyCode testPC=castRowCode++(headerCode rowCommands++
      (pairStoreCode++(advanceCode++[.jump testPC]))) := by
    simp only [rowBodyCode,List.append_assoc]
  rw [layout] at hfetch
  obtain ⟨castTrace,ch,cl,cc,ct,castHeader,castBase,castPC,castPrefixes⟩:=
    castRow_actual_region program input before base m values header hbase hm hfetch.append_left
  let castState:=castRowResult before base m
  have scalarFetch : FetchesCode program castState.pc (headerCode rowCommands) := by
    rw [castPC]
    exact hfetch.append_right.append_left
  obtain ⟨scalarTrace,scalarState,sh,sl,sc,st,scalarHeader,_,_,scalarBase,scalarPC,_,_,scalarMemory⟩:=
    row_scalar_actual P m program input castState base casted castHeader castBase
      (by simp [casted,hone]) (by simp [casted,htwo]) (by simp [casted,hpower])
      (by simp [casted,hfee]) (by simp [casted]) (by simp [casted,hden]) scalarFetch
  have castMemory : HeaderMemory before castState base :=
    HeaderMemory.write header 18 (by decide) (.rational (m:ℚ))
      (castRow_heap before base m) (castRow_live before base m) (castRow_output before base m)
  have scalarEnd : HeaderMemory castState scalarState base := by
    apply scalarMemory scalarState
    have split:=List.dropLast_append_getLast? scalarState (by rw [sl]; simp)
    rw [←split]
    simp
  have pairFetch : FetchesCode program scalarState.pc pairStoreCode := by
    rw [scalarPC,castPC]
    simpa only [castRowCode_length,rowScalarCode_length] using hfetch.append_right.append_right.append_left
  have scalarE : scalar 0=.natural E := by simp [scalar,rowValues,casted,hE]
  have scalarRow : scalar 8=.natural m := by simp [scalar,rowValues,casted,hm]
  have scalarError : scalar 9=.rational (P.endpointConstant m).error := by
    dsimp only [scalar]
    rw [rowValues_error,endpointFromPower_original]
  have scalarCharge : scalar 11=.rational (P.endpointConstant m).charge := by
    dsimp only [scalar]
    rw [rowValues_charge,endpointFromPower_original]
  obtain ⟨pairTrace,ph,pl,pc,pt,pairHeader,pairPrefixes⟩:=
    pairStore_actual_region program input scalarState base E m (P.endpointConstant m).error
      (P.endpointConstant m).charge scalar scalarHeader scalarBase scalarE scalarRow scalarError scalarCharge separated pairFetch
  let pairState:=pairStoreResult scalarState base E m (P.endpointConstant m).error (P.endpointConstant m).charge
  have pairBase : pairState.register .fresh=.natural base :=
    (pairStore_fresh scalarState base E m (P.endpointConstant m).error (P.endpointConstant m).charge).trans scalarBase
  have advanceFetch : FetchesCode program pairState.pc advanceCode := by
    rw [pairStore_pc,scalarPC,castPC]
    simpa only [castRowCode_length,rowScalarCode_length,pairStoreCode_length] using
      hfetch.append_right.append_right.append_right.append_left
  have scalarPower : scalar 7=.rational (powerRecurrence P.certificate.odds m) := by
    simp [scalar,rowValues,casted,hpower]
  have scalarOdds : scalar 6=.rational P.certificate.odds := by simp [scalar,rowValues,casted,hodds]
  obtain ⟨advanceTrace,advanced,ah,al,ac,advanceTime,advancePC,advanceBase,advanceHeader,advanceMemory⟩:=
    advance_actual P m program input pairState base scalar pairHeader pairBase scalarPower scalarOdds scalarRow advanceFetch
  let after : State:={advanced with pc:=testPC}
  have fetchJump : program[advanced.pc]?=some (.jump testPC) := by
    rw [advancePC,pairStore_pc,scalarPC,castPC]
    simpa [castRowCode_length,rowScalarCode_length,pairStoreCode_length,advanceCode_length,
      Nat.add_assoc] using
      hfetch.append_right.append_right.append_right.append_right 0 (by simp)
  have control : step program input advanced=some after := by simp [step,fetchJump,Instruction.execute,after]
  have joined1:=joinTrace_spec program input castTrace scalarTrace before castState scalarState
    120 1320 ch cl sh sl cc sc ct st
  let first:=joinTrace castTrace scalarTrace
  have joined2:=joinTrace_spec program input first pairTrace before scalarState pairState
    1440 315 joined1.1 joined1.2.1 ph pl joined1.2.2.1 pc joined1.2.2.2 pt
  let second:=joinTrace first pairTrace
  have joined3:=joinTrace_spec program input second advanceTrace before pairState advanced
    1755 465 joined2.1 joined2.2.1 ah al joined2.2.2.1 ac joined2.2.2.2 advanceTime
  let whole:=joinTrace second advanceTrace
  have firstMemory : ∀ state∈first,RegionMemory before state (endpointRowRegion base E m) :=
    RegionMemory.join_trace castTrace scalarTrace before castState _ cl
      (fun state member => (castPrefixes state member).enlarge Finset.subset_union_left)
      (fun state member => (scalarMemory state member).region _ Finset.subset_union_left)
  have secondMemory : ∀ state∈second,RegionMemory before state (endpointRowRegion base E m) :=
    RegionMemory.join_trace first pairTrace before scalarState _ joined1.2.1 firstMemory
      (fun state member => (pairPrefixes state member).enlarge Finset.subset_union_right)
  have wholeMemory : ∀ state∈whole,RegionMemory before state (endpointRowRegion base E m) :=
    RegionMemory.join_trace second advanceTrace before pairState _ joined2.2.1 secondMemory
      (fun state member => (advanceMemory state member).region _ Finset.subset_union_left)
  have joined4:=chain_append_control program input whole advanced after joined3.2.2.1 joined3.2.1 control
  have nonempty : whole≠[] := by
    intro eq
    have head : whole.head?=some before := joined3.1
    rw [eq] at head
    cases head
  have lastMemory : HeaderMemory pairState advanced base := by
    have split:=List.dropLast_append_getLast? advanced (by rw [al]; simp)
    apply advanceMemory advanced
    rw [←split]
    simp
  have cells:=pairStore_cells scalarState base E m (P.endpointConstant m).error (P.endpointConstant m).charge
  refine ⟨whole++[after],after,?_,by simp,joined4.1,?_,rfl,advanceBase,advanceHeader,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil whole nonempty] using joined3.1
  · have wholeTime : time program whole≤2220 := joined3.2.2.2
    exact joined4.2.trans (Nat.add_le_add_right wholeTime 15)
  · change E+1+2*m∈advanced.live
    rw [lastMemory.2.1]
    exact cells.1
  · change E+2+2*m∈advanced.live
    rw [lastMemory.2.1]
    exact cells.2.1
  · change advanced.heap (E+1+2*m)=_
    rw [lastMemory.1 _ (Or.inr (by change base+48≤E+1+2*m; omega))]
    exact cells.2.2.1
  · change advanced.heap (E+2+2*m)=_
    rw [lastMemory.1 _ (Or.inr (by change base+48≤E+2+2*m; omega))]
    exact cells.2.2.2

  · intro address outside notFirst notSecond
    change advanced.heap address=before.heap address
    rw [lastMemory.1 address outside,pairStore_heap,
      Function.update_of_ne (by omega : address≠E+(m*2+1)+1),
      Function.update_of_ne (by omega : address≠E+(m*2+1))]
    exact (scalarEnd.1 address outside).trans (castMemory.1 address outside)
  · change advanced.live=insert (E+2+2*m) (insert (E+1+2*m) before.live)
    rw [lastMemory.2.1,pairStore_live,scalarEnd.2.1,castMemory.2.1]
    congr 1
    · omega
    · congr 1
      omega
  · change advanced.output=before.output
    calc
      advanced.output=pairState.output := lastMemory.2.2
      _=scalarState.output := pairStore_output scalarState base E m (P.endpointConstant m).error (P.endpointConstant m).charge
      _=castState.output := scalarEnd.2.2
      _=before.output := castRow_output before base m

  · intro state member
    rcases List.mem_append.mp member with prior|terminal
    · exact wholeMemory state prior
    · have same : state=after := List.mem_singleton.mp terminal
      subst state
      exact wholeMemory advanced (List.mem_of_getLast? joined3.2.1)

end RootD27.Endpoint
