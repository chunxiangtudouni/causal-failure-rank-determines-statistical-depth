module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036h

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocatePass023
attribute [local implicit_reducible] cachedFieldCap sourceLoopCap cachedCycleCap firstCachedCap headerCachedCap thirdCachedCap fourCachedCap rawCachedPassCap

def cachedTail (records : List RecordSpec) (n : Nat) : List Bool := bankTail records (gapWord n)

private def pairFee (j k n : Nat) (records : List RecordSpec) (nx dx ny dy : List Bool) : Nat :=
  cachedFieldFee j k records n nx.length (dx.length+ny.length+dy.length)+
    cachedFieldFee j k records (n+k*nx.length) dx.length (ny.length+dy.length)
private def threeFee (j k n : Nat) (records : List RecordSpec) (nx dx ny dy : List Bool) : Nat :=
  pairFee j k n records nx dx ny dy+3+
    cachedFieldFee j k records (n+k*nx.length+k*dx.length) ny.length dy.length
private def fourFee (j k n : Nat) (records : List RecordSpec) (nx dx ny dy : List Bool) : Nat :=
  threeFee j k n records nx dx ny dy+
    cachedFieldFee j k records (n+k*nx.length+k*dx.length+k*ny.length) dy.length 0

private def startTape (records : List RecordSpec) (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::nxContext sx counter) (bank nx dx ny dy (cachedTail records n))
private def dxTape (records : List RecordSpec) (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::dxContext sx counter nx)
    (nxStream dx (false::false::nxStream ny (nxStream dy (false::cachedTail records n))))
private def yHeaderTape (records : List RecordSpec) (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (pushField (false::dxContext sx counter nx) dx)
    (false::false::nxStream ny (nxStream dy (false::cachedTail records n)))
private def nyTape (records : List RecordSpec) (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::nyContext sx counter nx dx) (nxStream ny (nxStream dy (false::cachedTail records n)))
private def dyTape (records : List RecordSpec) (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::dyContext sx counter nx dx ny) (nxStream dy (false::cachedTail records n))
private def footerTape (records : List RecordSpec) (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (pushField (false::dyContext sx counter nx dx ny) dy) (false::cachedTail records n)

/-- A folded two-field interface avoids comparing the full machine at every later transfer. -/
private theorem pair_pass_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j) (sx : Bool) (counter : List Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    let nx := false::nxTail; let dx := false::dxTail
    let ny := false::nyTail; let dy := false::dyTail
    BoundedRun (s:=firstCachedCap j k) (firstCachedMachine j k) (startTape records sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=cachedFieldCap j k) (cachedFieldExit j k))
      (yHeaderTape records sx counter nx dx ny dy (n+k*nx.length+k*dx.length))
      (pairFee j k n records nx dx ny dy) := by
  dsimp only
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  have hx : BoundedRun (s:=cachedFieldCap j k) (nxCachedFieldMachine j k) (startTape records sx counter nx dx ny dy n) (cachedFieldExit j k)
      (dxTape records sx counter nx dx ny dy (n+k*nx.length))
      (cachedFieldFee j k records n nx.length (dx.length+ny.length+dy.length)) :=
    cached_field_bounded j k outNxCode returnNxCode 10 26 (nxRest dxTail nyTail dyTail)
      (nxFooter dxTail nyTail dyTail) (dx.length+ny.length+dy.length) (nx_source_routes dxTail nyTail dyTail) records hj
      (false::nxContext sx counter) nx n
  have hd : BoundedRun (s:=cachedFieldCap j k) (dxCachedFieldMachine j k) (dxTape records sx counter nx dx ny dy (n+k*nx.length)) (cachedFieldExit j k)
      (yHeaderTape records sx counter nx dx ny dy (n+k*nx.length+k*dx.length))
      (cachedFieldFee j k records (n+k*nx.length) dx.length (ny.length+dy.length)) :=
    cached_field_bounded j k outDxCode returnDxCode 8 20 (dxRest nyTail dyTail) (dxFooter nyTail dyTail)
      (ny.length+dy.length) (dx_source_routes nyTail dyTail) records hj (false::dxContext sx counter nx) dx (n+k*nx.length)
  exact hx.seq hd

private theorem three_pass_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j) (sx : Bool) (counter : List Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    let nx := false::nxTail; let dx := false::dxTail
    let ny := false::nyTail; let dy := false::dyTail
    BoundedRun (s:=thirdCachedCap j k) (thirdCachedMachine j k) (startTape records sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=headerCachedCap j k) (cachedFieldExit j k))
      (dyTape records sx counter nx dx ny dy (n+k*nx.length+k*dx.length+k*ny.length))
      (threeFee j k n records nx dx ny dy) := by
  dsimp only
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  let n2 := n+k*nx.length+k*dx.length
  have hp := pair_pass_bounded j k records hj sx counter n nxTail dxTail nyTail dyTail
  have hh : BoundedRun (s:=2) headerRightMachine (yHeaderTape records sx counter nx dx ny dy n2) 2
      (nyTape records sx counter nx dx ny dy n2) 3 :=
    ⟨headerRightTrace (pushField (false::dxContext sx counter nx) dx) false false
       (nxStream ny (nxStream dy (false::cachedTail records n2))),
     headerRight_runsFrom (pushField (false::dxContext sx counter nx) dx) false false
       (nxStream ny (nxStream dy (false::cachedTail records n2))),by rfl⟩
  have hb : BoundedRun (s:=headerCachedCap j k) (headerCachedMachine j k) (startTape records sx counter nx dx ny dy n) 
      (PSTRTMSeq005.rightLabel (a:=firstCachedCap j k) (2 : Fin 3))
      (nyTape records sx counter nx dx ny dy n2) (pairFee j k n records nx dx ny dy+3) := hp.seq hh
  have hy : BoundedRun (s:=cachedFieldCap j k) (nyCachedFieldMachine j k) (nyTape records sx counter nx dx ny dy n2) (cachedFieldExit j k)
      (dyTape records sx counter nx dx ny dy (n2+k*ny.length))
      (cachedFieldFee j k records n2 ny.length dy.length) :=
    cached_field_bounded j k outNyCode returnNyCode 3 11 (nyRest dyTail) (nyFooter dyTail) dy.length
      (ny_source_routes dyTail) records hj (false::nyContext sx counter nx dx) ny n2
  exact hb.seq hy

private theorem four_pass_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j) (sx : Bool) (counter : List Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    let nx := false::nxTail; let dx := false::dxTail
    let ny := false::nyTail; let dy := false::dyTail
    BoundedRun (s:=fourCachedCap j k) (fourCachedMachine j k) (startTape records sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=thirdCachedCap j k) (cachedFieldExit j k))
      (footerTape records sx counter nx dx ny dy (n+k*nx.length+k*dx.length+k*ny.length+k*dy.length))
      (fourFee j k n records nx dx ny dy) := by
  dsimp only
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  let n3 := n+k*nx.length+k*dx.length+k*ny.length
  have ht := three_pass_bounded j k records hj sx counter n nxTail dxTail nyTail dyTail
  have hd : BoundedRun (s:=cachedFieldCap j k) (dyCachedFieldMachine j k) (dyTape records sx counter nx dx ny dy n3) (cachedFieldExit j k)
      (footerTape records sx counter nx dx ny dy (n3+k*dy.length)) (cachedFieldFee j k records n3 dy.length 0) :=
    cached_field_bounded j k outDyCode returnDyCode 1 5 dyRest dyFooter 0 dy_source_routes records hj
      (false::dyContext sx counter nx dx ny) dy n3
  exact ht.seq hd

/-- The complete original-bank pass, with only folded component interfaces
at the final actual transfer. All moves, flag writes and HALTs are paid. -/
theorem raw_cached_pass_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j) (sx : Bool) (h n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (s:=rawCachedPassCap j k) (rawCachedPassMachine j k)
      (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones h))
        (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) (cachedTail records n)))
      (Fin.last (rawCachedPassCap j k))
      (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
          (cachedTail records (n+k*bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail))))))
      (cachedPassFee j k records (bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)) n) := by
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  let counter := false::ROOTTMGCDCounter011.ones h
  let n4 := n+k*nx.length+k*dx.length+k*ny.length+k*dy.length
  have hs := four_pass_bounded j k records hj sx counter n nxTail dxTail nyTail dyTail
  have hf := finishBack_bounded sx counter nx dx ny dy (cachedTail records n4)
  have hr : BoundedRun (s:=rawCachedPassCap j k) (rawCachedPassMachine j k) (startTape records sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=fourCachedCap j k) (34 : Fin 35))
      (Turing.Tape.mk₂ counter (prefixRight sx (bank nx dx ny dy (cachedTail records n4))))
      (fourFee j k n records nx dx ny dy+(2*bankWidth nx dx ny dy+31)) := hs.seq hf
  have hq : PSTRTMSeq005.rightLabel (a:=fourCachedCap j k) (34 : Fin 35)=Fin.last (rawCachedPassCap j k) := by
    apply Fin.ext
    change fourCachedCap j k+1+34=fourCachedCap j k+34+1
    omega
  have hn : n4=n+k*bankWidth nx dx ny dy := by
    dsimp [n4,bankWidth]
    ring
  rw [hq,hn] at hr
  have hb : fourFee j k n records nx dx ny dy+(2*bankWidth nx dx ny dy+31) ≤
      cachedPassFee j k records (bankWidth nx dx ny dy) n :=
    cachedTraceFee_le j k records n nx.length dx.length ny.length dy.length
  exact hr.mono hb


end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
