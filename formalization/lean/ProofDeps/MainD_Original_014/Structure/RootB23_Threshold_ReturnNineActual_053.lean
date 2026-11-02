module
public import Structure.RootB23_Threshold_ReturnNineMarshal_052

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineActual
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticBookmark014
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
open ReturnNineLayout (Data)

def phase (memory : Fin 8) : Fin 9 := ⟨memory.val+1,by omega⟩

def rowMemory (phase : Fin 9) (_nonzero : phase.val≠0) : Fin 8 := ⟨phase.val-1,by have bound:=phase.isLt;omega⟩

def rows (phase : Fin 9) : Machine 11615 :=
  if first : phase.val=0 then padMachine (by decide : 223≤11615) ReturnNineObserved.code
  else ReturnNineMarshal.code (rowMemory phase first)

def dispatch (q : Fin 11616) : Option (Fin 8) := match q.val with
  | 126=>some 0 | 127=>some 1 | 158=>some 2 | 159=>some 3
  | 190=>some 4 | 191=>some 5 | 222=>some 6 | 223=>some 7 | _=>none

def ports (current : Fin 9) (q : Fin 11616) : Option (Fin 9 × Fin 11616) :=
  if current.val=0 then (dispatch q).map (fun memory=>(phase memory,0)) else none

def blockCap : ℕ := totalStates 8 11615
def blockCode : Machine blockCap := blockMachine rows ports
def cap : ℕ := 3+blockCap+1
def code : Machine cap := PSTRTMSeq005.seqMachine PayloadSteps.nextAnchorMachine blockCode

def finalPort (memory : Fin 8) : Fin (cap+1) := PSTRTMSeq005.rightLabel (a:=3)
  (label (p:=8) (s:=11615) (phase memory) (11615 : Fin 11616))

def observed (v : Data) : Fin 8 := ReturnNineObserved.memory (observedFirst v.i) (observedFirst v.e) (observedFirst v.b)

def fee (v : Data) : ℕ := 4+ReturnNineObserved.fee v+ReturnNineMarshal.fee v (observed v)

theorem rows_first : rows (0 : Fin 9)=padMachine (by decide : 223≤11615) ReturnNineObserved.code := rfl

theorem rows_memory (memory : Fin 8) : rows (phase memory)=ReturnNineMarshal.code memory := by
  have positive : (phase memory).val≠0 := by dsimp only [phase];omega
  simp only [rows,dite_eq_right positive]
  congr 1

theorem ports_observed (c t b : Bool) :
    ports 0 (padLabel (by decide : 223≤11615) (ReturnNineObserved.finalPort c t b))=
      some (phase (ReturnNineObserved.memory c t b),0) := by
  cases c <;> cases t <;> cases b <;> rfl

theorem ports_memory (memory : Fin 8) (q : Fin 11616) : ports (phase memory) q=none := by
  have positive : (phase memory).val≠0 := by dsimp only [phase];omega
  unfold ports
  rw [ite_eq_right positive]

/-- The actual observed HALT label chooses the matching fixed copy row.
No read bit, answer or memory value is supplied by the original caller. -/
theorem block_bounded (base : List Bool) (v : Data)
    (bNonempty : v.b≠[]) (eNonempty : v.e≠[]) (gNonempty : v.g≠[]) (iNonempty : v.i≠[]) :
    BoundedRun blockCode (Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::workSuffix 0 []))
      (label (p:=8) (s:=11615) (phase (observed v)) (11615 : Fin 11616))
      (Tape.mk₂ (ReturnNineCopy.home base v) (ReturnNineMarshal.word v (observed v)))
      (ReturnNineObserved.fee v+ReturnNineMarshal.fee v (observed v)) := by
  unfold blockCode blockCap
  have first:=bounded_pad (by decide : 223≤11615)
    (ReturnNineObserved.bounded base v (workSuffix 0 []) bNonempty eNonempty gNonempty iNonempty)
  have second:=ReturnNineMarshal.bounded base v (observed v)
  obtain ⟨xs,run0,time0⟩:=first
  obtain ⟨ys,run1,time1⟩:=second
  have row0 : PSTRTMSeq005.RunsFrom (rows 0)
      ⟨0,Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::workSuffix 0 [])⟩ xs
      ⟨padLabel (by decide : 223≤11615) (ReturnNineObserved.finalPort (observedFirst v.i) (observedFirst v.e) (observedFirst v.b)),
        ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 (workSuffix 0 [])⟩ := run0
  have row1 : PSTRTMSeq005.RunsFrom (rows (phase (observed v)))
      ⟨0,ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 (workSuffix 0 [])⟩ ys
      ⟨11615,Tape.mk₂ (ReturnNineCopy.home base v) (ReturnNineMarshal.word v (observed v))⟩ := by
    rw [rows_memory]
    exact run1
  have firstSegment:=block_segment rows ports (0 : Fin 9) _ _ xs row0
  have secondSegment:=block_segment rows ports (phase (observed v)) _ _ ys row1
  have transfer:=block_transfer rows ports (0 : Fin 9) _ (phase (observed v),0) row0.2.2.2
    (ports_observed (observedFirst v.i) (observedFirst v.e) (observedFirst v.b))
  have segment:=segment_append _ _ _ _ _ _ _ firstSegment secondSegment transfer
  have halt:=block_halt rows ports (phase (observed v)) _ row1.2.2.2 (ports_memory _ _)
  have actual:=segment_runsFrom _ _ _ _ segment halt
  have entry:=blockCfg_zero (p:=8) (s:=11615) (Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::workSuffix 0 []))
  rw [entry] at actual
  refine ⟨xs.map (blockCfg (p:=8) (s:=11615) 0)++ys.map (blockCfg (p:=8) (s:=11615) (phase (observed v))),?_,?_⟩
  · exact actual
  · simpa only [List.length_append,List.length_map] using Nat.add_le_add time0 time1

/-- One fixed producer from the genuine nine-field source footer to
the exact seven-prefix/9-block/0010/00TRUE serializer entrance. -/
theorem bounded (base : List Bool) (v : Data)
    (bNonempty : v.b≠[]) (eNonempty : v.e≠[]) (gNonempty : v.g≠[]) (iNonempty : v.i≠[]) :
    BoundedRun code (Tape.mk₂ (ReturnNineLayout.footerLeft base v) [false]) (finalPort (observed v))
      (Tape.mk₂ (ReturnNineCopy.home base v) (ReturnNineMarshal.word v (observed v))) (fee v) := by
  have first:=PayloadSteps.nextAnchor_bounded (ReturnNineLayout.footerLeft base v)
  have second:=block_bounded base v bNonempty eNonempty gNonempty iNonempty
  simpa only [code,cap,finalPort,fee,Nat.add_assoc] using first.seq second

theorem restored_fields (v : Data) (bNonempty : v.b≠[]) (eNonempty : v.e≠[]) (iNonempty : v.i≠[])
    (gFirst : true::v.g.tail=v.g) :
    ReturnNineCopy.fields v (observed v)=[v.c,v.d,v.e,v.a,v.b,v.f,v.g,v.h,v.i] := by
  change [v.c,v.d,(observed v).val.testBit 1::v.e.tail,v.a,(observed v).val.testBit 0::v.b.tail,
    v.f,true::v.g.tail,v.h,(observed v).val.testBit 2::v.i.tail]=_
  dsimp only [observed]
  rw [ReturnNineObserved.memory_t,ReturnNineObserved.memory_b,ReturnNineObserved.memory_c,
    ←digits_observedFirst v.e eNonempty,←digits_observedFirst v.b bNonempty,←digits_observedFirst v.i iNonempty,gFirst]

end RootB23.Threshold.ReturnNineActual
