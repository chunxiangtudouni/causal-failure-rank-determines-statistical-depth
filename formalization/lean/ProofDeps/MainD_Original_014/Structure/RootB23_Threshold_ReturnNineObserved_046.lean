module
public import Structure.RootB23_Threshold_ReturnNineBook_045

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineObserved
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticFarLoad031
open ReturnNineLayout (Data)

/-- This is one fixed finite controller. Its three bits are read from
real source DATA cells and retained in distinct final control labels. -/
def rows (phase : Fin 7) : Machine 31 :=
  if phase.val=0 then padMachine (by decide : 7≤31) ReturnNineBook.stage0
  else if phase.val≤2 then padMachine (by decide : 29≤31) ReturnNineBook.stage1
  else ReturnNineBook.stage2

def middle (c : Bool) : Fin 7 := if c then 2 else 1

def last (c t : Bool) : Fin 7 :=
  ⟨3+(if c then 2 else 0)+(if t then 1 else 0),by cases c <;> cases t <;> decide⟩

def ports (phase : Fin 7) (q : Fin 32) : Option (Fin 7 × Fin 32) :=
  if phase.val=0 then
    if q.val=6 then some (1,0) else if q.val=7 then some (2,0) else none
  else if phase.val=1 then
    if q.val=28 then some (3,0) else if q.val=29 then some (4,0) else none
  else if phase.val=2 then
    if q.val=28 then some (5,0) else if q.val=29 then some (6,0) else none
  else none

def code : Machine (totalStates 6 31) := blockMachine rows ports

def finalPort (c t b : Bool) : Fin (totalStates 6 31+1) := label (p:=6) (s:=31) (last c t) (ReturnNineBook.port2 b)

def memory (c t b : Bool) : Fin 8 :=
  ⟨(if b then 1 else 0)+(if t then 2 else 0)+(if c then 4 else 0),by cases c <;> cases t <;> cases b <;> decide⟩

theorem memory_b (c t b : Bool) : (memory c t b).val.testBit 0=b := by cases c <;> cases t <;> cases b <;> decide

theorem memory_t (c t b : Bool) : (memory c t b).val.testBit 1=t := by cases c <;> cases t <;> cases b <;> decide

theorem memory_c (c t b : Bool) : (memory c t b).val.testBit 2=c := by cases c <;> cases t <;> cases b <;> decide

theorem rows_first : rows (0 : Fin 7)=padMachine (by decide : 7≤31) ReturnNineBook.stage0 := rfl

theorem rows_middle (c : Bool) : rows (middle c)=padMachine (by decide : 29≤31) ReturnNineBook.stage1 := by cases c <;> rfl

theorem rows_last (c t : Bool) : rows (last c t)=ReturnNineBook.stage2 := by cases c <;> cases t <;> rfl

theorem ports_first (c : Bool) :
    ports 0 (padLabel (by decide : 7≤31) (ReturnNineBook.port0 c))=some (middle c,0) := by cases c <;> rfl

theorem ports_middle (c t : Bool) :
    ports (middle c) (padLabel (by decide : 29≤31) (ReturnNineBook.port1 t))=some (last c t,0) := by
  cases c <;> cases t <;> rfl

theorem ports_last (c t : Bool) (q : Fin 32) : ports (last c t) q=none := by cases c <;> cases t <;> rfl

theorem masked_exact (v : Data) : ReturnNineBook.clearB (ReturnNineBook.clearGE (ReturnNineBook.clearI v))=ReturnNineOut.mask v := rfl

def fee (v : Data) : ℕ :=
  2*(v.a.length+v.b.length+v.c.length+v.d.length+v.e.length+v.f.length+v.g.length+v.h.length+v.i.length)+64

/-- True source observation, real source clamping, charged transfers,
and actual final HALT in one of eight distinct memory ports. -/
theorem bounded (base : List Bool) (v : Data) (suffix : List Bool)
    (bNonempty : v.b≠[]) (eNonempty : v.e≠[]) (gNonempty : v.g≠[]) (iNonempty : v.i≠[]) :
    BoundedRun code (Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::suffix))
      (finalPort (observedFirst v.i) (observedFirst v.e) (observedFirst v.b))
      (ReturnNineBook.tapeAt base (ReturnNineOut.mask v) 1 suffix) (fee v) := by
  let c:=observedFirst v.i
  let t:=observedFirst v.e
  let b:=observedFirst v.b
  let v0:=ReturnNineBook.clearI v
  let v1:=ReturnNineBook.clearGE v0
  let v2:=ReturnNineBook.clearB v1
  have first:=bounded_pad (by decide : 7≤31) (ReturnNineBook.stage0_bounded base v suffix iNonempty)
  have second:=bounded_pad (by decide : 29≤31) (ReturnNineBook.stage1_bounded base v0 suffix gNonempty eNonempty)
  have third:=ReturnNineBook.stage2_bounded base v1 suffix bNonempty
  obtain ⟨xs,run0,time0⟩:=first
  obtain ⟨ys,run1,time1⟩:=second
  obtain ⟨zs,run2,time2⟩:=third
  have row0 : PSTRTMSeq005.RunsFrom (rows 0)
      ⟨0,Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::suffix)⟩ xs
      ⟨padLabel (by decide : 7≤31) (ReturnNineBook.port0 c),ReturnNineBook.tapeAt base v0 8 suffix⟩ := by
    exact run0
  have row1 : PSTRTMSeq005.RunsFrom (rows (middle c))
      ⟨0,ReturnNineBook.tapeAt base v0 8 suffix⟩ ys
      ⟨padLabel (by decide : 29≤31) (ReturnNineBook.port1 t),ReturnNineBook.tapeAt base v1 4 suffix⟩ := by
    rw [rows_middle]
    exact run1
  have row2 : PSTRTMSeq005.RunsFrom (rows (last c t))
      ⟨0,ReturnNineBook.tapeAt base v1 4 suffix⟩ zs
      ⟨ReturnNineBook.port2 b,ReturnNineBook.tapeAt base v2 1 suffix⟩ := by
    rw [rows_last]
    exact run2
  have segment0:=block_segment rows ports (0 : Fin 7) _ _ xs row0
  have segment1:=block_segment rows ports (middle c) _ _ ys row1
  have segment2:=block_segment rows ports (last c t) _ _ zs row2
  have transfer0:=block_transfer rows ports (0 : Fin 7) _ (middle c,0) row0.2.2.2 (ports_first c)
  have transfer1:=block_transfer rows ports (middle c) _ (last c t,0) row1.2.2.2 (ports_middle c t)
  have joined:=segment_append _ _ _ _ _ _ _ segment0 segment1 transfer0
  have complete:=segment_append _ _ _ _ _ _ _ joined segment2 transfer1
  have halted:=block_halt rows ports (last c t) _ row2.2.2.2 (ports_last c t _)
  have actual:=segment_runsFrom _ _ _ _ complete halted
  have entry : blockCfg (p:=6) (s:=31) (0 : Fin 7)
      (⟨0,Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::suffix)⟩ : MachineState 31)=
      (⟨0,Tape.mk₂ (ReturnNineLayout.footerLeft base v) (false::suffix)⟩ : MachineState (totalStates 6 31)) := blockCfg_zero _
  rw [entry] at actual
  refine ⟨(xs.map (blockCfg (p:=6) (s:=31) 0)++ys.map (blockCfg (p:=6) (s:=31) (middle c)))++
      zs.map (blockCfg (p:=6) (s:=31) (last c t)),?_,?_⟩
  · simpa only [code,blockCfg,finalPort,c,t,b,v2,v1,v0,masked_exact] using actual
  · simp only [List.length_append,List.length_map]
    dsimp only [v0,v1,ReturnNineBook.clearI,ReturnNineBook.clearGE,ReturnNineBook.clearE,ReturnNineBook.clearG] at time1 time2
    dsimp only [fee]
    omega

end RootB23.Threshold.ReturnNineObserved
