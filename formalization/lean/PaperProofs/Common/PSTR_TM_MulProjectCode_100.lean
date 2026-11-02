module
public import PaperProofs.Common.PSTR_TM_MulExpandCode_095
public import PaperProofs.Common.PSTR_TM_CompactRun_051

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectCode100
open PaperProofs.Common.Native.RationalControllerComputation

def oldLabel (q : Fin 112) : Fin 115 := ⟨2+q.val,by have hq := q.isLt; omega⟩
def liftOld (old : MachineState 111) : MachineState 114 := ⟨oldLabel old.q,old.Tape⟩

/-- ONE fixed115-label projection preparation. It physically skips each
retained C pair, reuses095's real marker/prefix-shifter to insert a zero
pair before A, and really overwrites A and B with zero. Thus output is four
flagged digits [C,0,0,0] per original tuple. Original C is retained by the
actual prefix copy, not a stored answer. Both whole-tape compatible frozen
051 compact calls can then remove the three zero digits. Correctness/cost
and canonical high-zero trimming are separate outstanding obligations. -/
def prepareMachine : Machine 114 := fun q symbol =>
  if h0 : q.val<2 then
    if q.val=0 then some (1,.move .right)
    else if symbol then some (2,.move .right) else some (110,.move .left)
  else if h1 : q.val<114 then
    if q.val=101 then some (103,.write false)
    else if q.val=102 then some (104,.write false)
    else if q.val=108 then some (114,.write false)
    else if q.val=109 then some (0,.move .right)
    else (PSTRTMMulExpandCode095.expandMachine ⟨q.val-2,by omega⟩ symbol).map
      (fun (next,statement) => (oldLabel next,statement))
  else some (109,.move .right)

def state (q : Fin 115) (left right : List Bool) : MachineState 114 := ⟨q,Turing.Tape.mk₂ left right⟩
def cBits (triples : List PSTRTMMulPassCode079.Triple) : List Bool := triples.map (fun (c,_,_) => c)
def quadBits (triples : List PSTRTMMulPassCode079.Triple) : List Bool := triples.flatMap (fun (c,_,_) => [c,false,false,false])

theorem prepare_halt (left right : List Bool) : Turing.TM0.step prepareMachine (state 113 left right)=none := by
  simp [Turing.TM0.step,prepareMachine,state,PSTRTMMulExpandCode095.expandMachine,PSTRTMMulRewind085.rewindMachine]

/-- Exact tape-format identities for the TWO REAL frozen compact calls.
They certify their common whole-tape ABI, not a free data reformatting. -/
theorem quad_format (triples : List PSTRTMMulPassCode079.Triple) :
    PSTRTMIncrement009.blocks (quadBits triples)=PSTRTMBinaryAdd024.resultColumns
      (PSTRTMCompactUnit048.paddedDigits (cBits triples)) := by
  induction triples with
  | nil => rfl
  | cons triple later ih =>
    obtain ⟨c,a,b⟩ := triple
    simpa only [quadBits,cBits,List.flatMap_cons,List.map_cons,PSTRTMIncrement009.blocks,
      PSTRTMCompactUnit048.paddedDigits,List.cons_append,List.nil_append,PSTRTMBinaryAdd024.resultColumns] using
        congrArg (fun bits => c::true::false::true::false::true::false::true::bits) ih

theorem first_compact_format (triples : List PSTRTMMulPassCode079.Triple) :
    PSTRTMIncrement009.blocks (PSTRTMCompactUnit048.paddedDigits (cBits triples))=
      PSTRTMBinaryAdd024.resultColumns (cBits triples) := PSTRTMCompactUnit048.blocks_paddedDigits _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectCode100
