module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038c

/-! Original SOURCE with an existing nonempty cache bank. The old original
footer is really written TRUE for the backward record walk and really
restored FALSE before the frozen original-field return. The latest end is
always TRUE. This is the per-bit route, not a canonical EOF shortcut. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticWidth018 (BoundedRun)

def originalFarContext (context : List Bool) (first : RecordSpec) (later : List RecordSpec) : List Bool :=
  context++false::(List.replicate first.gap false++true::false::
    (PSTRTMIncrement009.blocks first.digits++false::cacheContext later))

theorem originalFarContext_word (context : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (suffix : List Bool) :
    originalFarContext context first later++true::suffix=context++false::bankTail (first::later) suffix := by
  simp only [originalFarContext,bankTail,PA17TMRatArithmeticRecordNav032.recordWord,
    List.append_assoc,List.cons_append,cacheContext_word]

theorem originalFarContext_head (context : List Bool) (first : RecordSpec) (later : List RecordSpec)
    (h : context.headD false=false) : (originalFarContext context first later).head?=some false := by
  cases context with
  | nil => rfl
  | cons bit tail =>
    have hb : bit=false := h
    subst bit
    rfl

def originalFarFinish (finish : List Bool → List Bool → List Bool) (records : List RecordSpec)
    (left remaining : List Bool) : List Bool := bankLeft (finish left remaining) records

theorem originalFarFinish_cons (finish : List Bool → List Bool → List Bool)
    (hc : ∀ left bit later, finish (true::bit::left) later=finish left (bit::later))
    (records : List RecordSpec) (left : List Bool) (bit : Bool) (remaining : List Bool) :
    originalFarFinish finish records (true::bit::left) remaining=
      originalFarFinish finish records left (bit::remaining) := by
  unfold originalFarFinish
  rw [hc]

def originalOutCap (j : Nat) : Nat := 12+forwardCap (j+1)+1
def originalOutMachine (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) : Machine (originalOutCap j) :=
  PSTRTMSeq005.seqMachine (a:=12) (b:=forwardCap (j+1))
    (PA17TMRatArithmeticFarLoad031.outSetMachine route) (forwardMachine (j+1))
def originalOutPort (j : Nat) : Fin (originalOutCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=12) (forwardPort (j+1))

/-- j is the compiled count of records AFTER the first existing record;
the nonempty bank has j+1 records. No width or value enters the code. -/
theorem original_out_bounded (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (left remaining suffix : List Bool) :
    BoundedRun (originalOutMachine route j)
      (Tape.mk₂ left (PSTRTMIncrement009.blocks remaining++false::
        (originalFarContext context first records++true::suffix))) (originalOutPort j)
      (Tape.mk₂ (originalFarFinish finish (first::records) left remaining) (true::suffix))
      (2*remaining.length+cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3) := by
  have ho := correct.out_run left remaining (bankTail (first::records) suffix)
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ (finish left remaining) (false::bankTail (first::records) suffix)) 1
      (Tape.mk₂ (finish left remaining) (true::bankTail (first::records) suffix)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true (finish left remaining) (bankTail (first::records) suffix),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false true (finish left remaining) (bankTail (first::records) suffix),by rfl⟩
  have hlen : (first::records).length=j+1 := by simp only [List.length_cons,hj]
  have hf := forward_bounded (j+1) (first::records) hlen (finish left remaining) suffix
  have result := (ho.seq ht).seq hf
  have hcost : (2*remaining.length+cost)+2+
      (totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+1)≤
      2*remaining.length+cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3 := by omega
  simpa only [originalOutMachine,originalOutCap,PA17TMRatArithmeticFarLoad031.outSetMachine,originalOutPort,
    PA17TMRatArithmeticFarLoad031.fieldWord,originalFarContext_word,originalFarFinish,bankStart,bankEnd] using result.mono hcost

def originalBackClearCap (j : Nat) : Nat := backwardCap (j+1)+1+1
def originalBackClearMachine (j : Nat) : Machine (originalBackClearCap j) :=
  PSTRTMSeq005.seqMachine (a:=backwardCap (j+1)) (b:=1)
    (backwardMachine (j+1)) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def originalBackCap (j : Nat) : Nat := originalBackClearCap j+26+1
def originalBackMachine (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) : Machine (originalBackCap j) :=
  PSTRTMSeq005.seqMachine (a:=originalBackClearCap j) (b:=26) (originalBackClearMachine j) route.back
def originalBackPort (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) : Fin (originalBackCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=originalBackClearCap j) route.backPort

theorem original_back_bounded (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (archive remaining suffix : List Bool) :
    BoundedRun (originalBackMachine route j)
      (Tape.mk₂ (originalFarFinish finish (first::records) (false::archive) remaining) (true::suffix))
      (originalBackPort route j)
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks remaining++false::
        (originalFarContext context first records++true::suffix)))
      (2*remaining.length+cost+totalGap (first::records)+2*totalWidth (first::records)+12*(j+1)+3) := by
  have hlen : (first::records).length=j+1 := by simp only [List.length_cons,hj]
  have hb := backward_bounded (j+1) (first::records) hlen (finish (false::archive) remaining) suffix
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ (finish (false::archive) remaining) (true::bankTail (first::records) suffix)) 1
      (Tape.mk₂ (finish (false::archive) remaining) (false::bankTail (first::records) suffix)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false (finish (false::archive) remaining) (bankTail (first::records) suffix),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom true false (finish (false::archive) remaining) (bankTail (first::records) suffix),by rfl⟩
  have hr := correct.back_run archive remaining (bankTail (first::records) suffix)
  have result := (hb.seq ht).seq hr
  have hcost : (totalGap (first::records)+2*totalWidth (first::records)+12*(j+1)+1)+2+
      (2*remaining.length+cost)≤
      2*remaining.length+cost+totalGap (first::records)+2*totalWidth (first::records)+12*(j+1)+3 := by omega
  simpa only [originalBackMachine,originalBackCap,originalBackClearCap,originalBackClearMachine,originalBackPort,
    PA17TMRatArithmeticFarLoad031.fieldWord,originalFarContext_word,originalFarFinish,bankStart,bankEnd] using result.mono hcost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
