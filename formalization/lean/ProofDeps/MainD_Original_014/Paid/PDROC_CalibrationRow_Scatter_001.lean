module

public import Paid.PDROC_CalibrationRow_037
public import Paid.PDROC_CalibrationRow_Init_SafeSegment_001
public import Paid.PDROC_CalibrationRow_Init_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Concrete entry facts for each original scatter block. The two stores
have different physical rows: the right store sees the actual left bump.
The source cursor in header7 changes only in scatterNext. -/
inductive ScatterEntry (P : Parameters) (base level clock cursor read write : ℕ)
    (before : State) : Label → Prop where
  | gate (data : ScatterData P base level clock cursor read write before)
      (bound : cursor≤2*level+1) : ScatterEntry P base level clock cursor read write before .scatterGate
  | leftRead (data : ScatterData P base level clock cursor read write before)
      (inside : cursor<2*level+1) (index : before.register .index=.natural cursor) :
      ScatterEntry P base level clock cursor read write before .leftRead
  | leftInterior (data : ScatterData P base level clock cursor read write before)
      (inside : cursor<2*level+1) (interior : ¬(cursor=0 ∨ cursor=2*level))
      (index : before.register .index=.natural cursor)
      (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma))) :
      ScatterEntry P base level clock cursor read write before .leftInterior
  | leftStore (data : ScatterData P base level clock cursor read write before)
      (inside : cursor<2*level+1)
      (index : before.register .index=.natural (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val)
      (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma))) :
      ScatterEntry P base level clock cursor read write before .leftStore
  | rightRead (inside : cursor<2*level+1)
      (data : ScatterLeftData P base level clock cursor read write inside before) :
      ScatterEntry P base level clock cursor read write before .rightRead
  | rightInterior (inside : cursor<2*level+1)
      (data : ScatterLeftData P base level clock cursor read write inside before)
      (interior : ¬(cursor=0 ∨ cursor=2*level)) (index : before.register .index=.natural cursor)
      (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma))) :
      ScatterEntry P base level clock cursor read write before .rightInterior
  | rightStore (inside : cursor<2*level+1)
      (data : ScatterLeftData P base level clock cursor read write inside before)
      (index : before.register .index=.natural (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val)
      (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma))) :
      ScatterEntry P base level clock cursor read write before .rightStore
  | next (data : ScatterBothData P base level clock cursor read write before)
      (inside : cursor<2*level+1) : ScatterEntry P base level clock cursor read write before .scatterNext

theorem ScatterEntry.header {P : Parameters} {base level clock cursor read write : ℕ}
    {before : State} {label : Label}
    (entry : ScatterEntry P base level clock cursor read write before label) : Header P base level before := by
  cases entry with
  | gate data _ => exact data.control.header
  | leftRead data _ _ => exact data.control.header
  | leftInterior data _ _ _ _ => exact data.control.header
  | leftStore data _ _ _ => exact data.control.header
  | rightRead _ data => exact data.control.header
  | rightInterior _ data _ _ _ => exact data.control.header
  | rightStore _ data _ _ => exact data.control.header
  | next data _ => exact data.control.header

def ScatterClosed (P : Parameters) (origin base level clock read write : ℕ) (input : List Cell)
    (Good : State→Prop) : Prop :=
  ∀ cursor label before middle after,ScatterEntry P base level clock cursor read write before label →
    Good before → before.pc=labelAddress origin label →
    linearExecute input (basicBlock label).body before=some middle →
    (controlInstruction origin (basicBlock label).control).execute input middle=some after →
    ∀ state,((∃ count≤(basicBlock label).body.length,
      linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) → Good state

theorem scatterBlock_safe (P : Parameters) (origin base level clock cursor read write : ℕ)
    (input : List Cell) (Good : State→Prop)
    (closed : ScatterClosed P origin base level clock read write input Good)
    (label : Label) (row : rowLabel label=true) (before middle after : State)
    (entry : ScatterEntry P base level clock cursor read write before label) (good : Good before)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (frames : LinearFrames (region base P.certificate.M) input (basicBlock label).body before)
    (lastFrame : MemoryFrame (region base P.certificate.M) before after)
    (lastOutput : after.output=before.output) (lastFresh : after.register .fresh=before.register .fresh)
    (lastLive : before.live ⊆ after.live) :
    SafeSegment origin base (region base P.certificate.M) input Good before after
      (15*((basicBlock label).body.length+2)) :=
  SafeSegment.ofBlock origin base _ input Good label row before middle after position body control frames
    entry.header.live lastFrame lastOutput lastFresh lastLive
    (closed cursor label before middle after entry good position body control)

def scatterNoMemory : Instruction → Bool
  | .store _ _ | .release _ => false
  | _ => true

theorem scatterNoMemory_correct (region : Finset ℕ) (instruction : Instruction) (before : State)
    (safe : scatterNoMemory instruction=true) : WritesWithin region instruction before := by
  cases instruction <;> simp_all [scatterNoMemory,WritesWithin]

theorem scatterRead_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State)
    (label : Label) (read : label=.leftRead ∨ label=.rightRead) :
    LinearFrames region input (basicBlock label).body before := by
  have all : (basicBlock label).body.all scatterNoMemory=true := by
    rcases read with rfl|rfl <;> rfl
  exact LinearFrames.of_static region input _
    (fun instruction member state => scatterNoMemory_correct region instruction state
      ((List.all_eq_true.mp all) instruction member)) before

end PDROC.CalibrationRow
