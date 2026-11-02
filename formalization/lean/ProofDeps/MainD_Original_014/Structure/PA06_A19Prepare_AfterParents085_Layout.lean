module

public import Structure.PA06_A19Prepare_AfterGate081_Word
public import Structure.PA06_A19Prepare_AllQCode082
public import Structure.PA06_A19Prepare_PreBuildCards048

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED layouts for the actual post-parent continuation in the
fixed all-q program.  Every left prefix below includes the real early
gate patch; the four executed blocks keep their original absolute labels. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims

abbrev program := PA06A19PrepareAllQCode082.program
abbrev bits := PA06A19PreparePreBuild044.bits
abbrev controlBase := PA06A19PreparePreBuild044.controlBase
abbrev allocation := PA06A19PreparePreBuild044.allocation

def oldTail : List PackingOp :=
  PA06A19PreparePostDP055.tail
    (PA06A19PrepareRawActive076.bodyTail PA06A19PrepareAllQCode082.right)

def patch (code : List PackingOp) : List PackingOp :=
  PA06A19PrepareEarlyGate079.program (5 * PA06A19PrepareAllQCode082.handlerStart) code

def headerRight : List PackingOp :=
  PA06A19PrepareRawSequence043.suffix (PA06A19PreparePreBuild044.suffix oldTail)
def headerLeft : List PackingOp :=
  patch (PA06A19PrepareRawHeader039Entry.front headerRight)
def sequenceRight : List PackingOp := PA06A19PreparePreBuild044.suffix oldTail
def sequenceLeft : List PackingOp :=
  patch (PA06A19PrepareRawSequence043.front sequenceRight)
def cacheLeft : List PackingOp := patch (PA06A19PreparePreBuild044.rawFront oldTail)
def clearLeft : List PackingOp := patch (PA06A19PreparePreBuild044.clearFront oldTail)
def cacheRight : List PackingOp := PA06A19PrepareClearVM045.programAt 1588 ++ oldTail

theorem oldCode_eq : PA06A19PreparePreBuild044.program oldTail =
    PA06A19PrepareAllQCode082.oldP := rfl

theorem patch_length (code : List PackingOp) (room : 10 ≤ code.length) :
    (patch code).length = code.length :=
  PA06A19PrepareEarlyGate079.program_length _ code room

theorem patch_layout (left block right : List PackingOp) (room : 10 ≤ left.length)
    (layout : left ++ block ++ right = PA06A19PrepareAllQCode082.oldP) :
    patch left ++ block ++ right = program := by
  have old : PA06A19PrepareAllQCode082.oldP = left ++ (block ++ right) := by
    simpa only [List.append_assoc] using layout.symm
  change patch left ++ block ++ right =
    PA06A19PrepareEarlyGate079.program (5 * PA06A19PrepareAllQCode082.handlerStart)
      PA06A19PrepareAllQCode082.oldP
  rw [old, PA06A19PrepareAllQCode082.patch_append _ _ _ room]
  exact List.append_assoc _ _ _

private theorem raw_header_front_length (tail : List PackingOp) :
    (PA06A19PrepareRawHeader039Entry.front tail).length = 1206 :=
  (PA06A19PrepareRawHeader039Entry.front_length tail).trans
    PA06A19PrepareCompactCandidates007.inputStart_eq

theorem headerLeft_length : headerLeft.length = 1206 := by
  unfold headerLeft
  rw [patch_length _ (by rw [raw_header_front_length]; decide), raw_header_front_length]

theorem sequenceLeft_length : sequenceLeft.length = 1310 := by
  unfold sequenceLeft
  rw [patch_length _ (by rw [PA06A19PrepareRawSequence043.front_length]; decide),
    PA06A19PrepareRawSequence043.front_length]

theorem cacheLeft_length : cacheLeft.length = 1444 := by
  unfold cacheLeft
  rw [patch_length _ (by rw [PA06A19PreparePreBuild044.rawFront_length]; decide),
    PA06A19PreparePreBuild044.rawFront_length]

theorem clearLeft_length : clearLeft.length = 1588 := by
  unfold clearLeft
  rw [patch_length _ (by rw [PA06A19PreparePreBuild044.clearFront_length]; decide),
    PA06A19PreparePreBuild044.clearFront_length]

theorem header_layout :
    headerLeft ++ PA06A19PrepareRawHeader039Body.headerProgram headerLeft.length ++ headerRight = program := by
  rw [headerLeft_length]
  change patch (PA06A19PrepareRawHeader039Entry.front headerRight) ++
    PA06A19PrepareRawHeader039Body.headerProgram 1206 ++ headerRight = program
  apply patch_layout (PA06A19PrepareRawHeader039Entry.front headerRight)
    (PA06A19PrepareRawHeader039Body.headerProgram 1206) headerRight
    (by rw [raw_header_front_length]; decide)
  have layout := PA06A19PrepareRawHeader039Entry.program_layout headerRight
  rw [raw_header_front_length] at layout
  exact layout.trans oldCode_eq

theorem sequence_layout :
    sequenceLeft ++ PA06A19PrepareRuntimeLayout026.sequence sequenceLeft.length ++ sequenceRight = program := by
  rw [sequenceLeft_length]
  change patch (PA06A19PrepareRawSequence043.front sequenceRight) ++
    PA06A19PrepareRuntimeLayout026.sequence 1310 ++ sequenceRight = program
  apply patch_layout (PA06A19PrepareRawSequence043.front sequenceRight)
    (PA06A19PrepareRuntimeLayout026.sequence 1310) sequenceRight
    (by rw [PA06A19PrepareRawSequence043.front_length]; decide)
  have layout := PA06A19PrepareRawSequence043.program_layout sequenceRight
  rw [PA06A19PrepareRawSequence043.front_length] at layout
  exact layout.trans oldCode_eq

theorem cache_layout :
    cacheLeft ++ PA06A19PrepareChildrenCache023.programAt cacheLeft.length ++ cacheRight = program := by
  rw [cacheLeft_length]
  change patch (PA06A19PreparePreBuild044.rawFront oldTail) ++
    PA06A19PrepareChildrenCache023.programAt 1444 ++ cacheRight = program
  apply patch_layout (PA06A19PreparePreBuild044.rawFront oldTail)
    (PA06A19PrepareChildrenCache023.programAt 1444) cacheRight
    (by rw [PA06A19PreparePreBuild044.rawFront_length]; decide)
  have layout := PA06A19PreparePreBuild044.cache_layout oldTail
  rw [PA06A19PreparePreBuild044.rawFront_length] at layout
  exact layout.trans oldCode_eq

theorem clear_layout :
    clearLeft ++ PA06A19PrepareClearVM045.programAt clearLeft.length ++ oldTail = program := by
  rw [clearLeft_length]
  change patch (PA06A19PreparePreBuild044.clearFront oldTail) ++
    PA06A19PrepareClearVM045.programAt 1588 ++ oldTail = program
  apply patch_layout (PA06A19PreparePreBuild044.clearFront oldTail)
    (PA06A19PrepareClearVM045.programAt 1588) oldTail
    (by rw [PA06A19PreparePreBuild044.clearFront_length]; decide)
  have layout := PA06A19PreparePreBuild044.clear_layout oldTail
  rw [PA06A19PreparePreBuild044.clearFront_length] at layout
  exact layout.trans oldCode_eq

theorem cache_code : PA06A19PrepareChildrenCache023.CodeAt program 1444 := by
  have code := PA06A19PrepareChildrenCache023.append_code cacheLeft cacheRight
  rw [cache_layout, cacheLeft_length] at code
  exact code

def clock (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  PA06A19PrepareRawHeader039Body.headerClock full.length q +
    PA06A19PrepareRuntimeLayout026.sequenceClock full.length q +
    PA06A19PrepareChildrenCache023.totalSteps q full +
    PA06A19PrepareClearVM045.clock full.length q (treeSize q full)

def Safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (before : WordState (bits q full)) (steps : Nat) : Prop :=
  ∀ count < steps, PA06A19PrepareInitialUsed037.Fetched (allocation q full)
    (controllerInput q full used) program
    (packingRun (controllerInput q full used) program count before)

theorem Safe.add {q : Nat} {full : List (Finset (Fin q))} {used : Finset (Fin q)}
    {before : WordState (bits q full)} {left right : Nat}
    (first : Safe q full used before left)
    (second : Safe q full used
      (packingRun (controllerInput q full used) program left before) right) :
    Safe q full used before (left + right) := by
  intro count bound
  by_cases early : count < left
  · exact first count early
  · have split : count = left + (count - left) := by omega
    have safe := second (count - left) (by omega)
    rw [split, PA06A19PrepareRawHeader039Body.wordRun_add]
    exact safe

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085
