module

public import Paid.PDCompute_CorePreludePC_Segments_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

private theorem positive_offset (label : Label) (different : label≠.enter) :
    0<((labels.take (labels.idxOf label)).map blockLength).sum := by
  cases label <;> first | exact False.elim (different rfl) | decide

theorem label_after_enter (origin : ℕ) (label : Label) (different : label≠.enter) :
    origin+1 ≤ labelAddress origin label := by
  have positive:=positive_offset label different
  unfold labelAddress
  omega

private def SafeControl : Control→Prop
  | .go target=>target≠.enter
  | .branch _ zero nonzero=>zero≠.enter ∧ nonzero≠.enter
  | .returnToCaller=>False

private theorem safe_control (label : Label) (different : label≠.finish) :
    SafeControl (basicBlock label).control := by
  cases label <;> first | exact False.elim (different rfl) | simp [SafeControl,basicBlock]

/-- Every direct control target in the ORIGINAL kernel is after enter.
The only indirect control is finish and is handled by the real return ABI. -/
theorem control_after_enter (origin : ℕ) (input : List Cell) (label : Label)
    (middle after : State) (different : label≠.finish)
    (executed : (controlInstruction origin (basicBlock label).control).execute input middle=some after) :
    origin+1 ≤ after.pc := by
  have safe:=safe_control label different
  generalize controlValue : (basicBlock label).control=control at safe executed
  cases control with
  | go target =>
    change target≠.enter at safe
    have equal : {middle with pc:=labelAddress origin target}=after := by
      simpa [controlInstruction,Instruction.execute] using executed
    rw [←equal]
    exact label_after_enter origin target safe
  | branch register zero nonzero =>
    change zero≠.enter ∧ nonzero≠.enter at safe
    cases value : (middle.register register).nat? with
    | none => simp [controlInstruction,Instruction.execute,value] at executed
    | some count =>
      by_cases empty : count=0
      · have equal : {middle with pc:=labelAddress origin zero}=after := by
          simpa [controlInstruction,Instruction.execute,value,empty] using executed
        rw [←equal]
        exact label_after_enter origin zero safe.1
      · have equal : {middle with pc:=labelAddress origin nonzero}=after := by
          simpa [controlInstruction,Instruction.execute,value,empty] using executed
        rw [←equal]
        exact label_after_enter origin nonzero safe.2
  | returnToCaller => exact False.elim safe

theorem prefix_after_enter (origin : ℕ) (input : List Cell) (label : Label)
    (before state : State) (count : ℕ) (lower : origin+1 ≤ before.pc)
    (executed : linearExecute input ((basicBlock label).body.take count) before=some state) :
    origin+1 ≤ state.pc := by
  have straight : StraightCode ((basicBlock label).body.take count):=
    fun instruction member=>basicBlock_straight label instruction (List.mem_of_mem_take member)
  have pc:=linearExecute_pc input _ straight before state executed
  omega

theorem block_prefix_after_enter (origin : ℕ) (input : List Cell) (label : Label)
    (before after state : State) (first : origin+1 ≤ before.pc) (last : origin+1 ≤ after.pc)
    (prefixRun : PDROC.CalibrationRow.BlockPrefix input label before after state) :
    origin+1 ≤ state.pc := by
  rcases prefixRun with ⟨count,_bound,executed⟩|same
  · exact prefix_after_enter origin input label before state count first executed
  · subst state
    exact last

private theorem init_entry_not_finish {level cursor : ℕ} {label : Label} {before : State}
    (entry : PDROC.CalibrationRow.InitLabelEntry level cursor label before) : label≠.finish := by
  intro same
  subst label
  simp [PDROC.CalibrationRow.InitLabelEntry] at entry

theorem init_provenance_lower (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (caller state : State) (lower : origin+1 ≤ caller.pc)
    (actual : PDROC.CalibrationRow.InitProvenance P origin base level input caller state) :
    origin+1 ≤ state.pc := by
  induction actual with
  | initial => exact lower
  | block cursor label before middle after state _previous _data _bound entry _position _body control prefixRun ih =>
    exact block_prefix_after_enter origin input label before after state ih
      (control_after_enter origin input label middle after (init_entry_not_finish entry) control) prefixRun

theorem scatter_provenance_lower (P : Parameters) (origin base level clock read write : ℕ)
    (input : List Cell) (caller state : State) (lower : origin+1 ≤ caller.pc)
    (actual : PDROC.CalibrationRow.ScatterProvenance P origin base level clock read write input caller state) :
    origin+1 ≤ state.pc := by
  induction actual with
  | initial => exact lower
  | block cursor label before middle after state _previous entry _position _body control prefixRun ih =>
    have different : label≠.finish:=by cases entry <;> decide
    exact block_prefix_after_enter origin input label before after state ih
      (control_after_enter origin input label middle after different control) prefixRun

theorem zero_provenance_lower (P : Parameters) (origin base level clock read write : ℕ)
    (previous : Array ℚ) (input : List Cell) (caller state : State) (lower : origin+1 ≤ caller.pc)
    (actual : PDROC.CalibrationRow.ZeroRuntime.ZeroProvenance P origin base level clock read write previous input caller state) :
    origin+1 ≤ state.pc := by
  induction actual with
  | initial _data => exact lower
  | gate cursor before middle after state _previous _entry _bound _position _body control location _phase ih =>
    exact block_prefix_after_enter origin input .zeroGate before after state ih
      (control_after_enter origin input .zeroGate middle after (by decide) control) location
  | cell cursor before middle after state _previous _entry _inside _index _position _body control location ih =>
    rcases location with ⟨count,_bound,run,_phase⟩|⟨same,_phase⟩
    · exact prefix_after_enter origin input .zeroCell before state count ih run
    · subst state
      exact control_after_enter origin input .zeroCell middle after (by decide) control

theorem q_provenance_lower (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (caller state : State) (lower : origin+1 ≤ caller.pc)
    (actual : PDROC.CalibrationRow.QProvenance P origin base level input caller state) :
    origin+1 ≤ state.pc := by
  induction actual with
  | initial => exact lower
  | block label before middle after state _previous entry _position _body control prefixRun ih =>
    have different : label≠.finish:=by cases entry <;> decide
    exact block_prefix_after_enter origin input label before after state ih
      (control_after_enter origin input label middle after different control) prefixRun
  | zero clock before state _previous _bound _data _position phase ih =>
    exact zero_provenance_lower P origin base level clock _ _ _ input before state ih phase
  | scatter clock before state _previous _bound _data _position phase ih =>
    exact scatter_provenance_lower P origin base level clock _ _ input before state ih phase

theorem row_provenance_lower (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (caller state : State) (position : caller.pc=labelAddress origin .levelInit)
    (actual : PDROC.CalibrationRow.RowProvenance P origin base level input caller state) :
    origin+1 ≤ state.pc := by
  have initial : origin+1 ≤ caller.pc:=by rw [position];exact label_after_enter origin .levelInit (by decide)
  induction actual with
  | initial => exact initial
  | levelInit state _header _position prefixRun =>
    exact block_prefix_after_enter origin input .levelInit caller _ state initial
      (label_after_enter origin .initGate (by decide)) prefixRun
  | init before state _previous _header _position _cursor _width _read _write phase ih =>
    exact init_provenance_lower P origin base level input before state ih phase
  | scaffold label before middle after state _previous entry _position _body control prefixRun ih =>
    have different : label≠.finish:=by cases entry <;> decide
    exact block_prefix_after_enter origin input label before after state ih
      (control_after_enter origin input label middle after different control) prefixRun
  | q before state _previous _data _position phase ih =>
    exact q_provenance_lower P origin base level input before state ih phase

/-- The original complete row and caller-header reconstruction, with
all PC facts interpreted on its SAME frozen canonical provenance trace. -/
theorem row_call_lower (P : Parameters) (origin base : ℕ) (input : List Cell)
    (before : State) (header : PDLower.CalibrationCompute.Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (M : header.M=P.certificate.M) (Q : header.Q=P.certificate.Q)
    (gamma : header.gamma=P.certificate.gamma)
    (position : before.pc=labelAddress origin .levelInit) (bounded : header.level≤P.certificate.M+1) :
    ∃ after : State, LowerSegment origin input (origin+1) before after ∧
      after.pc=labelAddress origin .sumStart ∧
      ({header with
        clock:=P.certificate.Q,cursor:=2*header.level+1,width:=2*header.level+1,
        readBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1,
        writeBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).2}).At after base ∧
      RowAt after (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1
        (P.walkRow header.level true P.certificate.Q) ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧
      MemoryFrame (PDROC.CalibrationRow.region base P.certificate.M) before after := by
  have arguments:=represented.rowArguments fresh M Q gamma
  obtain ⟨after,actual,pc,data,clock,cursor,width,read,write,row⟩:=
    PDROC.CalibrationRow.row_complete_provenance input P origin base header.level before arguments position bounded
  have final:=actual.final
  have callerFrame : MemoryFrame (PDROC.CalibrationRow.region base header.M) before after:=by simpa only [M] using final.1
  have callerHeader:=represented.afterRow callerFrame final.2.2.2.1 _ _ _ _ _ clock cursor width read write
  exact ⟨after,row_lower actual (fun state provenance=>row_provenance_lower P origin base header.level input before state position provenance),
    pc,callerHeader,row,final.2.2.1.trans fresh,final.2.1,final.1⟩

end PDCompute.CorePreludePC
