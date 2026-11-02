module
public import Paid.PDCompute_CoreProgram_Fetch_002
public import Paid.PDCompute_CoreSuffix_Actual_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreRun
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open RootD27.Core PDCompute.Solver

/-- Recombine actual adjacent fetches with abstract lists and addresses.
No concrete instruction array is normalized. -/
theorem append_fetch (ram : Program) (origin : ℕ) (first later : List Instruction)
    (front : FetchesCode ram origin first) (back : FetchesCode ram (origin+first.length) later) :
    FetchesCode ram origin (first++later) := by
  intro offset inside
  by_cases earlier : offset<first.length
  · exact (front offset earlier).trans (List.getElem?_append_left earlier).symm
  · have bound : offset-first.length<later.length := by
      rw [List.length_append] at inside
      omega
    have actual:=back (offset-first.length) bound
    have position : origin+first.length+(offset-first.length)=origin+offset := by omega
    rw [position] at actual
    exact actual.trans (List.getElem?_append_right (by omega)).symm

theorem three_fetch (ram : Program) (origin : ℕ) (first second third : List Instruction)
    (one : FetchesCode ram origin first)
    (two : FetchesCode ram (origin+first.length) second)
    (three : FetchesCode ram (origin+first.length+second.length) third) :
    FetchesCode ram origin (first++(second++third)) :=
  append_fetch ram origin first (second++third) one (append_fetch ram (origin+first.length) second third two three)

theorem body_expression (origin entry : ℕ) (labels : RoutineLabels) (label : labels.solveEntry=entry) :
    bisectionBodyCode (origin+4) entry (origin+520)=originalSearchBody origin labels := by
  unfold originalSearchBody
  exact congrArg (fun target=>bisectionBodyCode (origin+4) target (origin+520)) label.symm

theorem final_expression (start outer selected : ℕ) (loop : start+164=outer) (finish : outer+529=selected) :
    finalizationCode selected=finalizationCode (start+693) :=
  congrArg finalizationCode (by omega)

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program PDCompute.CorePrelude.bodyStart PDCompute.CorePrelude.afterCalibration
  initializeSearchCode bisectionBodyCode finalizationCode PDCompute.CoreSearchLoop.code
  PDCompute.CoreProgram.program PDCompute.CoreProgram.suffix PDCompute.CoreProgram.calleeCode
  PDCompute.CoreProgram.bodyCode PDCompute.CoreProgram.loopCode PDCompute.CoreProgram.finalCode
  PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.outerPC PDCompute.CoreProgram.bodyOrigin
  PDCompute.CoreProgram.decrementOrigin PDCompute.CoreProgram.selectorPC PDCompute.CoreProgram.tailPC
  PDCompute.CoreProgram.haltPC PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn
  PDCompute.CoreProgram.labels PDCompute.CoreProgram.pcUpper

theorem body_alias : PDCompute.CoreProgram.bodyCode=
    originalSearchBody PDCompute.CoreProgram.outerPC PDCompute.CoreProgram.labels := by
  unfold PDCompute.CoreProgram.bodyCode PDCompute.CoreProgram.bodyOrigin PDCompute.CoreProgram.decrementOrigin
  exact body_expression PDCompute.CoreProgram.outerPC PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.labels
    PDCompute.CoreProgram.fixed_labels.1

theorem loop_alias : PDCompute.CoreProgram.loopCode=
    PDCompute.CoreSearchLoop.code (PDCompute.CoreProgram.initializationPC+164)
      (originalSearchBody (PDCompute.CoreProgram.initializationPC+164) PDCompute.CoreProgram.labels) := by
  rw [PDCompute.CoreProgram.loopCode,body_alias,PDCompute.CoreProgram.outerPC]

theorem final_alias : PDCompute.CoreProgram.finalCode=
    finalizationCode (PDCompute.CoreProgram.initializationPC+693) := by
  unfold PDCompute.CoreProgram.finalCode
  exact final_expression PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.outerPC PDCompute.CoreProgram.selectorPC
    PDCompute.CoreProgram.static_bounds.2.1 PDCompute.CoreProgram.static_bounds.2.2.1

/-- The already certified three blocks of the ONE fixed Program pay
the exact whole945 premise of the frozen actual suffix producer. -/
theorem main_fetch : FetchesCode PDCompute.CoreProgram.program PDCompute.CoreProgram.initializationPC
    (PDCompute.CoreSuffix.code PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.labels) := by
  have initial:=PDCompute.CoreProgram.initialization_fetch
  have looping:=PDCompute.CoreProgram.suffix_fetch.2.1
  have finalizing:=PDCompute.CoreProgram.suffix_fetch.2.2.1
  have second : FetchesCode PDCompute.CoreProgram.program
      (PDCompute.CoreProgram.initializationPC+(initializeSearchCode PDCompute.CoreProgram.initializationPC
        PDCompute.CoreProgram.labels.solveEntry).length) PDCompute.CoreProgram.loopCode := by
    simpa only [initializeSearch_length,PDCompute.CoreProgram.static_bounds.2.1] using looping
  have third : FetchesCode PDCompute.CoreProgram.program
      (PDCompute.CoreProgram.initializationPC+(initializeSearchCode PDCompute.CoreProgram.initializationPC
        PDCompute.CoreProgram.labels.solveEntry).length+PDCompute.CoreProgram.loopCode.length)
      PDCompute.CoreProgram.finalCode := by
    simpa only [initializeSearch_length,PDCompute.CoreProgram.loop_length,
      PDCompute.CoreProgram.static_bounds.2.1,PDCompute.CoreProgram.static_bounds.2.2.1] using finalizing
  have combined:=three_fetch PDCompute.CoreProgram.program PDCompute.CoreProgram.initializationPC _ _ _ initial second third
  rw [loop_alias,final_alias] at combined
  exact combined

theorem main_end : PDCompute.CoreProgram.initializationPC+945=PDCompute.CoreProgram.labels.solveEntry := by
  have bounds:=PDCompute.CoreProgram.static_bounds
  have label:=PDCompute.CoreProgram.fixed_labels.1
  omega

theorem fixed_program : PDCompute.CoreProgram.program=
    PDCompute.CorePrelude.program PDCompute.CoreProgram.suffix.toArray := by
  unfold PDCompute.CoreProgram.program
  rfl

end PDCompute.CoreRun
