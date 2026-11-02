module

public import Paid.PDCompute_SolverMinimumCompare_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def minimumUpdateCommands : List HeaderCommand := [.copy 25 23,.copy 28 24]

def minimumUpdateValues (values : ℕ → Cell) : ℕ → Cell :=
  Function.update (Function.update values 23 (values 25)) 24 (values 28)

def minimumUpdateCode (origin : ℕ) : List Instruction :=
  minimumCompareCode++[.branchZero .index (origin+20) (origin+8)]++headerCode minimumUpdateCommands

theorem minimumUpdateCode_length (origin : ℕ) : (minimumUpdateCode origin).length=20 := rfl

theorem minimumUpdateCommands_valid : ∀ command ∈ minimumUpdateCommands, command.Valid := by
  intro command member
  simp only [minimumUpdateCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide

theorem minimumUpdateCommands_eval (values : ℕ → Cell) :
    headerEval minimumUpdateCommands values=some (minimumUpdateValues values) := by
  simp [minimumUpdateCommands,headerEval,HeaderCommand.eval,minimumUpdateValues]

theorem minimumUpdate_compare_fetch (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (minimumUpdateCode origin)) (before : State) (hpc : before.pc=origin) :
    FetchesCode program before.pc minimumCompareCode := by
  intro offset inside
  have hi : offset < 7 := by simpa only [minimumCompareCode_length] using inside
  have h := hcode offset (by rw [minimumUpdateCode_length]; omega)
  rw [hpc]
  apply h.trans
  unfold minimumUpdateCode
  rw [List.getElem?_append_left (by change offset < 8; omega),List.getElem?_append_left inside]

theorem minimumUpdate_body_fetch (program : Program) (origin : ℕ)
    (hcode : FetchesCode program origin (minimumUpdateCode origin)) (before : State) (hpc : before.pc=origin+8) :
    FetchesCode program before.pc (headerCode minimumUpdateCommands) := by
  intro offset inside
  have hi : offset < 12 := by change offset < 12 at inside; exact inside
  have h := hcode (8+offset) (by rw [minimumUpdateCode_length]; omega)
  have he : before.pc+offset=origin+(8+offset) := by omega
  rw [he]
  apply h.trans
  unfold minimumUpdateCode
  have hl : (minimumCompareCode++[Instruction.branchZero .index (origin+20) (origin+8)]).length=8 := rfl
  rw [List.getElem?_append_right (by rw [hl]; omega),hl]
  have hs : 8+offset-8=offset := by omega
  rw [hs]

/-- True strict-less compare/branch/update. Equality follows the actual
zero branch and retains the older level. The update path copies the real
current index and candidate score using twelve ordinary ISA instructions. -/
theorem minimumUpdateCode_trace (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (minimumUpdateCode origin)) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (candidate best : ℚ)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hc : values 28=.rational candidate) (hb : values 24=.rational best) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 630 ∧
      Header after base (if candidate < best then minimumUpdateValues values else values) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+20 ∧
      Frame before after base n k ∧ after.output=before.output := by
  let compared := minimumCompareResult before base candidate best
  let returned : State := {compared with pc:=if candidate < best then origin+8 else origin+20}
  have fields := minimumCompareResult_fields before base candidate best
  obtain ⟨trace,hh,hl,hchain,ht,_⟩ := linearExecute_trace_time program input minimumCompareCode
    minimumCompareCode_straight before compared (minimumUpdate_compare_fetch program origin hcode before hpc)
    (minimumCompareCode_execute input before base values candidate best header hbase hc hb)
  have ht' : time program trace ≤ 120 := ht
  have hj : program[compared.pc]?=some (.branchZero .index (origin+20) (origin+8)) := by
    have he : compared.pc=origin+7 := fields.2.2.2.2.1.trans (congrArg (·+7) hpc)
    rw [he]
    have hclosed : (minimumUpdateCode origin)[7]?=some (.branchZero .index (origin+20) (origin+8)) := rfl
    exact (hcode 7 (by rw [minimumUpdateCode_length]; omega)).trans hclosed
  have hs : step program input compared=some returned := by
    unfold step
    rw [hj]
    have hi : compared.register .index=.natural (if candidate < best then 1 else 0) := fields.2.2.2.1
    by_cases less : candidate < best <;>
      simp [Instruction.execute,hi,Cell.nat?,returned,less]
  have controlled := chain_append_control program input trace compared returned hchain hl hs
  let branchTrace := trace++[returned]
  have hbh : branchTrace.head?=some before := by
    have hn : trace ≠ [] := by intro he; simp only [he,List.head?_nil,reduceCtorEq] at hh
    simpa only [branchTrace,List.head?_append_of_ne_nil trace hn] using hh
  have hbl : branchTrace.getLast?=some returned := by simp [branchTrace]
  have hbt : time program branchTrace ≤ 135 := by
    change time program (trace++[returned]) ≤ 135
    have h := controlled.2
    omega
  have hrh : Header returned base values := minimumCompareResult_header before base values candidate best header
  have hrb : returned.register .fresh=.natural base := fields.2.2.1.trans hbase
  have hrf : Frame before returned base n k := minimumCompareResult_frame before base n k candidate best
  have hro : returned.output=before.output := fields.2.2.2.2.2
  by_cases less : candidate < best
  · have hrpc : returned.pc=origin+8 := by simp only [returned,ite_eq_left less]
    obtain ⟨body,after,hbodyHead,hbodyLast,hbodyChain,hbodyTime,hafterHeader,hafterBase,hafterPC,hafterFrame,hafterOutput,_⟩ :=
      headerCode_trace minimumUpdateCommands program input returned base n k values _
        minimumUpdateCommands_valid hrh hrb (minimumUpdateCommands_eval values)
        (minimumUpdate_body_fetch program origin hcode returned hrpc)
    have joined := joinTrace_spec program input branchTrace body before returned after 135 495
      hbh hbl hbodyHead hbodyLast controlled.1 hbodyChain hbt hbodyTime
    refine ⟨joinTrace branchTrace body,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,?_,
      hafterBase,?_,hrf.trans hafterFrame,hafterOutput.trans hro⟩
    · simpa only [ite_eq_left less] using hafterHeader
    · have hlc : (headerCode minimumUpdateCommands).length=12 := rfl
      rw [hafterPC,hrpc,hlc]
  · refine ⟨branchTrace,returned,hbh,hbl,controlled.1,hbt.trans (by decide),?_,hrb,?_,hrf,hro⟩
    · simpa only [ite_eq_right less] using hrh
    · simp only [returned,ite_eq_right less]

end PDCompute.Solver
