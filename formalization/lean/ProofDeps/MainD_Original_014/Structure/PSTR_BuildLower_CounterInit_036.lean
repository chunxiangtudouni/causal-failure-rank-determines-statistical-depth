module

public import Structure.PSTR_BuildLower_ConcreteAST_031
public import Structure.PSTR_BuildLower_BankFrame_017

/-! Genuine compiler-private lexical-counter initialization. The64 real
instructions precede the fixed AST at label64, after the producer has finished.
They never rely on a caller zero-heap promise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterInit
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

def clearOps : List Nat → List PackingOp
  | [] => []
  | offset :: later => relativeWrite offset ++ clearOps later

def offsets : List Nat := (List.range 21).map (64 + ·)

def code : List PackingOp := [.base (.base (.constant .value 0))] ++ clearOps offsets

theorem offsets_eq : offsets = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84] := by decide

theorem code_length : code.length = 64 := by decide

theorem clearOps_straight (points : List Nat) : StraightProgram (clearOps points) := by
  induction points with
  | nil => simp [clearOps, StraightProgram]
  | cons offset later ih =>
    intro op hm
    simp only [clearOps, List.mem_append] at hm
    exact hm.elim (relativeWrite_straight offset op) (ih op)

theorem code_straight : StraightProgram code := by
  intro op hm
  simp only [code, List.mem_append, List.mem_singleton] at hm
  rcases hm with rfl | hm
  · trivial
  · exact clearOps_straight offsets op hm

private theorem write_range (rom : PhysicalROM) (offset : Nat) (ho : 64 ≤ offset) (ht : offset < 85) :
    BankRangeFrame (bits := bits) rom (relativeWrite offset) 64 85 := by
  refine ⟨fun state count => relativeWrite_prefix_base rom offset state count, ?_⟩
  intro state point outside count
  exact relativeWrite_prefix_frame rom offset state point (outside offset ho ht) count

private theorem clearOps_range (rom : PhysicalROM) (points : List Nat)
    (hp : ∀ offset ∈ points, 64 ≤ offset ∧ offset < 85) :
    BankRangeFrame (bits := bits) rom (clearOps points) 64 85 := by
  induction points with
  | nil => exact ⟨fun _ _ => by simp [clearOps, executeOps], fun _ _ _ _ => by simp [clearOps, executeOps]⟩
  | cons offset later ih =>
    apply bankRangeFrame_append
    · exact write_range rom offset (hp offset List.mem_cons_self).1 (hp offset List.mem_cons_self).2
    · exact ih (fun point hm => hp point (List.mem_cons_of_mem _ hm))

theorem code_range (rom : PhysicalROM) : BankRangeFrame (bits := bits) rom code 64 85 := by
  apply bankRangeFrame_append
  · refine ⟨?_, ?_⟩
    · intro state count
      cases count <;> simp [executeOps, packingExecuteOp, wordOp, wordInstruction]
    · intro state point _ count
      cases count <;> simp [executeOps, packingExecuteOp, wordOp, wordInstruction]
  · apply clearOps_range
    intro offset hm
    obtain ⟨index, hi, rfl⟩ := List.mem_map.mp hm
    have hh := List.mem_range.mp hi
    omega

private theorem clearOps_value (rom : PhysicalROM) (points : List Nat) (state : WordState bits) :
    (executeOps rom (clearOps points) state).register .value = state.register .value := by
  induction points generalizing state with
  | nil => rfl
  | cons offset later ih =>
    rw [clearOps, executeOps_append, ih]
    rfl

private theorem clearOps_preserves_zero (rom : PhysicalROM) (points : List Nat) (state : WordState bits)
    (point : BitVec bits) (hv : state.register .value = 0) (hh : state.heap point = 0) :
    (executeOps rom (clearOps points) state).heap point = 0 := by
  induction points generalizing state with
  | nil => exact hh
  | cons offset later ih =>
    rw [clearOps, executeOps_append]
    apply ih
    · change state.register .value = 0
      exact hv
    · rw [relativeWrite_heap]
      by_cases he : point = state.register .address + BitVec.ofNat bits offset
      · rw [he, Function.update_self]
        exact hv
      · rw [Function.update_of_ne he]
        exact hh

private theorem clearOps_member_zero (rom : PhysicalROM) (points : List Nat) (state : WordState bits)
    (offset : Nat) (hv : state.register .value = 0) (hm : offset ∈ points) :
    (executeOps rom (clearOps points) state).heap (state.register .address + BitVec.ofNat bits offset) = 0 := by
  induction points generalizing state with
  | nil => simp at hm
  | cons first later ih =>
    rw [clearOps, executeOps_append]
    rcases List.mem_cons.mp hm with he | hl
    · subst offset
      apply clearOps_preserves_zero rom later
      · change state.register .value = 0
        exact hv
      · rw [relativeWrite_heap, Function.update_self]
        exact hv
    · let mid := executeOps rom (relativeWrite first) state
      have hbase : mid.register .address = state.register .address := rfl
      have hvalue : mid.register .value = 0 := hv
      have result := ih mid hvalue hl
      rw [hbase] at result
      exact result

theorem counters_zero (rom : PhysicalROM) (state : WordState bits) (counter : Nat) (hc : counter < 21) :
    (executeOps rom code state).heap (state.register .address + BitVec.ofNat bits (64 + counter)) = 0 := by
  rw [code, executeOps_append]
  let initial := executeOps rom [.base (.base (.constant .value 0))] state
  have hbase : initial.register .address = state.register .address := rfl
  have hvalue : initial.register .value = 0 := rfl
  have hm : 64 + counter ∈ offsets := List.mem_map.mpr ⟨counter, List.mem_range.mpr hc, rfl⟩
  have result := clearOps_member_zero rom offsets initial (64 + counter) hvalue hm
  rw [hbase] at result
  exact result

theorem run (rom : PhysicalROM) (left right : List PackingOp) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code ++ right).length)) :
    packingRun rom (left ++ code ++ right) 64 state = executeOps rom code state := by
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append, code_length]; omega)
    (PA17UniformGenerator035a.segment_index left code right) code_straight hcode hpcfit state hpc ha

def builderCode (start : Nat) : List PackingOp :=
  code ++ lowerProgram ConcreteAST.ports PA17ProgramTemplates041.fullBuild (start + 64) 0

def program : List PackingOp := builderCode 0

theorem builder_head_run (rom : PhysicalROM) (left right : List PackingOp) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ builderCode left.length ++ right)))
    (hpcfit : Fits bits (5 * (left ++ builderCode left.length ++ right).length)) :
    packingRun rom (left ++ builderCode left.length ++ right) 64 state = executeOps rom code state := by
  have hh := run rom left
    (lowerProgram ConcreteAST.ports PA17ProgramTemplates041.fullBuild (left.length + 64) 0 ++ right)
    state hpc ha (by simpa only [builderCode, List.append_assoc] using hcode)
    (by simpa only [builderCode, List.append_assoc] using hpcfit)
  simpa only [builderCode, List.append_assoc] using hh

theorem builder_head_pc (rom : PhysicalROM) (state : WordState bits) (start : Nat)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) :
    (executeOps rom code state).pc = BitVec.ofNat bits (5 * (start + 64)) := by
  rw [executeOps_pc rom code state code_straight, code_length, hp, BitVec.ofNat_add_ofNat]
  congr 1

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterInit
