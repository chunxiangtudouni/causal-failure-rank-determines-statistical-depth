module

public import Structure.PSTR_BuildLower_Dispatch_018

/-! The original fixed builder never reads the children ROM. This connects the
closed typed-AST fact to every literal operation of the actual old buildProgram;
it is not a new qualification on a caller or on an alternative target. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17ProgramTemplates041

def plainReadsChildren : Op → Bool
  | .base (.loadROM .children _ _) => true
  | _ => false

theorem opEval_readsChildren (expr : OpExpr) (rom : PhysicalROM) (environment : Nat → Nat) :
    plainReadsChildren (OpExpr.eval rom environment expr) = opReadsChildren expr := by
  cases expr with
  | constant target value => rfl
  | literal op =>
    cases op with
    | subtract target left right => rfl
    | base instruction =>
      cases instruction with
      | constant target value => rfl
      | add target left right => rfl
      | minimum target left right => rfl
      | select target condition whenTrue whenFalse => rfl
      | loadROM region target pointer => cases region <;> rfl
      | loadHeap target pointer => rfl
      | storeHeap pointer source => rfl

theorem program_eval_no_children (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (hstatic : programReadsChildren program = false) :
    ∀ op ∈ program.eval rom environment, plainReadsChildren op = false := by
  induction program generalizing environment with
  | code ops =>
    change ∀ op ∈ ops.map (OpExpr.eval rom environment), plainReadsChildren op = false
    intro op hm
    rcases List.mem_map.mp hm with ⟨expr, hexpr, rfl⟩
    rw [opEval_readsChildren]
    exact Bool.eq_false_iff.mpr ((List.any_eq_false.mp hstatic) expr hexpr)
  | append left right ihl ihr =>
    have hh := Bool.or_eq_false_iff.mp hstatic
    intro op hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ihl environment hh.1 op hm
    · exact ihr environment hh.2 op hm
  | «repeat» counter bound body ih =>
    intro op hm
    rcases List.mem_flatMap.mp hm with ⟨index, _, hm⟩
    exact ih (Function.update environment counter (index + 1)) hstatic op hm

theorem original_buildProgram_no_children (N q t : Nat) (op : Op)
    (hm : op ∈ PA17TableBuild005.buildProgram N q t) : plainReadsChildren op = false := by
  have hmem : op ∈ fullBuild.eval (dimensionROM N q t) (fun _ => 0) := by
    rw [fullBuild_eval]
    exact hm
  exact program_eval_no_children fullBuild _ _ fullBuild_no_children op hmem

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
