module
public import PaperProofs.Structure.PA17_UniformGenerator_035k
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035t
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035f PA17UniformGenerator035k
theorem block_semantics_preserves (template : Template) (rom : PhysicalROM) (stack cursor saved outputBase : Nat)
    (scope : Finset Nat) (environment : Nat → Nat)
    (hscope : template.WellScoped (insert saved scope)) (hbelow : template.Below stack)
    (hfits : template.StackFits stack outputBase) (havoid : CountersAvoid cursor template)
    (hsb : ScopeBelow stack scope) (hc : cursor < stack) (hsaved : saved < stack) (hne : cursor ≠ saved)
    (hnot : cursor ∉ scope) (hbase : stack + 1 ≤ outputBase)
    (left right : List PackingOp) (state : NatState) (old : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (he : EnvRep scope environment state.heap) (hs : StreamRep cursor outputBase old state.heap) :
    let code := template.denote rom (Function.update environment saved old.length)
    let fresh := natRun rom (left ++ block template stack cursor saved outputBase left.length ++ right)
      (measuredClock template rom environment stack saved old.length) state
    fresh.pc = 5 * (left.length + template.codeLength stack + 23) ∧ fresh.halted = false ∧
      EnvRep (insert saved scope) (Function.update environment saved old.length) fresh.heap ∧
      StreamRep cursor outputBase (old ++ code.length :: code) fresh.heap := by
  let pre := wrapperHead stack cursor saved outputBase
  let body := template.compile stack cursor outputBase (left.length + 13)
  let tail := patch cursor saved outputBase
  let allCode := left ++ pre ++ body ++ tail ++ right
  let snap := runOps rom (snapshot cursor saved) state
  let prepared := runOps rom pre state
  let updated := Function.update environment saved old.length
  have henv : EnvRep (insert saved scope) updated snap.heap := by
    intro address hm
    dsimp only [updated]
    rw [snapshot_heap, hs.1]
    by_cases hz : address = saved
    · subst address; simp only [Function.update_self]
    · rw [Function.update_of_ne hz, Function.update_of_ne hz]
      exact he address ((Finset.mem_insert.mp hm).resolve_left hz)
  have hsnap : StreamRep cursor outputBase old snap.heap := by
    constructor
    · rw [snapshot_heap, Function.update_of_ne hne]; exact hs.1
    · intro position hp
      rw [snapshot_heap, Function.update_of_ne (show outputBase + position ≠ saved by omega)]
      exact hs.2 position hp
  have hscopeBelow : ScopeBelow stack (insert saved scope) := by
    intro address hm
    rcases Finset.mem_insert.mp hm with hz | hm
    · simpa only [hz] using hsaved
    · exact hsb address hm
  have hcursorNot : cursor ∉ insert saved scope := by
    intro hm
    rcases Finset.mem_insert.mp hm with hz | hm
    · exact hne hz
    · exact hnot hm
  have hprepHeap : prepared.heap = (runOps rom (emitWord (.constant 0) stack cursor outputBase) snap).heap := by
    change (runOps rom (snapshot cursor saved ++ emitWord (.constant 0) stack cursor outputBase) state).heap = _
    rw [runOps_append]
  have hprepEnv : EnvRep (insert saved scope) updated prepared.heap := by
    rw [hprepHeap]
    exact emitWord_env (.constant 0) rom stack cursor outputBase (by trivial) hc hbase
      (insert saved scope) hscopeBelow hcursorNot updated snap henv
  have hprepStream : StreamRep cursor outputBase (old ++ [0]) prepared.heap := by
    rw [hprepHeap]
    exact emitWord_stream (.constant 0) rom stack cursor outputBase (by trivial) hc hbase old snap hsnap
  have hppc : prepared.pc = 5 * (left.length + 13) := by
    rw [runOps_pc rom pre state (prefix_noJump stack cursor saved outputBase), hpc, prefix_length]
    omega
  have hpactive : prepared.halted = false := (runOps_halted rom pre state).trans ha
  let done := natRun rom allCode (clock rom updated stack template) prepared
  have hresult := compiled_semantics template rom stack cursor outputBase (insert saved scope) updated hscope hbelow hfits havoid
    hscopeBelow hc hcursorNot (by omega) (left ++ pre) (tail ++ right) prepared (old ++ [0])
    (by simpa only [List.length_append, pre, prefix_length] using hppc) hpactive hprepEnv hprepStream
  have hresult' : Result (insert saved scope) updated cursor outputBase
      ((old ++ [0]) ++ template.denote rom updated) (5 * (left.length + 13 + template.codeLength stack)) done := by
    simpa only [done, allCode, body, pre, List.length_append, prefix_length, List.append_assoc] using hresult
  have hsavedWord : done.heap saved = old.length := by
    have hh := hresult'.2.2.1 saved (Finset.mem_insert_self _ _)
    simpa only [updated, Function.update_self] using hh
  have htailRun : natRun rom allCode 10 done = runOps rom tail done := by
    have hh := natRun_of_straight_segment rom ((left ++ pre ++ body) ++ tail ++ right) tail (left ++ pre ++ body).length
      (by simp only [List.length_append]; omega) (segment_index (left ++ pre ++ body) tail right)
      (patch_noJump cursor saved outputBase) done
      (by simpa only [List.length_append, pre, prefix_length, body, Template.compile_length] using hresult'.1) hresult'.2.1
    simpa only [allCode, tail, patch_length] using hh
  have hpreRun : natRun rom allCode 13 state = prepared := by
    have hh := natRun_of_straight_segment rom (left ++ pre ++ (body ++ tail ++ right)) pre left.length
      (by simp only [List.length_append]; omega) (segment_index left pre _) (prefix_noJump stack cursor saved outputBase) state hpc ha
    simpa only [allCode, List.append_assoc, pre, prefix_length] using hh
  have hcode : left ++ block template stack cursor saved outputBase left.length ++ right = allCode := by
    simp only [block, allCode, pre, body, tail, List.append_assoc]
  have hrun : natRun rom allCode (measuredClock template rom environment stack saved old.length) state = runOps rom tail done := by
    rw [measuredClock, natRun_add, natRun_add, hpreRun, htailRun]
  rw [hcode, hrun]
  refine ⟨?_, (runOps_halted rom tail done).trans hresult'.2.1, ?_, ?_⟩
  · rw [runOps_pc rom tail done (patch_noJump cursor saved outputBase), hresult'.1, patch_length]
    omega
  · intro address hm
    have hab : address < stack := hscopeBelow address hm
    rw [patch_heap, Function.update_of_ne (show address ≠ outputBase + done.heap saved by omega)]
    exact hresult'.2.2.1 address hm
  · exact patch_stream rom cursor saved outputBase old (template.denote rom updated) done
      (by simpa only [List.append_assoc, List.singleton_append] using hresult'.2.2.2) hsavedWord (by omega)


end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035t

