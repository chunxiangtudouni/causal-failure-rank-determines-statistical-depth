module

public import PaperProofs.Structure.PA17_UniformGenerator_035s
public import PaperProofs.Structure.PA17_UniformGenerator_035t
public import PaperProofs.Structure.PA17_UniformGenerator_035q

/-! Whole measured-code-block prefix certificate. The bound on every
template expression is a syntax/lexical contract; actual body safety,
measurement and patching are derived, not supplied as a run oracle. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035v

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035d
  PA17UniformGenerator035e PA17UniformGenerator035f PA17UniformGenerator035j PA17UniformGenerator035k
  PA17UniformGenerator035l PA17UniformGenerator035m PA17UniformGenerator035o PA17UniformGenerator035q
  PA17UniformGenerator035s

theorem wrapperHead_environment (rom : PhysicalROM) (stack cursor saved outputBase : Nat)
    (scope : Finset Nat) (environment : Nat → Nat) (state : NatState) (old : List Nat)
    (hsb : ScopeBelow stack scope) (hc : cursor < stack) (hsaved : saved < stack) (hne : cursor ≠ saved)
    (hnot : cursor ∉ scope) (hbase : stack + 1 ≤ outputBase)
    (he : EnvRep scope environment state.heap) (hs : StreamRep cursor outputBase old state.heap) :
    EnvRep (insert saved scope) (Function.update environment saved old.length)
      (runOps rom (wrapperHead stack cursor saved outputBase) state).heap ∧
    StreamRep cursor outputBase (old ++ [0]) (runOps rom (wrapperHead stack cursor saved outputBase) state).heap := by
  let snap := runOps rom (snapshot cursor saved) state
  have henv : EnvRep (insert saved scope) (Function.update environment saved old.length) snap.heap := by
    intro address hm
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
  rw [PA17UniformGenerator035k.wrapperHead, runOps_append]
  exact ⟨emitWord_env (.constant 0) rom stack cursor outputBase (by trivial) hc hbase
      (insert saved scope) hscopeBelow hcursorNot _ snap henv,
    emitWord_stream (.constant 0) rom stack cursor outputBase (by trivial) hc hbase old snap hsnap⟩

theorem block_safe (template : Template) (rom : PhysicalROM) (B heapWords stack cursor saved outputBase : Nat)
    (scope : Finset Nat) (environment : Nat → Nat)
    (hscope : template.WellScoped (insert saved scope)) (hbelow : template.Below stack)
    (hfits : template.StackFits stack outputBase) (havoid : CountersAvoid cursor template)
    (hsb : ScopeBelow stack scope) (hc : cursor < stack) (hsaved : saved < stack) (hne : cursor ≠ saved)
    (hnot : cursor ∉ scope) (hbase : stack + 1 ≤ outputBase)
    (left right : List PackingOp) (state : NatState) (old : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (he : EnvRep scope environment state.heap) (hs : StreamRep cursor outputBase old state.heap)
    (hchecked : TemplateChecked rom B heapWords (Function.update environment saved old.length) template)
    (hpcB : 5 * (left ++ block template stack cursor saved outputBase left.length ++ right).length ≤ B)
    (houtputB : outputBase + old.length + (template.denote rom (Function.update environment saved old.length)).length + 2 ≤ B)
    (houtputH : outputBase + old.length + (template.denote rom (Function.update environment saved old.length)).length + 2 ≤ heapWords) :
    RunSafe B heapWords rom (left ++ block template stack cursor saved outputBase left.length ++ right)
      (measuredClock template rom environment stack saved old.length) state := by
  let pre := wrapperHead stack cursor saved outputBase
  let body := template.compile stack cursor outputBase (left.length + 13)
  let tail := patch cursor saved outputBase
  let allCode := left ++ pre ++ body ++ tail ++ right
  let prepared := runOps rom pre state
  let updated := Function.update environment saved old.length
  change outputBase + old.length + (template.denote rom updated).length + 2 ≤ B at houtputB
  change outputBase + old.length + (template.denote rom updated).length + 2 ≤ heapWords at houtputH
  have hcode : left ++ block template stack cursor saved outputBase left.length ++ right = allCode := by
    simp only [block, allCode, pre, body, tail, List.append_assoc]
  have hAllPc : 5 * allCode.length ≤ B := by rw [← hcode]; exact hpcB
  have hcount : state.heap cursor = old.length := hs.1
  have hhead := wrapperHead_numeric rom B heapWords stack cursor saved outputBase (by omega) (by omega)
    hc (by omega) (by omega) (by omega) hne (by omega) state hr (by omega) (by omega) (by omega)
  have hheadSafe : RunSafe B heapWords rom allCode 13 state := by
    have hh := straight_segment_safe rom B heapWords left pre (body ++ tail ++ right)
      (prefix_noJump stack cursor saved outputBase) state hpc ha hhead
    simpa only [allCode, pre, prefix_length, List.append_assoc] using hh
  have hpreRun : natRun rom allCode 13 state = prepared := by
    have hh := straight_prefix_run rom left pre (body ++ tail ++ right) (prefix_noJump stack cursor saved outputBase)
      state hpc ha 13 (by rw [prefix_length])
    simpa only [allCode, List.append_assoc, pre, ← prefix_length stack cursor saved outputBase, List.take_length] using hh
  have hheadEnv := wrapperHead_environment rom stack cursor saved outputBase scope environment state old hsb hc hsaved hne hnot hbase he hs
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
  have hppc : prepared.pc = 5 * (left.length + 13) := by
    rw [runOps_pc rom pre state (prefix_noJump stack cursor saved outputBase), hpc, prefix_length]
    omega
  have hpactive : prepared.halted = false := (runOps_halted rom pre state).trans ha
  have hpreg : RegistersLE B prepared := by
    have hh := (hheadSafe.final _ _ _ _ _).1
    rw [hpreRun] at hh
    exact hh
  let done := natRun rom allCode (clock rom updated stack template) prepared
  have hbodySafe := compiled_safe template rom B heapWords stack cursor outputBase (insert saved scope) updated
    hscope hbelow hfits havoid hscopeBelow hc hcursorNot (by omega) hchecked
    (left ++ pre) (tail ++ right) prepared (old ++ [0])
    (by simpa only [List.length_append, pre, prefix_length] using hppc) hpactive hpreg hheadEnv.1 hheadEnv.2
    (by simpa only [allCode, body, List.length_append, pre, prefix_length, List.append_assoc] using hAllPc)
    (by simp only [List.length_append, List.length_singleton]; omega)
    (by simp only [List.length_append, List.length_singleton]; omega)
  have hbodySafe' : RunSafe B heapWords rom allCode (clock rom updated stack template) prepared := by
    simpa only [allCode, body, List.length_append, pre, prefix_length, List.append_assoc] using hbodySafe
  have hbodyResult := compiled_semantics template rom stack cursor outputBase (insert saved scope) updated
    hscope hbelow hfits havoid hscopeBelow hc hcursorNot (by omega) (left ++ pre) (tail ++ right) prepared (old ++ [0])
    (by simpa only [List.length_append, pre, prefix_length] using hppc) hpactive hheadEnv.1 hheadEnv.2
  have hresult : Result (insert saved scope) updated cursor outputBase ((old ++ [0]) ++ template.denote rom updated)
      (5 * (left.length + 13 + template.codeLength stack)) done := by
    simpa only [done, allCode, body, List.length_append, pre, prefix_length, List.append_assoc] using hbodyResult
  have hdcount : done.heap cursor = old.length + (template.denote rom updated).length + 1 := by
    have hh := hresult.2.2.2.1
    simp only [List.length_append, List.length_singleton] at hh
    omega
  have hdsaved : done.heap saved = old.length := by
    have hh := hresult.2.2.1 saved (Finset.mem_insert_self _ _)
    simpa only [updated, Function.update_self] using hh
  have hpatch := patch_numeric rom B heapWords cursor saved outputBase (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) done (hbodySafe'.final _ _ _ _ _).1
    (by rw [hdcount]; exact by omega) (by rw [hdsaved]; omega) (by rw [hdsaved]; omega) (by rw [hdsaved]; omega)
  have htailSafe : RunSafe B heapWords rom allCode 10 done := by
    have hh := straight_segment_safe rom B heapWords (left ++ pre ++ body) tail right (patch_noJump cursor saved outputBase)
      done (by simpa only [List.length_append, pre, prefix_length, body, Template.compile_length] using hresult.1) hresult.2.1 hpatch
    simpa only [allCode, tail, patch_length] using hh
  have hfirstRun : natRun rom allCode (13 + clock rom updated stack template) state = done := by
    rw [natRun_add, hpreRun]
  have hfirst := RunSafe.add _ _ _ _ _ _ state hheadSafe (by rw [hpreRun]; exact hbodySafe')
  rw [hcode, measuredClock]
  exact RunSafe.add _ _ _ _ _ _ state hfirst (by rw [hfirstRun]; exact htailSafe)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035v
