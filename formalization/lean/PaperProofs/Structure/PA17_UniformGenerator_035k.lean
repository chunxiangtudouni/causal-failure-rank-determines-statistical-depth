module

public import PaperProofs.Structure.PA17_UniformGenerator_035f

/-! Real length-wrapperHead measurement: save the current cursor, emit a zero
placeholder, execute the finite code template, and patch its measured size.
No closed-form generated-length answer is required by this runtime code. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035k

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035f

def snapshot (cursor saved : Nat) : List PackingOp :=
  [.base (.base (.constant .index cursor)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .index saved)), .base (.base (.storeHeap .index .value))]

def patch (cursor saved outputBase : Nat) : List PackingOp :=
  [.base (.base (.constant .index cursor)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .index saved)), .base (.base (.loadHeap .old .index)),
   .base (.base (.constant .fresh 1)), .base (.subtract .value .total .old),
   .base (.subtract .value .value .fresh), .base (.base (.constant .index outputBase)),
   .base (.base (.add .index .index .old)), .base (.base (.storeHeap .index .value))]

def wrapperHead (stack cursor saved outputBase : Nat) : List PackingOp :=
  snapshot cursor saved ++ emitWord (.constant 0) stack cursor outputBase

def block (template : Template) (stack cursor saved outputBase start : Nat) : List PackingOp :=
  wrapperHead stack cursor saved outputBase ++
    template.compile stack cursor outputBase (start + 13) ++ patch cursor saved outputBase

def measuredClock (template : Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (stack saved count : Nat) : Nat :=
  13 + clock rom (Function.update environment saved count) stack template + 10

theorem snapshot_heap (rom : PhysicalROM) (cursor saved : Nat) (state : NatState) :
    (runOps rom (snapshot cursor saved) state).heap = Function.update state.heap saved (state.heap cursor) := rfl

theorem patch_heap (rom : PhysicalROM) (cursor saved outputBase : Nat) (state : NatState) :
    (runOps rom (patch cursor saved outputBase) state).heap =
      Function.update state.heap (outputBase + state.heap saved) (state.heap cursor - state.heap saved - 1) := rfl

theorem prefix_noJump (stack cursor saved outputBase : Nat) :
    ∀ op ∈ wrapperHead stack cursor saved outputBase, NoJump op := by
  intro op hm
  rw [wrapperHead, List.mem_append] at hm
  rcases hm with hm | hm
  · have hh : ∀ entry ∈ snapshot cursor saved, NoJump entry := by simp [snapshot, NoJump]
    exact hh op hm
  · exact emitWord_noJump (.constant 0) stack cursor outputBase op hm

theorem patch_noJump (cursor saved outputBase : Nat) : ∀ op ∈ patch cursor saved outputBase, NoJump op := by
  simp [patch, NoJump]

theorem prefix_length (stack cursor saved outputBase : Nat) : (wrapperHead stack cursor saved outputBase).length = 13 := rfl

theorem patch_length (cursor saved outputBase : Nat) : (patch cursor saved outputBase).length = 10 := rfl

theorem block_length (template : Template) (stack cursor saved outputBase start : Nat) :
    (block template stack cursor saved outputBase start).length = template.codeLength stack + 23 := by
  simp only [block, List.length_append, prefix_length, Template.compile_length, patch_length]
  omega

theorem patch_stream (rom : PhysicalROM) (cursor saved outputBase : Nat) (old code : List Nat)
    (state : NatState) (hs : StreamRep cursor outputBase (old ++ 0 :: code) state.heap)
    (hm : state.heap saved = old.length) (hc : cursor < outputBase) :
    StreamRep cursor outputBase (old ++ code.length :: code) (runOps rom (patch cursor saved outputBase) state).heap := by
  have hlength : state.heap cursor = old.length + code.length + 1 := by
    have hh := hs.1
    simpa only [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have hvalue : state.heap cursor - state.heap saved - 1 = code.length := by rw [hlength, hm]; omega
  have hheap : (runOps rom (patch cursor saved outputBase) state).heap =
      Function.update state.heap (outputBase + old.length) code.length := by rw [patch_heap, hvalue, hm]
  constructor
  · rw [hheap, Function.update_of_ne (show cursor ≠ outputBase + old.length by omega), hlength]
    simp only [List.length_append, List.length_cons]
    omega
  · intro position hp
    rw [hheap]
    by_cases hpos : position < old.length
    · rw [Function.update_of_ne (show outputBase + position ≠ outputBase + old.length by omega), List.getElem_append_left hpos]
      exact (hs.2 position (by simp only [List.length_append, List.length_cons]; omega)).trans (List.getElem_append_left hpos)
    · by_cases heq : position = old.length
      · subst position
        simp only [Function.update_self, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      · have hlt : old.length < position := by omega
        rw [Function.update_of_ne (show outputBase + position ≠ outputBase + old.length by omega)]
        have hprior := hs.2 position (by simpa only [List.length_append, List.length_cons] using hp)
        have hpge : old.length ≤ position := by omega
        rw [List.getElem_append_right hpge] at hprior ⊢
        simp only [List.getElem_cons, show position - old.length ≠ 0 by omega, dite_false] at hprior ⊢
        exact hprior

theorem block_semantics (template : Template) (rom : PhysicalROM) (stack cursor saved outputBase : Nat)
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
  refine ⟨?_, (runOps_halted rom tail done).trans hresult'.2.1, ?_⟩
  · rw [runOps_pc rom tail done (patch_noJump cursor saved outputBase), hresult'.1, patch_length]
    omega
  · exact patch_stream rom cursor saved outputBase old (template.denote rom updated) done
      (by simpa only [List.append_assoc, List.singleton_append] using hresult'.2.2.2) hsavedWord (by omega)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035k
