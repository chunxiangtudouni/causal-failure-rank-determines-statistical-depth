module

public import PaperProofs.Structure.PA17_UniformGenerator_035v

/-! A single finite sequence of real measured code blocks. Runtime snapshot
lengths are computed by stores/loads in each block, not supplied in ROM. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ac

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035d
  PA17UniformGenerator035e PA17UniformGenerator035f PA17UniformGenerator035j PA17UniformGenerator035k
  PA17UniformGenerator035m PA17UniformGenerator035o PA17UniformGenerator035t PA17UniformGenerator035v

def streams (stack cursor saved outputBase start : Nat) : List Template → List PackingOp
  | [] => []
  | first :: later =>
      let code := block first stack cursor saved outputBase start
      code ++ streams stack cursor saved outputBase (start + code.length) later

def streamLength (stack : Nat) : List Template → Nat
  | [] => 0
  | first :: later => first.codeLength stack + 23 + streamLength stack later

theorem streams_length (templates : List Template) (stack cursor saved outputBase start : Nat) :
    (streams stack cursor saved outputBase start templates).length = streamLength stack templates := by
  induction templates generalizing start with
  | nil => rfl
  | cons first later ih => simp only [streams, streamLength, List.length_append, block_length, ih]

def streamWords (rom : PhysicalROM) (environment : Nat → Nat) (saved count : Nat) : List Template → List Nat
  | [] => []
  | first :: later =>
      let code := first.denote rom (Function.update environment saved count)
      code.length :: (code ++ streamWords rom environment saved (count + code.length + 1) later)

def streamClock (rom : PhysicalROM) (environment : Nat → Nat) (stack saved count : Nat) : List Template → Nat
  | [] => 0
  | first :: later =>
      let code := first.denote rom (Function.update environment saved count)
      measuredClock first rom environment stack saved count + streamClock rom environment stack saved (count + code.length + 1) later

def StreamsChecked (rom : PhysicalROM) (B heapWords : Nat) (environment : Nat → Nat) (saved count : Nat) : List Template → Prop
  | [] => True
  | first :: later =>
      let updated := Function.update environment saved count
      TemplateChecked rom B heapWords updated first ∧
        StreamsChecked rom B heapWords environment saved (count + (first.denote rom updated).length + 1) later

theorem streams_semantics_safe (templates : List Template) (rom : PhysicalROM) (B heapWords stack cursor saved outputBase : Nat)
    (scope : Finset Nat) (environment : Nat → Nat)
    (hscope : ∀ template ∈ templates, template.WellScoped (insert saved scope))
    (hbelow : ∀ template ∈ templates, template.Below stack)
    (hfits : ∀ template ∈ templates, template.StackFits stack outputBase)
    (havoid : ∀ template ∈ templates, CountersAvoid cursor template)
    (hsb : ScopeBelow stack scope) (hc : cursor < stack) (hsaved : saved < stack) (hne : cursor ≠ saved)
    (hnot : cursor ∉ scope) (hsavedNot : saved ∉ scope) (hbase : stack + 1 ≤ outputBase)
    (left right : List PackingOp) (state : NatState) (old : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (he : EnvRep scope environment state.heap) (hs : StreamRep cursor outputBase old state.heap)
    (hchecked : StreamsChecked rom B heapWords environment saved old.length templates)
    (hpcB : 5 * (left ++ streams stack cursor saved outputBase left.length templates ++ right).length ≤ B)
    (houtputB : outputBase + old.length + (streamWords rom environment saved old.length templates).length + 1 ≤ B)
    (houtputH : outputBase + old.length + (streamWords rom environment saved old.length templates).length + 1 ≤ heapWords) :
    let fresh := natRun rom (left ++ streams stack cursor saved outputBase left.length templates ++ right)
      (streamClock rom environment stack saved old.length templates) state
    Result scope environment cursor outputBase (old ++ streamWords rom environment saved old.length templates)
      (5 * (left.length + streamLength stack templates)) fresh ∧
      RunSafe B heapWords rom (left ++ streams stack cursor saved outputBase left.length templates ++ right)
        (streamClock rom environment stack saved old.length templates) state := by
  induction templates generalizing left state old with
  | nil =>
    change Result scope environment cursor outputBase (old ++ []) (5 * (left.length + 0)) state ∧
      RunSafe B heapWords rom (left ++ [] ++ right) 0 state
    refine ⟨⟨by simpa only [Nat.add_zero] using hpc, ha, he,
      by simpa only [List.append_nil] using hs⟩, ?_⟩
    constructor
    · intro count hn
      change count ≤ 0 at hn
      have hz : count = 0 := by omega
      subst count
      exact ⟨hr, ha, left.length, by simp only [List.length_append]; omega, hpc⟩
    · intro count hn
      change count < 0 at hn
      omega
  | cons first later ih =>
    let firstCode := block first stack cursor saved outputBase left.length
    let laterCode := streams stack cursor saved outputBase (left.length + firstCode.length) later
    let allCode := left ++ firstCode ++ laterCode ++ right
    let code := first.denote rom (Function.update environment saved old.length)
    let done := natRun rom allCode (measuredClock first rom environment stack saved old.length) state
    have hcode : left ++ streams stack cursor saved outputBase left.length (first :: later) ++ right = allCode := by
      simp only [streams, allCode, firstCode, laterCode, List.append_assoc]
    have hAllPc : 5 * allCode.length ≤ B := by rw [← hcode]; exact hpcB
    have hfirstB : outputBase + old.length + code.length + 2 ≤ B := by
      simp only [streamWords, List.length_cons, List.length_append] at houtputB
      dsimp only [code]
      omega
    have hfirstH : outputBase + old.length + code.length + 2 ≤ heapWords := by
      simp only [streamWords, List.length_cons, List.length_append] at houtputH
      dsimp only [code]
      omega
    have hfirst := block_semantics_preserves first rom stack cursor saved outputBase scope environment
      (hscope first List.mem_cons_self) (hbelow first List.mem_cons_self) (hfits first List.mem_cons_self) (havoid first List.mem_cons_self)
      hsb hc hsaved hne hnot hbase left (laterCode ++ right) state old hpc ha he hs
    have hfirst' : done.pc = 5 * (left.length + first.codeLength stack + 23) ∧ done.halted = false ∧
        EnvRep (insert saved scope) (Function.update environment saved old.length) done.heap ∧
        StreamRep cursor outputBase (old ++ code.length :: code) done.heap := by
      simpa only [done, allCode, firstCode, code, List.append_assoc] using hfirst
    have hfirstSafe := block_safe first rom B heapWords stack cursor saved outputBase scope environment
      (hscope first List.mem_cons_self) (hbelow first List.mem_cons_self) (hfits first List.mem_cons_self) (havoid first List.mem_cons_self)
      hsb hc hsaved hne hnot hbase left (laterCode ++ right) state old hpc ha hr he hs hchecked.1
      (by simpa only [allCode, firstCode, List.append_assoc] using hAllPc) hfirstB hfirstH
    have hfirstSafe' : RunSafe B heapWords rom allCode (measuredClock first rom environment stack saved old.length) state := by
      simpa only [allCode, firstCode, List.append_assoc] using hfirstSafe
    have henv : EnvRep scope environment done.heap := env_drop scope environment done.heap saved old.length hsavedNot hfirst'.2.2.1
    have hlen : (old ++ code.length :: code).length = old.length + code.length + 1 := by simp; omega
    have hremaining := ih (fun template hm => hscope template (List.mem_cons_of_mem _ hm))
      (fun template hm => hbelow template (List.mem_cons_of_mem _ hm)) (fun template hm => hfits template (List.mem_cons_of_mem _ hm))
      (fun template hm => havoid template (List.mem_cons_of_mem _ hm)) (left ++ firstCode) done (old ++ code.length :: code)
      (by simpa only [List.length_append, firstCode, block_length, Nat.add_assoc] using hfirst'.1)
      hfirst'.2.1 (hfirstSafe'.final _ _ _ _ _).1 henv hfirst'.2.2.2
      (by simpa only [hlen, code] using hchecked.2)
      (by simpa only [allCode, laterCode, firstCode, List.length_append] using hAllPc)
      (by simpa only [streamWords, List.length_cons, List.length_append, hlen, code, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using houtputB)
      (by simpa only [streamWords, List.length_cons, List.length_append, hlen, code, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using houtputH)
    have hremaining' : Result scope environment cursor outputBase
        ((old ++ code.length :: code) ++ streamWords rom environment saved (old.length + code.length + 1) later)
        (5 * (left.length + first.codeLength stack + 23 + streamLength stack later))
        (natRun rom allCode (streamClock rom environment stack saved (old.length + code.length + 1) later) done) ∧
        RunSafe B heapWords rom allCode (streamClock rom environment stack saved (old.length + code.length + 1) later) done := by
      simpa only [allCode, laterCode, firstCode, List.length_append, block_length, List.append_assoc, Nat.add_assoc, hlen] using hremaining
    rw [hcode, streamClock]
    rw [natRun_add]
    refine ⟨?_, RunSafe.add _ _ _ _ _ _ state hfirstSafe' hremaining'.2⟩
    simpa only [streamWords, code, streamLength, done, List.append_assoc, List.singleton_append, List.cons_append, Nat.add_assoc]
      using hremaining'.1

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ac
