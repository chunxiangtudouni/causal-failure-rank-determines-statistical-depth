module

public import PaperProofs.Structure.PA17_UniformGenerator_035e

/-! Fetched template execution with lexical heap environments and real
stream output. The induction uses actual loop segments and explicit clocks. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035f

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e

def Result (scope : Finset Nat) (environment : Nat → Nat) (cursor outputBase : Nat)
    (words : List Nat) (pc : Nat) (state : NatState) : Prop :=
  state.pc = pc ∧ state.halted = false ∧ EnvRep scope environment state.heap ∧ StreamRep cursor outputBase words state.heap

theorem env_drop (scope : Finset Nat) (environment heap : Nat → Nat) (counter value : Nat)
    (hc : counter ∉ scope) (he : EnvRep (insert counter scope) (Function.update environment counter value) heap) :
    EnvRep scope environment heap := by
  intro address ha
  rw [he address (Finset.mem_insert_of_mem ha), Function.update_of_ne (by intro hz; subst address; exact hc ha)]

theorem tail_env (rom : PhysicalROM) (counter entry : Nat) (scope : Finset Nat)
    (hc : counter ∉ scope) (environment : Nat → Nat) (state : NatState) (he : EnvRep scope environment state.heap) :
    EnvRep scope environment (runOps rom (loopTail counter entry) state).heap := by
  intro address ha
  rw [tail_heap, Function.update_of_ne (by intro hz; subst address; exact hc ha)]
  exact he address ha

theorem tail_stream (rom : PhysicalROM) (counter entry cursor outputBase : Nat)
    (hc : counter < outputBase) (hne : cursor ≠ counter) (words : List Nat) (state : NatState)
    (hs : StreamRep cursor outputBase words state.heap) :
    StreamRep cursor outputBase words (runOps rom (loopTail counter entry) state).heap := by
  constructor
  · rw [tail_heap, Function.update_of_ne hne]
    exact hs.1
  · intro position hp
    rw [tail_heap, Function.update_of_ne (show outputBase + position ≠ counter by omega)]
    exact hs.2 position hp

theorem loop_stream_run (rom : PhysicalROM) (left bodyCode right : List PackingOp)
    (counter cursor outputBase stack : Nat) (scope : Finset Nat) (environment : Nat → Nat)
    (body : Template) (hcounter : counter < outputBase) (hc : counter ∉ scope) (hne : cursor ≠ counter)
    (hbody : ∀ (count : Nat) (state : NatState) (words : List Nat),
      state.pc = 5 * (left.length + 4) → state.halted = false →
      EnvRep scope environment state.heap → state.heap counter = count → StreamRep cursor outputBase words state.heap →
      Result (insert counter scope) (Function.update environment counter count) cursor outputBase
        (words ++ body.denote rom (Function.update environment counter count)) (5 * (left.length + 4 + bodyCode.length))
        (natRun rom (left ++ loopBlock counter left.length bodyCode ++ right)
          (clock rom (Function.update environment counter count) stack body) state))
    (count : Nat) (state : NatState) (words : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (he : EnvRep scope environment state.heap) (hn : state.heap counter = count)
    (hs : StreamRep cursor outputBase words state.heap) :
    Result scope environment cursor outputBase (words ++ loopWords rom environment counter body count)
      (5 * (left.length + bodyCode.length + 12))
      (natRun rom (left ++ loopBlock counter left.length bodyCode ++ right)
        (loopClock rom environment stack counter body count) state) := by
  induction count generalizing state words with
  | zero =>
    rw [loopClock_zero, head_run rom left bodyCode right counter state hpc ha]
    refine ⟨?_, (runOps_halted rom _ state).trans ha, he, ?_⟩
    · rw [head_pc, hn, ite_eq_left rfl]
    · simpa only [loopWords_zero, List.append_nil, head_heap] using hs
  | succ count ih =>
    let tested := runOps rom (loopHead counter (5 * (left.length + bodyCode.length + 12))) state
    have htpc : tested.pc = 5 * (left.length + 4) := by
      rw [head_pc, ite_eq_right (show state.heap counter ≠ 0 by omega), hpc]
      omega
    have htactive : tested.halted = false := (runOps_halted rom _ state).trans ha
    let done := natRun rom (left ++ loopBlock counter left.length bodyCode ++ right)
      (clock rom (Function.update environment counter (count + 1)) stack body) tested
    have hd : Result (insert counter scope) (Function.update environment counter (count + 1)) cursor outputBase
        (words ++ body.denote rom (Function.update environment counter (count + 1)))
        (5 * (left.length + 4 + bodyCode.length)) done := hbody (count + 1) tested words htpc htactive he hn hs
    let latched := runOps rom (loopTail counter (5 * left.length)) done
    have hlpc : latched.pc = 5 * left.length := tail_pc _ _ _ _
    have hlactive : latched.halted = false := (runOps_halted rom _ done).trans hd.2.1
    have hdcount : done.heap counter = count + 1 := by
      have hh := hd.2.2.1 counter (Finset.mem_insert_self _ _)
      simpa only [Function.update_self] using hh
    have hlcount : latched.heap counter = count := by rw [tail_heap, Function.update_self, hdcount]; omega
    have hlenv : EnvRep scope environment latched.heap := tail_env rom counter _ scope hc environment done
      (env_drop scope environment done.heap counter (count + 1) hc hd.2.2.1)
    have hlstream := tail_stream rom counter (5 * left.length) cursor outputBase hcounter hne _ done hd.2.2.2
    have hr := ih latched (words ++ body.denote rom (Function.update environment counter (count + 1)))
      hlpc hlactive hlenv hlcount hlstream
    have hrun : natRun rom (left ++ loopBlock counter left.length bodyCode ++ right)
        (loopClock rom environment stack counter body (count + 1)) state =
        natRun rom (left ++ loopBlock counter left.length bodyCode ++ right)
          (loopClock rom environment stack counter body count) latched := by
      rw [loopClock_succ, natRun_add, natRun_add, natRun_add, head_run rom left bodyCode right counter state hpc ha,
        tail_run rom left bodyCode right counter done hd.1 hd.2.1]
    rw [hrun]
    simpa only [loopWords_succ, List.append_assoc] using hr

theorem compiled_semantics (template : Template) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (scope : Finset Nat) (environment : Nat → Nat)
    (hscope : template.WellScoped scope) (hbelow : template.Below stack)
    (hfits : template.StackFits stack outputBase) (havoid : CountersAvoid cursor template)
    (hsb : ScopeBelow stack scope) (hc : cursor < stack) (hnot : cursor ∉ scope) (hbase : stack ≤ outputBase)
    (left right : List PackingOp) (state : NatState) (words : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (he : EnvRep scope environment state.heap) (hs : StreamRep cursor outputBase words state.heap) :
    Result scope environment cursor outputBase (words ++ template.denote rom environment)
      (5 * (left.length + template.codeLength stack))
      (natRun rom (left ++ template.compile stack cursor outputBase left.length ++ right)
        (clock rom environment stack template) state) := by
  induction template generalizing scope environment left right state words with
  | empty =>
    change Result scope environment cursor outputBase (words ++ []) (5 * (left.length + 0)) state
    exact ⟨by simpa only [Nat.add_zero] using hpc, ha, he,
      by simpa only [List.append_nil] using hs⟩
  | word expression =>
    change Result scope environment cursor outputBase (words ++ [expression.eval rom environment])
      (5 * (left.length + ((expression.compile stack).length + 8)))
      (natRun rom (left ++ emitWord expression stack cursor outputBase ++ right)
        ((expression.compile stack).length + 8) state)
    rw [← emitWord_length expression stack cursor outputBase, emitWord_segment_run expression rom stack cursor outputBase left right state hpc ha]
    refine ⟨?_, (runOps_halted rom _ state).trans ha,
      emitWord_env expression rom stack cursor outputBase hbelow hc hfits scope hsb hnot environment state he, ?_⟩
    · rw [runOps_pc rom _ state (emitWord_noJump expression stack cursor outputBase), hpc]
      omega
    · have hh := emitWord_stream expression rom stack cursor outputBase hbelow hc hfits words state hs
      simpa only [Expr.eval_cells_congr expression rom scope hscope environment state.heap he] using hh
  | append first later ihl ihr =>
    let firstCode := first.compile stack cursor outputBase left.length
    let laterCode := later.compile stack cursor outputBase (left.length + first.codeLength stack)
    let allCode := left ++ firstCode ++ laterCode ++ right
    let fresh := natRun rom allCode (clock rom environment stack first) state
    have hfirst := ihl scope environment hscope.1 hbelow.1 hfits.1 havoid.1 hsb hnot
      left (laterCode ++ right) state words hpc ha he hs
    have hfirst' : Result scope environment cursor outputBase (words ++ first.denote rom environment)
        (5 * (left.length + first.codeLength stack)) fresh := by
      simpa only [fresh, allCode, firstCode, List.append_assoc] using hfirst
    have hsecond := ihr scope environment hscope.2 hbelow.2 hfits.2 havoid.2 hsb hnot
      (left ++ firstCode) right fresh (words ++ first.denote rom environment)
      (by simpa only [List.length_append, firstCode, Template.compile_length] using hfirst'.1)
      hfirst'.2.1 hfirst'.2.2.1 hfirst'.2.2.2
    have hsecond' : Result scope environment cursor outputBase
        ((words ++ first.denote rom environment) ++ later.denote rom environment)
        (5 * ((left.length + first.codeLength stack) + later.codeLength stack))
        (natRun rom allCode (clock rom environment stack later) fresh) := by
      simpa only [allCode, laterCode, firstCode, List.length_append, Template.compile_length, List.append_assoc] using hsecond
    have hcode : left ++ (Template.append first later).compile stack cursor outputBase left.length ++ right = allCode := by
      simp only [Template.compile, allCode, firstCode, laterCode, List.append_assoc]
    rw [hcode]
    change Result scope environment cursor outputBase (words ++ (first.denote rom environment ++ later.denote rom environment))
      (5 * (left.length + (first.codeLength stack + later.codeLength stack)))
      (natRun rom allCode (clock rom environment stack first + clock rom environment stack later) state)
    rw [natRun_add]
    simpa only [List.append_assoc, Nat.add_assoc] using hsecond'
  | «repeat» counter bound body ih =>
    let pre := PA17UniformGenerator035d.bind bound stack counter
    let prepared := runOps rom pre state
    let lead := left ++ pre
    let bodyCode := body.compile stack cursor outputBase (lead.length + 4)
    let allCode := lead ++ loopBlock counter lead.length bodyCode ++ right
    let count := bound.eval rom environment
    have hpframe := bind_env bound rom stack counter hbelow.2.1 scope hsb hscope.1 environment state he
    have hpstream := bind_stream bound rom stack counter cursor outputBase hbelow.2.1 hbelow.1 hc
      (Ne.symm havoid.1) hfits.1 words state hs
    have hpcount : prepared.heap counter = count := by
      rw [bind_target bound rom stack counter hbelow.2.1 state]
      exact Expr.eval_cells_congr bound rom scope hscope.2.1 environment state.heap he
    have hppc : prepared.pc = 5 * lead.length := by
      rw [runOps_pc rom pre state (bind_noJump bound stack counter), hpc]
      simp only [lead, List.length_append]
      omega
    have hpactive : prepared.halted = false := (runOps_halted rom pre state).trans ha
    have hbody : ∀ (n : Nat) (before : NatState) (prior : List Nat),
        before.pc = 5 * (lead.length + 4) → before.halted = false → EnvRep scope environment before.heap →
        before.heap counter = n → StreamRep cursor outputBase prior before.heap →
        Result (insert counter scope) (Function.update environment counter n) cursor outputBase
          (prior ++ body.denote rom (Function.update environment counter n))
          (5 * (lead.length + 4 + bodyCode.length))
          (natRun rom allCode (clock rom (Function.update environment counter n) stack body) before) := by
      intro n before prior hbpc hbactive hbenv hbcount hbstream
      let head := loopHead counter (5 * (lead.length + bodyCode.length + 12))
      let leftBody := lead ++ head
      let rightBody := loopTail counter (5 * lead.length) ++ right
      have hh : head.length = 4 := rfl
      have henv : EnvRep (insert counter scope) (Function.update environment counter n) before.heap := by
        intro address haddr
        by_cases hz : address = counter
        · subst address
          simpa only [Function.update_self] using hbcount
        · rw [Function.update_of_ne hz]
          exact hbenv address ((Finset.mem_insert.mp haddr).resolve_left hz)
      have hbbelow : ScopeBelow stack (insert counter scope) := by
        intro address haddr
        rcases Finset.mem_insert.mp haddr with hz | hm
        · simpa only [hz] using hbelow.1
        · exact hsb address hm
      have hbnot : cursor ∉ insert counter scope := by
        intro hm
        rcases Finset.mem_insert.mp hm with hz | hm
        · exact havoid.1 hz.symm
        · exact hnot hm
      have hi := ih (insert counter scope) (Function.update environment counter n) hscope.2.2
        hbelow.2.2 hfits.2 havoid.2 hbbelow hbnot leftBody rightBody before prior
        (by simpa only [leftBody, List.length_append, hh] using hbpc) hbactive henv hbstream
      have hcode : leftBody ++ body.compile stack cursor outputBase leftBody.length ++ rightBody = allCode := by
        simp only [leftBody, rightBody, allCode, loopBlock, bodyCode, List.length_append, hh, head, List.append_assoc]
      rw [hcode] at hi
      simpa only [leftBody, List.length_append, hh, bodyCode, Template.compile_length] using hi
    have hloop := loop_stream_run rom lead bodyCode right counter cursor outputBase stack scope environment body
      (lt_of_lt_of_le hbelow.1 hbase) hscope.1 (Ne.symm havoid.1) hbody count prepared words hppc hpactive hpframe hpcount hpstream
    have hpreRun : natRun rom allCode pre.length state = prepared := by
      have hp := natRun_of_straight_segment rom
        (left ++ pre ++ (loopBlock counter lead.length bodyCode ++ right)) pre left.length
        (by simp only [List.length_append]; omega)
        (segment_index left pre (loopBlock counter lead.length bodyCode ++ right))
        (bind_noJump bound stack counter) state hpc ha
      simpa only [allCode, lead, List.append_assoc] using hp
    have hcode : left ++ (Template.repeat counter bound body).compile stack cursor outputBase left.length ++ right = allCode := by
      simp only [Template.compile, allCode, lead, pre, List.length_append, bodyCode, List.append_assoc]
    have hclock : clock rom environment stack (Template.repeat counter bound body) =
        pre.length + loopClock rom environment stack counter body count := by
      simp only [clock, loopClock, pre, bind_length, count]
      omega
    rw [hcode, hclock, natRun_add, hpreRun]
    simpa only [Template.denote, loopWords, count, Template.codeLength, allCode, lead, List.length_append,
      bodyCode, Template.compile_length, pre, bind_length, Nat.add_assoc] using hloop

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035f
