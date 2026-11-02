module

public import PaperProofs.Structure.PA17_UniformGenerator_035r

/-! Whole finite-template prefix certificate. The contract is on the
original finite syntax and actual lexical values; all body-run premises
are eliminated by induction, including arbitrary nested loops. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035s

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035d
  PA17UniformGenerator035e PA17UniformGenerator035f PA17UniformGenerator035j PA17UniformGenerator035l
  PA17UniformGenerator035m PA17UniformGenerator035o PA17UniformGenerator035r

theorem compiled_safe (template : Template) (rom : PhysicalROM) (B heapWords stack cursor outputBase : Nat)
    (scope : Finset Nat) (environment : Nat → Nat)
    (hscope : template.WellScoped scope) (hbelow : template.Below stack)
    (hfits : template.StackFits stack outputBase) (havoid : CountersAvoid cursor template)
    (hsb : ScopeBelow stack scope) (hc : cursor < stack) (hnot : cursor ∉ scope) (hbase : stack ≤ outputBase)
    (hchecked : TemplateChecked rom B heapWords environment template)
    (left right : List PackingOp) (state : NatState) (old : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (he : EnvRep scope environment state.heap) (hs : StreamRep cursor outputBase old state.heap)
    (hpcB : 5 * (left ++ template.compile stack cursor outputBase left.length ++ right).length ≤ B)
    (houtputB : outputBase + (old ++ template.denote rom environment).length + 1 ≤ B)
    (houtputH : outputBase + (old ++ template.denote rom environment).length + 1 ≤ heapWords) :
    RunSafe B heapWords rom (left ++ template.compile stack cursor outputBase left.length ++ right)
      (clock rom environment stack template) state := by
  induction template generalizing scope environment left right state old with
  | empty =>
    constructor
    · intro count hn
      change count ≤ 0 at hn
      have hz : count = 0 := by omega
      subst count
      exact ⟨hr, ha, left.length, by simp only [List.length_append]; omega, hpc⟩
    · intro count hn
      change count < 0 at hn
      omega
  | word expression =>
    have hspace : stack + expression.size ≤ outputBase := hfits
    simp only [Template.denote, List.length_append, List.length_singleton] at houtputB houtputH
    have hvalue := expression_checked_scoped expression rom B heapWords scope hscope environment state.heap he hchecked
    have hcount := hs.1
    have hsafe := emitWord_numeric expression rom B heapWords stack cursor outputBase hbelow
      (by omega) (by omega)
      hc (by omega) (by omega) state hr hvalue
      (by omega)
      (by omega) (by omega)
    have hh := straight_segment_safe rom B heapWords left (emitWord expression stack cursor outputBase) right
      (emitWord_noJump expression stack cursor outputBase) state hpc ha hsafe
    simpa only [Template.compile, clock, emitWord_length] using hh
  | append first later ihl ihr =>
    let firstCode := first.compile stack cursor outputBase left.length
    let laterCode := later.compile stack cursor outputBase (left.length + first.codeLength stack)
    let allCode := left ++ firstCode ++ laterCode ++ right
    let fresh := natRun rom allCode (clock rom environment stack first) state
    have hcode : left ++ (Template.append first later).compile stack cursor outputBase left.length ++ right = allCode := by
      simp only [Template.compile, allCode, firstCode, laterCode, List.append_assoc]
    have hfirst := ihl scope environment hscope.1 hbelow.1 hfits.1 havoid.1 hsb hnot hchecked.1
      left (laterCode ++ right) state old hpc ha hr he hs
      (by simpa only [hcode, allCode, firstCode, List.append_assoc] using hpcB)
      (by simp only [Template.denote, List.length_append] at houtputB; simp only [List.length_append]; omega)
      (by simp only [Template.denote, List.length_append] at houtputH; simp only [List.length_append]; omega)
    have hfirst' : RunSafe B heapWords rom allCode (clock rom environment stack first) state := by
      simpa only [allCode, firstCode, List.append_assoc] using hfirst
    have hsemantic := compiled_semantics first rom stack cursor outputBase scope environment hscope.1 hbelow.1 hfits.1 havoid.1
      hsb hc hnot hbase left (laterCode ++ right) state old hpc ha he hs
    have hresult : Result scope environment cursor outputBase (old ++ first.denote rom environment)
        (5 * (left.length + first.codeLength stack)) fresh := by
      simpa only [fresh, allCode, firstCode, List.append_assoc] using hsemantic
    have hsecond := ihr scope environment hscope.2 hbelow.2 hfits.2 havoid.2 hsb hnot hchecked.2
      (left ++ firstCode) right fresh (old ++ first.denote rom environment)
      (by simpa only [List.length_append, firstCode, Template.compile_length] using hresult.1)
      hresult.2.1 (hfirst'.final _ _ _ _ _).1 hresult.2.2.1 hresult.2.2.2
      (by simpa only [List.length_append, firstCode, Template.compile_length, laterCode, allCode, hcode] using hpcB)
      (by simpa only [Template.denote, List.append_assoc] using houtputB)
      (by simpa only [Template.denote, List.append_assoc] using houtputH)
    have hsecond' : RunSafe B heapWords rom allCode (clock rom environment stack later) fresh := by
      simpa only [allCode, laterCode, firstCode, List.length_append, Template.compile_length, List.append_assoc] using hsecond
    rw [hcode]
    exact RunSafe.add _ _ _ _ _ _ state hfirst' hsecond'
  | «repeat» counter bound body ih =>
    let pre := PA17UniformGenerator035d.bind bound stack counter
    let prepared := runOps rom pre state
    let lead := left ++ pre
    let bodyCode := body.compile stack cursor outputBase (lead.length + 4)
    let allCode := lead ++ loopBlock counter lead.length bodyCode ++ right
    let count := bound.eval rom environment
    have hcounter : counter < stack := hbelow.1
    have hspace : stack + bound.size ≤ outputBase := hfits.1
    have hcB : counter ≤ B := by omega
    have hcH : counter < heapWords := by omega
    have hbound := expression_checked_scoped bound rom B heapWords scope hscope.2.1 environment state.heap he hchecked.1
    have hpre := bind_numeric bound rom B heapWords stack counter hbelow.2.1
      (by omega) (by omega) hcB hcH state hr hbound
    have hcode : left ++ (Template.repeat counter bound body).compile stack cursor outputBase left.length ++ right = allCode := by
      simp only [Template.compile, allCode, lead, pre, bodyCode, List.length_append, List.append_assoc]
    have hAllPc : 5 * allCode.length ≤ B := by rw [← hcode]; exact hpcB
    have hphead : RunSafe B heapWords rom allCode pre.length state := by
      have hh := straight_segment_safe rom B heapWords left pre (loopBlock counter lead.length bodyCode ++ right)
        (bind_noJump bound stack counter) state hpc ha hpre
      simpa only [allCode, lead, List.append_assoc] using hh
    have hpreRun : natRun rom allCode pre.length state = prepared := by
      have hh := natRun_of_straight_segment rom (left ++ pre ++ (loopBlock counter lead.length bodyCode ++ right)) pre left.length
        (by simp only [List.length_append]; omega) (segment_index left pre _) (bind_noJump bound stack counter) state hpc ha
      simpa only [allCode, lead, List.append_assoc] using hh
    have hppc : prepared.pc = 5 * lead.length := by
      rw [runOps_pc rom pre state (bind_noJump bound stack counter), hpc]
      simp only [lead, List.length_append]
      omega
    have hpactive : prepared.halted = false := (runOps_halted rom pre state).trans ha
    have hpreg : RegistersLE B prepared := by
      have hh := (hphead.final _ _ _ _ _).1
      rw [hpreRun] at hh
      exact hh
    have hpcount : prepared.heap counter = count := by
      rw [bind_target bound rom stack counter hbelow.2.1 state]
      exact Expr.eval_cells_congr bound rom scope hscope.2.1 environment state.heap he
    have hpenv := bind_env bound rom stack counter hbelow.2.1 scope hsb hscope.1 environment state he
    have hpstream := bind_stream bound rom stack counter cursor outputBase hbelow.2.1 hbelow.1 hc
      (Ne.symm havoid.1) hfits.1 old state hs
    have hbody : ∀ (n : Nat) (before : NatState) (prior : List Nat), n ≤ count →
        before.pc = 5 * (lead.length + 4) → before.halted = false → RegistersLE B before →
        EnvRep scope environment before.heap → before.heap counter = n → StreamRep cursor outputBase prior before.heap →
        outputBase + (prior ++ body.denote rom (Function.update environment counter n)).length + 1 ≤ B →
        outputBase + (prior ++ body.denote rom (Function.update environment counter n)).length + 1 ≤ heapWords →
        Result (insert counter scope) (Function.update environment counter n) cursor outputBase
          (prior ++ body.denote rom (Function.update environment counter n)) (5 * (lead.length + 4 + bodyCode.length))
          (natRun rom allCode (clock rom (Function.update environment counter n) stack body) before) ∧
        RunSafe B heapWords rom allCode (clock rom (Function.update environment counter n) stack body) before := by
      intro n before prior hn hbpc hba hbreg hbenv hbn hbstream hbB hbH
      let head := loopHead counter (5 * (lead.length + bodyCode.length + 12))
      let leftBody := lead ++ head
      let rightBody := loopTail counter (5 * lead.length) ++ right
      have hh : head.length = 4 := rfl
      have henv : EnvRep (insert counter scope) (Function.update environment counter n) before.heap := by
        intro address hm
        by_cases hz : address = counter
        · subst address; simpa only [Function.update_self] using hbn
        · rw [Function.update_of_ne hz]; exact hbenv address ((Finset.mem_insert.mp hm).resolve_left hz)
      have hbbelow : ScopeBelow stack (insert counter scope) := by
        intro address hm
        rcases Finset.mem_insert.mp hm with hz | hm
        · simpa only [hz] using hbelow.1
        · exact hsb address hm
      have hbnot : cursor ∉ insert counter scope := by
        intro hm
        rcases Finset.mem_insert.mp hm with hz | hm
        · exact havoid.1 hz.symm
        · exact hnot hm
      have hbodyCode : leftBody ++ body.compile stack cursor outputBase leftBody.length ++ rightBody = allCode := by
        simp only [leftBody, rightBody, allCode, loopBlock, bodyCode, List.length_append, hh, head, List.append_assoc]
      have hsem := compiled_semantics body rom stack cursor outputBase (insert counter scope) (Function.update environment counter n)
        hscope.2.2 hbelow.2.2 hfits.2 havoid.2 hbbelow hc hbnot hbase leftBody rightBody before prior
        (by simpa only [leftBody, List.length_append, hh] using hbpc) hba henv hbstream
      have hsafe := ih (insert counter scope) (Function.update environment counter n) hscope.2.2 hbelow.2.2 hfits.2 havoid.2 hbbelow hbnot
        (hchecked.2 n hn) leftBody rightBody before prior
        (by simpa only [leftBody, List.length_append, hh] using hbpc) hba hbreg henv hbstream
        (by rw [hbodyCode]; exact hAllPc) hbB hbH
      rw [hbodyCode] at hsem hsafe
      exact ⟨by simpa only [leftBody, List.length_append, hh, bodyCode, Template.compile_length] using hsem, hsafe⟩
    have hloop := loop_safe rom B heapWords lead bodyCode right counter cursor outputBase stack count scope environment body
      (lt_of_lt_of_le hbelow.1 hbase) hscope.1 (Ne.symm havoid.1) hcB hcH (by omega)
      hAllPc hbody count prepared old hppc hpactive hpreg hpenv hpcount
      (checked_value bound rom environment B heapWords hchecked.1) le_rfl hpstream houtputB houtputH
    have hclock : clock rom environment stack (Template.repeat counter bound body) =
        pre.length + loopClock rom environment stack counter body count := by
      simp only [clock, loopClock, pre, bind_length, count]
      omega
    rw [hcode, hclock]
    exact RunSafe.add _ _ _ _ _ _ state hphead (by rw [hpreRun]; exact hloop)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035s
