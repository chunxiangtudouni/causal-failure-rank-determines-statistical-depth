module

public import PaperProofs.Structure.PA17_UniformGenerator_035m
public import PaperProofs.Structure.PA17_UniformGenerator_035o

/-! Actual whole-loop fetched-prefix safety, with body correctness supplied
only as the induction hypothesis of the finite-template compiler proof. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035r

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035d
  PA17UniformGenerator035e PA17UniformGenerator035f PA17UniformGenerator035j PA17UniformGenerator035l
  PA17UniformGenerator035m PA17UniformGenerator035o

theorem loop_safe (rom : PhysicalROM) (B heapWords : Nat) (left bodyCode right : List PackingOp)
    (counter cursor outputBase stack maximum : Nat) (scope : Finset Nat) (environment : Nat → Nat) (body : Template)
    (hcounter : counter < outputBase) (hc : counter ∉ scope) (hne : cursor ≠ counter)
    (hcounterB : counter ≤ B) (hcounterH : counter < heapWords) (hone : 1 ≤ B)
    (hpcB : 5 * (left ++ loopBlock counter left.length bodyCode ++ right).length ≤ B)
    (hbody : ∀ (n : Nat) (state : NatState) (words : List Nat),
      n ≤ maximum →
      state.pc = 5 * (left.length + 4) → state.halted = false → RegistersLE B state →
      EnvRep scope environment state.heap → state.heap counter = n → StreamRep cursor outputBase words state.heap →
      outputBase + (words ++ body.denote rom (Function.update environment counter n)).length + 1 ≤ B →
      outputBase + (words ++ body.denote rom (Function.update environment counter n)).length + 1 ≤ heapWords →
      Result (insert counter scope) (Function.update environment counter n) cursor outputBase
        (words ++ body.denote rom (Function.update environment counter n)) (5 * (left.length + 4 + bodyCode.length))
        (natRun rom (left ++ loopBlock counter left.length bodyCode ++ right)
          (clock rom (Function.update environment counter n) stack body) state) ∧
      RunSafe B heapWords rom (left ++ loopBlock counter left.length bodyCode ++ right)
        (clock rom (Function.update environment counter n) stack body) state)
    (count : Nat) (state : NatState) (words : List Nat)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (he : EnvRep scope environment state.heap) (hn : state.heap counter = count) (hcount : count ≤ B) (hmax : count ≤ maximum)
    (hs : StreamRep cursor outputBase words state.heap)
    (houtputB : outputBase + (words ++ loopWords rom environment counter body count).length + 1 ≤ B)
    (houtputH : outputBase + (words ++ loopWords rom environment counter body count).length + 1 ≤ heapWords) :
    RunSafe B heapWords rom (left ++ loopBlock counter left.length bodyCode ++ right)
      (loopClock rom environment stack counter body count) state := by
  induction count generalizing state words with
  | zero =>
    rw [loopClock_zero]
    have hshead := loopHead_safe rom B heapWords counter (left.length + bodyCode.length + 12) left
      (bodyCode ++ loopTail counter (5 * left.length) ++ right) hcounterB hcounterH
      (by simp only [List.length_append, loopBlock_length] at hpcB; omega)
      (by simp only [List.length_append]; change left.length + bodyCode.length + 12 ≤ left.length + 4 + (bodyCode.length + 8 + right.length); omega)
      state hpc ha hr (by rw [hn]; omega)
    simpa only [loopBlock, List.append_assoc] using hshead
  | succ count ih =>
    let allCode := left ++ loopBlock counter left.length bodyCode ++ right
    let head := loopHead counter (5 * (left.length + bodyCode.length + 12))
    let tested := runOps rom head state
    have hshead : RunSafe B heapWords rom allCode 4 state := by
      have hh := loopHead_safe rom B heapWords counter (left.length + bodyCode.length + 12) left
        (bodyCode ++ loopTail counter (5 * left.length) ++ right) hcounterB hcounterH
        (by simp only [List.length_append, loopBlock_length] at hpcB; omega)
        (by simp only [List.length_append]; change left.length + bodyCode.length + 12 ≤ left.length + 4 + (bodyCode.length + 8 + right.length); omega)
        state hpc ha hr (by rw [hn]; exact hcount)
      simpa only [allCode, loopBlock, List.append_assoc] using hh
    have hheadRun : natRun rom allCode 4 state = tested := head_run rom left bodyCode right counter state hpc ha
    have htestreg : RegistersLE B tested := by
      have hh := (hshead.final _ _ _ _ _).1
      rw [hheadRun] at hh
      exact hh
    have htpc : tested.pc = 5 * (left.length + 4) := by
      rw [head_pc, ite_eq_right (show state.heap counter ≠ 0 by omega), hpc]
      omega
    have hta : tested.halted = false := (runOps_halted rom head state).trans ha
    have hbodyB : outputBase + (words ++ body.denote rom (Function.update environment counter (count + 1))).length + 1 ≤ B := by
      rw [loopWords_succ] at houtputB
      simp only [List.length_append] at houtputB ⊢
      omega
    have hbodyH : outputBase + (words ++ body.denote rom (Function.update environment counter (count + 1))).length + 1 ≤ heapWords := by
      rw [loopWords_succ] at houtputH
      simp only [List.length_append] at houtputH ⊢
      omega
    have hd := hbody (count + 1) tested words hmax htpc hta htestreg he hn hs hbodyB hbodyH
    let done := natRun rom allCode (clock rom (Function.update environment counter (count + 1)) stack body) tested
    have hdresult : Result (insert counter scope) (Function.update environment counter (count + 1)) cursor outputBase
        (words ++ body.denote rom (Function.update environment counter (count + 1)))
        (5 * (left.length + 4 + bodyCode.length)) done := hd.1
    have hdreg : RegistersLE B done := (hd.2.final _ _ _ _ _).1
    have hdcount : done.heap counter = count + 1 := by
      have hh := hdresult.2.2.1 counter (Finset.mem_insert_self _ _)
      simpa only [Function.update_self] using hh
    let latched := runOps rom (loopTail counter (5 * left.length)) done
    have hstail : RunSafe B heapWords rom allCode 8 done := by
      let lead := left ++ head ++ bodyCode
      have hlead : lead.length = left.length + 4 + bodyCode.length := by simp only [lead, List.length_append]; rfl
      have hh := loopTail_safe rom B heapWords counter left.length lead right hcounterB hcounterH
        (by simp only [List.length_append, loopBlock_length] at hpcB; omega) hone
        (by simp only [List.length_append, hlead]; omega) done
        (by rw [hlead]; exact hdresult.1) hdresult.2.1 hdreg (by rw [hdcount]; exact hcount)
      simpa only [allCode, loopBlock, lead, head, List.append_assoc] using hh
    have htailRun : natRun rom allCode 8 done = latched := tail_run rom left bodyCode right counter done hdresult.1 hdresult.2.1
    have hlpc : latched.pc = 5 * left.length := tail_pc _ _ _ _
    have hla : latched.halted = false := (runOps_halted rom _ done).trans hdresult.2.1
    have hlreg : RegistersLE B latched := by
      have hh := (hstail.final _ _ _ _ _).1
      rw [htailRun] at hh
      exact hh
    have hlenv := tail_env rom counter (5 * left.length) scope hc environment done
      (env_drop scope environment done.heap counter (count + 1) hc hdresult.2.2.1)
    have hln : latched.heap counter = count := by rw [tail_heap, Function.update_self, hdcount]; omega
    have hlstream := tail_stream rom counter (5 * left.length) cursor outputBase hcounter hne _ done hdresult.2.2.2
    have hlB : outputBase + ((words ++ body.denote rom (Function.update environment counter (count + 1))) ++
        loopWords rom environment counter body count).length + 1 ≤ B := by
      simpa only [loopWords_succ, List.append_assoc] using houtputB
    have hlH : outputBase + ((words ++ body.denote rom (Function.update environment counter (count + 1))) ++
        loopWords rom environment counter body count).length + 1 ≤ heapWords := by
      simpa only [loopWords_succ, List.append_assoc] using houtputH
    have hsrest := ih latched (words ++ body.denote rom (Function.update environment counter (count + 1)))
      hlpc hla hlreg hlenv hln (by omega) (by omega) hlstream hlB hlH
    have hfirstRun : natRun rom allCode (4 + clock rom (Function.update environment counter (count + 1)) stack body) state = done := by
      rw [natRun_add, hheadRun]
    have hsecondRun : natRun rom allCode (4 + clock rom (Function.update environment counter (count + 1)) stack body + 8) state = latched := by
      rw [natRun_add, hfirstRun, htailRun]
    have hfirst := RunSafe.add B heapWords rom allCode 4
      (clock rom (Function.update environment counter (count + 1)) stack body) state hshead
      (by rw [hheadRun]; exact hd.2)
    have hsecond := RunSafe.add B heapWords rom allCode
      (4 + clock rom (Function.update environment counter (count + 1)) stack body) 8 state hfirst
      (by rw [hfirstRun]; exact hstail)
    rw [loopClock_succ]
    exact RunSafe.add _ _ _ _ _ _ state hsecond (by rw [hsecondRun]; exact hsrest)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035r
