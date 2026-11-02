module

public import Paid.PDROC_EndpointOperands_Loop_019

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver PDMenu.ComputeFrame

/-- The original remaining-row induction, strengthened at the actual
component producers. Each local trace is selected ONCE, and its same
joinTrace witness retains functional cache/return, memory and any proved
local prefix invariant. Final canonical/numeric instances remove Closed. -/
theorem loop_cache_actual_closed (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (separated : base + 48 ≤ E)
    (testFetch : FetchesCode program testPC (rowTestCode bodyPC exitPC))
    (bodyFetch : FetchesCode program bodyPC (rowBodyCode testPC))
    (returnFetch : FetchesCode program exitPC returnCode)
    (Good : State → Prop) (closed : LoopClosed P program input base E returnPC testPC bodyPC exitPC Good)
    (fuel m : ℕ) (before : State) (values : ℕ → Cell)
    (position : before.pc = testPC) (header : Header before base values)
    (fresh : before.register .fresh = .natural base) (invariant : EndpointValues P E returnPC m values)
    (stored : StoredCache P E m before) (remaining : m + fuel = P.certificate.M + 1) (initial : Good before) :
    ∃ trace : List State, ∃ after : State,
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 2370 * fuel + 360 ∧ after.pc = returnPC ∧
      after.register .fresh = .natural base ∧ after.register .old = .natural returnPC ∧
      after.register .address = .natural E ∧ after.register .index = .natural (2 * P.certificate.M + 3) ∧
      StoredCache P E (P.certificate.M + 1) after ∧ after.output = before.output ∧ BelowBase before after base ∧
      (∀ state ∈ trace, RegionMemory before state (endpointLoopRegion base E P.certificate.M)) ∧
      (∀ state ∈ trace, Good state) := by
  induction fuel generalizing m before values with
  | zero =>
    have finished : m = P.certificate.M + 1 := by omega
    have outside : ¬m ≤ P.certificate.M := by omega
    obtain ⟨testTrace, tested, th, tl, tc, tt, testedPC, testedFresh, testedHeader, testMemory, testPrefixes⟩ :=
      rowTest_actual_prefix program input before base m P.certificate.M bodyPC exitPC values header fresh
        invariant.counter invariant.stop (by rw [position]; exact testFetch)
    have exit : tested.pc = exitPC := by simpa only [ite_eq_right outside] using testedPC
    have testGood : ∀ state ∈ testTrace, Good state := by
      intro state member
      exact closed .test m values before state ⟨position, header, fresh, invariant, stored, by omega, True.intro⟩
        initial (testPrefixes state member)
    have unchanged := testMemory tested (trace_last_member testTrace tested tl)
    have storedTest : StoredCache P E m tested := stored.congr unchanged.1 unchanged.2.1
    obtain ⟨returnTrace, after, rh, rl, rc, rt, afterPC, afterFresh, afterOld, afterAddress, afterIndex, returnMemory, returnPrefixes⟩ :=
      return_actual_prefix program input tested base E P.certificate.M returnPC values testedHeader testedFresh
        invariant.cache invariant.stop invariant.ret (by rw [exit]; exact returnFetch)
    have returnGood : ∀ state ∈ returnTrace, Good state := by
      intro state member
      exact closed .restore m values tested state ⟨exit, testedHeader, testedFresh, invariant, storedTest, by omega, finished⟩
        (testGood tested (trace_last_member testTrace tested tl)) (returnPrefixes state member)
    have finalMemory := returnMemory after (trace_last_member returnTrace after rl)
    have finalStored : StoredCache P E (P.certificate.M + 1) tested := by
      rw [←finished]
      exact storedTest
    have joined := joinTrace_spec program input testTrace returnTrace before tested after
      135 225 th tl rh rl tc rc tt rt
    refine ⟨joinTrace testTrace returnTrace, after, joined.1, joined.2.1, joined.2.2.1, joined.2.2.2,
      afterPC, afterFresh, afterOld, afterAddress, afterIndex,
      finalStored.congr finalMemory.1 finalMemory.2.1, finalMemory.2.2.trans unchanged.2.2,
      (BelowBase.of_unchanged base unchanged.1 unchanged.2.1).trans
        (BelowBase.of_unchanged base finalMemory.1 finalMemory.2.1), ?_,
      PDCompute.Pack.joinTrace_invariant testTrace returnTrace Good testGood returnGood⟩
    exact RegionMemory.join_trace testTrace returnTrace before tested _ tl
      (fun state member => RegionMemory.of_unchanged _ (testMemory state member).1
        (testMemory state member).2.1 (testMemory state member).2.2)
      (fun state member => RegionMemory.of_unchanged _ (returnMemory state member).1
        (returnMemory state member).2.1 (returnMemory state member).2.2)
  | succ fuel ih =>
    have inside : m ≤ P.certificate.M := by omega
    obtain ⟨testTrace, tested, th, tl, tc, tt, testedPC, testedFresh, testedHeader, testMemory, testPrefixes⟩ :=
      rowTest_actual_prefix program input before base m P.certificate.M bodyPC exitPC values header fresh
        invariant.counter invariant.stop (by rw [position]; exact testFetch)
    have bodyPosition : tested.pc = bodyPC := by simpa only [ite_eq_left inside] using testedPC
    have testGood : ∀ state ∈ testTrace, Good state := by
      intro state member
      exact closed .test m values before state ⟨position, header, fresh, invariant, stored, by omega, True.intro⟩
        initial (testPrefixes state member)
    have unchanged := testMemory tested (trace_last_member testTrace tested tl)
    have storedTest : StoredCache P E m tested := stored.congr unchanged.1 unchanged.2.1
    obtain ⟨bodyTrace, bodyAfter, bh, bl, bc, bt, bodyPC', bodyFresh, bodyHeader, bodyInvariant, bodyStored,
      bodyOutput, bodyFrame, bodyPrefixes, bodyPhase⟩ :=
      rowBody_actual_prefix P m program input tested base E returnPC testPC values testedHeader testedFresh
        invariant storedTest separated (by rw [bodyPosition]; exact bodyFetch)
    have bodyGood : ∀ state ∈ bodyTrace, Good state := by
      intro state member
      exact closed .body m values tested state
        ⟨bodyPosition, testedHeader, testedFresh, invariant, storedTest, by omega, inside⟩
        (testGood tested (trace_last_member testTrace tested tl)) (bodyPhase state member)
    obtain ⟨later, after, lh, ll, lc, lt, afterPC, afterFresh, afterOld, afterAddress, afterIndex, afterStored,
      afterOutput, laterFrame, laterPrefixes, laterGood⟩ :=
      ih (m := m + 1) (before := bodyAfter) (values := bodyValues P values m) bodyPC' bodyHeader bodyFresh
        bodyInvariant bodyStored (by omega) (bodyGood bodyAfter (trace_last_member bodyTrace bodyAfter bl))
    have first := joinTrace_spec program input testTrace bodyTrace before tested bodyAfter
      135 2235 th tl bh bl tc bc tt bt
    have joined := joinTrace_spec program input (joinTrace testTrace bodyTrace) later before bodyAfter after
      2370 (2370 * fuel + 360) first.1 first.2.1 lh ll first.2.2.1 lc first.2.2.2 lt
    refine ⟨joinTrace (joinTrace testTrace bodyTrace) later, after, joined.1, joined.2.1, joined.2.2.1, ?_,
      afterPC, afterFresh, afterOld, afterAddress, afterIndex, afterStored,
      afterOutput.trans (bodyOutput.trans unchanged.2.2),
      (BelowBase.of_unchanged base unchanged.1 unchanged.2.1).trans (bodyFrame.trans laterFrame), ?_,
      PDCompute.Pack.joinTrace_invariant (joinTrace testTrace bodyTrace) later Good
        (PDCompute.Pack.joinTrace_invariant testTrace bodyTrace Good testGood bodyGood) laterGood⟩
    · exact joined.2.2.2.trans_eq (loop_budget_succ fuel)
    · have testMemory' : ∀ state ∈ testTrace, RegionMemory before state (endpointLoopRegion base E P.certificate.M) :=
        fun state member => RegionMemory.of_unchanged _ (testMemory state member).1
          (testMemory state member).2.1 (testMemory state member).2.2
      have bodyMemory' : ∀ state ∈ bodyTrace, RegionMemory tested state (endpointLoopRegion base E P.certificate.M) :=
        fun state member => (bodyPrefixes state member).enlarge (endpointRowRegion_subset_loop base E m P.certificate.M inside)
      have firstPrefixes := RegionMemory.join_trace testTrace bodyTrace before tested _ tl testMemory' bodyMemory'
      exact RegionMemory.join_trace (joinTrace testTrace bodyTrace) later before bodyAfter _ first.2.1 firstPrefixes laterPrefixes

end PDROC.EndpointOperands.Loop
