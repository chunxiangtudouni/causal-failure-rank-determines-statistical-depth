module
public import Structure.RootB236_Controller_Candidate_Code_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing

/-- This proof-only path records actual TM2.step edges, not host macro steps. -/
inductive Run (bg : Stack → List Bool) (bound : Nat) : ScanState → ScanState → Nat → Prop where
  | refl {current : ScanState} (valid : Valid bg bound current) : Run bg bound current current 0
  | step {before after final : ScanState} {steps : Nat} (label : ScanLabel)
      (valid : Valid bg bound before) (active : before.l=some label) (proper : Proper label)
      (edge : TM2.step scanner before=some after) (rest : Run bg bound after final steps) :
      Run bg bound before final (steps+1)

theorem Run.append {bg : Stack → List Bool} {bound : Nat}
    {before middle final : ScanState} {early later : Nat}
    (first : Run bg bound before middle early) (last : Run bg bound middle final later) :
    Run bg bound before final (early+later) := by
  induction first with
  | refl _ => simpa only [Nat.zero_add] using last
  | step label valid active proper edge _ ih =>
    simpa only [Nat.add_right_comm] using Run.step label valid active proper edge (ih last)

theorem Run.single {bg : Stack → List Bool} {bound : Nat} (before after : ScanState)
    (label : ScanLabel) (hb : Valid bg bound before) (ha : Valid bg bound after)
    (active : before.l=some label) (proper : Proper label)
    (edge : TM2.step scanner before=some after) : Run bg bound before after 1 :=
  .step label hb active proper edge (.refl ha)

theorem Run.actual {bg : Stack → List Bool} {bound : Nat}
    {before final : ScanState} {steps : Nat} (run : Run bg bound before final steps) :
    ∃ trace : List ScanState, trace.head?=some before ∧
      trace.IsChain (fun a b => TM2.step scanner a=some b) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧
      (∀ current∈trace, Valid bg bound current) ∧
      ∀ current∈trace.dropLast, ∃ label, current.l=some label ∧ Proper label := by
  induction run with
  | refl valid =>
    refine ⟨[_],rfl,List.isChain_singleton _,rfl,rfl,?_,?_⟩
    · intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact valid
    · simp
  | @step before after final steps label valid active proper edge rest ih =>
    obtain ⟨trace,head,chain,last,length,bounds,interior⟩:=ih
    obtain ⟨tail,rfl⟩:=List.head?_eq_some_iff.mp head
    refine ⟨before::after::tail,rfl,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_,?_,?_⟩
    · change (after::tail).getLast?=some final
      exact last
    · simp only [List.length_cons] at length ⊢
      omega
    · intro current member
      rcases List.mem_cons.mp member with same | later
      · subst current; exact valid
      · exact bounds current later
    · intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with same | later
      · subst current; exact ⟨label,active,proper⟩
      · exact interior current later

theorem clear_run (bg : Stack → List Bool) (mem : Store) (bits old cur : List Bool) (bound : Nat)
    (hb : bits.length≤bound) (ho : old.length≤bound) (hc : cur.length≤bound) :
    Run bg bound (state bg .clear mem bits old cur [])
      (state bg .scan (false,false) bits [] cur []) (old.length+1) := by
  induction old generalizing mem with
  | nil =>
    exact Run.single _ _ .clear
      (valid_state _ _ _ _ _ _ _ _ hb (by simp) hc (by simp))
      (valid_state _ _ _ _ _ _ _ _ hb (by simp) hc (by simp)) rfl (by simp [Proper])
      (step_clear_end bg mem bits cur)
  | cons bit old ih =>
    have tail : old.length≤bound := by simpa only [List.length_cons] using (Nat.le_trans (Nat.le_succ old.length) ho)
    exact Run.step .clear
      (valid_state _ _ _ _ _ _ _ _ hb ho hc (by simp)) rfl (by simp [Proper])
      (step_clear bg mem bits old cur bit) (ih (true,bit) tail)

theorem copy_run (bg : Stack → List Bool) (mem : Store) (bits : List Bool)
    (rest made bound : Nat) (hb : bits.length≤bound) (ht : rest+made≤bound) :
    Run bg bound (state bg .copy mem bits (unary made) (unary rest) (unary made))
      (state bg .restore (false,false) bits (unary (rest+made)) [] (unary (rest+made)))
      (rest+1) := by
  induction rest generalizing made mem with
  | zero =>
    simp only [Nat.zero_add] at ht ⊢
    exact Run.single _ _ .copy
      (valid_state _ _ _ _ _ _ _ _ hb (by simpa [unary] using ht) (by simp [unary]) (by simpa [unary] using ht))
      (valid_state _ _ _ _ _ _ _ _ hb (by simpa [unary] using ht) (by simp) (by simpa [unary] using ht))
      rfl (by simp [Proper]) (step_copy_end bg mem bits made)
  | succ rest ih =>
    have next := ih (true,true) (made+1) (by omega)
    have eqn : rest+(made+1)=rest+1+made := by omega
    rw [eqn] at next
    exact Run.step .copy
      (valid_state _ _ _ _ _ _ _ _ hb (by simp [unary];omega) (by simp [unary];omega) (by simp [unary];omega))
      rfl (by simp [Proper]) (step_copy bg mem bits rest made) next

theorem restore_run (bg : Stack → List Bool) (mem : Store) (bits : List Bool)
    (tool rest copied bound : Nat) (hb : bits.length≤bound)
    (ht : tool≤bound) (hc : rest+copied+1≤bound) :
    Run bg bound (state bg .restore mem bits (unary tool) (unary copied) (unary rest))
      (state bg .found (false,false) bits (unary tool) (unary (rest+copied+1)) [])
      (rest+1) := by
  induction rest generalizing copied mem with
  | zero =>
    simp only [Nat.zero_add] at hc ⊢
    exact Run.single _ _ .restore
      (valid_state _ _ _ _ _ _ _ _ hb (by simpa [unary] using ht) (by simp [unary];omega) (by simp [unary]))
      (valid_state _ _ _ _ _ _ _ _ hb (by simpa [unary] using ht) (by simpa [unary] using hc) (by simp))
      rfl (by simp [Proper]) (step_restore_end bg mem bits tool copied)
  | succ rest ih =>
    have next := ih (true,true) (copied+1) (by omega)
    have eqn : rest+(copied+1)+1=rest+1+copied+1 := by omega
    rw [eqn] at next
    exact Run.step .restore
      (valid_state _ _ _ _ _ _ _ _ hb (by simpa [unary] using ht) (by simp [unary];omega) (by simp [unary];omega))
      rfl (by simp [Proper]) (step_restore bg mem bits tool rest copied) next

theorem hit_run (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (k bound : Nat)
    (hb : bits.length+1≤bound) (hk : k+1≤bound) :
    Run bg bound (state bg .scan mem (true::bits) [] (unary k) [])
      (state bg .found (false,false) bits (unary k) (unary (k+1)) []) (2*k+3) := by
  have copy := copy_run bg (true,true) bits k 0 bound (by omega) (by omega)
  simp only [Nat.add_zero,unary,List.replicate_zero] at copy
  have restore := restore_run bg (false,false) bits k k 0 bound (by omega) (by omega) (by omega)
  simp only [Nat.add_zero,unary,List.replicate_zero] at restore
  have joined := Run.step .scan
    (valid_state bg .scan mem (true::bits) [] (unary k) [] bound (by simpa using hb)
      (by simp) (by simp [unary];omega) (by simp)) rfl (by simp [Proper])
    (step_hit bg mem bits k) (copy.append restore)
  have cost : (k+1+(k+1))+1=2*k+3 := by omega
  rw [cost] at joined
  exact joined

theorem scan_found_run (bg : Stack → List Bool) (mem : Store) (tail : List Bool)
    (skipped k bound : Nat) (hb : skipped+1+tail.length≤bound) (hk : k+skipped+1≤bound) :
    Run bg bound (state bg .scan mem (List.replicate skipped false++true::tail) [] (unary k) [])
      (state bg .found (false,false) tail (unary (k+skipped)) (unary (k+skipped+1)) [])
      (skipped+2*(k+skipped)+3) := by
  induction skipped generalizing k mem with
  | zero => simpa using hit_run bg mem tail k bound (by omega) (by omega)
  | succ skipped ih =>
    have next := ih (true,false) (k+1) (by omega) (by omega)
    have eqn : k+1+skipped=k+(skipped+1) := by omega
    rw [eqn] at next
    have joined := Run.step .scan
      (valid_state bg .scan mem (List.replicate (skipped+1) false++true::tail) [] (unary k) [] bound
        (by simp only [List.length_append,List.length_replicate,List.length_cons];omega) (by simp) (by simp [unary];omega) (by simp)) rfl (by simp [Proper])
      (by simpa only [List.replicate_succ,List.cons_append] using
        step_skip bg mem (List.replicate skipped false++true::tail) k) next
    convert joined using 1; omega

theorem scan_empty_run (bg : Stack → List Bool) (mem : Store) (count k bound : Nat)
    (hb : count≤bound) (hk : k+count≤bound) :
    Run bg bound (state bg .scan mem (List.replicate count false) [] (unary k) [])
      (state bg .empty (false,false) [] [] (unary (k+count)) []) (count+1) := by
  induction count generalizing k mem with
  | zero =>
    simp only [Nat.add_zero,List.replicate_zero] at hk ⊢
    exact Run.single _ _ .scan
      (valid_state _ _ _ _ _ _ _ _ (by simp) (by simp) (by simpa [unary] using hk) (by simp))
      (valid_state _ _ _ _ _ _ _ _ (by simp) (by simp) (by simpa [unary] using hk) (by simp))
      rfl (by simp [Proper]) (step_empty bg mem k)
  | succ count ih =>
    have next := ih (true,false) (k+1) (by omega) (by omega)
    have eqn : k+1+count=k+(count+1) := by omega
    rw [eqn] at next
    exact Run.step .scan
      (valid_state _ _ _ _ _ _ _ _ (by simp;omega) (by simp) (by simp [unary];omega) (by simp))
      rfl (by simp [Proper]) (by simpa only [List.replicate_succ] using step_skip bg mem (List.replicate count false) k) next

theorem first_decomposition (bits : List Bool) :
    bits=List.replicate bits.length false ∨
      ∃ skipped tail, bits=List.replicate skipped false++true::tail := by
  induction bits with
  | nil => exact Or.inl rfl
  | cons bit bits ih =>
    cases bit with
    | true => exact Or.inr ⟨0,bits,rfl⟩
    | false =>
      rcases ih with all | ⟨skipped,tail,same⟩
      · exact Or.inl (by
          rw [List.length_cons,List.replicate_succ]
          exact congrArg (List.cons false) all)
      · exact Or.inr ⟨skipped+1,tail,by
          rw [List.replicate_succ,List.cons_append,same]⟩

def Outcome (bg : Stack → List Bool) (bits : List Bool) (k : Nat) (final : ScanState) : Prop :=
  (∃ skipped tail, bits=List.replicate skipped false++true::tail ∧
    final=state bg .found (false,false) tail (unary (k+skipped)) (unary (k+skipped+1)) []) ∨
  (bits=List.replicate bits.length false ∧
    final=state bg .empty (false,false) [] [] (unary (k+bits.length)) [])

/-- Pure continuation entry; the old result stack is already empty. -/
theorem actual_scan (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (k bound : Nat)
    (hb : bits.length≤bound) (hk : k+bits.length+1≤bound) :
    ∃ steps final, Run bg bound (state bg .scan mem bits [] (unary k) []) final steps ∧
      steps≤3*(k+bits.length+1) ∧ Outcome bg bits k final := by
  rcases first_decomposition bits with all | ⟨skipped,tail,same⟩
  · refine ⟨bits.length+1,_,?_,by omega,Or.inr ⟨all,rfl⟩⟩
    simpa only [←all] using scan_empty_run bg mem bits.length k bound hb (by omega)
  · have len : bits.length=skipped+1+tail.length := by simp only [same,List.length_append,List.length_replicate,List.length_cons];omega
    refine ⟨skipped+2*(k+skipped)+3,_,?_,by omega,Or.inl ⟨skipped,tail,same,rfl⟩⟩
    simpa only [←same] using scan_found_run bg mem tail skipped k bound (by omega) (by omega)

/-- Reentry clears OLD5 through real pop instructions. No free host reset. -/
theorem actual_resume (bg : Stack → List Bool) (mem : Store) (bits old : List Bool) (k : Nat) :
    ∃ steps final, Run bg (old.length+k+bits.length+1)
      (state bg .clear mem bits old (unary k) []) final steps ∧
      steps+1≤6*(old.length+k+bits.length+1) ∧ Outcome bg bits k final := by
  let bound:=old.length+k+bits.length+1
  have clear := clear_run bg mem bits old (unary k) bound (by dsimp [bound];omega)
    (by dsimp [bound];omega) (by simp [unary,bound];omega)
  obtain ⟨steps,final,scan,time,outcome⟩:=actual_scan bg (false,false) bits k bound
    (by dsimp [bound];omega) (by dsimp [bound];omega)
  refine ⟨old.length+1+steps,final,clear.append scan,?_,outcome⟩
  omega
end RootB236.ControllerCandidate
