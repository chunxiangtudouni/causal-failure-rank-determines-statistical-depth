module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038l

/-! Actual read-and-clear dispatch. Both continuation rows are compiled
before the input. The actual read HALT port chooses the row through a real
charged write-self transition. This is finite control, not a host LSB. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
variable {s : Nat}

def observedPhase (bit : Bool) : Fin 2 := if bit then 1 else 0

def observeRows (h : 4≤s) (bodies : Fin 2 → Machine s) (row : Fin 3) : Machine s :=
  if row.val=0 then padMachine h readMachine else bodies (if row.val=2 then 1 else 0)

def observePorts (row : Fin 3) (q : Fin (s+1)) : Option (Fin 3 × Fin (s+1)) :=
  if row.val=0 then
    if q.val=1 then some (1,0) else if q.val=2 then some (2,0) else none
  else none

def observeThenMachine (h : 4≤s) (bodies : Fin 2 → Machine s) : Machine (totalStates 2 s) :=
  blockMachine (observeRows h bodies) observePorts

def observedPort (last : Fin 2 → Fin (s+1)) (bit : Bool) : Fin (totalStates 2 s+1) :=
  label (PA17TMRatArithmeticBookmark014.readPort bit) (last (observedPhase bit))

theorem observed_block_end (last : Fin 2 → Fin (s+1)) (bit : Bool) (output : Tape Bool) :
    blockCfg (PA17TMRatArithmeticBookmark014.readPort bit)
      (⟨last (observedPhase bit),output⟩ : MachineState s)=
      (⟨observedPort last bit,output⟩ : MachineState (totalStates 2 s)) := rfl

/-- The conditional input is an ACTUAL run of a fixed compiled body. A
closed caller must prove it; it is never an answer/width machine argument. -/
theorem observe_then_bounded (h : 4≤s) (bodies : Fin 2 → Machine s)
    (last : Fin 2 → Fin (s+1)) (left suffix : List Bool) (bit : Bool)
    (output : Tape Bool) (bound : Nat)
    (bodyRun : BoundedRun (bodies (observedPhase bit))
      (Tape.mk₂ left (false::suffix)) (last (observedPhase bit)) output bound) :
    BoundedRun (observeThenMachine h bodies) (Tape.mk₂ left (bit::suffix))
      (observedPort last bit) output (2+bound) := by
  let reader := (readTrace left bit suffix).map (padCfg h)
  have hr : PSTRTMSeq005.RunsFrom (observeRows h bodies 0)
      ⟨0,Tape.mk₂ left (bit::suffix)⟩ reader
      ⟨padLabel h (savedPort bit),Tape.mk₂ left (false::suffix)⟩ :=
    pad_runsFrom h readMachine _ _ _ (read_runsFrom left bit suffix)
  obtain ⟨body,he,hl⟩ := bodyRun
  have hee : PSTRTMSeq005.RunsFrom (observeRows h bodies (PA17TMRatArithmeticBookmark014.readPort bit))
      ⟨0,Tape.mk₂ left (false::suffix)⟩ body
      ⟨last (observedPhase bit),output⟩ := by
    cases bit <;> exact he
  have hs := segment_append (observeThenMachine h bodies) _ _ _ _ _ _
    (block_segment (observeRows h bodies) observePorts 0 _ _ reader hr)
    (block_segment (observeRows h bodies) observePorts
      (PA17TMRatArithmeticBookmark014.readPort bit) _ _ body hee)
    (block_transfer (observeRows h bodies) observePorts 0 _
      (PA17TMRatArithmeticBookmark014.readPort bit,0) hr.2.2.2 (by cases bit <;> rfl))
  have halt := block_halt (observeRows h bodies) observePorts
    (PA17TMRatArithmeticBookmark014.readPort bit) _ hee.2.2.2 (by cases bit <;> rfl)
  refine ⟨reader.map (blockCfg (p:=2) (s:=s) (0 : Fin 3))++
    body.map (blockCfg (p:=2) (s:=s) (PA17TMRatArithmeticBookmark014.readPort bit)),?_,?_⟩
  · have run := segment_runsFrom _ _ _ _ hs halt
    simpa only [observeThenMachine,observed_block_end,blockCfg_zero] using run
  · simp only [List.length_append,List.length_map,reader,readTrace_length]
    omega

def observeFamilyRows (p : Nat) (h : 4≤s) (bodies : Fin 2 → Machine s) :
    Fin (p+1) → Machine (totalStates 2 s) := fun _ => observeThenMachine h bodies
def observeFamilyPorts (p : Nat) : Fin (p+1) → Fin (totalStates 2 s+1) →
    Option (Fin (p+1) × Fin (totalStates 2 s+1)) := fun _ _ => none
def observeFamily (p : Nat) (h : 4≤s) (bodies : Fin 2 → Machine s) :
    Machine (totalStates p (totalStates 2 s)) :=
  blockMachine (observeFamilyRows p h bodies) (observeFamilyPorts p)

theorem observe_family_contract (p : Nat) (memory : Fin (p+1)) (h : 4≤s)
    (bodies : Fin 2 → Machine s) (last : Fin 2 → Fin (s+1))
    (left suffix : List Bool) (bit : Bool) (output : Tape Bool) (bound inputLength : Nat)
    (bodyRun : BoundedRun (bodies (observedPhase bit))
      (Tape.mk₂ left (false::suffix)) (last (observedPhase bit)) output bound) :
    ∃ trace, PSTRTMSeq005.RunsFrom (observeFamily p h bodies)
      (blockCfg memory (⟨0,Tape.mk₂ left (bit::suffix)⟩ : MachineState (totalStates 2 s))) trace
      (blockCfg memory (⟨observedPort last bit,output⟩ : MachineState (totalStates 2 s))) ∧
      trace.length≤2+bound ∧
      ∀ k, visitedSpace (observeFamily p h bodies) inputLength (trace.take k) ≤ inputLength+2*(2+bound)+1 := by
  obtain ⟨trace,hr,hl⟩ := observe_then_bounded h bodies last left suffix bit output bound bodyRun
  have hb := block_runsFrom (observeFamilyRows p h bodies) (observeFamilyPorts (s:=s) p) memory _ _ trace hr rfl
  refine ⟨trace.map (blockCfg memory),hb,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k
    have hs := PSTRTMTrace002.visitedSpace_le (observeFamily p h bodies) inputLength ((trace.map (blockCfg memory)).take k)
    have hk : ((trace.map (blockCfg memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

theorem observed_carry_preserved (p : Nat) (memory : Fin (p+1))
    (last : Fin 2 → Fin (s+1)) (bit : Bool) :
    phaseOf (label memory (observedPort last bit))=memory := phaseOf_label _ _

theorem observed_control_retained (last : Fin 2 → Fin (s+1)) (bit : Bool) :
    phaseOf (observedPort last bit)=PA17TMRatArithmeticBookmark014.readPort bit := phaseOf_label _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
