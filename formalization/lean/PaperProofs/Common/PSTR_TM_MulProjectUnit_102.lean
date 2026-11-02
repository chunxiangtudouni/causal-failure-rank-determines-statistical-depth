module
public import PaperProofs.Common.PSTR_TM_MulProjectLift_101

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectUnit102
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulProjectCode100

def phase (base : Fin 111) (savedA : Bool) : Fin 115 := oldLabel (PSTRTMMulExpandUnit097.modeLabel base savedA)
def restoreTrace (digits : List Bool) (a b : Bool) (tail : List Bool) : List (MachineState 114) :=
  let left := PSTRTMRawNat010.leftBlocks digits.reverse
  [state (phase 93 a) left (false::false::true::false::b::true::tail),
    state (phase 95 a) (false::left) (false::true::false::b::true::tail),
    state (phase 97 a) (false::left) (true::true::false::b::true::tail),
    state (phase 99 a) (true::false::left) (true::false::b::true::tail),
    state (phase 101 a) (true::false::left) (false::false::b::true::tail),
    state (phase 103 a) (false::true::false::left) (false::b::true::tail),
    state (oldLabel 105) (false::true::false::left) (true::b::true::tail),
    state (oldLabel 106) (true::false::true::false::left) (b::true::tail),
    state 114 (true::false::true::false::left) (false::true::tail),
    state (oldLabel 107) (false::true::false::true::false::left) (true::tail)]

theorem restore_head (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (restoreTrace digits a b tail).head?=some (state (phase 93 a)
      (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)) := rfl
theorem restore_last (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (restoreTrace digits a b tail).getLast?=some (state (oldLabel 107)
      (false::true::false::true::false::PSTRTMRawNat010.leftBlocks digits.reverse) (true::tail)) := rfl

private theorem commands (a b : Bool) :
    prepareMachine (phase 93 a) false=some (phase 95 a,.move .right) ∧
    prepareMachine (phase 95 a) false=some (phase 97 a,.write true) ∧
    prepareMachine (phase 97 a) true=some (phase 99 a,.move .right) ∧
    prepareMachine (phase 99 a) true=some (phase 101 a,.write false) ∧
    prepareMachine (phase 101 a) false=some (phase 103 a,.move .right) ∧
    prepareMachine (phase 103 a) false=some (oldLabel 105,.write true) ∧
    prepareMachine (oldLabel 105) true=some (oldLabel 106,.move .right) ∧
    prepareMachine (oldLabel 106) b=some (114,.write false) ∧
    prepareMachine 114 false=some (oldLabel 107,.move .right) := by
  cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem restore_chain (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (restoreTrace digits a b tail).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := commands a b
  simp [restoreTrace,List.isChain_cons_cons,Turing.TM0.step,state,Turing.Tape.mk₂,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem pad_advance (digits : List Bool) (a b : Bool) (tail : List Bool) :
    Turing.TM0.step prepareMachine (PSTRTMMulProjectLift101.liftPad a (PSTRTMPadInsert034.state 40
      (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)))=
      some (state (phase 93 a) (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)) := by
  apply PSTRTMMulProjectLift101.retained_step _ _ _ (PSTRTMMulExpandUnit097.pad_advance digits a b tail)
  change 11+41*a.toNat+40<93
  have ha := Bool.toNat_le a
  omega

theorem restore_advance (digits : List Bool) (tail : List Bool) :
    Turing.TM0.step prepareMachine (state (oldLabel 107)
      (false::true::false::true::false::PSTRTMRawNat010.leftBlocks digits.reverse) (true::tail))=
      some (state 0 (PSTRTMRawNat010.leftBlocks (digits++[false,false,false]).reverse) tail) := by
  simp [Turing.TM0.step,prepareMachine,state,oldLabel,Turing.Tape.mk₂,PSTRTMRawNat010.leftBlocks,List.reverse_append]

def unitTrace (digits : List Bool) (a b : Bool) (tail : List Bool) : List (MachineState 114) :=
  PSTRTMMulProjectLift101.markTrace digits a b tail ++
    (PSTRTMPadTrace035.padTrace digits (b::true::tail)).map (PSTRTMMulProjectLift101.liftPad a) ++
    restoreTrace digits a b tail

private theorem append_link (xs ys : List (MachineState 114)) (last first : MachineState 114)
    (hx : xs.IsChain (fun a b => Turing.TM0.step prepareMachine a=some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step prepareMachine a=some b))
    (hl : xs.getLast?=some last) (hh : ys.head?=some first)
    (hs : Turing.TM0.step prepareMachine last=some first) :
    (xs++ys).IsChain (fun a b => Turing.TM0.step prepareMachine a=some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

theorem unit_head (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).head?=some (liftOld (PSTRTMMulExpandCode095.state 0
      (PSTRTMRawNat010.leftBlocks digits.reverse) (a::true::b::true::tail))) := by
  simp only [unitTrace,List.head?_append,PSTRTMMulProjectLift101.mark_head,Option.some_or]
theorem unit_last (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).getLast?=some (state (oldLabel 107)
      (false::true::false::true::false::PSTRTMRawNat010.leftBlocks digits.reverse) (true::tail)) := by
  simp only [unitTrace,List.getLast?_append,restore_last,Option.some_or]
theorem unit_length (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).length=12*digits.length+26 := by
  simp only [unitTrace,List.length_append,List.length_map,PSTRTMPadTrace035.pad_length,
    PSTRTMMulProjectLift101.markTrace,PSTRTMMulExpandUnit097.markTrace,restoreTrace,List.length_cons,List.length_nil]
  omega

/-- This REAL preparation call inserts one zero pair, erases A and B,
restores all flags true and retains the already copied prefix, including C.
The added B-write configuration is charged explicitly before its move. -/
theorem unit_chain (digits : List Bool) (a b : Bool) (tail : List Bool) :
    (unitTrace digits a b tail).IsChain (fun x y => Turing.TM0.step prepareMachine x=some y) := by
  unfold unitTrace
  refine append_link _ _
    (PSTRTMMulProjectLift101.liftPad a (PSTRTMPadInsert034.state 40
      (PSTRTMRawNat010.leftBlocks digits.reverse) (false::false::true::false::b::true::tail)))
    _ ?_ (restore_chain digits a b tail) ?_ (restore_head digits a b tail) (pad_advance digits a b tail)
  · exact append_link _ _ _ _ (PSTRTMMulProjectLift101.mark_chain digits a b tail)
      (PSTRTMMulProjectLift101.pad_chain a _ (PSTRTMPadTrace035.pad_chain digits (b::true::tail)))
      (PSTRTMMulProjectLift101.mark_last digits a b tail)
      (by simp only [List.head?_map,PSTRTMPadTrace035.pad_head,Option.map_some])
      (PSTRTMMulProjectLift101.mark_advance digits a b tail)
  · simp only [List.getLast?_append,List.getLast?_map,PSTRTMPadTrace035.pad_last,Option.map_some,Option.some_or]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulProjectUnit102
