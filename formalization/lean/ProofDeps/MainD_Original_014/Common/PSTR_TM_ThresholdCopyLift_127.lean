module
public import Common.PSTR_TM_ThresholdCopyCode_126

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyLift127
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCopyCode126

/-- Three actual initialization scans: NUM, DEN and DEPTH. -/
def cursorLabel (entry : Fin 3) (q : Fin 3) : Fin 131 :=
  let base := if entry.val=0 then 0 else if entry.val=1 then 4 else 6
  ⟨base+q.val,by
    have hq := q.isLt
    dsimp [base]
    split
    · omega
    · split <;> omega⟩

def liftCursor (entry : Fin 3) (old : MachineState 2) : MachineState 130 :=
  ⟨cursorLabel entry old.q,old.Tape⟩

/-- Three actual initialization returns: DEPTH, DEN and NUM. -/
def rewindLabel (entry : Fin 3) (q : Fin 4) : Fin 131 :=
  match entry.val,q.val with
  | 0,0 => 16 | 0,1 => 17 | 0,2 => 18 | 0,_ => 20
  | 1,0 => 22 | 1,1 => 23 | 1,2 => 24 | 1,_ => 26
  | _,0 => 30 | _,1 => 31 | _,2 => 32 | _,_ => 34

def liftRewind (entry : Fin 3) (old : MachineState 3) : MachineState 130 :=
  ⟨rewindLabel entry old.q,old.Tape⟩

theorem cursor_command (entry : Fin 3) (q next : Fin 3) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMThresholdCursor115.cursorMachine q symbol=some (next,statement)) :
    copyMachine (cursorLabel entry q) symbol=some (cursorLabel entry next,statement) := by
  fin_cases entry <;> fin_cases q <;> cases symbol <;>
    simp [PSTRTMThresholdCursor115.cursorMachine] at old <;>
    rcases old with ⟨rfl,rfl⟩ <;> rfl

theorem rewind_command (entry : Fin 3) (q next : Fin 4) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMMulRewind085.rewindMachine q symbol=some (next,statement)) :
    copyMachine (rewindLabel entry q) symbol=some (rewindLabel entry next,statement) := by
  fin_cases entry <;> fin_cases q <;> cases symbol <;>
    simp [PSTRTMMulRewind085.rewindMachine] at old <;>
    rcases old with ⟨rfl,rfl⟩ <;> rfl

private theorem retained_step {a b : Nat} (oldMachine : Machine a) (newMachine : Machine b)
    (labelMap : Fin (a+1) → Fin (b+1))
    (commands : ∀ q next symbol statement, oldMachine q symbol=some (next,statement) →
      newMachine (labelMap q) symbol=some (labelMap next,statement))
    (before after : MachineState a) (old : Turing.TM0.step oldMachine before=some after) :
    Turing.TM0.step newMachine ⟨labelMap before.q,before.Tape⟩=some ⟨labelMap after.q,after.Tape⟩ := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : oldMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next,statement⟩ := command
      simp only [hc,Option.map_some,Option.some.injEq] at old
      subst after
      have hm := commands q next tape.head statement hc
      simp only [Turing.TM0.step,hm,Option.map_some]

theorem cursor_step (entry : Fin 3) (before after : MachineState 2)
    (old : Turing.TM0.step PSTRTMThresholdCursor115.cursorMachine before=some after) :
    Turing.TM0.step copyMachine (liftCursor entry before)=some (liftCursor entry after) :=
  retained_step _ _ (cursorLabel entry) (cursor_command entry) before after old

theorem rewind_step (entry : Fin 3) (before after : MachineState 3)
    (old : Turing.TM0.step PSTRTMMulRewind085.rewindMachine before=some after) :
    Turing.TM0.step copyMachine (liftRewind entry before)=some (liftRewind entry after) :=
  retained_step _ _ (rewindLabel entry) (rewind_command entry) before after old

theorem cursor_chain (entry : Fin 3) (trace : List (MachineState 2))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMThresholdCursor115.cursorMachine before=some after)) :
    (trace.map (liftCursor entry)).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply (List.isChain_map _).mpr
  exact h.imp (cursor_step entry)

theorem rewind_chain (entry : Fin 3) (trace : List (MachineState 3))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMMulRewind085.rewindMachine before=some after)) :
    (trace.map (liftRewind entry)).IsChain (fun before after => Turing.TM0.step copyMachine before=some after) := by
  apply (List.isChain_map _).mpr
  exact h.imp (rewind_step entry)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCopyLift127
