module
public import Common.PSTR_TM_MulLoopCode_088

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopLift090
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulLoopCode088

theorem half_command (q next : Fin 34) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMMulHalfCode082.halfMachine q symbol=some (next,statement)) :
    loopMachine (halfLabel q) symbol=some (halfLabel next,statement) := by
  have hq : q.val<30 := by
    by_contra hn
    simp [PSTRTMMulHalfCode082.halfMachine,show q.val≠0 by omega,show q.val≠1 by omega,
      show ¬q.val<6 by omega,hn] at old
  simp [loopMachine,halfLabel,show ¬2+q.val<2 by omega,show 2+q.val<36 by omega,
    show 2+q.val≠33 by omega,show 2+q.val≠34 by omega,show 2+q.val≠35 by omega,old]

theorem append_command (mode : Bool) (q next : Fin 18) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMMulAppendCode086.appendMachine q symbol=some (next,statement)) :
    loopMachine (appendLabel mode q) symbol=some (appendLabel mode next,statement) := by
  have hq : q.val<17 := by
    have hbound := q.isLt
    by_contra hn
    have he : q=(17 : Fin 18) := Fin.ext (by omega)
    subst q
    simp [PSTRTMMulAppendCode086.appendMachine,PSTRTMMulRewind085.rewindMachine] at old
  cases mode <;>
    simp [loopMachine,appendLabel,show ¬36+q.val<2 by omega,show ¬36+q.val<36 by omega,
      show 36+q.val<54 by omega,show 36+q.val≠53 by omega,
      show ¬54+q.val<2 by omega,show ¬54+q.val<36 by omega,show ¬54+q.val<54 by omega,
      show 54+q.val<72 by omega,show 54+q.val≠71 by omega,old]

theorem pass_command (q next : Fin 192) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMMulPassCode079.passMachine q symbol=some (next,statement)) :
    loopMachine (passLabel q) symbol=some (passLabel next,statement) := by
  have hq : q.val<184 := by
    by_contra hn
    simp [PSTRTMMulPassCode079.passMachine,show ¬q.val<8 by omega,show ¬q.val<24 by omega,
      show ¬q.val<40 by omega,show ¬q.val<72 by omega,show ¬q.val<104 by omega,
      show ¬q.val<120 by omega,show ¬q.val<136 by omega,show ¬q.val<152 by omega,hn] at old
  simp [loopMachine,passLabel,show ¬72+q.val<2 by omega,show ¬72+q.val<36 by omega,
    show ¬72+q.val<54 by omega,show ¬72+q.val<72 by omega,
    show 72+q.val≠256 by omega,show 72+q.val≠260 by omega,old]

private theorem retained_step {a : Nat} (oldMachine : Machine a)
    (labelMap : Fin (a+1) → Fin 264)
    (commands : ∀ q next symbol statement, oldMachine q symbol=some (next,statement) →
      loopMachine (labelMap q) symbol=some (labelMap next,statement))
    (before after : MachineState a) (old : Turing.TM0.step oldMachine before=some after) :
    Turing.TM0.step loopMachine ⟨labelMap before.q,before.Tape⟩=some ⟨labelMap after.q,after.Tape⟩ := by
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

theorem half_step (before after : MachineState 33)
    (old : Turing.TM0.step PSTRTMMulHalfCode082.halfMachine before=some after) :
    Turing.TM0.step loopMachine (liftHalf before)=some (liftHalf after) :=
  retained_step _ halfLabel half_command before after old
theorem append_step (mode : Bool) (before after : MachineState 17)
    (old : Turing.TM0.step PSTRTMMulAppendCode086.appendMachine before=some after) :
    Turing.TM0.step loopMachine (liftAppend mode before)=some (liftAppend mode after) :=
  retained_step _ (appendLabel mode) (append_command mode) before after old
theorem pass_step (before after : MachineState 191)
    (old : Turing.TM0.step PSTRTMMulPassCode079.passMachine before=some after) :
    Turing.TM0.step loopMachine (liftPass before)=some (liftPass after) :=
  retained_step _ passLabel pass_command before after old

theorem half_chain (trace : List (MachineState 33))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMMulHalfCode082.halfMachine a=some b)) :
    (trace.map liftHalf).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) :=
  (List.isChain_map _).mpr (old.imp half_step)
theorem append_chain (mode : Bool) (trace : List (MachineState 17))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMMulAppendCode086.appendMachine a=some b)) :
    (trace.map (liftAppend mode)).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) :=
  (List.isChain_map _).mpr (old.imp (append_step mode))
theorem pass_chain (trace : List (MachineState 191))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMMulPassCode079.passMachine a=some b)) :
    (trace.map liftPass).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) :=
  (List.isChain_map _).mpr (old.imp pass_step)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopLift090
