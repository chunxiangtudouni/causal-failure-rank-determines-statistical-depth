module
public import Common.PSTR_TM_ContextRaw_028
public import Common.PSTR_TM_FullRawPadding_015

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthCode116
open PaperProofs.Common.Native.RationalControllerComputation

def embedRaw (q : Fin 17) : Fin 20 := ⟨q.val,by have hq := q.isLt; omega⟩
def liftRaw (old : MachineState 16) : MachineState 19 := ⟨embedRaw old.q,old.Tape⟩
def EntrySafe (old : MachineState 16) : Prop := old.q.val≠0 ∨ old.Tape.head=true

/-- ONE fixed20-label contextual depth decoder. Original raw010 rotations
are unchanged. At actual field EOF(q0,false), it REALLY moves to the
original list-end TRUE, writes it FALSE, returns left and performs the
original contextual rewind. This creates a genuine00 right blank boundary;
the earlier numerator/denominator archive beyond the real false tag guard
is retained. No padding routine is incorrectly assumed safe in context. -/
def depthMachine : Machine 19 := fun q symbol =>
  if h : q.val<17 then
    if q.val=0 ∧ symbol=false then some (17,.move .right)
    else (PSTRTMRawNat010.rawNatMachine ⟨q.val,h⟩ symbol).map
      (fun (next,statement) => (embedRaw next,statement))
  else if q.val=17 then some (18,.write false)
  else if q.val=18 then some (19,.move .left)
  else some (12,.move .left)

def state (q : Fin 20) (left right : List Bool) : MachineState 19 := ⟨q,Turing.Tape.mk₂ left right⟩

theorem raw_lookup (q : Fin 17) (symbol : Bool) (h : q.val≠0 ∨ symbol=true) :
    depthMachine (embedRaw q) symbol=(PSTRTMRawNat010.rawNatMachine q symbol).map
      (fun (next,statement) => (embedRaw next,statement)) := by
  have hn : ¬(q.val=0 ∧ symbol=false) := by
    rcases h with hq|hs
    · exact fun hh => hq hh.1
    · intro hh
      rw [hs] at hh
      cases hh.2
  simp only [depthMachine,embedRaw,Fin.eta]
  simp only [q.isLt,↓reduceDIte,hn,↓reduceIte]

theorem raw_step (before : MachineState 16) (h : EntrySafe before) :
    Turing.TM0.step depthMachine (liftRaw before)=
      (Turing.TM0.step PSTRTMRawNat010.rawNatMachine before).map liftRaw := by
  cases before with
  | mk q tape =>
    simp only [Turing.TM0.step,liftRaw]
    rw [raw_lookup q tape.head h]
    cases hc : PSTRTMRawNat010.rawNatMachine q tape.head with
    | none => rfl
    | some cmd => obtain ⟨next,statement⟩ := cmd; cases statement <;> rfl

theorem retained_chain (trace : List (MachineState 16))
    (hc : trace.IsChain (fun x y => Turing.TM0.step PSTRTMRawNat010.rawNatMachine x=some y))
    (hs : ∀ before∈trace,EntrySafe before) :
    (trace.map liftRaw).IsChain (fun x y => Turing.TM0.step depthMachine x=some y) := by
  apply (List.isChain_map _).mpr
  apply hc.imp_of_mem_imp
  intro before after hb _ hstep
  rw [raw_step before (hs before hb),hstep]
  rfl

theorem depth_halt (left right : List Bool) : Turing.TM0.step depthMachine (state 16 left right)=none := by
  simp [Turing.TM0.step,depthMachine,state,PSTRTMRawNat010.rawNatMachine]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthCode116
