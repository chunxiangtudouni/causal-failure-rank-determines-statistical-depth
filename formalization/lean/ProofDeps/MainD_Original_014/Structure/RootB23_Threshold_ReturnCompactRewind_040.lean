module
public import Common.PSTR_TM_PairRewind_105
public import Structure.PA17_TM_RatArithmetic_Width_018f

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnCompactRewind
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

/-! The nine-field copy's two middle return routes would exceed the
frozen Route100 binding if every elementary left-prefix used a separate
Seq HALT/write-self row. This direct prefix has exactly the SAME physical
LEFTs, then the frozen pair rewind, sharing their actual boundary state.
Only fixed prefix lengths1/3/4/10/13 enter the consumer's control tables. -/

def liftLabel (n : ℕ) (q : Fin (n+3+1)) : Fin (n+1+3+1) := ⟨q.val+1,by omega⟩
def liftCfg (n : ℕ) (state : MachineState (n+3)) : MachineState (n+1+3) :=
  ⟨liftLabel n state.q,state.Tape⟩
def code : (n : ℕ) → Machine (n+3)
  | 0=>PSTRTMMulRewind085.rewindMachine
  | n+1=>fun q symbol=>
      if zero : q.val=0 then some (1,.move .left)
      else (code n ⟨q.val-1,by have bound:=q.isLt;omega⟩ symbol).map
        (fun (next,statement)=>(liftLabel n next,statement))

theorem lift_lookup (n : ℕ) (q : Fin (n+3+1)) (symbol : Bool) :
    code (n+1) (liftLabel n q) symbol=(code n q symbol).map (fun (next,statement)=>(liftLabel n next,statement)) := by
  simp [code,liftLabel]

theorem lift_step (n : ℕ) (state : MachineState (n+3)) :
    TM0.step (code (n+1)) (liftCfg n state)=(TM0.step (code n) state).map (liftCfg n) := by
  cases state with
  | mk q tape=>
    simp only [TM0.step,liftCfg]
    rw [lift_lookup]
    cases lookup : code n q tape.head with
    | none=>rfl
    | some pair=>
      obtain ⟨next,statement⟩:=pair
      cases statement <;> rfl

theorem lift_runs (n : ℕ) (first last : MachineState (n+3)) (trace : List (MachineState (n+3)))
    (run : PSTRTMSeq005.RunsFrom (code n) first trace last) :
    PSTRTMSeq005.RunsFrom (code (n+1)) (liftCfg n first) (trace.map (liftCfg n)) (liftCfg n last) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.head?_map,run.1,Option.map_some]
  · apply (List.isChain_map _).mpr
    apply run.2.1.imp
    intro before after step
    simp only [lift_step,step,Option.map_some]
  · simp only [List.getLast?_map,run.2.2.1,Option.map_some]
  · simp only [lift_step,run.2.2.2,Option.map_none]

/-- Every prefix bit is physically crossed; none is a supplied distance.
The final nine-field controller instantiates this with fixed literal
prefixes, not with a value-dependent executable width. -/
theorem bounded (padding archive digits suffix : List Bool) :
    BoundedRun (code padding.length)
      (Tape.mk₂ (padding++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) suffix)
      ⟨padding.length+3,Nat.lt_succ_self _⟩
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++(padding.reverse++suffix)))
      (2*digits.length+padding.length+3) := by
  induction padding generalizing suffix with
  | nil=>
    exact ⟨PSTRTMPairRewind105.fullTrace archive digits.reverse suffix,
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,by
        rw [PSTRTMPairRewind105.full_length,List.length_reverse]
        exact le_refl _⟩
  | cons bit later ih=>
    obtain ⟨part,run,time⟩:=ih (bit::suffix)
    have lifted:=lift_runs later.length _ _ part run
    let initial : MachineState ((bit::later).length+3) :=
      ⟨0,Tape.mk₂ ((bit::later)++(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) suffix⟩
    have suffixEq : (bit::later).reverse++suffix=later.reverse++bit::suffix := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    rw [suffixEq]
    refine ⟨initial::part.map (liftCfg later.length),⟨rfl,?_,?_,?_⟩,?_⟩
    · apply List.IsChain.cons lifted.2.1
      intro next head
      rw [lifted.1] at head
      simp only [Option.mem_some_iff] at head
      subst next
      simp [initial,TM0.step,code,liftCfg,liftLabel,Tape.mk₂]
    · change ([initial]++part.map (liftCfg later.length)).getLast?=some _
      rw [List.getLast?_append,lifted.2.2.1]
      rfl
    · exact lifted.2.2.2
    · simp only [List.length_cons,List.length_map]
      omega

end RootB23.Threshold.ReturnCompactRewind
