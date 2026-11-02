module

public import B23_4_RatWordPrep_SeqCmp_ChannelsPaths_077

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem round_shared (before : State C) (digits : List Bool)
    (active : before.l=some (.round 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    roundCfg (RootB234.RuntimeCounter.Round.entry before.stk ((roundIso C).symm before.var) digits)=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.round 0) at active
    subst point
    change (⟨some (.round 0),roundIso C ((roundIso C).symm memory),
      RootB234.RuntimeCounter.Round.cells slots _ _ _⟩ : State C)=⟨some (.round 0),memory,slots⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Round.cells]

theorem actual_round (caller : Statement C) (before : State C) (digits : List Bool)
    (active : before.l=some (.round 0))
    (right : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (if PSTRTMIncrement009.valueDigits digits=0 then .done else .read .boot) ∧
      final.var.2=before.var.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (RootB234.RuntimeCounter.Round.Raw.outputDigits digits) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot) ∧
      run.trace.length≤256*RootB234.RuntimeCounter.Round.scale before.stk digits := by
  obtain ⟨trace,final,facts⟩ := RootB234.RuntimeCounter.Round.actual_polynomial
    before.stk ((roundIso C).symm before.var) digits
  have path := round_path caller facts
  let run : Segment caller before (roundCfg final) :=
    ⟨trace.map roundCfg,path.1.trans (congrArg some (round_shared before digits active right left scratch)),
      path.2.1,path.2.2⟩
  obtain ⟨outRight,outLeft,outScratch⟩ := RootB234.RuntimeCounter.Round.exact_output facts
  refine ⟨roundCfg final,run,?_,?_,outRight,outLeft,outScratch,?_,?_⟩
  · change final.l.map roundLabel=some _
    rw [facts.port]
    by_cases zero : PSTRTMIncrement009.valueDigits digits=0 <;> simp [roundLabel,zero]
  · exact congrArg (fun v : RoundContext C => v.2) facts.context
  · intro slot n4 n10 n11
    exact RootB234.RuntimeCounter.Round.exact_frame facts slot (by
      simp only [RootB234.RuntimeCounter.Round.Work,n4,n10,n11,or_self,not_false_eq_true])
  · simpa only [run,List.length_map] using facts.time

theorem read_shared (before : State C) (active : before.l=some (.read .boot)) :
    readCfg (⟨some .boot,(rawIso C).symm before.var,before.stk⟩ : RawGetter.State (RawContext C))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.read .boot) at active
    subst point
    change (⟨some (.read .boot),rawIso C ((rawIso C).symm memory),slots⟩ : State C)=_
    rw [Equiv.apply_symm_apply]

theorem actual_read (caller : Statement C) (before : State C) (x : Rat) (suffix : List Bool)
    (active : before.l=some (.read .boot))
    (right : ListBlank.mk (before.stk 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true])) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.move 0) ∧ final.var.2=before.var.2 ∧
      final.stk 15=RatInput.Encoder.packet x (before.stk 15) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      (∀ slot,slot≠0→slot≠1→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤RawGetter.time x := by
  obtain ⟨trace,final,parsed,first,chain,last,_member,activeFinal,context,contents,tape,
      scratch,_target,time,boundaries,_proper⟩ :=
    RawGetter.actual_current_bounded before.stk ((rawIso C).symm before.var) x suffix right
  have path := read_path caller trace _ final first chain last activeFinal
  let run : Segment caller before (readCfg final) :=
    ⟨trace.map readCfg,path.1.trans (congrArg some (read_shared before active)),path.2.1,path.2.2⟩
  have finalFrame := (boundaries final (List.mem_of_getLast? last)).2.2.2
  refine ⟨readCfg final,run,?_,?_,?_,?_,?_,?_⟩
  · change final.l.map readLabel=some (.move 0)
    rw [activeFinal]
    rfl
  · exact congrArg (fun v : RawContext C => v.2) context
  · change final.stk 15=_
    rw [contents,Function.update_self]
  · have rightTape := congrArg Tape.right₀ tape
    simp only [Tape.mk₂,Tape.mk'_right₀] at rightTape
    change ListBlank.mk (final.stk 0)=_
    rw [contents,Function.update_of_ne (by decide : (0 : RatInput.Stack)≠15)]
    exact rightTape
  · intro slot n0 n1 n15
    change final.stk slot=_
    by_cases s7 : slot=7
    · subst slot
      rw [contents,Function.update_of_ne (by decide : (7 : RatInput.Stack)≠15)]
      exact scratch
    · exact finalFrame slot (by simp only [RawGetter.Work,n0,n1,n15,s7,or_self,not_false_eq_true])
  · simpa only [run,List.length_map] using time

theorem move_shared (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (.move 0)) (source : before.stk 15=RatInput.Encoder.packet x tail)
    (scratch : before.stk 4=[]) :
    moveCfg (RootB234.RatPacketTransport.atState RootB234.RatPacketTransport.Public.move15To2Roles
      before.stk 0 ((packetIso C).symm before.var).1 ((packetIso C).symm before.var).2
      (RatInput.Encoder.packet x tail) [] (before.stk 2))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.move 0) at active
    subst point
    change (⟨some (.move 0),packetIso C ((packetIso C).symm memory),
      RootB234.RatPacketTransport.bank slots _ _ _⟩ : State C)=⟨some (.move 0),memory,slots⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RatPacketTransport.bank]

theorem actual_move (caller : Statement C) (before : State C) (x : Rat) (tail : List Bool)
    (active : before.l=some (.move 0)) (source : before.stk 15=RatInput.Encoder.packet x tail)
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.round 0) ∧ final.var.2=before.var.2 ∧
      final.stk 15=tail ∧ final.stk 2=RatInput.Encoder.packet x (before.stk 2) ∧ final.stk 4=[] ∧
      (∀ slot,slot≠2→slot≠4→slot≠15→final.stk slot=before.stk slot) ∧
      run.trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let registers := (packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RatPacketTransport.Public.move15To2_actual
    before.stk registers.1 registers.2 x tail (before.stk 2)
  let final := RootB234.RatPacketTransport.atState RootB234.RatPacketTransport.Public.move15To2Roles
    before.stk 4 registers.1 (false,false) tail [] (RatInput.Encoder.packet x (before.stk 2))
  have path := move_path caller trace _ final facts.first facts.chain facts.last rfl
  let run : Segment caller before (moveCfg final) :=
    ⟨trace.map moveCfg,path.1.trans (congrArg some (move_shared before x tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨moveCfg final,run,rfl,?_,rfl,rfl,rfl,?_,?_⟩
  · change registers.1.2=before.var.2
    rfl
  · intro slot n2 n4 n15
    change RootB234.RatPacketTransport.bank before.stk _ _ _ slot=before.stk slot
    simp only [RootB234.RatPacketTransport.bank,n2,n4,n15,ite_false]
  · simpa only [run,List.length_map] using facts.count

end B23_4_RatWordPrep.Channels
