module
public import RootPaper_TableCost_Final015

/-! A cost attachment to the same actual persistent Word run and policy.
Every past stage is read from the archive produced so far. The only code
choice is the already-closed WORD implementation, before all instances. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims PA17A19RuntimeEntry020
open CompactPrice PSTRQueryRecords RationalControllerComputation
open scoped BigOperators
variable {I : Instance}

def nativeHorizon (input : StatisticalInput I) (budget : Rat) : Nat:=quotaActionBound I (computedQuotas input budget)+1
noncomputable def perClockDegree (runtime : WordCode) : Nat:=33*(runningDegree runtime+2)
noncomputable def perClockRate (runtime : WordCode) : Nat:=(inputRate+1)^(runningDegree runtime+2)*localRate runtime
noncomputable def nativeDegree (runtime : WordCode) : Nat:=perClockDegree runtime+1
noncomputable def nativeRate (runtime : WordCode) : Nat:=4*perClockRate runtime+4096

theorem native_horizon_bound (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    nativeHorizon input budget≤4*arithmeticScale input C budget := by
  unfold nativeHorizon quotaActionBound arithmeticScale inputSize numericalQuota
  omega

private theorem add_one_scale (b k p : Nat) (bound : b≤k*p) (one : 1≤p) : b+1≤(k+1)*p := by
  nlinarith

def producedArchive {bits q : Nat} (full : List (Finset (Fin q))) (commands : List Command)
    (counts : List Nat) (heap : BitVec bits→BitVec bits) : List Nat:=
  saved [] (packets q full RootPaper.Table.live commands counts heap)

noncomputable def nativeClockCost (runtime : WordCode) (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat) (positive : 0<budget)
    (policy : Policy input C .native accounting Unit) (sample : Unit×input.World) (clock : Nat) (records : List Nat) : Nat:=
  let state:=run input C .native accounting policy.rule sample clock
  if state.halted then 0 else
    256*bitCost runtime (localSize input C budget state.history records (indexWidth 32 I.stageCount I.toolCount))
      (indexWidth 32 I.stageCount I.toolCount) records (preparedCandidate input C available budget positive state.history records)

theorem native_clock_bound (runtime : WordCode) (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat) (positive : 0<budget) (small : budget≤1/2)
    (policy : Policy input C .native accounting Unit) (sample : Unit×input.World) (clock : Nat) (records : List Nat)
    (early : clock≤nativeHorizon input budget) (length : records.length≤4*(2*I.stageCount+1))
    (words : ∀ value∈records,value<2^indexWidth 32 I.stageCount I.toolCount) :
    nativeClockCost runtime input C accounting available budget positive policy sample clock records≤
      perClockRate runtime*(arithmeticScale input C budget)^perClockDegree runtime := by
  let P:=arithmeticScale input C budget
  let B:=localSize input C budget (run input C .native accounting policy.rule sample clock).history records
    (indexWidth 32 I.stageCount I.toolCount)
  have positiveP : 1≤P:=by dsimp only [P,arithmeticScale];omega
  have original:=native_localSize input C accounting available budget policy sample clock records
    (early.trans (native_horizon_bound input C budget)) length words
  have one:1≤P^33:=Nat.one_le_pow _ _ positiveP
  have extended:B+1≤(inputRate+1)*P^33:=add_one_scale B inputRate (P^33) original one
  have lifted:=polynomial_cap (localRate runtime) (inputRate+1) (P-1) 33 (runningDegree runtime+2)
    (perClockDegree runtime) (perClockRate runtime) (B+1)
    (by simpa only [Nat.sub_add_cancel positiveP] using extended) (Nat.le_refl _) (Nat.le_refl _)
  have power:localRate runtime*(B+1)^(runningDegree runtime+2)≤perClockRate runtime*P^perClockDegree runtime := by
    simpa only [Nat.sub_add_cancel positiveP] using lifted
  unfold nativeClockCost
  dsimp only
  split
  · exact Nat.zero_le _
  · exact (local_fee_bound runtime input C available budget positive small _ records _).trans power

theorem archive_save_bound (input : StatisticalInput I) (C : Contract I) (budget : Rat)
    (commands : List Command) (counts : List Nat)
    (heap : BitVec (indexWidth 32 I.stageCount I.toolCount)→BitVec (indexWidth 32 I.stageCount I.toolCount))
    (length : commands.length≤2*I.stageCount+1) :
    saveDebit (indexWidth 32 I.stageCount I.toolCount) []
      (packets I.toolCount I.compatibility RootPaper.Table.live commands counts heap)≤4096*(arithmeticScale input C budget)^3 := by
  let P:=arithmeticScale input C budget
  have positive:1≤P:=by dsimp only [P,arithmeticScale];omega
  have dimensions:I.stageCount+I.toolCount+1≤P:=by dsimp only [P,arithmeticScale,inputSize];omega
  have width:=(physical_word_width I.stageCount I.toolCount)
  have a:commands.length≤3*P:=by omega
  have b:4*commands.length+2≤14*P:=by omega
  have c:indexWidth 32 I.stageCount I.toolCount+4*commands.length+2≤78*P:=by omega
  have multiplied:=Nat.mul_le_mul (Nat.mul_le_mul a b) c
  have bounded:commands.length*(4*commands.length+2)*(indexWidth 32 I.stageCount I.toolCount+4*commands.length+2)≤3276*P^3:=
    multiplied.trans_eq (by ring)
  exact (physical_archive I.compatibility RootPaper.Table.live commands counts heap).2 |>.trans
    (bounded.trans (Nat.mul_le_mul_right _ (by decide : 3276≤4096)))

def NativeChargeBound (runtime : WordCode) (coefficient degree : Nat) (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat) (positive : 0<budget)
    (policy : Policy input C .native accounting Unit)
    (heap : BitVec (indexWidth 32 I.stageCount I.toolCount)→BitVec (indexWidth 32 I.stageCount I.toolCount)) : Prop:=
  ∀ sample : Unit×input.World,
    let horizon:=nativeHorizon input budget
    let commands:=commandsAt I (run input C .native accounting policy.rule sample horizon).history
    ∃ counts : List Nat,counts.length=commands.length ∧
      CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility) (allocatedWords I.compatibility)
        RootPaper.Table.live ⟨0,Finset.univ\available,false⟩ commands counts heap ∧
      (∀ clock : Fin horizon,
        let history:=(run input C .native accounting policy.rule sample clock.val).history
        let current:=commandsAt I history
        let archive:=producedArchive I.compatibility current (counts.take current.length) heap
        archive=nativeRecords available history ∧
        archive.IsPrefix (producedArchive I.compatibility commands counts heap) ∧
        (preparedCandidate input C available budget positive history archive).action=policy.rule () history) ∧
      saveDebit (indexWidth 32 I.stageCount I.toolCount) []
          (packets I.toolCount I.compatibility RootPaper.Table.live commands counts heap)+
        ∑ clock : Fin horizon,nativeClockCost runtime input C accounting available budget positive policy sample clock.val
          (producedArchive I.compatibility (commandsAt I (run input C .native accounting policy.rule sample clock.val).history)
            (counts.take (commandsAt I (run input C .native accounting policy.rule sample clock.val).history).length) heap)≤
        coefficient*(arithmeticScale input C budget)^degree

theorem native_cost_on_run (runtime : WordCode) (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat) (positive : 0<budget) (small : budget≤1/2)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule=tableRule input available budget (some (computedQuotas input budget)))
    (heap : BitVec (indexWidth 32 I.stageCount I.toolCount)→BitVec (indexWidth 32 I.stageCount I.toolCount))
    (wordRun : RootPaper.Table.NativeWordRun input C accounting available (computedQuotas input budget) policy heap) :
    NativeChargeBound runtime (nativeRate runtime) (nativeDegree runtime) input C accounting available budget positive policy heap := by
  intro sample
  let horizon:=nativeHorizon input budget
  let commands:=commandsAt I (run input C .native accounting policy.rule sample horizon).history
  obtain ⟨halted,counts,countLength,commandLength,execution,wordCost,finalRecords,prefixes⟩:=wordRun sample
  refine ⟨counts,countLength,execution,?_,?_⟩
  · intro clock
    have front:=prefixes clock
    let history:=(run input C .native accounting policy.rule sample clock.val).history
    let commandsNow:=commandsAt I history
    have archived:producedArchive I.compatibility commandsNow (counts.take commandsNow.length) heap=nativeRecords available history:=
      (physical_archive I.compatibility RootPaper.Table.live commandsNow (counts.take commandsNow.length) heap).1.trans front.2.2.1
    refine ⟨archived,?_,?_⟩
    · exact saved_prefix [] _ _ (packets_prefix I.compatibility RootPaper.Table.live commands commandsNow counts heap front.1)
    · rw [archived,preparedCandidate_eq]
      exact actual_native_candidate input C laminar current accounting available budget positive small
        (some (computedQuotas input budget)) policy sameRule sample clock.val
  · let P:=arithmeticScale input C budget
    have positiveP:1≤P:=by dsimp only [P,arithmeticScale];omega
    have all : (∑ clock : Fin horizon,nativeClockCost runtime input C accounting available budget positive policy sample clock.val
        (producedArchive I.compatibility (commandsAt I (run input C .native accounting policy.rule sample clock.val).history)
          (counts.take (commandsAt I (run input C .native accounting policy.rule sample clock.val).history).length) heap))≤
        (4*perClockRate runtime)*P^(nativeDegree runtime) := by
      have each : ∀ clock : Fin horizon,nativeClockCost runtime input C accounting available budget positive policy sample clock.val
          (producedArchive I.compatibility (commandsAt I (run input C .native accounting policy.rule sample clock.val).history)
            (counts.take (commandsAt I (run input C .native accounting policy.rule sample clock.val).history).length) heap)≤
            perClockRate runtime*P^perClockDegree runtime := by
        intro clock
        have front:=prefixes clock
        have archived:=(physical_archive I.compatibility RootPaper.Table.live
          (commandsAt I (run input C .native accounting policy.rule sample clock.val).history)
          (counts.take (commandsAt I (run input C .native accounting policy.rule sample clock.val).history).length) heap).1
        apply native_clock_bound runtime input C accounting available budget positive small policy sample clock.val _ (Nat.le_of_lt clock.isLt)
        · exact (congrArg (fun values : List Nat=>values.length≤4*(2*I.stageCount+1)) archived).mpr front.2.2.2.1
        · have raw : ∀ value∈queryRecords I.toolCount I.compatibility RootPaper.Table.live
              (commandsAt I (run input C .native accounting policy.rule sample clock.val).history)
              (counts.take (commandsAt I (run input C .native accounting policy.rule sample clock.val).history).length) heap,
              value<2^indexWidth 32 I.stageCount I.toolCount := by
            simpa only [wordBits,Instance.stageCount] using front.2.2.2.2
          exact (congrArg (fun values : List Nat=>∀ value∈values,value<2^indexWidth 32 I.stageCount I.toolCount) archived).mpr raw
      calc
        _≤∑ _clock : Fin horizon,perClockRate runtime*P^perClockDegree runtime:=Finset.sum_le_sum (fun clock _=>each clock)
        _=horizon*(perClockRate runtime*P^perClockDegree runtime):=by simp
        _≤(4*P)*(perClockRate runtime*P^perClockDegree runtime):=Nat.mul_le_mul_right _ (native_horizon_bound input C budget)
        _=_:=by unfold nativeDegree;rw [pow_succ];ring
    have savedBound:=archive_save_bound input C budget commands counts heap commandLength
    have degree:3≤nativeDegree runtime:=by unfold nativeDegree perClockDegree runningDegree;omega
    have savedLarger:=savedBound.trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_right positiveP degree))
    exact (Nat.add_le_add savedLarger all).trans_eq (by unfold nativeRate;ring)

def StrongWordCode (runtime : WordCode) : Prop:=
  ∃ port : Fin (runtime.states+1),∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
    ∃ trace final,Runs runtime.code (wordInput E target word) trace final ∧ final.q=port ∧
      Turing.TM0.step runtime.code final=none ∧ final.Tape.right₀=Turing.ListBlank.mk (wordOutput E target word) ∧
      trace.length+(wordInput E target word).length+(wordOutput E target word).length≤
        runtime.coefficient*((wordInput E target word).length+word.1+1)^runtime.degree ∧
      ∀ clock,visitedSpace runtime.code (wordInput E target word).length (trace.take clock)≤
        runtime.coefficient*((wordInput E target word).length+word.1+1)^runtime.degree

theorem original_cost_attachment :
    ∃ runtime : WordCode,StrongWordCode runtime ∧ 0<nativeRate runtime ∧ 0<nativeDegree runtime ∧
    ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I),LaminarSchedule I.compatibility→C.IsCurrentAllocation→
    ∀ (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat) (positive : 0<budget),budget≤1/2→
    ∀ policy : Policy input C .native accounting Unit,
    policy.rule=tableRule input available budget (some (computedQuotas input budget))→
    ∃ prepSteps headSteps,
      RootPaper.Table.PreparedRun I.compatibility (Finset.univ\available) prepSteps headSteps ∧
      NativeChargeBound runtime (nativeRate runtime) (nativeDegree runtime) input C accounting available budget positive policy
        (RootPaper.Table.preparedHeap I.compatibility (Finset.univ\available) prepSteps) := by
  obtain ⟨states,code,port,c,d,hc,hd,actual⟩:=RootPaper.Scalar.word_closed
  let runtime : WordCode:=⟨states,code,c,d,⟨hc,hd⟩,fun E target word=>by
    obtain ⟨trace,final,run,atPort,halted,output,time,space⟩:=actual E target word
    exact ⟨trace,final,run,output,time⟩⟩
  have strong : StrongWordCode runtime:=⟨port,actual⟩
  refine ⟨runtime,strong,by unfold nativeRate;omega,by unfold nativeDegree;omega,?_⟩
  intro I input C laminar current accounting available budget positive small policy sameRule
  obtain ⟨prepSteps,headSteps,prepared,actual⟩:=RootPaper.Table.word_run input C laminar current accounting available budget positive small
    (computedQuotas input budget) policy sameRule
  exact ⟨prepSteps,headSteps,prepared,native_cost_on_run runtime input C laminar current accounting available budget positive small policy sameRule _ actual⟩

theorem computed_quota_eq_of_choice (input : StatisticalInput I) (delta : Real) (exponent : Nat) (budget : Rat)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    computedQuotas input budget=referenceQuota input exponent := by
  unfold computedQuotas computedExponent
  rw [choice.same_exponent]

end RootPaper.TableCost
