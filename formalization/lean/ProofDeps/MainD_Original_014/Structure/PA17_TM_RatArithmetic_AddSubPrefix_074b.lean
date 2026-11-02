module
public import Structure.PA17_TM_RatArithmetic_AddSubPrefix_074a

/-! Actual producer and copy contracts for the five-cache shared prefix.
All bank bounds below describe already-produced tapes. The final raw
contract discharges them from original x,y; none parameterizes code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubPrefix074

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticSignedSumFields072 PA17TMRatArithmeticMulStart049
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticCachedOuter043 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticMulClosure059 PA17TMRatArithmeticAllocationBounds056
open PA17TMRatArithmeticPairBounds061 PA17TMRatArithmeticPairInput050
open PA17TMRatArithmeticMulController057 (widen64 row64_entry row64_decode)
attribute [local implicit_reducible] totalStates carriedTailCap tailCap nativeRecordCap
  PA17TMRatArithmeticCachedOuter043.carryCap originalPairCap cachedPairCap

def freshGap (x y : Rat) : Nat := allocationK*(fieldWidth x y)^2
def power (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def prefixTimeCoefficient : Nat := PA17TMRatArithmeticDivPrefix067.prefixTimeCoefficient+
  3*allocationCoefficient+3*feeConstant allocationK+3*nativeCoefficient
def prefixResourceCoefficient : Nat := 2*prefixTimeCoefficient+2

theorem prefixResourceCoefficient_pos : 0<prefixResourceCoefficient := by
  unfold prefixResourceCoefficient
  omega

def RecordBound (x y : Rat) (record : RecordSpec) : Prop :=
  record.gap≤2*allocationK*(fieldWidth x y)^2 ∧ record.digits.length≤fieldWidth x y
def BankBound (x y : Rat) (records : List RecordSpec) : Prop := ∀ r∈records,RecordBound x y r

theorem result_bound (x y : Rat) (gap value : Nat)
    (hg : gap≤2*allocationK*(fieldWidth x y)^2) (hv : natBits value≤fieldWidth x y) :
    RecordBound x y (resultRecord gap value) := by
  refine ⟨hg,?_⟩
  simpa only [resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn] using hv

theorem bank_nil (x y : Rat) : BankBound x y [] := by
  intro r hr
  exact False.elim (List.not_mem_nil hr)

theorem bank_cons (x y : Rat) (record : RecordSpec) (records : List RecordSpec)
    (head : RecordBound x y record) (tail : BankBound x y records) : BankBound x y (record::records) := by
  intro r hr
  rcases List.mem_cons.mp hr with equal | inside
  · subst r;exact head
  · exact tail r inside

theorem bank_sums (x y : Rat) (records : List RecordSpec) (hlen : records.length≤5)
    (bound : BankBound x y records) : totalGap records≤10*allocationK*(fieldWidth x y)^2 ∧
      totalWidth records≤5*fieldWidth x y := by
  obtain ⟨hg,hv⟩ := PA17TMRatArithmeticMulFields048.bank_sum_bounds records
    (2*allocationK*(fieldWidth x y)^2) (fieldWidth x y)
    (fun r hr => (bound r hr).1) (fun r hr => (bound r hr).2)
  constructor
  · calc
      _ ≤ records.length*(2*allocationK*(fieldWidth x y)^2) := hg
      _ ≤ 5*(2*allocationK*(fieldWidth x y)^2) := Nat.mul_le_mul_right _ hlen
      _ = _ := by ring
  · exact hv.trans (Nat.mul_le_mul_right _ hlen)

theorem allocation_run (total : Nat) (htotal : total≤4) (x y : Rat)
    (first : RecordSpec) (later : List RecordSpec) (hcount : (first::later).length=total)
    (bound : BankBound x y (first::later)) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryMachine 63 total allocationK)
      (carryEntry 63 total allocationK (actualMemory x y) (bankHeader x y (first::later))) trace
      (carryFinal 63 total allocationK (actualMemory x y) (bankWork x y first later (freshGap x y))) ∧
      trace.length≤allocationCoefficient*power x y := by
  obtain ⟨trace,run,time,_space⟩ := actual_allocation_contract 63 total (actualMemory x y)
    (first::later) hcount htotal x y (fun r hr => (bound r hr).1) (fun r hr => (bound r hr).2)
  rw [allocated_is_work] at run
  exact ⟨trace,run,time⟩

theorem original_run (x y : Rat) (first : RecordSpec) (later : List RecordSpec)
    (hcount : later.length=1) (bound : BankBound x y (first::later)) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalPairMachine 63 .dx .dy 1)
      (blockCfg (actualMemory x y) (⟨0,bankWork x y first later (freshGap x y)⟩ : MachineState (originalPairCap 1))) trace
      (blockCfg (actualMemory x y) (⟨originalPairPort 1,bankNative x y first later (freshGap x y) x.den y.den⟩ :
        MachineState (originalPairCap 1))) ∧ trace.length≤feeConstant allocationK*power x y := by
  have ha := actual_restored_with_carry .dx (actualMemory x y).val x y (actualMemory_retains_old x y)
  have hb := actual_restored_with_carry .dy (actualMemory x y).val x y (actualMemory_retains_old x y)
  obtain ⟨trace,run,time,_space⟩ := original_pair_contract 63 .dx .dy 1 (actualMemory x y) first later hcount
    (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail
    (denominatorDigits y).tail (freshGap x y) x.den y.den ha hb
  have fee := original_fee_polynomial allocationK 1 (by decide) (actualMemory x y).val x y first later hcount
    (fun r hr => (bound r hr).1) (fun r hr => (bound r hr).2)
  exact ⟨trace,run,time.trans fee⟩

theorem cached_run (j aLater bLater : Nat) (hj : j≤3) (x y : Rat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hcount : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (bound : BankBound x y (first::records)) (a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedPairMachine 63 j aLater bLater)
      (blockCfg (actualMemory x y) (⟨0,bankWork x y first records (freshGap x y)⟩ : MachineState (cachedPairCap j aLater bLater))) trace
      (blockCfg (actualMemory x y) (⟨cachedPairPort j aLater bLater,
        bankNative x y first records (freshGap x y) a b⟩ : MachineState (cachedPairCap j aLater bLater))) ∧
      trace.length≤feeConstant allocationK*power x y := by
  have hdA := ha.trans (canonical_head_tail a)
  have hdB := hb.trans (canonical_head_tail b)
  obtain ⟨trace,run,time,_space⟩ := cached_pair_contract 63 j aLater bLater (actualMemory x y) first
    records beforeA sourceA followingA beforeB sourceB followingB hcount hbankA haLater hbankB hbLater
    (PA17TMRatArithmeticPairEncode017.payload a).head! (PA17TMRatArithmeticPairEncode017.payload b).head!
    (PA17TMRatArithmeticPairEncode017.payload a).tail (PA17TMRatArithmeticPairEncode017.payload b).tail hdA hdB
    (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail
    (denominatorDigits y).tail (freshGap x y) a b ha hb
  have fee := (cached_fees_polynomial allocationK j aLater bLater (by omega) x y first records beforeA sourceA
    followingA beforeB sourceB followingB hcount hbankA haLater hbankB hbLater
    (fun r hr => (bound r hr).1) (fun r hr => (bound r hr).2) a b ha hb).1
  exact ⟨trace,run,time.trans fee⟩

/-- The actual WideCacheResult is supplied only by045's already-closed
native theorem. Its arbitrary final label is consumed by055's real home. -/
theorem native_run {states : Nat} (native : Machine states) (j : Nat) (hj : j≤3) (x y : Rat)
    (first : RecordSpec) (later : List RecordSpec) (hcount : later.length=j)
    (bound : BankBound x y (first::later)) (a b value : Nat)
    (hsize : PA17TMRatArithmeticNativeCache030.scale a b≤4*fieldWidth x y)
    (hvalue : natBits value≤fieldWidth x y)
    (actual : WideCacheResult native a b value
      (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
        (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) first later) (freshGap x y)) :
    ∃ gap trace, 6≤gap ∧ gap≤2*allocationK*(fieldWidth x y)^2 ∧
      PSTRTMSeq005.RunsFrom (carriedTailMachine 63 native j)
        (⟨carriedTailEntry 63 states j (actualMemory x y),bankNative x y first later (freshGap x y) a b⟩ :
          MachineState (carriedTailCap 63 states j)) trace
        (⟨carriedTailPort 63 states j (actualMemory x y),bankHeader x y (first::(later++[resultRecord gap value]))⟩ :
          MachineState (carriedTailCap 63 states j)) ∧ trace.length≤nativeCoefficient*power x y := by
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  obtain ⟨gap,trace,lower,upper,run,time,_space⟩ := carriedTail_contract 63 native j (actualMemory x y)
    first later hcount (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail (freshGap x y) a b value actual
  have ug := new_gap_bound a b (fieldWidth x y) gap hw hsize upper
  rw [←native_is_tail_input x y first later (freshGap x y) a b,tail_output_is_header] at run
  have hlen : (first::later).length≤5 := by simp only [List.length_cons,hcount];omega
  obtain ⟨hg,hv⟩ := bank_sums x y (first::later) hlen bound
  have width := original_source_width x y
  change PA17TMRatArithmeticWidth018.bankWidth (false::(numeratorDigits x).tail)
    (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail)
    (false::(denominatorDigits y).tail)=fieldWidth x y at width
  have fee := native_tail_fee_le j hj first later (false::(numeratorDigits x).tail)
    (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gap a b value (fieldWidth x y) ((encode [.rational x,.rational y]).length+1)
    hg hv ug hsize hvalue (by rw [width]) (by have h:=original_width_le_input x y;omega)
    (Nat.succ_le_succ (Nat.zero_le _))
  exact ⟨gap,trace,lower,ug,run,time.trans fee⟩

theorem row_entry (states : Nat) (code : Machine (totalStates 63 states)) (memory : Fin 64) (tape : Tape Bool) :
    (⟨(PA17TMRatArithmeticMulController057.row64Component states code).entry (widen64 memory),tape⟩ :
      MachineState (totalStates 63 states))=blockCfg memory (⟨0,tape⟩ : MachineState states) := by
  rw [row64_entry]
  rfl

theorem transfer_to (phase next : Fin 10) (hp : phase.val<9) (hn : nextPhase phase=next)
    (last : MachineState (component phase).states) (memory : Fin 128) (tape : Tape Bool)
    (halt : TM0.step (component phase).code last=none)
    (decode : (component phase).decode last.q=memory) (whole : last.Tape=tape) :
    TM0.step prefixMachine (liftCfg phase last)=some (entryCfg next memory tape) := by
  rw [paid_transfer phase hp last halt,hn,decode,whole]

attribute [local implicit_reducible] prefixCap allocationStates originalStates mulStates
  leftPairStates leftStates rightPairStates rightStates

theorem retarget_run_first {states : Nat} (code : Machine states)
    (first next last : MachineState states) (trace : List (MachineState states))
    (same : first=next) (run : PSTRTMSeq005.RunsFrom code first trace last) :
    PSTRTMSeq005.RunsFrom code next trace last := same ▸ run

theorem original_prefix_runs (x y : Rat) :
    ∃ gm gn ge gp gq trace, 6≤gm ∧ gm≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gn ∧ gn≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤ge ∧ ge≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gp ∧ gp≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gq ∧ gq≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs prefixMachine (encode [.rational x,.rational y]) trace (prefixFinal x y gm gn ge gp gq) ∧
      trace.length≤prefixTimeCoefficient*power x y := by
  let memory := actualMemory x y
  obtain ⟨gm,gn,t0,lm,um,ln,un,r0,len0⟩ := PA17TMRatArithmeticDivPrefix067.original_prefix_runs x y
  let m := resultRecord gm (leftMagnitude x y)
  let n := resultRecord gn (rightMagnitude x y)
  have bm : RecordBound x y m := result_bound x y gm _ um (left_bits x y)
  have bn : RecordBound x y n := result_bound x y gn _ un (right_bits x y)
  have b2 : BankBound x y [m,n] := bank_cons x y m [n] bm (bank_cons x y n [] bn (bank_nil x y))
  obtain ⟨t1,r1,len1⟩ := allocation_run 2 (by decide) x y m [n] rfl b2
  obtain ⟨t2,r2,len2⟩ := original_run x y m [n] rfl b2
  obtain ⟨_,_,sizeE,sizeP,sizeQ,_,_,_,_⟩ := nine_scales false x y
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  let arc2 := true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n]
  obtain ⟨ge,t3,le,ue,r3,len3⟩ := native_run PSTRTMNativeMul112.nativeMulMachine 1 (by decide) x y m [n] rfl b2
    x.den y.den (commonDenominator x y) sizeE (denominator_bits x y)
    (mul_allocated_runsFrom x.den y.den (fieldWidth x y) arc2 hw sizeE)
  let e := resultRecord ge (commonDenominator x y)
  have be : RecordBound x y e := result_bound x y ge _ ue (denominator_bits x y)
  have b3 : BankBound x y [m,n,e] := bank_cons x y m [n,e] bm
    (bank_cons x y n [e] bn (bank_cons x y e [] be (bank_nil x y)))
  obtain ⟨t4,r4,len4⟩ := allocation_run 3 (by decide) x y m [n,e] rfl b3
  obtain ⟨t5,r5,len5⟩ := cached_run 2 2 1 (by decide) x y m [n,e] [] m [n,e] [m] n [e]
    rfl rfl rfl rfl rfl b3 (leftMagnitude x y) (rightMagnitude x y) rfl rfl
  let arc3 := true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e]
  obtain ⟨gp,t6,lp,up,r6,len6⟩ := native_run PA17TMRatArithmeticSub016.nativeSubMachine 2 (by decide) x y m [n,e] rfl b3
    (leftMagnitude x y) (rightMagnitude x y) (leftDifference x y) sizeP (difference_bits x y).1
    (sub_allocated_runsFrom (leftMagnitude x y) (rightMagnitude x y) (fieldWidth x y) arc3 hw sizeP)
  let p := resultRecord gp (leftDifference x y)
  have bp : RecordBound x y p := result_bound x y gp _ up (difference_bits x y).1
  have b4 : BankBound x y [m,n,e,p] := bank_cons x y m [n,e,p] bm
    (bank_cons x y n [e,p] bn (bank_cons x y e [p] be (bank_cons x y p [] bp (bank_nil x y))))
  obtain ⟨t7,r7,len7⟩ := allocation_run 4 (by decide) x y m [n,e,p] rfl b4
  obtain ⟨t8,r8,len8⟩ := cached_run 3 2 3 (by decide) x y m [n,e,p] [m] n [e,p] [] m [n,e,p]
    rfl rfl rfl rfl rfl b4 (rightMagnitude x y) (leftMagnitude x y) rfl rfl
  let arc4 := true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e,p]
  obtain ⟨gq,t9,lq,uq,r9,len9⟩ := native_run PA17TMRatArithmeticSub016.nativeSubMachine 3 (by decide) x y m [n,e,p] rfl b4
    (rightMagnitude x y) (leftMagnitude x y) (rightDifference x y) sizeQ (difference_bits x y).2
    (sub_allocated_runsFrom (rightMagnitude x y) (leftMagnitude x y) (fieldWidth x y) arc4 hw sizeQ)
  let q := resultRecord gq (rightDifference x y)
  let end0 : MachineState (component (0 : Fin 10)).states := PA17TMRatArithmeticDivPrefix067.prefixFinal x y gm gn
  let end1 : MachineState (component (1 : Fin 10)).states := carryFinal 63 2 allocationK memory (bankWork x y m [n] (freshGap x y))
  let end2 : MachineState (component (2 : Fin 10)).states := blockCfg memory
    (⟨originalPairPort 1,bankNative x y m [n] (freshGap x y) x.den y.den⟩ : MachineState (originalPairCap 1))
  let end3 : MachineState mulStates := ⟨carriedTailPort 63 982 1 memory,bankHeader x y [m,n,e]⟩
  let end4 : MachineState (component (4 : Fin 10)).states := carryFinal 63 3 allocationK memory (bankWork x y m [n,e] (freshGap x y))
  let end5 : MachineState (component (5 : Fin 10)).states := blockCfg memory
    (⟨cachedPairPort 2 2 1,bankNative x y m [n,e] (freshGap x y) (leftMagnitude x y) (rightMagnitude x y)⟩ :
      MachineState (cachedPairCap 2 2 1))
  let end6 : MachineState leftStates := ⟨carriedTailPort 63 596 2 memory,bankHeader x y [m,n,e,p]⟩
  let end7 : MachineState (component (7 : Fin 10)).states := carryFinal 63 4 allocationK memory (bankWork x y m [n,e,p] (freshGap x y))
  let end8 : MachineState (component (8 : Fin 10)).states := blockCfg memory
    (⟨cachedPairPort 3 2 3,bankNative x y m [n,e,p] (freshGap x y) (rightMagnitude x y) (leftMagnitude x y)⟩ :
      MachineState (cachedPairCap 3 2 3))
  let end9 : MachineState rightStates := ⟨carriedTailPort 63 596 3 memory,bankHeader x y [m,n,e,p,q]⟩
  have start1 := row_entry (outerCap 2 allocationK) (carryMachine 63 2 allocationK) memory (bankHeader x y [m,n])
  have start2 := row_entry (originalPairCap 1) (originalPairMachine 63 .dx .dy 1) memory (bankWork x y m [n] (freshGap x y))
  have start3 := row_entry (tailCap 982 1) (carriedTailMachine 63 PSTRTMNativeMul112.nativeMulMachine 1) memory
    (bankNative x y m [n] (freshGap x y) x.den y.den)
  have start4 := row_entry (outerCap 3 allocationK) (carryMachine 63 3 allocationK) memory (bankHeader x y [m,n,e])
  have start5 := row_entry (cachedPairCap 2 2 1) (cachedPairMachine 63 2 2 1) memory (bankWork x y m [n,e] (freshGap x y))
  have start6 := row_entry (tailCap 596 2) (carriedTailMachine 63 PA17TMRatArithmeticSub016.nativeSubMachine 2) memory
    (bankNative x y m [n,e] (freshGap x y) (leftMagnitude x y) (rightMagnitude x y))
  have start7 := row_entry (outerCap 4 allocationK) (carryMachine 63 4 allocationK) memory (bankHeader x y [m,n,e,p])
  have start8 := row_entry (cachedPairCap 3 2 3) (cachedPairMachine 63 3 2 3) memory (bankWork x y m [n,e,p] (freshGap x y))
  have start9 := row_entry (tailCap 596 3) (carriedTailMachine 63 PA17TMRatArithmeticSub016.nativeSubMachine 3) memory
    (bankNative x y m [n,e,p] (freshGap x y) (rightMagnitude x y) (leftMagnitude x y))
  have r0From : PSTRTMSeq005.RunsFrom (component (0 : Fin 10)).code (TM0.init (encode [.rational x,.rational y])) t0 end0 :=
    ⟨r0.1,r0.2.1,r0.2.2.1,r0.2.2.2.1⟩
  have enter0 : entryCfg (1 : Fin 10) ((component (0 : Fin 10)).decode end0.q) (bankHeader x y [m,n])=
      entryCfg (1 : Fin 10) (widen64 memory) (bankHeader x y [m,n]) :=
    congrArg (fun saved : Fin 64 => liftCfg (1 : Fin 10)
      (carryEntry 63 2 allocationK saved (bankHeader x y [m,n])))
      ((first_memory_narrow x y gm gn).trans (PA17TMRatArithmeticMulController057.narrow_widen memory).symm)
  have step0raw := paid_transfer (0 : Fin 10) (by decide) end0 r0From.2.2.2
  have step0 : TM0.step prefixMachine (liftCfg (0 : Fin 10) end0)=
      some (entryCfg (1 : Fin 10) (widen64 memory) (bankHeader x y [m,n])) :=
    step0raw.trans (congrArg some enter0)
  have rr1 := retarget_run_first (states:=allocationStates 2) (carryMachine 63 2 allocationK) _ _ _ _ start1.symm r1
  change PSTRTMSeq005.RunsFrom (component (1 : Fin 10)).code _ t1 end1 at rr1
  have d1 : (component (1 : Fin 10)).decode end1.q=widen64 memory :=
    row64_decode (outerCap 2 allocationK) (carryMachine 63 2 allocationK) memory (outerPort 2 allocationK)
  have step1 := transfer_to 1 2 (by decide) (by decide) end1 (widen64 memory) _ rr1.2.2.2 d1 rfl
  have rr2 := retarget_run_first (states:=originalStates) (originalPairMachine 63 .dx .dy 1) _ _ _ _ start2.symm r2
  change PSTRTMSeq005.RunsFrom (component (2 : Fin 10)).code _ t2 end2 at rr2
  have d2 : (component (2 : Fin 10)).decode end2.q=widen64 memory :=
    row64_decode (originalPairCap 1) (originalPairMachine 63 .dx .dy 1) memory (originalPairPort 1)
  have step2 := transfer_to 2 3 (by decide) (by decide) end2 (widen64 memory) _ rr2.2.2.2 d2 rfl
  have rr3 := retarget_run_first (states:=mulStates) (carriedTailMachine 63 PSTRTMNativeMul112.nativeMulMachine 1)
    _ _ _ _ start3.symm r3
  change PSTRTMSeq005.RunsFrom (component (3 : Fin 10)).code _ t3 end3 at rr3
  have d3 : (component (3 : Fin 10)).decode end3.q=widen64 memory :=
    row64_decode (tailCap 982 1) (carriedTailMachine 63 PSTRTMNativeMul112.nativeMulMachine 1) memory (tailPort 982 1)
  have step3 := transfer_to 3 4 (by decide) (by decide) end3 (widen64 memory) _ rr3.2.2.2 d3 rfl
  have rr4 := retarget_run_first (states:=allocationStates 3) (carryMachine 63 3 allocationK) _ _ _ _ start4.symm r4
  change PSTRTMSeq005.RunsFrom (component (4 : Fin 10)).code _ t4 end4 at rr4
  have d4 : (component (4 : Fin 10)).decode end4.q=widen64 memory :=
    row64_decode (outerCap 3 allocationK) (carryMachine 63 3 allocationK) memory (outerPort 3 allocationK)
  have step4 := transfer_to 4 5 (by decide) (by decide) end4 (widen64 memory) _ rr4.2.2.2 d4 rfl
  have rr5 := retarget_run_first (states:=leftPairStates) (cachedPairMachine 63 2 2 1) _ _ _ _ start5.symm r5
  change PSTRTMSeq005.RunsFrom (component (5 : Fin 10)).code _ t5 end5 at rr5
  have d5 : (component (5 : Fin 10)).decode end5.q=widen64 memory :=
    row64_decode (cachedPairCap 2 2 1) (cachedPairMachine 63 2 2 1) memory (cachedPairPort 2 2 1)
  have step5 := transfer_to 5 6 (by decide) (by decide) end5 (widen64 memory) _ rr5.2.2.2 d5 rfl
  have rr6 := retarget_run_first (states:=leftStates) (carriedTailMachine 63 PA17TMRatArithmeticSub016.nativeSubMachine 2)
    _ _ _ _ start6.symm r6
  change PSTRTMSeq005.RunsFrom (component (6 : Fin 10)).code _ t6 end6 at rr6
  have d6 : (component (6 : Fin 10)).decode end6.q=widen64 memory :=
    row64_decode (tailCap 596 2) (carriedTailMachine 63 PA17TMRatArithmeticSub016.nativeSubMachine 2) memory (tailPort 596 2)
  have step6 := transfer_to 6 7 (by decide) (by decide) end6 (widen64 memory) _ rr6.2.2.2 d6 rfl
  have rr7 := retarget_run_first (states:=allocationStates 4) (carryMachine 63 4 allocationK) _ _ _ _ start7.symm r7
  change PSTRTMSeq005.RunsFrom (component (7 : Fin 10)).code _ t7 end7 at rr7
  have d7 : (component (7 : Fin 10)).decode end7.q=widen64 memory :=
    row64_decode (outerCap 4 allocationK) (carryMachine 63 4 allocationK) memory (outerPort 4 allocationK)
  have step7 := transfer_to 7 8 (by decide) (by decide) end7 (widen64 memory) _ rr7.2.2.2 d7 rfl
  have rr8 := retarget_run_first (states:=rightPairStates) (cachedPairMachine 63 3 2 3) _ _ _ _ start8.symm r8
  change PSTRTMSeq005.RunsFrom (component (8 : Fin 10)).code _ t8 end8 at rr8
  have d8 : (component (8 : Fin 10)).decode end8.q=widen64 memory :=
    row64_decode (cachedPairCap 3 2 3) (cachedPairMachine 63 3 2 3) memory (cachedPairPort 3 2 3)
  have step8 := transfer_to 8 9 (by decide) (by decide) end8 (widen64 memory) _ rr8.2.2.2 d8 rfl
  have rr9 := retarget_run_first (states:=rightStates) (carriedTailMachine 63 PA17TMRatArithmeticSub016.nativeSubMachine 3)
    _ _ _ _ start9.symm r9
  change PSTRTMSeq005.RunsFrom (component (9 : Fin 10)).code _ t9 end9 at rr9
  have s0raw := component_segment 0 _ _ _ r0From
  have s0 := retarget_first (states:=prefixCap) prefixMachine _ _ _ _ (initial_mapped (encode [.rational x,.rational y])) s0raw
  have s1 := component_segment 1 _ _ _ rr1
  have s2 := component_segment 2 _ _ _ rr2
  have s3 := component_segment 3 _ _ _ rr3
  have s4 := component_segment 4 _ _ _ rr4
  have s5 := component_segment 5 _ _ _ rr5
  have s6 := component_segment 6 _ _ _ rr6
  have s7 := component_segment 7 _ _ _ rr7
  have s8 := component_segment 8 _ _ _ rr8
  have s9 := component_segment 9 _ _ _ rr9
  have join1 := segment_append prefixMachine _ _ _ _ _ _ s0 s1 step0
  have join2 := segment_append prefixMachine _ _ _ _ _ _ join1 s2 step1
  have join3 := segment_append prefixMachine _ _ _ _ _ _ join2 s3 step2
  have join4 := segment_append prefixMachine _ _ _ _ _ _ join3 s4 step3
  have join5 := segment_append prefixMachine _ _ _ _ _ _ join4 s5 step4
  have join6 := segment_append prefixMachine _ _ _ _ _ _ join5 s6 step5
  have join7 := segment_append prefixMachine _ _ _ _ _ _ join6 s7 step6
  have join8 := segment_append prefixMachine _ _ _ _ _ _ join7 s8 step7
  have joined := segment_append prefixMachine _ _ _ _ _ _ join8 s9 step8
  have halted := final_halt end9 rr9.2.2.2
  have last9 : liftCfg (9 : Fin 10) end9=prefixFinal x y gm gn ge gp gq := rfl
  have doneRun := retarget_last (states:=prefixCap) prefixMachine _ _ _ _ last9 joined
  have doneHalt : TM0.step prefixMachine (prefixFinal x y gm gn ge gp gq)=none :=
    (congrArg (TM0.step prefixMachine) last9).symm.trans halted
  let trace := ((((((((liftTrace 0 t0++liftTrace 1 t1)++liftTrace 2 t2)++liftTrace 3 t3)++liftTrace 4 t4)++
    liftTrace 5 t5)++liftTrace 6 t6)++liftTrace 7 t7)++liftTrace 8 t8)++liftTrace 9 t9
  have actual : Runs prefixMachine (encode [.rational x,.rational y]) trace (prefixFinal x y gm gn ge gp gq) :=
    PSTRTMTrace002.runs_of_chain _ _ _ _ doneRun.1 doneRun.2.1 doneRun.2.2 doneHalt
  refine ⟨gm,gn,ge,gp,gq,trace,lm,um,ln,un,le,ue,lp,up,lq,uq,actual,?_⟩
  simp only [trace,List.length_append]
  rw [liftTrace_length (0 : Fin 10) t0,liftTrace_length (1 : Fin 10) t1,liftTrace_length (2 : Fin 10) t2,
    liftTrace_length (3 : Fin 10) t3,liftTrace_length (4 : Fin 10) t4,liftTrace_length (5 : Fin 10) t5,
    liftTrace_length (6 : Fin 10) t6,liftTrace_length (7 : Fin 10) t7,liftTrace_length (8 : Fin 10) t8,
    liftTrace_length (9 : Fin 10) t9]
  change t0.length≤PA17TMRatArithmeticDivPrefix067.prefixTimeCoefficient*power x y at len0
  calc
    _ ≤ ((((((((PA17TMRatArithmeticDivPrefix067.prefixTimeCoefficient*power x y+allocationCoefficient*power x y)+
        feeConstant allocationK*power x y)+nativeCoefficient*power x y)+allocationCoefficient*power x y)+
        feeConstant allocationK*power x y)+nativeCoefficient*power x y)+allocationCoefficient*power x y)+
        feeConstant allocationK*power x y)+nativeCoefficient*power x y :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add len0 len1) len2) len3) len4) len5) len6) len7) len8) len9
    _ = prefixTimeCoefficient*power x y := by unfold prefixTimeCoefficient;ring

theorem original_prefix_contract (x y : Rat) :
    ∃ gm gn ge gp gq trace, 6≤gm ∧ gm≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gn ∧ gn≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤ge ∧ ge≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gp ∧ gp≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gq ∧ gq≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs prefixMachine (encode [.rational x,.rational y]) trace (prefixFinal x y gm gn ge gp gq) ∧
      trace.length≤prefixResourceCoefficient*power x y ∧
      ∀ n,visitedSpace prefixMachine (encode [.rational x,.rational y]).length (trace.take n)≤
        prefixResourceCoefficient*power x y := by
  obtain ⟨gm,gn,ge,gp,gq,trace,lm,um,ln,un,le,ue,lp,up,lq,uq,run,time⟩ := original_prefix_runs x y
  let i := (encode [.rational x,.rational y]).length
  have hi : i+1≤(i+1)^4 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le i)) (by decide : 1≤4))
  have hc : prefixTimeCoefficient≤prefixResourceCoefficient := by unfold prefixResourceCoefficient;omega
  refine ⟨gm,gn,ge,gp,gq,trace,lm,um,ln,un,le,ue,lp,up,lq,uq,run,time.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro n
  have cells := PSTRTMTrace002.visitedSpace_le prefixMachine i (trace.take n)
  have taken : (trace.take n).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  change trace.length≤prefixTimeCoefficient*(i+1)^4 at time
  change visitedSpace prefixMachine i (trace.take n)≤prefixResourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take n).length+1 := cells
    _ ≤ i+2*(prefixTimeCoefficient*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(prefixTimeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(prefixTimeCoefficient*(i+1)^4) := Nat.add_le_add_right hi _
    _ = (2*prefixTimeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ prefixResourceCoefficient*(i+1)^4 := Nat.mul_le_mul_right _ (by unfold prefixResourceCoefficient;omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubPrefix074
