module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038c
public import Structure.PA17_TM_RatArithmetic_FlagZero_028b
public import Structure.PA17_TM_RatArithmetic_ReturnHome_037b
public import Structure.PA17_TM_Division_Compose_006a
public import Structure.PA17_TM_RatArithmetic_NativeTail_055a
public import Structure.PA17_TM_RatArithmetic_MulStart_049d
public import Structure.PA17_TM_RatArithmetic_MulFields_048a

/-! Consolidated coherent Uzero/carry ABI. Historical a-d drafts are retained
UNRUN and are not imports. No earlier source/product is rewritten. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticZeroCarry058

/-! Observe the real canonical U cache before selecting an output sign.
The incoming six control bits and the actually observed zero bit occupy
fixed finite rows. Neither the value U nor a zero flag is supplied to code. -/

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticReturnHome037 PA17TMRatArithmeticFlagZero028

def readCap (sourceLater : Nat) : Nat := cachedBackCap sourceLater+9+1

def readMachine (sourceLater : Nat) : Machine (readCap sourceLater) :=
  PSTRTMSeq005.seqMachine (cachedBackMachine sourceLater) zeroMachine

def readPort (sourceLater : Nat) (u : Nat) : Fin (readCap sourceLater+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedBackCap sourceLater) (chosenPort u)

def readZeroPort (sourceLater : Nat) : Fin (readCap sourceLater+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedBackCap sourceLater) zeroPort

def returnCap (sourceLater allLater : Nat) : Nat := cachedOutCap sourceLater+homeCap allLater+1

def returnMachine (sourceLater allLater : Nat) : Machine (returnCap sourceLater allLater) :=
  PSTRTMSeq005.seqMachine (cachedOutMachine sourceLater) (returnHomeMachine allLater)

def returnPort (sourceLater allLater : Nat) : Fin (returnCap sourceLater allLater+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedOutCap sourceLater) (homePort allLater)

def commonCap (sourceLater allLater : Nat) : Nat := readCap sourceLater+returnCap sourceLater allLater

theorem readFits (sourceLater allLater : Nat) : readCap sourceLater≤commonCap sourceLater allLater := by
  unfold commonCap;omega

theorem returnFits (sourceLater allLater : Nat) : returnCap sourceLater allLater≤commonCap sourceLater allLater := by
  unfold commonCap;omega

def observedMemory (memory : Fin 64) (isZero : Bool) : Fin 128 :=
  ⟨memory.val+(if isZero then 64 else 0),by split <;> omega⟩

def oldPhase (memory : Fin 64) : Fin 192 := ⟨memory.val,by omega⟩

def newPhase (memory : Fin 128) : Fin 192 := ⟨64+memory.val,by omega⟩

def observeFamily (sourceLater allLater : Nat) (phase : Fin 192) :
    Machine (commonCap sourceLater allLater) :=
  if phase.val<64 then padMachine (readFits sourceLater allLater) (readMachine sourceLater)
  else padMachine (returnFits sourceLater allLater) (returnMachine sourceLater allLater)

def observePorts (sourceLater allLater : Nat) (phase : Fin 192)
    (q : Fin (commonCap sourceLater allLater+1)) :
    Option (Fin 192 × Fin (commonCap sourceLater allLater+1)) :=
  if h : phase.val<64 then
    some (newPhase (observedMemory ⟨phase.val,h⟩ (decide (q.val=(readZeroPort sourceLater).val))),0)
  else none

def observeCap (sourceLater allLater : Nat) : Nat := totalStates 191 (commonCap sourceLater allLater)
attribute [local implicit_reducible] observeCap totalStates

def observeMachine (sourceLater allLater : Nat) : Machine (observeCap sourceLater allLater) :=
  blockMachine (observeFamily sourceLater allLater) (observePorts sourceLater allLater)

def observeEntry (sourceLater allLater : Nat) (memory : Fin 64) : Fin (observeCap sourceLater allLater+1) :=
  label (oldPhase memory) (padLabel (readFits sourceLater allLater) (0 : Fin (readCap sourceLater+1)))

def observePort (sourceLater allLater : Nat) (memory : Fin 128) : Fin (observeCap sourceLater allLater+1) :=
  label (newPhase memory) (padLabel (returnFits sourceLater allLater) (returnPort sourceLater allLater))

theorem observedMemory_retains_old (memory : Fin 64) (isZero : Bool) :
    (observedMemory memory isZero).val%64=memory.val := by
  cases isZero with
  | false => change memory.val%64=memory.val;exact Nat.mod_eq_of_lt memory.isLt
  | true => change (memory.val+64)%64=memory.val;omega

theorem observedMemory_zero_bit (memory : Fin 64) (isZero : Bool) :
    (observedMemory memory isZero).val/64=(if isZero then 1 else 0) := by
  cases isZero with
  | false => change memory.val/64=0;omega
  | true => change (memory.val+64)/64=1;omega

theorem family_old (sourceLater allLater : Nat) (memory : Fin 64) :
    observeFamily sourceLater allLater (oldPhase memory)=
      padMachine (readFits sourceLater allLater) (readMachine sourceLater) := by
  unfold observeFamily
  exact ite_eq_left memory.isLt

theorem family_new (sourceLater allLater : Nat) (memory : Fin 128) :
    observeFamily sourceLater allLater (newPhase memory)=
      padMachine (returnFits sourceLater allLater) (returnMachine sourceLater allLater) := by
  have h : ¬(newPhase memory).val<64 := by change ¬64+memory.val<64;omega
  simp only [observeFamily,ite_eq_right h]

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticReturnHome037 PA17TMRatArithmeticFlagZero028
attribute [local implicit_reducible] readCap returnCap commonCap

theorem readPort_zero_iff (sourceLater u : Nat) :
    (readPort sourceLater u).val=(readZeroPort sourceLater).val ↔ u=0 := by
  have h6 : zeroPort.val=6 := by decide
  have h9 : nonzeroPort.val=9 := by decide
  by_cases hz : u=0
  · have eqPort : readPort sourceLater u=readZeroPort sourceLater := by
      unfold readPort chosenPort
      rw [ite_eq_left hz]
      rfl
    exact iff_of_true (congrArg Fin.val eqPort) hz
  · simp only [readPort,readZeroPort,chosenPort,ite_eq_right hz,PSTRTMSeq005.rightLabel,h6,h9]
    omega

/-- The cache is canonical because it was actually written by Store019.
Both cachedBack and028 preserve every field, flag and suffix, and028's
chosen port is reached by its physical read, not by inspecting u in code. -/
theorem read_bounded (sourceLater : Nat) (following : List RecordSpec)
    (hj : following.length=sourceLater) (archive : List Bool) (u : Nat) (suffix : List Bool) :
    BoundedRun (readMachine sourceLater)
      (Tape.mk₂ (cachedFinish following (false::archive) (PSTRTMNatValue017.rawPayload u)) (true::suffix))
      (readPort sourceLater u)
      (Tape.mk₂ (false::archive) (cachedWord following (PSTRTMNatValue017.rawPayload u) suffix))
      (2*natBits u+totalGap following+2*totalWidth following+12*sourceLater+15) := by
  have back := cached_back_bounded sourceLater following hj archive (PSTRTMNatValue017.rawPayload u) suffix
  have sensor : BoundedRun zeroMachine
      (Tape.mk₂ (false::archive) (cachedWord following (PSTRTMNatValue017.rawPayload u) suffix))
      (chosenPort u)
      (Tape.mk₂ (false::archive) (cachedWord following (PSTRTMNatValue017.rawPayload u) suffix)) 7 := by
    refine ⟨canonicalTrace (false::archive) u (true::bankTail following suffix),?_,
      canonicalTrace_length_le _ _ _⟩
    simpa only [canonicalInitial,canonicalFinal,PA17TMRatArithmeticFlagZero028.state,cacheWord,cachedWord,cacheContext_word] using
      canonical_runsFrom (false::archive) u (true::bankTail following suffix)
  have combined : BoundedRun (s:=readCap sourceLater) _ _ _ _ _ := back.seq sensor
  change BoundedRun (s:=readCap sourceLater) (readMachine sourceLater)
    (Tape.mk₂ (cachedFinish following (false::archive) (PSTRTMNatValue017.rawPayload u)) (true::suffix))
    (readPort sourceLater u)
    (Tape.mk₂ (false::archive) (cachedWord following (PSTRTMNatValue017.rawPayload u) suffix)) _ at combined
  apply combined.mono
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]; omega

theorem observed_dispatch (sourceLater allLater : Nat) (memory : Fin 64) (u : Nat) :
    observePorts sourceLater allLater (oldPhase memory)
      (padLabel (readFits sourceLater allLater) (readPort sourceLater u))=
      some (newPhase (observedMemory memory (decide (u=0))),0) := by
  have h : decide ((readPort sourceLater u).val=(readZeroPort sourceLater).val)=decide (u=0) := by
    simp only [readPort_zero_iff]
  unfold observePorts
  change (if h' : memory.val<64 then
    some (newPhase (observedMemory ⟨memory.val,h'⟩
      (decide ((readPort sourceLater u).val=(readZeroPort sourceLater).val))),0) else none)=_
  rw [dite_eq_left memory.isLt]
  change some (newPhase (observedMemory memory
    (decide ((readPort sourceLater u).val=(readZeroPort sourceLater).val))),0)=_
  rw [h]

theorem observed_stop (sourceLater allLater : Nat) (memory : Fin 128)
    (q : Fin (commonCap sourceLater allLater+1)) :
    observePorts sourceLater allLater (newPhase memory) q=none := by
  have h : ¬(newPhase memory).val<64 := by change ¬64+memory.val<64;omega
  simp only [observePorts,dite_eq_right h]

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticReturnHome037 PA17TMRatArithmeticFlagZero028
open PA17TMRatArithmeticNativeTail055 (bankLeft_append resultRecord)

def sourceArchive (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (before : List RecordSpec) (sourceGap : Nat) : List Bool :=
  true::(List.replicate sourceGap false++true::bankLeft (firstLeft sx counter nx dx ny dy first) before)

def observedRecords (before following : List RecordSpec) (sourceGap u : Nat) : List RecordSpec :=
  before++resultRecord sourceGap u::following

theorem observer_latest (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (before following : List RecordSpec) (sourceGap u : Nat) :
    Tape.mk₂ (cachedFinish following
      (false::sourceArchive sx counter nx dx ny dy first before sourceGap) (PSTRTMNatValue017.rawPayload u)) [true]=
      homeInput sx counter nx dx ny dy first (observedRecords before following sourceGap u) [] := by
  simp only [homeInput,bankEnd,observedRecords,bankLeft_append,bankLeft]
  rfl

def readFee (sourceLater : Nat) (following : List RecordSpec) (u : Nat) : Nat :=
  2*natBits u+totalGap following+2*totalWidth following+12*sourceLater+15

def returnFee (sourceLater allLater : Nat) (first : RecordSpec) (before following : List RecordSpec)
    (nx dx ny dy : List Bool) (sourceGap u : Nat) : Nat :=
  (2*natBits u+totalGap following+2*totalWidth following+9*sourceLater+5)+
    (totalGap (first::observedRecords before following sourceGap u)+
      2*totalWidth (first::observedRecords before following sourceGap u)+12*allLater+
      2*bankWidth nx dx ny dy+49)

def observeFee (sourceLater allLater : Nat) (first : RecordSpec) (before following : List RecordSpec)
    (nx dx ny dy : List Bool) (sourceGap u : Nat) : Nat :=
  readFee sourceLater following u+returnFee sourceLater allLater first before following nx dx ny dy sourceGap u+1

theorem return_bounded (sourceLater allLater : Nat) (first : RecordSpec) (before following : List RecordSpec)
    (sourceGap u : Nat)
    (hj : following.length=sourceLater) (hall : (observedRecords before following sourceGap u).length=allLater)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) :
    BoundedRun (returnMachine sourceLater allLater)
      (Tape.mk₂ (false::sourceArchive sx counter nx dx ny (false::dyTail) first before sourceGap)
        (cachedWord following (PSTRTMNatValue017.rawPayload u) []))
      (returnPort sourceLater allLater)
      (homeOutput sx counter nx dx ny (false::dyTail) first (observedRecords before following sourceGap u) [])
      (returnFee sourceLater allLater first before following nx dx ny (false::dyTail) sourceGap u) := by
  have out := cached_out_bounded sourceLater following hj
    (false::sourceArchive sx counter nx dx ny (false::dyTail) first before sourceGap)
    (PSTRTMNatValue017.rawPayload u) []
  have home := returnHome_bounded allLater first (observedRecords before following sourceGap u) hall
    sx counter nx dx ny dyTail []
  rw [←observer_latest sx counter nx dx ny (false::dyTail) first before following sourceGap u] at home
  have combined : BoundedRun (s:=returnCap sourceLater allLater) _ _ _ _ _ := out.seq home
  change BoundedRun (s:=returnCap sourceLater allLater) (returnMachine sourceLater allLater)
    (Tape.mk₂ (false::sourceArchive sx counter nx dx ny (false::dyTail) first before sourceGap)
      (cachedWord following (PSTRTMNatValue017.rawPayload u) []))
    (returnPort sourceLater allLater)
    (homeOutput sx counter nx dx ny (false::dyTail) first (observedRecords before following sourceGap u) []) _ at combined
  apply combined.mono
  simp only [returnFee,PSTRTMNatValue017.rawPayload,List.length_ofFn]; omega

/-- All seven bits are real finite control: the incoming six observations
survive; the seventh comes from the028 port after physically returning to
the selected canonical cache. Every old record and original cell survives. -/
theorem observe_contract (sourceLater allLater : Nat) (memory : Fin 64)
    (first : RecordSpec) (before following : List RecordSpec) (sourceGap u : Nat)
    (hj : following.length=sourceLater) (hall : (observedRecords before following sourceGap u).length=allLater)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (observeMachine sourceLater allLater)
        ⟨observeEntry sourceLater allLater memory,
          homeInput sx counter nx dx ny (false::dyTail) first (observedRecords before following sourceGap u) []⟩ trace
        ⟨observePort sourceLater allLater (observedMemory memory (decide (u=0))),
          homeOutput sx counter nx dx ny (false::dyTail) first (observedRecords before following sourceGap u) []⟩ ∧
      trace.length≤observeFee sourceLater allLater first before following nx dx ny (false::dyTail) sourceGap u ∧
      ∀ prefixLength chargedL, visitedSpace (observeMachine sourceLater allLater) chargedL (trace.take prefixLength)≤
        chargedL+2*observeFee sourceLater allLater first before following nx dx ny (false::dyTail) sourceGap u+1 := by
  let input := homeInput sx counter nx dx ny (false::dyTail) first (observedRecords before following sourceGap u) []
  let middle := Tape.mk₂ (false::sourceArchive sx counter nx dx ny (false::dyTail) first before sourceGap)
    (cachedWord following (PSTRTMNatValue017.rawPayload u) [])
  let output := homeOutput sx counter nx dx ny (false::dyTail) first (observedRecords before following sourceGap u) []
  let selected := observedMemory memory (decide (u=0))
  obtain ⟨tr,hr,hlr⟩ := read_bounded sourceLater following hj
    (sourceArchive sx counter nx dx ny (false::dyTail) first before sourceGap) u []
  rw [observer_latest sx counter nx dx ny (false::dyTail) first before following sourceGap u] at hr
  obtain ⟨tt,ht,hlt⟩ := return_bounded sourceLater allLater first before following sourceGap u hj hall
    sx counter nx dx ny dyTail
  have rp := pad_runsFrom (readFits sourceLater allLater) (readMachine sourceLater)
    (⟨0,input⟩ : MachineState (readCap sourceLater)) ⟨readPort sourceLater u,middle⟩ tr hr
  have tp := pad_runsFrom (returnFits sourceLater allLater) (returnMachine sourceLater allLater)
    (⟨0,middle⟩ : MachineState (returnCap sourceLater allLater)) ⟨returnPort sourceLater allLater,output⟩ tt ht
  have rf : PSTRTMSeq005.RunsFrom (observeFamily sourceLater allLater (oldPhase memory))
      (padCfg (readFits sourceLater allLater) ⟨0,input⟩) (tr.map (padCfg (readFits sourceLater allLater)))
      (padCfg (readFits sourceLater allLater) ⟨readPort sourceLater u,middle⟩) := by
    rw [family_old];exact rp
  have tf : PSTRTMSeq005.RunsFrom (observeFamily sourceLater allLater (newPhase selected))
      (padCfg (returnFits sourceLater allLater) ⟨0,middle⟩) (tt.map (padCfg (returnFits sourceLater allLater)))
      (padCfg (returnFits sourceLater allLater) ⟨returnPort sourceLater allLater,output⟩) := by
    rw [family_new];exact tp
  have rs := block_segment (observeFamily sourceLater allLater) (observePorts sourceLater allLater)
    (oldPhase memory) _ _ _ rf
  have ts := block_segment (observeFamily sourceLater allLater) (observePorts sourceLater allLater)
    (newPhase selected) _ _ _ tf
  have transfer := block_transfer (observeFamily sourceLater allLater) (observePorts sourceLater allLater)
    (oldPhase memory) (padCfg (readFits sourceLater allLater) ⟨readPort sourceLater u,middle⟩)
    (newPhase selected,0) rf.2.2.2 (observed_dispatch sourceLater allLater memory u)
  have joined := segment_append (observeMachine sourceLater allLater) _ _ _ _ _ _ rs ts transfer
  have halted := block_halt (observeFamily sourceLater allLater) (observePorts sourceLater allLater)
    (newPhase selected) (padCfg (returnFits sourceLater allLater) ⟨returnPort sourceLater allLater,output⟩)
    tf.2.2.2 (observed_stop sourceLater allLater selected _)
  have run := segment_runsFrom (observeMachine sourceLater allLater) _ _ _ joined halted
  let trace := (tr.map (padCfg (readFits sourceLater allLater))).map (blockCfg (oldPhase memory))++
    (tt.map (padCfg (returnFits sourceLater allLater))).map (blockCfg (newPhase selected))
  have length : trace.length≤observeFee sourceLater allLater first before following nx dx ny (false::dyTail) sourceGap u := by
    simp only [trace,List.length_append,List.length_map]
    change _≤readFee sourceLater following u+returnFee sourceLater allLater first before following nx dx ny (false::dyTail) sourceGap u+1
    change tr.length≤readFee sourceLater following u at hlr
    omega
  refine ⟨trace,?_,length,?_⟩
  · simpa only [observeEntry,observePort,padCfg,blockCfg,selected] using run
  · intro prefixLength chargedL
    have hs := PSTRTMTrace002.visitedSpace_le (observeMachine sourceLater allLater) chargedL (trace.take prefixLength)
    have ht : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
    omega

open PA17TMRatArithmeticSignRead021 PA17TMRatArithmeticMulStart049
open PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticMulFields048

/-- A finite table on an actually reached row. Bit6 comes from028,
bit5 from021, and bit2 from014's actual SY read. Bit0 is the Dy LSB. -/
def repairedNegative (memory : Fin 128) : Bool :=
  if memory.val.testBit 6 then false else Bool.xor (memory.val.testBit 5) (memory.val.testBit 2)

theorem observed_negative_table (memory : Fin 64) (isZero : Bool) :
    repairedNegative (observedMemory memory isZero)=
      (if isZero then false else Bool.xor (memory.val.testBit 5) (memory.val.testBit 2)) := by
  fin_cases memory <;> cases isZero <;> decide

theorem saved_sign_table (memory : Fin 32) (sx : Bool) :
    (selectedMemory memory sx).val.testBit 5=sx ∧
      (selectedMemory memory sx).val.testBit 2=memory.val.testBit 2 := by
  fin_cases memory <;> cases sx <;> decide

/-- Interpret only physically observed ports. The enclosing actual caller
still must transfer into the chosen044 entry and execute its whole trace. -/
theorem actual_repaired_negative (x y : Rat) (u : Nat) :
    repairedNegative (observedMemory (actualMemory x y) (decide (u=0)))=
      zeroRepairedSign (sign x) (sign y) u := by
  have sx := (saved_sign_table (mNx x y) (sign x)).1
  have sy := (saved_sign_table (mNx x y) (sign x)).2.trans (observed_memory_bits x y).2.2.1
  rw [observed_negative_table]
  change (if decide (u=0) then false else Bool.xor
    ((selectedMemory (mNx x y) (sign x)).val.testBit 5)
    ((selectedMemory (mNx x y) (sign x)).val.testBit 2))=_
  rw [sx,sy]
  by_cases hu : u=0 <;> simp [zeroRepairedSign,hu]

theorem actual_product_negative (x y : Rat) :
    repairedNegative (observedMemory (actualMemory x y) (decide (quotientNumerator x y=0)))=sign (x*y) :=
  (actual_repaired_negative x y _).trans (pipeline_fields x y).2.2

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticZeroCarry058
