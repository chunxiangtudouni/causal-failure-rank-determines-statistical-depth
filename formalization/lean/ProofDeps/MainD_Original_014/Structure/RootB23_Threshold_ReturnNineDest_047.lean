module
public import Structure.RootB23_Threshold_ReturnNineObserved_046
public import Structure.RootB23_Threshold_Window_PayloadSteps_023

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineDest
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocatePass023
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def core : List (List Bool) → List Bool
  | []=>[]
  | [a]=>PSTRTMIncrement009.blocks a++[false]
  | a::b::rest=>PA17TMRatArithmeticCopy006.workspace a++true::false::core (b::rest)

def finish (left : List Bool) : List (List Bool) → List Bool
  | []=>left
  | [a]=>pushField left a
  | a::b::rest=>finish (PayloadNav.nextLeft left a) (b::rest)

def width (previous : List (List Bool)) : ℕ := (previous.map List.length).sum

def home (left : List Bool) : List Bool := List.replicate 7 false++true::false::left

def stepCode : Machine 5 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine ReturnTraverse.rightCode

def skipCap : ℕ→ℕ | 0=>1 | n+1=>5+skipCap n+1

def skipCode : (n : ℕ)→Machine (skipCap n)
  | 0=>PA17TMRatArithmeticWidth018.scanMachine
  | n+1=>PSTRTMSeq005.seqMachine stepCode (skipCode n)

def skipPort (n : ℕ) : Fin (skipCap n+1) := ⟨skipCap n,Nat.lt_succ_self _⟩

def backCap : ℕ→ℕ | 0=>4 | n+1=>backCap n+7+1

def backCode : (n : ℕ)→Machine (backCap n)
  | 0=>ReturnCompactRewind.code 1
  | n+1=>PSTRTMSeq005.seqMachine (backCode n) (ReturnCompactRewind.code 4)

def backPort (n : ℕ) : Fin (backCap n+1) := ⟨backCap n,Nat.lt_succ_self _⟩

theorem skipCap_eq (n : ℕ) : skipCap n=6*n+1 := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [skipCap,ih];omega

theorem backCap_eq (n : ℕ) : backCap n=8*n+4 := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [backCap,ih];omega

theorem skipPort_succ (n : ℕ) : PSTRTMSeq005.rightLabel (a:=5) (skipPort n)=skipPort (n+1) := by
  apply Fin.ext
  simp only [PSTRTMSeq005.rightLabel,skipPort,skipCap]
  omega

theorem backPort_succ (n : ℕ) : PSTRTMSeq005.rightLabel (a:=backCap n) (7 : Fin 8)=backPort (n+1) := by
  apply Fin.ext
  change backCap n+1+7=backCap (n+1)
  rw [backCap]

/-- The preceding destination fields are crossed by real flagged scans
and three paid RIGHTs at each actual0010 delimiter. -/
theorem skip_bounded (n : ℕ) (previous : List (List Bool)) (lengthEq : previous.length=n+1)
    (left suffix : List Bool) :
    BoundedRun (skipCode n) (Tape.mk₂ left (core previous++false::suffix)) (skipPort n)
      (Tape.mk₂ (finish left previous) (false::suffix)) (2*width previous+8*(n+1)) := by
  induction n generalizing previous left with
  | zero=>
    cases previous with
    | nil=>simp only [List.length_nil] at lengthEq;omega
    | cons a rest=>
      have empty : rest=[] := by apply List.length_eq_zero_iff.mp;simpa only [List.length_cons] using Nat.succ.inj lengthEq
      subst rest
      have actual:=PayloadNav.scan_bounded left a suffix
      simpa [skipCode,skipPort,skipCap,core,finish,width,outDyMachine,PA17TMRatArithmeticCopy006.workspace] using actual.mono (by omega : 2*a.length+2≤2*a.length+8)
  | succ n ih=>
    cases previous with
    | nil=>simp only [List.length_nil] at lengthEq;omega
    | cons a rest=>
      cases rest with
      | nil=>simp only [List.length_cons,List.length_nil] at lengthEq;omega
      | cons b later=>
        have tailLength : (b::later).length=n+1 := by simp only [List.length_cons] at lengthEq ⊢;omega
        have scan:=PayloadNav.scan_bounded left a (true::false::(core (b::later)++false::suffix))
        have jump:=ReturnTraverse.right_bounded (pushField left a) (core (b::later)++false::suffix) false true false
        have restRun:=ih (b::later) tailLength (PayloadNav.nextLeft left a)
        have actual:=(scan.seq jump).seq restRun
        rw [skipPort_succ] at actual
        simpa [skipCode,skipCap,stepCode,core,finish,width,outDyMachine,PA17TMRatArithmeticCopy006.workspace,List.append_assoc]
          using actual.mono (by simp only [width,List.map_cons,List.sum_cons];omega :
            (2*a.length+2)+4+(2*width (b::later)+8*(n+1))≤2*width (a::b::later)+8*(n+1+1))

/-- The current old footer is its second real FALSE. The first field
uses one compact LEFT prefix; the remaining real0010 markers use four. -/
theorem back_bounded (n : ℕ) (previous : List (List Bool)) (lengthEq : previous.length=n+1)
    (archive suffix : List Bool) :
    BoundedRun (backCode n) (Tape.mk₂ (finish (false::archive) previous) (false::suffix)) (backPort n)
      (Tape.mk₂ (false::archive) (core previous++false::suffix)) (2*width previous+8*(n+1)) := by
  induction n generalizing previous archive with
  | zero=>
    cases previous with
    | nil=>simp only [List.length_nil] at lengthEq;omega
    | cons a rest=>
      have empty : rest=[] := by apply List.length_eq_zero_iff.mp;simpa only [List.length_cons] using Nat.succ.inj lengthEq
      subst rest
      have actual:=ReturnCompactRewind.bounded [false] archive a (false::suffix)
      simpa [backCode,backPort,backCap,core,finish,width,pushField,List.append_assoc]
        using actual.mono (by simp only [List.length_cons,List.length_nil];omega :
          2*a.length+[false].length+3≤2*a.length+8)
  | succ n ih=>
    cases previous with
    | nil=>simp only [List.length_nil] at lengthEq;omega
    | cons a rest=>
      cases rest with
      | nil=>simp only [List.length_cons,List.length_nil] at lengthEq;omega
      | cons b later=>
        have tailLength : (b::later).length=n+1 := by simp only [List.length_cons] at lengthEq ⊢;omega
        have restRun:=ih (b::later) tailLength (true::false::pushField (false::archive) a)
        have lastRun : BoundedRun (ReturnCompactRewind.code 4) _ (7 : Fin 8) _ (2*a.length+7) :=
          (ReturnCompactRewind.bounded [false,true,false,false] archive a (core (b::later)++false::suffix)).mono (by
            change 2*a.length+4+3≤2*a.length+7;omega)
        have actual:=restRun.seq lastRun
        rw [backPort_succ] at actual
        simpa [backCode,backCap,core,finish,width,PayloadNav.nextLeft,pushField,
          PA17TMRatArithmeticCopy006.workspace,List.append_assoc]
          using actual.mono (by simp only [width,List.map_cons,List.sum_cons];omega :
            (2*width (b::later)+8*(n+1))+(2*a.length+7)≤2*width (a::b::later)+8*(n+1+1))

def homeRightCode : Machine 11 := ReturnNineOut.right9

theorem homeRight_bounded (left suffix : List Bool) :
    BoundedRun homeRightCode
      (Tape.mk₂ left (false::true::(List.replicate 7 false++suffix))) 11
      (Tape.mk₂ (home left) suffix) 12 := by
  have first:=ReturnTraverse.right_bounded left (List.replicate 6 false++suffix) false true false
  have second:=ReturnTraverse.right_bounded (false::true::false::left) (List.replicate 3 false++suffix) false false false
  have third:=ReturnTraverse.right_bounded (List.replicate 4 false++true::false::left) suffix false false false
  have actual:=(first.seq second).seq third
  have exit : PSTRTMSeq005.rightLabel (a:=7) (3 : Fin 4)=(11 : Fin 12) := by decide
  rw [exit] at actual
  exact actual

def homeLeftSixCode : Machine 7 := PSTRTMSeq005.seqMachine ReturnBank.leftCode ReturnBank.leftCode
def homeLeftCode : Machine 11 := PSTRTMSeq005.seqMachine homeLeftSixCode CountAppend.fromDestinationMachine

theorem homeLeft_bounded (left suffix : List Bool) :
    BoundedRun homeLeftCode (Tape.mk₂ (home left) suffix) 11
      (Tape.mk₂ left (false::true::(List.replicate 7 false++suffix))) 12 := by
  have first:=ReturnBank.left_bounded (List.replicate 4 false++true::false::left) suffix
  have second:=ReturnBank.left_bounded (false::true::false::left) (List.replicate 3 false++suffix)
  have third:=CountAppend.fromDestination_bounded left (List.replicate 6 false++suffix)
  have actual:=(first.seq second).seq third
  have exit : PSTRTMSeq005.rightLabel (a:=7) (3 : Fin 4)=(11 : Fin 12) := by decide
  rw [exit] at actual
  exact actual

end RootB23.Threshold.ReturnNineDest
