module

public import PaperProofs.Paid.PenaltyProgram

/-! D16 transport work: inject k real tools into k+1 real tools while keeping
the same n facts, channels, fees, current-payment rights and visible history.
This file supplies concrete data maps, not a policy/value monotonicity oracle.
-/

@[expose] public section

namespace RootPaidToolTransport

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def upStage (n k : ℕ) (i : (freshInstance n k).Stage) :
    (freshInstance n (k + 1)).Stage :=
  ⟨i.val, by simpa only [freshInstance, List.length_replicate] using i.isLt⟩

def downStage (n k : ℕ) (i : (freshInstance n (k + 1)).Stage) :
    (freshInstance n k).Stage :=
  ⟨i.val, by simpa only [freshInstance, List.length_replicate] using i.isLt⟩

@[simp] theorem down_up_stage (n k : ℕ) (i : (freshInstance n k).Stage) :
    downStage n k (upStage n k i) = i := Fin.ext rfl

@[simp] theorem up_down_stage (n k : ℕ) (i : (freshInstance n (k + 1)).Stage) :
    upStage n k (downStage n k i) = i := Fin.ext rfl

def stages (n k : ℕ) : (freshInstance n k).Stage ≃ (freshInstance n (k + 1)).Stage where
  toFun := upStage n k
  invFun := downStage n k
  left_inv := down_up_stage n k
  right_inv := up_down_stage n k

def upTool (k : ℕ) (tool : Fin k) : Fin (k + 1) := tool.castSucc

def downTool (k : ℕ) (tool : Fin (k + 1)) : Option (Fin k) :=
  if h : tool.val < k then some ⟨tool.val, h⟩ else none

@[simp] theorem down_up_tool (k : ℕ) (tool : Fin k) :
    downTool k (upTool k tool) = some tool := by
  simp [downTool, upTool]

def upHandle (n k : ℕ) (h : MismatchHandle (freshInstance n k)) :
    MismatchHandle (freshInstance n (k + 1)) := ⟨upStage n k h.stage, h.writeSerial⟩

def downHandle (n k : ℕ) (h : MismatchHandle (freshInstance n (k + 1))) :
    MismatchHandle (freshInstance n k) := ⟨downStage n k h.stage, h.writeSerial⟩

@[simp] theorem down_up_handle (n k : ℕ) (h : MismatchHandle (freshInstance n k)) :
    downHandle n k (upHandle n k h) = h := by
  cases h
  simp [downHandle, upHandle]

def upAction (n k : ℕ) : Action (freshInstance n k) → Action (freshInstance n (k + 1))
  | .review stage => .review (upStage n k stage)
  | .write stage bit => .write (upStage n k stage) bit
  | .allocate handle tool => .allocate (upHandle n k handle) (upTool k tool)
  | .execute handle tool => .execute (upHandle n k handle) (upTool k tool)
  | .advance stage => .advance (upStage n k stage)
  | .stop => .stop
  | .abandon => .abandon

def upEvent (n k : ℕ) : VisibleEvent (freshInstance n k) → VisibleEvent (freshInstance n (k + 1))
  | .observation stage symbol => .observation (upStage n k stage) symbol
  | .wrote stage bit serial => .wrote (upStage n k stage) bit serial
  | .report stage truth serial => .report (upStage n k stage) truth serial
  | .committed handle tool => .committed (upHandle n k handle) (upTool k tool)
  | .executed handle tool => .executed (upHandle n k handle) (upTool k tool)
  | .advanced stage => .advanced (upStage n k stage)
  | .stopped => .stopped
  | .abandoned => .abandoned

def downEvent (n k : ℕ) : VisibleEvent (freshInstance n (k + 1)) → Option (VisibleEvent (freshInstance n k))
  | .observation stage symbol => some (.observation (downStage n k stage) symbol)
  | .wrote stage bit serial => some (.wrote (downStage n k stage) bit serial)
  | .report stage truth serial => some (.report (downStage n k stage) truth serial)
  | .committed handle tool => (downTool k tool).map (.committed (downHandle n k handle))
  | .executed handle tool => (downTool k tool).map (.executed (downHandle n k handle))
  | .advanced stage => some (.advanced (downStage n k stage))
  | .stopped => some .stopped
  | .abandoned => some .abandoned

@[simp] theorem down_up_event (n k : ℕ) (event : VisibleEvent (freshInstance n k)) :
    downEvent n k (upEvent n k event) = some event := by
  cases event with
  | observation _ _ => rfl
  | wrote _ _ _ => rfl
  | report _ _ _ => rfl
  | committed handle tool =>
      exact congrArg (Option.map (VisibleEvent.committed handle)) (down_up_tool k tool)
  | executed handle tool =>
      exact congrArg (Option.map (VisibleEvent.executed handle)) (down_up_tool k tool)
  | advanced _ => rfl
  | stopped => rfl
  | abandoned => rfl

def upHistory (n k : ℕ) (history : List (VisibleEvent (freshInstance n k))) :=
  history.map (upEvent n k)

def downHistory (n k : ℕ) (history : List (VisibleEvent (freshInstance n (k + 1)))) :=
  history.filterMap (downEvent n k)

@[simp] theorem down_up_history (n k : ℕ) (history : List (VisibleEvent (freshInstance n k))) :
    downHistory n k (upHistory n k history) = history := by
  induction history with
  | nil => rfl
  | cons event rest _ih => simp [upHistory, downHistory]

def upCommitment (n k : ℕ) (a : Commitment (freshInstance n k)) :
    Commitment (freshInstance n (k + 1)) := ⟨upHandle n k a.handle, upTool k a.tool, a.atTime⟩

def upExecution (n k : ℕ) (e : Execution (freshInstance n k)) :
    Execution (freshInstance n (k + 1)) := ⟨upHandle n k e.handle, upTool k e.tool, e.atTime⟩

def upLedger (n k : ℕ) (L : Ledger (freshInstance n k)) : Ledger (freshInstance n (k + 1)) where
  truth := L.truth ∘ downStage n k
  written := L.written ∘ downStage n k
  writeSerial := L.writeSerial ∘ downStage n k
  reportTime := L.reportTime ∘ downStage n k
  advanceTime := L.advanceTime ∘ downStage n k
  reviews := L.reviews ∘ downStage n k
  normalCalls := L.normalCalls
  commitments := L.commitments.map (upCommitment n k)
  executions := L.executions.map (upExecution n k)
  finished := L.finished
  abandoned := L.abandoned

def upState (n k : ℕ) (s : State (freshInstance n k)) : State (freshInstance n (k + 1)) where
  ledger := upLedger n k s.ledger
  cursor := s.cursor
  clock := s.clock
  history := upHistory n k s.history
  halted := s.halted

/-- A total rule on larger histories. Only histories actually generated by
the injected rule need obey the source correspondence in the legality proof. -/
def upRule {Seed : Type*} (n k : ℕ) (rule : PolicyRule (freshInstance n k) Seed) :
    PolicyRule (freshInstance n (k + 1)) Seed :=
  fun seed history => upAction n k (rule seed (downHistory n k history))

theorem upRule_on_history {Seed : Type*} (n k : ℕ)
    (rule : PolicyRule (freshInstance n k) Seed) (seed : Seed)
    (history : List (VisibleEvent (freshInstance n k))) :
    upRule n k rule seed (upHistory n k history) = upAction n k (rule seed history) := by
  simp [upRule]

end RootPaidToolTransport
