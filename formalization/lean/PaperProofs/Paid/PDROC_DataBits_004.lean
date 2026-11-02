module

public import PaperProofs.Paid.PDROC_DataBits_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

structure EntryRange (M : ℕ) (B T : ℚ) (entry : MenuEntry) : Prop where
  observation_nonneg : 0 ≤ entry.observation
  observation_le : entry.observation ≤ B
  repairs_nonneg : 0 ≤ entry.repairs
  repairs_le : entry.repairs ≤ T
  failure_nonneg : 0 ≤ entry.failure
  failure_le : entry.failure ≤ 1
  action_bits_le : menuActionBits entry.action ≤ 3 + natBits M

theorem convex_bounds {p a b U : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (ha : a ≤ U) (hb0 : 0 ≤ b) (hb : b ≤ U) :
    0 ≤ (1-p)*a + p*b ∧ (1-p)*a+p*b ≤ U := by
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hp1) ha0) (mul_nonneg hp0 hb0)
  · have hleft := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hp1)
    have hright := mul_le_mul_of_nonneg_left hb hp0
    nlinarith

theorem entryRange_abandon (M : ℕ) {B T : ℚ} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    EntryRange M B T abandonEntry := by
  refine ⟨le_refl _, hB, le_refl _, hT, by norm_num [abandonEntry], le_refl _, ?_⟩
  change 2 ≤ 3 + natBits M
  omega

theorem entryRange_finish (M : ℕ) {B T : ℚ} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    EntryRange M B T finishEntry := by
  refine ⟨le_refl _, hB, le_refl _, hT, le_refl _, by norm_num [finishEntry], ?_⟩
  change 2 ≤ 3 + natBits M
  omega

theorem entryRange_mono {M : ℕ} {B T B' T' : ℚ} {entry : MenuEntry}
    (h : EntryRange M B T entry) (hB : B ≤ B') (hT : T ≤ T') :
    EntryRange M B' T' entry :=
  ⟨h.observation_nonneg, h.observation_le.trans hB, h.repairs_nonneg,
    h.repairs_le.trans hT, h.failure_nonneg, h.failure_le, h.action_bits_le⟩

theorem entryRange_repair {M : ℕ} {B T : ℚ} {entry : MenuEntry}
    (h : EntryRange M B T entry) : EntryRange M B (T+1) (repairEntry entry) := by
  refine ⟨h.observation_nonneg, h.observation_le, ?_, ?_,
    h.failure_nonneg, h.failure_le, h.action_bits_le⟩
  · change 0 ≤ 1 + entry.repairs
    linarith [h.repairs_nonneg]
  · change 1 + entry.repairs ≤ T + 1
    linarith [h.repairs_le]

theorem menuBadBranch_entryRange (P : Parameters) (fee penalty : ℚ) (previous : MenuRow)
    (B T : ℚ) (tools : ℕ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hprev : ∀ k, EntryRange P.certificate.M B T (previous.getD k abandonEntry)) :
    EntryRange P.certificate.M B (T+1) (P.menuBadBranch fee penalty previous tools).2 := by
  cases tools with
  | zero => exact entryRange_abandon _ hB (by linarith)
  | succ tools =>
      unfold menuBadBranch
      dsimp only
      split_ifs
      · exact entryRange_repair (hprev tools)
      · exact entryRange_abandon _ hB (by linarith)

def menuChargeBound (P : Parameters) : ℚ :=
  P.reviewFee * P.certificate.M / (2 * P.certificate.gamma)

theorem menuChargeBound_nonneg (P : Parameters) : 0 ≤ menuChargeBound P := by
  unfold menuChargeBound
  have hc := P.reviewFee_pos
  have hg := P.certificate.gamma_pos
  positivity

theorem endpointCharge_le_menuChargeBound (P : Parameters) (m : ℕ)
    (hm : m ≤ P.certificate.M) : P.binarySymmetric.endpointCharge m ≤ menuChargeBound P := by
  rw [PaperProofs.Statistics.BinarySymmetric.Parameters.endpointCharge_formula]
  change P.reviewFee * (m : ℚ) / (2 * P.certificate.gamma) *
    (1 - 2 * P.binarySymmetric.endpointError m) ≤ menuChargeBound P
  have hp0 := (P.binarySymmetric.endpointError_pos m).le
  have hp1 := P.binarySymmetric.endpointError_le_half m
  have hfee := P.reviewFee_pos
  have hgamma := P.certificate.gamma_pos
  have hpre : 0 ≤ P.reviewFee * (m : ℚ) / (2 * P.certificate.gamma) := by positivity
  have hm' : (m : ℚ) ≤ P.certificate.M := by exact_mod_cast hm
  calc
    _ ≤ P.reviewFee * (m : ℚ) / (2 * P.certificate.gamma) := by
      nlinarith [mul_nonneg hpre hp0]
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm' P.reviewFee_pos.le) (by positivity)

theorem cachedMenuTestingEntry_entryRange (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (n tools level : ℕ) (hlevel : level ≤ P.certificate.M)
    (hprev : ∀ k, EntryRange P.certificate.M ((n:ℚ)*menuChargeBound P) n
      (previous.getD k abandonEntry)) :
    EntryRange P.certificate.M (((n+1:ℕ):ℚ)*menuChargeBound P) (n+1)
      (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) := by
  let good := previous.getD tools abandonEntry
  let bad := (P.menuBadBranch fee penalty previous tools).2
  let p := P.binarySymmetric.endpointError level
  let c := P.binarySymmetric.endpointCharge level
  have hp0 : 0 ≤ p := (P.binarySymmetric.endpointError_pos level).le
  have hp1 : p ≤ 1 := (P.binarySymmetric.endpointError_le_half level).trans (by norm_num)
  have hg := hprev tools
  have hb := menuBadBranch_entryRange P fee penalty previous
    ((n:ℚ)*menuChargeBound P) n tools (by have := menuChargeBound_nonneg P; positivity) (by positivity) hprev
  have ho := convex_bounds hp0 hp1 hg.observation_nonneg hg.observation_le
    hb.observation_nonneg hb.observation_le
  have hr := convex_bounds hp0 hp1 hg.repairs_nonneg (hg.repairs_le.trans (by linarith))
    hb.repairs_nonneg hb.repairs_le
  have hf := convex_bounds hp0 hp1 hg.failure_nonneg hg.failure_le hb.failure_nonneg hb.failure_le
  have hc0 : 0 ≤ c := P.binarySymmetric.endpointCharge_nonneg level
  have hc : c ≤ menuChargeBound P := endpointCharge_le_menuChargeBound P level hlevel
  rw [cachedMenuTestingEntry_eq]
  change EntryRange _ _ _ (P.menuTestingEntry fee penalty previous tools level)
  refine ⟨?_, ?_, hr.1, hr.2, hf.1, hf.2, ?_⟩
  · change 0 ≤ c + (1-p)*good.observation + p*bad.observation
    linarith [ho.1]
  · change c + (1-p)*good.observation + p*bad.observation ≤ _
    push_cast
    nlinarith [ho.2]
  · change 3 + natBits level ≤ 3 + natBits P.certificate.M
    exact Nat.add_le_add_left (natBits_mono hlevel) 3

theorem cachedNextMenuEntry_entryRange (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (n tools : ℕ)
    (hprev : ∀ k, EntryRange P.certificate.M ((n:ℚ)*menuChargeBound P) n
      (previous.getD k abandonEntry)) :
    EntryRange P.certificate.M (((n+1:ℕ):ℚ)*menuChargeBound P) (n+1)
      (P.cachedNextMenuEntry P.endpointCache fee penalty previous tools) := by
  have hl : P.cachedLeastTestingLevel P.endpointCache fee penalty previous tools ≤ P.certificate.M := by
    rw [cachedLeastTestingLevel_eq]
    exact (P.leastTestingLevel_spec fee penalty previous tools).1
  unfold cachedNextMenuEntry
  dsimp only
  split_ifs
  · exact entryRange_abandon _ (by have := menuChargeBound_nonneg P; positivity) (by positivity)
  · exact entryRange_abandon _ (by have := menuChargeBound_nonneg P; positivity) (by positivity)
  · exact cachedMenuTestingEntry_entryRange P fee penalty previous n tools _ hl hprev

theorem baseMenuRow_entryRange (P : Parameters) (tools k : ℕ) :
    EntryRange P.certificate.M 0 0 ((baseMenuRow tools).getD k abandonEntry) := by
  apply array_getD_pred _ _ (EntryRange _ 0 0) (entryRange_abandon _ (by rfl) (by rfl))
  intro i hi
  simpa only [baseMenuRow, Array.getElem_replicate] using entryRange_finish P.certificate.M (B:=0) (T:=0) (by rfl) (by rfl)

theorem cachedNextMenuRow_entryRange (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (n tools k : ℕ)
    (hprev : ∀ j, EntryRange P.certificate.M ((n:ℚ)*menuChargeBound P) n
      (previous.getD j abandonEntry)) :
    EntryRange P.certificate.M (((n+1:ℕ):ℚ)*menuChargeBound P) (n+1)
      ((P.cachedNextMenuRow P.endpointCache fee penalty previous tools).getD k abandonEntry) := by
  apply array_getD_pred _ _ (EntryRange _ _ _)
    (entryRange_abandon _ (by have := menuChargeBound_nonneg P; positivity) (by positivity))
  intro i hi
  simpa only [cachedNextMenuRow, Array.getElem_ofFn] using
    cachedNextMenuEntry_entryRange P fee penalty previous n i hprev

theorem cachedSolveMenuTable_entryRange (P : Parameters) (fee penalty : ℚ) (tools stages n k : ℕ)
    (hn : n ≤ stages) :
    EntryRange P.certificate.M ((n:ℚ)*menuChargeBound P) n
      (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages) n k) := by
  induction stages generalizing n k with
  | zero =>
      have hz : n = 0 := by omega
      subst n
      simpa [menuEntryAt, PaperProofs.Paid.Parameters.cachedSolveMenuTable] using baseMenuRow_entryRange P tools k
  | succ stages ih =>
      let rows := P.cachedSolveMenuTable P.endpointCache fee penalty tools stages
      have hs : rows.size = stages + 1 := cachedSolveMenuTable_size P fee penalty tools stages
      by_cases hle : n ≤ stages
      · have hi : n < rows.size := by omega
        change EntryRange _ _ _ (((rows.push
          (P.cachedNextMenuRow P.endpointCache fee penalty (rows.getD stages (baseMenuRow tools)) tools)).getD n #[]).getD k abandonEntry)
        rw [array_getD_push_lt _ _ _ _ hi]
        exact ih n k hle
      · have he : n = stages + 1 := by omega
        subst n
        have hp : ∀ j, EntryRange P.certificate.M ((stages:ℚ)*menuChargeBound P) stages
            ((rows.getD stages (baseMenuRow tools)).getD j abandonEntry) := by
          intro j
          rw [array_getD_default_eq rows stages (baseMenuRow tools) #[] (by omega)]
          exact ih stages j (le_refl _)
        change EntryRange _ _ _ (((rows.push
          (P.cachedNextMenuRow P.endpointCache fee penalty (rows.getD stages (baseMenuRow tools)) tools)).getD (stages+1) #[]).getD k abandonEntry)
        rw [← hs, array_getD_push_size, hs]
        simpa only [Nat.cast_add, Nat.cast_one] using
          cachedNextMenuRow_entryRange P fee penalty _ stages tools k hp

end PDROC.DataBits
