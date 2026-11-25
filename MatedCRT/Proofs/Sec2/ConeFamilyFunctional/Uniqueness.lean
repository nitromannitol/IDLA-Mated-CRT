import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import MatedCRT.Proofs.Sec5.StoppedClusterCode

/-!
# Families of Lemma 2.4: uniqueness of strict families and the obstacle code of the family

Let `ν` be a measure on `ℂ` and `ρ > 1/2`.

* On the common interval of two families of Lemma 2.4 for `ν` (`IsConeHarmonicBallFamilyOn`, stopped at `∂B_{1/2}`),
  condition (c) at the radius `1` gives `Λ_t = int cl Λ_{B_1;0}(t)` for both (`eq_of_stopped`).
* A strictly growing family of Lemma 2.4 is the unique family of Lemma 2.4 with its stopping time
  (`le_of_stopped_of_strict`, `strict_familyProcess_eq`): if `T₁ < T₂` for a stopped family `Λ₁` and a
  strict family `Λ₂`, then `cl Λ₂(T₁) ⊆ Λ₂(t') ⊆ B_{1/2}` for `T₁ < t' < T₂` is a compact subset of a disc of radius
  `r < 1/2`, which contains `Λ₁(t) = Λ₂(t)` for every `t < T₁`, against the stopping of `Λ₁`.
* For a locally finite `ν` and `0 < t < T`, the decoder of the obstacle problem on `B̄_ρ` (`exists_decoder_disk`) applied
  to `ν|_{B̄_ρ}` returns the least supersolution, and its regularized cluster is `Λ_t` (`codeBall_decoder_eq`): the
  least supersolution solves the obstacle problem by condition (c) (`isObstacleSolutionOn_of_familyOn`).
* The times `a` for which all the decoded clusters at rational times `q ≤ a` lie in a closed disc of radius `< 1/2`
  are exactly the times `a < T` when the closures `cl Λ_t`, `t < T`, lie in `B_{1/2}` (`admissible_iff`). So the
  stopping time and the family are read off from the decoded clusters (`familyProcess_eq_codeFamilyProcess`), and
  `codeFamilyProcess` is a Borel function of the local measure (`measurable_codeFamilyProcess`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace ConeFamilyFunctional

/-! ### Uniqueness of strict families -/

/-- A bounded set whose closure lies in `B_{1/2}` lies in a closed disc of radius `r < 1/2`. -/
theorem exists_radius_lt_of_closure_subset {A : Set ℂ} (hA : closure A ⊆ ball 0 (1 / 2))
    (hb : Bornology.IsBounded A) : ∃ r : ℝ, r < 1 / 2 ∧ closure A ⊆ closedBall 0 r := by
  by_cases hne : (closure A).Nonempty
  · obtain ⟨x0, hx0, hmax⟩ := hb.isCompact_closure.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖x0‖, mem_ball_zero_iff.1 (hA hx0), fun x hx => mem_closedBall_zero_iff.2 (isMaxOn_iff.1 hmax x hx)⟩
  · refine ⟨0, by norm_num, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- On the common interval two families of Lemma 2.4 for the same measure agree (condition (c) at radius `1`). -/
theorem eq_of_stopped {ν : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ} {T₁ T₂ : ℝ} (h₁ : IsConeHarmonicBallFamilyOn ν Λ₁ T₁)
    (hs₁ : IsStoppedAtHalfBall Λ₁ T₁) (h₂ : IsConeHarmonicBallFamilyOn ν Λ₂ T₂) (hs₂ : IsStoppedAtHalfBall Λ₂ T₂)
    {t : ℝ} (ht₁ : t ∈ Ioo 0 T₁) (ht₂ : t ∈ Ioo 0 T₂) : Λ₁ t = Λ₂ t := by
  rw [(h₁.2.2 t (1 / 2) ht₁ (by norm_num) (hs₁.1 t ht₁) 1 (by norm_num)).1,
    (h₂.2.2 t (1 / 2) ht₂ (by norm_num) (hs₂.1 t ht₂) 1 (by norm_num)).1]

/-- A strict family of Lemma 2.4 does not stop later than any family of Lemma 2.4 for the same measure. -/
theorem le_of_stopped_of_strict {ν : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ} {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (h₁ : IsConeHarmonicBallFamilyOn ν Λ₁ T₁) (hs₁ : IsStoppedAtHalfBall Λ₁ T₁)
    (h₂ : IsStrictHalfBallFamily ν Λ₂ T₂) : T₂ ≤ T₁ := by
  obtain ⟨-, hf₂, hs₂, hg₂⟩ := h₂
  by_contra hlt
  push Not at hlt
  set t' := (T₁ + T₂) / 2 with ht'
  have hT₁' : T₁ ∈ Ioo 0 T₂ := ⟨hT₁, hlt⟩
  have ht'2 : t' ∈ Ioo 0 T₂ := ⟨by linarith, by linarith⟩
  have hcl : closure (Λ₂ T₁) ⊆ ball 0 (1 / 2) :=
    (hg₂ T₁ t' hT₁ (by linarith) ht'2.2).trans (hs₂.1 t' ht'2)
  obtain ⟨r, hr, hrsub⟩ := exists_radius_lt_of_closure_subset hcl (hf₂.2.1.isBounded T₁ hT₁')
  obtain ⟨t, ht, hnot⟩ := hs₁.2 ((r + 1 / 2) / 2) (by linarith)
  apply hnot
  have ht2 : t ∈ Ioo 0 T₂ := ⟨ht.1, ht.2.trans hlt⟩
  rw [eq_of_stopped h₁ hs₁ hf₂ hs₂ ht ht2]
  intro x hx
  have hx1 : x ∈ Λ₂ T₁ := hf₂.2.1.monotoneOn ht2 hT₁' ht.2.le hx
  have hx2 := mem_closedBall_zero_iff.1 (hrsub (subset_closure hx1))
  rw [mem_ball_zero_iff]
  linarith

/-- **Strict families of Lemma 2.4 are unique**: same stopping time, same sets before it. -/
theorem strict_T_eq {ν : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ} {T₁ T₂ : ℝ}
    (h₁ : IsStrictHalfBallFamily ν Λ₁ T₁) (h₂ : IsStrictHalfBallFamily ν Λ₂ T₂) : T₁ = T₂ :=
  le_antisymm (le_of_stopped_of_strict h₂.1 h₂.2.1 h₂.2.2.1 h₁)
    (le_of_stopped_of_strict h₁.1 h₁.2.1 h₁.2.2.1 h₂)

/-- The family processes of two strict families of Lemma 2.4 for the same measure agree. -/
theorem strict_familyProcess_eq {ν : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ} {T₁ T₂ : ℝ}
    (h₁ : IsStrictHalfBallFamily ν Λ₁ T₁) (h₂ : IsStrictHalfBallFamily ν Λ₂ T₂) :
    familyProcess Λ₁ T₁ = familyProcess Λ₂ T₂ := by
  have hT := strict_T_eq h₁ h₂
  subst hT
  funext p
  apply propext
  simp only [familyProcess]
  constructor
  · rintro ⟨hp, hx⟩
    exact ⟨hp, eq_of_stopped h₁.2.1 h₁.2.2.1 h₂.2.1 h₂.2.2.1 hp hp ▸ hx⟩
  · rintro ⟨hp, hx⟩
    exact ⟨hp, (eq_of_stopped h₁.2.1 h₁.2.2.1 h₂.2.1 h₂.2.2.1 hp hp).symm ▸ hx⟩

/-- A strict family of Lemma 2.4 has its closures in `B_{1/2}` before the stopping time. -/
theorem strict_closure_subset {ν : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (h : IsStrictHalfBallFamily ν Λ T) : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball 0 (1 / 2) := by
  intro t ht
  obtain ⟨t', htt', ht'T⟩ := exists_between ht.2
  exact (h.2.2.2 t t' ht.1 htt' ht'T).trans (h.2.2.1.1 t' ⟨ht.1.trans htt', ht'T⟩)

/-! ### The decoder of the obstacle problem -/

/-- The Lusin-Souslin decoder of the obstacle problem on `B̄_ρ` at mass `t` (`exists_decoder_disk`), and the zero
map when `ρ ≤ 0` or `t ≤ 0`. -/
noncomputable def decoder (ρ t : ℝ) : FinMeasDisk ρ → DiskFun ρ :=
  if h : 0 < ρ ∧ 0 < t then
    Classical.choose (exists_decoder_disk (ρ := ρ) (t := t) frozenFiniteMeasureDiskStandardBorel_holds
      frozenGreenDiscPole_inRepo h.1 h.2)
  else fun _ => 0

theorem measurable_decoder (ρ t : ℝ) : Measurable (decoder ρ t) := by
  unfold decoder
  split_ifs with h
  · exact (Classical.choose_spec (exists_decoder_disk (ρ := ρ) (t := t)
      frozenFiniteMeasureDiskStandardBorel_holds frozenGreenDiscPole_inRepo h.1 h.2)).1
  · exact measurable_const

theorem decoder_spec {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (s : FinMeasDisk ρ)
    (hex : ∃ f : DiskFun ρ, IsObstacleSolutionOn ρ t (s : Measure ℂ) (extDisk ρ f)) :
    IsObstacleSolutionOn ρ t (s : Measure ℂ) (extDisk ρ (decoder ρ t s)) := by
  unfold decoder
  split_ifs with h
  swap
  · exact absurd ⟨hρ, ht⟩ h
  exact (Classical.choose_spec (exists_decoder_disk (ρ := ρ) (t := t)
    frozenFiniteMeasureDiskStandardBorel_holds frozenGreenDiscPole_inRepo hρ ht)).2.1 s hex

/-- **The least supersolution solves the obstacle problem on `B̄_ρ`** at a time `t ∈ (0, T)` of a family of Lemma 2.4
on `(0, T)` with `Λ_t ⊆ B_r`, `r < ρ`: continuity, the Laplacian and the boundary values come from condition (c), and
`Δ w̄ ≤ μ` from `Δ w̄ = μ|_{Λ_t}`. -/
theorem isObstacleSolutionOn_of_familyOn {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T ρ t r : ℝ}
    (hΛ : IsConeHarmonicBallFamilyOn μ Λ T) (ht : t ∈ Ioo 0 T) (hr : 0 < r) (hsub : Λ t ⊆ ball 0 r)
    (hrρ : r < ρ) :
    IsObstacleSolutionOn ρ t (μ.restrict (closedBall (0 : ℂ) ρ)) (leastSupersolution μ ρ 0 t) := by
  have hρ : 0 < ρ := hr.trans hrρ
  obtain ⟨hLam, hcont, hLap, hzero⟩ := hΛ.2.2 t r ht hr hsub ρ hrρ
  have hUopen : IsOpen (floorObstacleCluster ρ t (leastSupersolution μ ρ 0 t)) :=
    isOpen_obstacleCluster frozenGreenDiscPole_inRepo hρ ht.1 hcont
  have hUball : floorObstacleCluster ρ t (leastSupersolution μ ρ 0 t) ⊆ ball (0 : ℂ) ρ :=
    fun x hx => (mem_obstacleCluster.1 hx).1
  have hUsub : floorObstacleCluster ρ t (leastSupersolution μ ρ 0 t) ⊆ Λ t := by
    rw [hLam]
    exact hUopen.subset_interior_iff.mpr subset_closure
  refine ⟨hcont, hzero, fun x hx hx0 => le_leastSupersolution ht.1.le hx hx0, ?_, ?_⟩
  · refine ⟨hLap.1, fun φ hφ hφ0 hint => ?_⟩
    have hφμ : Integrable φ μ :=
      (integrable_restrict_iff_of_tsupport (hφ.2.2.trans ball_subset_closedBall)).1 hint
    obtain ⟨hI1, -, heq⟩ := hLap.2 φ hφ
    rw [integral_restrict_eq_of_tsupport hφ.2.2 ball_subset_closedBall, heq, integral_zero_measure, sub_zero]
    exact setIntegral_le_integral hφμ (Eventually.of_forall hφ0)
  · refine ⟨hLap.1.mono_set hUball, fun φ hφ => ?_⟩
    have hφb : IsTestFunction (ball (0 : ℂ) ρ) φ := isTestFunction_of_subset hφ hUball
    have hφΛ : tsupport φ ⊆ Λ t := hφ.2.2.trans hUsub
    obtain ⟨hI1, -, heq⟩ := hLap.2 φ hφb
    have hφμ : Integrable φ μ := (integrable_restrict_iff_of_tsupport hφΛ).1 hI1
    refine ⟨hφμ.restrict, integrable_zero_measure, ?_⟩
    rw [heq, integral_zero_measure, sub_zero,
      integral_restrict_eq_of_tsupport (A := Λ t) (S := Λ t) hφΛ subset_rfl,
      integral_restrict_eq_of_tsupport (hφ.2.2.trans hUball) ball_subset_closedBall, sub_zero]

/-- **The decoded code of a family of Lemma 2.4.** For a locally finite `ν`, `ρ > 1/2` and `0 < t < T`, the decoder
applied to `ν|_{B̄_ρ}` returns the least supersolution on `B̄_ρ`, and its regularized cluster is `Λ_t`. -/
theorem codeBall_decoder_eq {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] {Λ : ℝ → Set ℂ} {T ρ t : ℝ}
    (hρ : 1 / 2 < ρ) (hΛ : IsConeHarmonicBallFamilyOn ν Λ T) (hs : IsStoppedAtHalfBall Λ T) (ht : t ∈ Ioo 0 T) :
    (∀ x ∈ closedBall (0 : ℂ) ρ, extDisk ρ (decoder ρ t (diskMeasOf ρ ν)) x = leastSupersolution ν ρ 0 t x) ∧
      Λ t = StoppedCode.codeBall ρ t (decoder ρ t (diskMeasOf ρ ν)) := by
  have hρ0 : 0 < ρ := by linarith
  have hId := isObstacleSolutionOn_of_familyOn hΛ ht (by norm_num) (hs.1 t ht) hρ
  have hmeas : ((diskMeasOf ρ ν : FinMeasDisk ρ) : Measure ℂ) = ν.restrict (closedBall (0 : ℂ) ρ) :=
    restrictOrZero_eq_restrict inferInstance
  have hId' : IsObstacleSolutionOn ρ t ((diskMeasOf ρ ν : FinMeasDisk ρ) : Measure ℂ)
      (leastSupersolution ν ρ 0 t) := by
    rw [hmeas]
    exact hId
  let fW : DiskFun ρ := ⟨(closedBall (0 : ℂ) ρ).domRestrict (leastSupersolution ν ρ 0 t),
    continuousOn_iff_continuous_domRestrict.1 hId'.continuousOn⟩
  have hcong : IsObstacleSolutionOn ρ t ((diskMeasOf ρ ν : FinMeasDisk ρ) : Measure ℂ) (extDisk ρ fW) :=
    hId'.congr_closedBall frozenGreenDiscPole_inRepo hρ0 ht.1 (fun y hy => by rw [extDisk_apply_of_mem _ hy]; rfl)
  have hw : ∀ x ∈ closedBall (0 : ℂ) ρ, extDisk ρ (decoder ρ t (diskMeasOf ρ ν)) x = leastSupersolution ν ρ 0 t x :=
    fun x hx => (decoder_spec hρ0 ht.1 _ ⟨fW, hcong⟩).eqOn_closedBall hId' hx
  refine ⟨hw, ?_⟩
  rw [(hΛ.2.2 t (1 / 2) ht (by norm_num) (hs.1 t ht) ρ hρ).1, StoppedCode.codeBall,
    StoppedCode.codeCluster_eq_cluster hw]

/-! ### The stopping time from the decoded clusters -/

/-- The time `a` is admissible for the local measure `s`: some rational `r < 1/2` bounds all the decoded clusters at the
rational times `0 < q ≤ a`. -/
def Admissible (ρ : ℝ) (s : FinMeasDisk ρ) (a : ℝ) : Prop :=
  ∃ r : ℚ, (r : ℝ) < 1 / 2 ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ a →
    closure (StoppedCode.codeCluster ρ q (decoder ρ q s)) ⊆ closedBall 0 r

/-- For a family of Lemma 2.4 whose closures lie in `B_{1/2}` before `T`, the admissible times are the times `a < T`. -/
theorem admissible_iff {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] {Λ : ℝ → Set ℂ} {T ρ : ℝ} (hρ : 1 / 2 < ρ)
    (hΛ : IsConeHarmonicBallFamilyOn ν Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (hcl : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball 0 (1 / 2)) {a : ℝ} (ha : 0 < a) :
    Admissible ρ (diskMeasOf ρ ν) a ↔ a < T := by
  have hρ0 : 0 < ρ := by linarith
  have hclq : ∀ q : ℝ, q ∈ Ioo 0 T →
      closure (StoppedCode.codeCluster ρ q (decoder ρ q (diskMeasOf ρ ν))) = closure (Λ q) := by
    intro q hq
    rw [(codeBall_decoder_eq hρ hΛ hs hq).2, StoppedCode.codeBall,
      StoppedCode.closure_interior_closure_of_isOpen (StoppedCode.isOpen_codeCluster hρ0 hq.1 _)]
  constructor
  · rintro ⟨r, hr, hall⟩
    by_contra hle
    push Not at hle
    obtain ⟨t, ht, hnot⟩ := hs.2 (((r : ℝ) + 1 / 2) / 2) (by linarith)
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    have hq : (q : ℝ) ∈ Ioo 0 T := ⟨ht.1.trans htq, hqT⟩
    apply hnot
    intro x hx
    have hx1 : x ∈ Λ q := hΛ.2.1.monotoneOn ht hq htq.le hx
    have hx2 := mem_closedBall_zero_iff.1
      (hall q hq.1 (hqT.le.trans hle) (by rw [hclq q hq]; exact subset_closure hx1))
    rw [mem_ball_zero_iff]
    linarith
  · intro haT
    set a' := (a + T) / 2 with ha'
    have ha'T : a' ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
    obtain ⟨r0, hr0, hr0sub⟩ := exists_radius_lt_of_closure_subset (hcl a' ha'T) (hΛ.2.1.isBounded a' ha'T)
    obtain ⟨r, hr0r, hr⟩ := exists_rat_btwn hr0
    refine ⟨r, hr, fun q hq hqa => ?_⟩
    have hqT : (q : ℝ) ∈ Ioo 0 T := ⟨hq, by linarith⟩
    rw [hclq q hqT]
    refine (closure_mono (hΛ.2.1.monotoneOn hqT ha'T (by linarith))).trans (hr0sub.trans ?_)
    exact closedBall_subset_closedBall hr0r.le

/-- The family process of the decoded family: `(t, x)` with `0 < t`, some admissible rational time beyond `t`, and `x`
in the regularized decoded cluster at time `t`. -/
def codeFamilyProcess (ρ : ℝ) (s : FinMeasDisk ρ) : ℝ × ℂ → Prop :=
  fun p => 0 < p.1 ∧ (∃ a : ℚ, p.1 < a ∧ Admissible ρ s a) ∧ p.2 ∈ StoppedCode.codeBall ρ p.1 (decoder ρ p.1 s)

/-- For a family of Lemma 2.4 whose closures lie in `B_{1/2}` before `T`, its family process is the decoded one. -/
theorem familyProcess_eq_codeFamilyProcess {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] {Λ : ℝ → Set ℂ} {T ρ : ℝ}
    (hρ : 1 / 2 < ρ) (hΛ : IsConeHarmonicBallFamilyOn ν Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (hcl : ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball 0 (1 / 2)) :
    familyProcess Λ T = codeFamilyProcess ρ (diskMeasOf ρ ν) := by
  funext p
  apply propext
  simp only [familyProcess, codeFamilyProcess]
  constructor
  · rintro ⟨hp, hx⟩
    obtain ⟨a, hpa, haT⟩ := exists_rat_btwn hp.2
    refine ⟨hp.1, ⟨a, hpa, (admissible_iff hρ hΛ hs hcl (hp.1.trans hpa)).2 haT⟩, ?_⟩
    rw [← (codeBall_decoder_eq hρ hΛ hs hp).2]
    exact hx
  · rintro ⟨hp0, ⟨a, hpa, hadm⟩, hx⟩
    have hpT : p.1 ∈ Ioo 0 T := ⟨hp0, hpa.trans ((admissible_iff hρ hΛ hs hcl (hp0.trans hpa)).1 hadm)⟩
    refine ⟨hpT, ?_⟩
    rw [(codeBall_decoder_eq hρ hΛ hs hpT).2]
    exact hx

/-! ### Measurability -/

/-- The closure of the decoded cluster lies in a closed disc iff its points of `denseC` do. -/
theorem closure_codeCluster_subset_closedBall_iff {ρ t r : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (w : DiskFun ρ) :
    closure (StoppedCode.codeCluster ρ t w) ⊆ closedBall 0 r ↔
      ∀ x ∈ denseC, x ∈ StoppedCode.codeCluster ρ t w → ‖x‖ ≤ r := by
  constructor
  · intro h x _ hx
    exact mem_closedBall_zero_iff.1 (h (subset_closure hx))
  · intro h
    have hU := StoppedCode.isOpen_codeCluster hρ ht w
    refine closure_minimal ((denseC_spec.2.open_subset_closure_inter hU).trans
      (closure_minimal (fun x hx => mem_closedBall_zero_iff.2 (h x hx.2 hx.1)) isClosed_closedBall))
      isClosed_closedBall

theorem measurableSet_admissible {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ) :
    MeasurableSet {s : FinMeasDisk ρ | Admissible ρ s a} := by
  have : Countable denseC := denseC_spec.1.to_subtype
  have hq : ∀ (q : ℚ) (r : ℚ), MeasurableSet {s : FinMeasDisk ρ | 0 < (q : ℝ) → (q : ℝ) ≤ a →
      closure (StoppedCode.codeCluster ρ q (decoder ρ q s)) ⊆ closedBall 0 r} := by
    intro q r
    by_cases hqa : 0 < (q : ℝ) ∧ (q : ℝ) ≤ a
    · have h := MeasurableSet.iInter fun x : denseC =>
        StoppedCode.measurableSet_imp_const
          ((measurable_decoder ρ q) (StoppedCode.measurableSet_mem_codeCluster (ρ := ρ) (t := q) (x : ℂ)))
          (‖(x : ℂ)‖ ≤ r)
      convert h using 1
      ext s
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage, hqa.1, hqa.2, forall_true_left]
      rw [closure_codeCluster_subset_closedBall_iff hρ hqa.1]
      exact ⟨fun h x hx => h x x.2 hx, fun h x hxD hx => h ⟨x, hxD⟩ hx⟩
    · convert MeasurableSet.univ using 1
      ext s
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hqa
  have h := MeasurableSet.iUnion fun r : ℚ => StoppedCode.measurableSet_and_const
    (MeasurableSet.iInter fun q : ℚ => hq q r) ((r : ℝ) < 1 / 2)
  convert h using 1
  ext s
  simp only [Admissible, mem_ofPred_eq, mem_iUnion, mem_iInter]
  exact ⟨fun ⟨r, hr, hall⟩ => ⟨r, fun q => hall q, hr⟩, fun ⟨r, hall, hr⟩ => ⟨r, hr, fun q => hall q⟩⟩

/-- The decoded family process is a Borel function of the local measure (product σ-algebra on processes). -/
theorem measurable_codeFamilyProcess {ρ : ℝ} (hρ : 0 < ρ) : Measurable (codeFamilyProcess ρ) := by
  refine measurable_pi_iff.2 fun p => measurable_to_prop ?_
  by_cases hp : 0 < p.1
  · have h1 : MeasurableSet {s : FinMeasDisk ρ | ∃ a : ℚ, p.1 < a ∧ Admissible ρ s a} := by
      convert MeasurableSet.iUnion fun a : ℚ =>
        StoppedCode.measurableSet_and_const (measurableSet_admissible hρ a) (p.1 < a) using 1
      ext s
      simp only [mem_ofPred_eq, mem_iUnion]
      exact ⟨fun ⟨a, ha, h⟩ => ⟨a, h, ha⟩, fun ⟨a, h, ha⟩ => ⟨a, ha, h⟩⟩
    have h2 : MeasurableSet {s : FinMeasDisk ρ | p.2 ∈ StoppedCode.codeBall ρ p.1 (decoder ρ p.1 s)} :=
      (measurable_decoder ρ p.1) (StoppedCode.measurableSet_mem_codeBall hρ hp p.2)
    convert h1.inter h2 using 1
    ext s
    simp only [codeFamilyProcess, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, eq_iff_iff,
      iff_true, hp, true_and]
  · convert MeasurableSet.empty using 1
    ext s
    simp only [codeFamilyProcess, mem_preimage, mem_singleton_iff, eq_iff_iff, iff_true, hp, false_and,
      mem_empty_iff_false]

end ConeFamilyFunctional

end MatedCRT
