import MatedCRT.Proposed.DMSRemark44Printed
import MatedCRT.Proposed.DuplantierMillerSheffieldCone2014
import MarkovProcess.Path.RandomShiftMeasurability
import MarkovProcess.Path.ClosedSetDetection
import MarkovProcess.Path.ExitTime
import MarkovProcess.Path.Shift

/-!
# Positive-level shifted law of the post-last-zero path (DMS Remark 4.4, pp. 74–75)

On the canonical Wiener space `W = MarkovProcess.brownianMotion 0`, given the printed clauses of
`MatedCRT.Proposed.DMSRemark44Printed` for a measurable version `F` of the drifted post-last-zero path, this file proves:

1. the conversion of the positive-level shifted process to the normalized conditional Wiener law on
   `stayAboveEvent d δ`: for `δ > 0`, the image under `y ↦ y - δ - d·` of the conditioned law of Brownian motion
   with drift `d` started at `δ` is `W[· | stayAboveEvent d δ]` (`map_cond_driftedBrownianFrom`);
2. the measurability of the first-level hit and of the random shift, reusing the MarkovProcess path library
   (`ContinuousPath.measurable_exitTime`, `ContinuousPath.measurable_shift_of_measurable`);
3. the coupling: as `δ ↓ 0` the shifted undrifted paths converge pathwise in the compact-open topology, and
   dominated convergence on `𝓝[>] 0` gives `MatedCRT.IsBMConditionedPositive d (P.map G)` for `G = F - d·`
   (`isBMConditionedPositive_of_remark44`, for any probability space carrying `F`);
4. the canonical-space corollary `canonical_postLastZeroLaw_of_printedWiener`, conditional on the printed
   Wiener-space clause `DMS14Remark44PrintedWiener`.

The printed clauses enter only as explicit hypotheses. `DMS14Remark44PostLastZeroLaw` is not a premise anywhere;
the transfer from an arbitrary probability space with a.e.-measurable Brownian coordinates is not formalized here.
Path-space machinery (`ContinuousPath.shift`, exit times, hitting sets, `brownianMotion`) is Scott Armstrong's
`MarkovProcess` library; `lastZeroR` is Bonanno's, via `DMSRemark44Printed` and the target file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.Sec1

open MatedCRT.Proposed

/-! ### Affine changes of paths -/

/-- Joint continuity of the affine change in its two real parameters and its path, for the compact-open
topology on `ContinuousPath ℝ = C(ℝ≥0, ℝ)`. -/
theorem continuous_affinePath :
    Continuous (fun p : (ℝ × ℝ) × ContinuousPath ℝ => affinePath p.1.1 p.1.2 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hev : Continuous (fun q : ((ℝ × ℝ) × ContinuousPath ℝ) × ℝ≥0 => q.1.2 q.2) :=
    (ContinuousEval.continuous_eval (F := ContinuousPath ℝ)).comp
      (continuous_fst.snd.prodMk continuous_snd)
  exact (continuous_fst.fst.fst.add hev).add
    (continuous_fst.fst.snd.mul (NNReal.continuous_coe.comp continuous_snd))

/-- The affine change is Borel measurable in the path. -/
theorem measurable_affinePath (a b : ℝ) : Measurable (affinePath a b) := by
  have hc : Continuous (fun y : ContinuousPath ℝ => ((a, b), y)) :=
    continuous_const.prodMk continuous_id
  exact (continuous_affinePath.comp hc).measurable

/-- The change `y ↦ -δ + y - d·` undoes the change `w ↦ δ + w + d·`. -/
theorem affinePath_affinePath (d δ : ℝ) (w : ContinuousPath ℝ) :
    affinePath (-δ) (-d) (affinePath δ d w) = w := by
  ext t
  simp only [affinePath, ContinuousMap.coe_mk]
  ring

/-! ### Brownian motion from zero and the never-vanishing event -/

/-- Under `W = brownianMotion 0` the path vanishes at time `0` almost surely: `brownianMotion_map_eval` at
`t = 0` gives the Gaussian law `N(0, 0)`, which is the Dirac mass at `0`. -/
theorem ae_brownianMotion_zero_eq_zero :
    ∀ᵐ w ∂(MarkovProcess.brownianMotion 0), w 0 = 0 := by
  have hm : Measurable (fun w : ContinuousPath ℝ => w 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := ℝ) 0
  have hmap : Measure.map (fun w : ContinuousPath ℝ => w 0) (MarkovProcess.brownianMotion 0) =
      Measure.dirac (0 : ℝ) := by
    rw [MarkovProcess.brownianMotion_map_eval, gaussianReal_zero_var]
  have h : ∀ᵐ x ∂(Measure.map (fun w : ContinuousPath ℝ => w 0) (MarkovProcess.brownianMotion 0)),
      x = 0 := by
    rw [hmap]
    exact (ae_dirac_iff (measurableSet_singleton (0 : ℝ))).2 rfl
  exact (ae_map_iff hm.aemeasurable (measurableSet_singleton (0 : ℝ))).1 h

/-- Sign persistence. For `δ > 0` and a path `w` with `w 0 = 0`, the level `δ + w t + d t` never vanishes
if and only if `w` stays strictly above `-δ - d t` at every time, that is `w ∈ stayAboveEvent d δ`.
(Intermediate value theorem on `[0, t]`: the level starts positive and cannot cross zero.) -/
theorem neverZero_iff_mem_stayAboveEvent (d δ : ℝ) (hδ : 0 < δ) (w : ContinuousPath ℝ)
    (h0 : w 0 = 0) :
    (∀ t : ℝ≥0, δ + w t + d * (t : ℝ) ≠ 0) ↔ w ∈ MatedCRT.stayAboveEvent d δ := by
  have hc : Continuous (fun t : ℝ≥0 => δ + w t + d * (t : ℝ)) :=
    (continuous_const.add w.continuous).add (continuous_const.mul NNReal.continuous_coe)
  constructor
  · intro h t
    show -δ < w t + d * (t : ℝ)
    by_contra hneg
    have hle : δ + w t + d * (t : ℝ) ≤ 0 := by linarith [not_lt.1 hneg]
    have hlt : δ + w t + d * (t : ℝ) < 0 := lt_of_le_of_ne hle (h t)
    have hmem : (0 : ℝ) ∈ Icc (δ + w t + d * (t : ℝ)) (δ + w 0 + d * ((0 : ℝ≥0) : ℝ)) := by
      refine ⟨hlt.le, ?_⟩
      simp [h0, hδ.le]
    obtain ⟨s, _, hs⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t by positivity) hc.continuousOn hmem
    exact h s hs
  · intro hw t
    have hw' : ∀ u : ℝ≥0, -δ < w u + d * (u : ℝ) := fun u => hw u
    exact (show (0 : ℝ) < δ + w t + d * (t : ℝ) by linarith [hw' t]).ne'

/-- For `δ > 0` the never-vanishing event of the started-at-`δ` drifted path, pulled back to the Wiener space,
coincides `W`-almost surely with `stayAboveEvent d δ`. -/
theorem neverZero_preimage_ae_eq (d δ : ℝ) (hδ : 0 < δ) :
    (affinePath δ d) ⁻¹' {y : ContinuousPath ℝ | ∀ t : ℝ≥0, y t ≠ 0} =ᵐ[MarkovProcess.brownianMotion 0]
      MatedCRT.stayAboveEvent d δ := by
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_brownianMotion_zero_eq_zero] with w hw0
  exact neverZero_iff_mem_stayAboveEvent d δ hδ w hw0

/-- The never-vanishing event of continuous paths is Borel: its complement is the union over `n : ℕ` of the
hitting events `hitsSetBy n {0}` of the closed set `{0}` by time `n`. -/
theorem measurableSet_neverZero :
    MeasurableSet {y : ContinuousPath ℝ | ∀ t : ℝ≥0, y t ≠ 0} := by
  have hset : {y : ContinuousPath ℝ | ∀ t : ℝ≥0, y t ≠ 0} =
      (⋃ n : ℕ, ContinuousPath.hitsSetBy (alpha := ℝ) (n : ℝ≥0) ({0} : Set ℝ))ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, ContinuousPath.hitsSetBy,
      Set.mem_singleton_iff]
    constructor
    · rintro h ⟨n, s, hs⟩
      exact h s hs
    · intro h t hyt
      exact h ⟨⌈t⌉₊, ⟨t, Nat.le_ceil t⟩, hyt⟩
  rw [hset]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun n => ?_)
  exact (ContinuousPath.canonicalFiltration (alpha := ℝ)).le (n : ℝ≥0) _
    (ContinuousPath.measurableSet_hitsSetBy (n : ℝ≥0) ({0} : Set ℝ) isClosed_singleton)

/-! ### Conversion to the normalized conditional Wiener law -/

/-- Transport of a normalized restriction along a measurable map `Ψ` with a measurable left inverse `Φ`:
the image under `Φ` of `cond (μ.map Ψ) E` is `cond μ (Ψ⁻¹ E)`. -/
theorem map_cond_map_of_leftInverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {Ψ : α → β} {Φ : β → α} (hΨ : Measurable Ψ) (hΦ : Measurable Φ)
    (hΦΨ : ∀ a, Φ (Ψ a) = a) {E : Set β} (hE : MeasurableSet E) :
    Measure.map Φ (ProbabilityTheory.cond (Measure.map Ψ μ) E) =
      ProbabilityTheory.cond μ (Ψ ⁻¹' E) := by
  have hpre : ∀ A : Set α, Ψ ⁻¹' (Φ ⁻¹' A) = A := fun A => by
    ext a
    simp [hΦΨ]
  ext A hA
  rw [Measure.map_apply hΦ hA]
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply (hΦ hA), Measure.map_apply hΨ hE,
    Measure.map_apply hΨ ((hΦ hA).inter hE), Measure.restrict_apply hA, Set.preimage_inter, hpre]

/-- **Conversion** of the positive-level shifted law (DMS Remark 4.4, printed positive-level clause) to the
normalized conditional Wiener law on `stayAboveEvent`. For `δ > 0`, the law of Brownian motion with drift `d`
started at `δ`, conditioned never to vanish, is pushed by `y ↦ y - δ - d·` to `W[· | stayAboveEvent d δ]`,
`W = MarkovProcess.brownianMotion 0`. -/
theorem map_cond_driftedBrownianFrom (d δ : ℝ) (hδ : 0 < δ) :
    Measure.map (affinePath (-δ) (-d))
        (ProbabilityTheory.cond (driftedBrownianFrom d δ)
          {y : ContinuousPath ℝ | ∀ t : ℝ≥0, y t ≠ 0}) =
      ProbabilityTheory.cond (MarkovProcess.brownianMotion 0) (MatedCRT.stayAboveEvent d δ) := by
  unfold driftedBrownianFrom
  rw [map_cond_map_of_leftInverse (MarkovProcess.brownianMotion 0) (measurable_affinePath δ d)
    (measurable_affinePath (-δ) (-d)) (fun w => affinePath_affinePath d δ w) measurableSet_neverZero]
  unfold ProbabilityTheory.cond
  rw [measure_congr (neverZero_preimage_ae_eq d δ hδ),
    Measure.restrict_congr_set (neverZero_preimage_ae_eq d δ hδ)]

/-! ### First-level hit and random shift: measurability -/

/-- The first hitting time of a level is Borel measurable on path space (exit time from `(-∞, δ)`). -/
theorem measurable_dmsFirstLevelHit (δ : ℝ) :
    Measurable (fun y : ContinuousPath ℝ => dmsFirstLevelHit δ y) :=
  ENNReal.measurable_toNNReal.comp (ContinuousPath.measurable_exitTime (Set.Iio δ) isOpen_Iio)

/-- The random shift `ω ↦ X_{τ_δ(X_ω) + ·}` at the first level hit is measurable, by
`ContinuousPath.measurable_shift_of_measurable` applied to the Borel first hit. -/
theorem measurable_shift_dmsFirstLevelHit {Ω : Type*} [MeasurableSpace Ω] (δ : ℝ)
    {X : Ω → ContinuousPath ℝ} (hX : Measurable X) :
    Measurable (fun ω => ContinuousPath.shift (dmsFirstLevelHit δ (X ω)) (X ω)) :=
  (ContinuousPath.measurable_shift_of_measurable (fun y => dmsFirstLevelHit δ y)
    (measurable_dmsFirstLevelHit δ)).comp hX

/-! ### Pathwise convergence as `δ ↓ 0` -/

/-- If `δ ≤ y η` then the first hit of `δ` occurs by time `η`. -/
theorem dmsFirstLevelHit_le (δ : ℝ) (y : ContinuousPath ℝ) (η : ℝ≥0) (h : δ ≤ y η) :
    dmsFirstLevelHit δ y ≤ η := by
  have hle : ContinuousPath.exitTime (Set.Iio δ) y ≤ (η : ℝ≥0∞) :=
    ContinuousPath.exitTime_le_of_notMem (Set.Iio δ) y η
      (fun hlt => (not_lt.2 h) (Set.mem_Iio.1 hlt))
  have hmono := ENNReal.toNNReal_mono ENNReal.coe_ne_top hle
  rw [ENNReal.toNNReal_coe] at hmono
  exact hmono

/-- If a path is positive at every positive time, its first hit of `δ` tends to `0` as `δ ↓ 0`. -/
theorem tendsto_dmsFirstLevelHit (y : ContinuousPath ℝ) (hy : ∀ η : ℝ≥0, 0 < η → 0 < y η) :
    Tendsto (fun δ : ℝ => dmsFirstLevelHit δ y) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => by simp at ha, fun a ha => ?_⟩
  have ha2 : (0 : ℝ≥0) < a / 2 := half_pos ha
  have hpos : (0 : ℝ) < y (a / 2) := hy (a / 2) ha2
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  exact lt_of_le_of_lt (dmsFirstLevelHit_le δ y (a / 2) hδ.2.le) (half_lt_self ha)

/-- Pathwise convergence of the conditioned-shift coordinates: if `y` is positive at every positive time, then
`δ ↦ affinePath (-δ) (-d) (y_{τ_δ + ·})` tends to `affinePath 0 (-d) y` in the compact-open topology as `δ ↓ 0`.
Uses joint continuity of `ContinuousPath.shift` and of the affine change, and the first hit tending to `0`. -/
theorem tendsto_affine_shift_firstLevelHit (d : ℝ) (y : ContinuousPath ℝ)
    (hy : ∀ η : ℝ≥0, 0 < η → 0 < y η) :
    Tendsto (fun δ : ℝ => affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ y) y))
      (𝓝[>] 0) (𝓝 (affinePath 0 (-d) y)) := by
  have h1 : Tendsto (fun δ : ℝ => ContinuousPath.shift (dmsFirstLevelHit δ y) y) (𝓝[>] 0) (𝓝 y) := by
    have hc : Tendsto (fun δ : ℝ => ((dmsFirstLevelHit δ y, y) : ℝ≥0 × ContinuousPath ℝ)) (𝓝[>] 0)
        (𝓝 ((0 : ℝ≥0), y)) :=
      (tendsto_dmsFirstLevelHit y hy).prodMk_nhds tendsto_const_nhds
    have h : Tendsto (fun δ : ℝ => ContinuousPath.shift (dmsFirstLevelHit δ y) y) (𝓝[>] 0)
        (𝓝 (ContinuousPath.shift (0 : ℝ≥0) y)) :=
      (ContinuousPath.continuous_shift.tendsto ((0 : ℝ≥0), y)).comp hc
    rwa [ContinuousPath.shift_zero] at h
  have hneg : Tendsto (fun δ : ℝ => -δ) (𝓝[>] 0) (𝓝 (-0)) :=
    (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun δ : ℝ => ((-δ, -d), ContinuousPath.shift (dmsFirstLevelHit δ y) y))
      (𝓝[>] 0) (𝓝 ((-0, -d), y)) :=
    (hneg.prodMk_nhds tendsto_const_nhds).prodMk_nhds h1
  have h3 := (continuous_affinePath.tendsto ((-0, -d), y)).comp h2
  rw [neg_zero] at h3
  exact h3

/-! ### The coupling: printed clauses give the conditioned weak limit -/

/-- **Coupling** (DMS Remark 4.4, printed clauses ⇒ conditioned weak limit). Let `F` be a measurable
continuous-path version of the drifted post-last-zero path, with the printed realization clause and the printed
positive-level clause for drift `d > 0`. Then the undrifted path `G = F - d·` has the conditioned weak limit
`MatedCRT.IsBMConditionedPositive d (P.map G)`. The printed clauses enter only as hypotheses; the weak-limit
conclusion is derived here, by conditional-law identities at each `δ > 0` and dominated convergence on `𝓝[>] 0`. -/
theorem isBMConditionedPositive_of_remark44 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℝ} (_hd : 0 < d) (F : Ω → ContinuousPath ℝ) (hF : Measurable F)
    (hreal : DMS14Remark44PositiveRealization P F) (hlaw : DMS14Remark44PositiveLevelLaw P d F) :
    MatedCRT.IsBMConditionedPositive d (P.map (fun ω => affinePath 0 (-d) (F ω))) := by
  have hG : Measurable (fun ω => affinePath 0 (-d) (F ω)) :=
    (measurable_affinePath 0 (-d)).comp hF
  have hZ : ∀ δ : ℝ, Measurable
      (fun ω => affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω))) :=
    fun δ => (measurable_affinePath (-δ) (-d)).comp (measurable_shift_dmsFirstLevelHit δ hF)
  have hlawZ : ∀ δ : ℝ, 0 < δ → P.map
      (fun ω => affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω))) =
      ProbabilityTheory.cond (MarkovProcess.brownianMotion 0) (MatedCRT.stayAboveEvent d δ) := by
    intro δ hδ
    calc P.map (fun ω => affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω)))
        = Measure.map (affinePath (-δ) (-d))
            (Measure.map (fun ω => ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω)) P) :=
          (Measure.map_map (measurable_affinePath (-δ) (-d))
            (measurable_shift_dmsFirstLevelHit δ hF)).symm
      _ = ProbabilityTheory.cond (MarkovProcess.brownianMotion 0) (MatedCRT.stayAboveEvent d δ) := by
          rw [hlaw δ hδ]
          exact map_cond_driftedBrownianFrom d δ hδ
  have : IsProbabilityMeasure (P.map (fun ω => affinePath 0 (-d) (F ω))) :=
    (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).2 inferInstance
  refine ⟨inferInstance, fun f => ?_⟩
  have hGf : ∫ w, f w ∂(P.map (fun ω => affinePath 0 (-d) (F ω))) =
      ∫ ω, f (affinePath 0 (-d) (F ω)) ∂P :=
    integral_map hG.aemeasurable f.continuous.measurable.aestronglyMeasurable
  rw [hGf]
  have hdct : Tendsto (fun δ : ℝ =>
      ∫ ω, f (affinePath (-δ) (-d) (ContinuousPath.shift (dmsFirstLevelHit δ (F ω)) (F ω))) ∂P)
      (𝓝[>] 0) (𝓝 (∫ ω, f (affinePath 0 (-d) (F ω)) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖) ?_ ?_ (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun δ =>
        (f.continuous.measurable.comp (hZ δ)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun δ => Filter.Eventually.of_forall fun ω =>
        f.norm_coe_le_norm _
    · filter_upwards [hreal] with ω hω
      exact (f.continuous.tendsto _).comp
        (tendsto_affine_shift_firstLevelHit d (F ω) (fun η hη => hω.2 η hη))
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [← hlawZ δ hδ, integral_map (hZ δ).aemeasurable f.continuous.measurable.aestronglyMeasurable]

/-! ### Canonical Wiener space: the printed clauses give the conditioned weak limit -/

/-- Redrifting and then undrifting is the identity: `(w + d·) - d· = w`. -/
theorem affinePath_zero_inv (d : ℝ) (w : ContinuousPath ℝ) :
    affinePath 0 (-d) (affinePath 0 d w) = w := by
  ext t
  simp only [affinePath, ContinuousMap.coe_mk]
  ring

/-- The drifted post-last-zero path is the undrifted one plus the drift: `c(ℓ + t) = (c(ℓ + t) - d t) + d t`. -/
theorem dmsDriftedPostLastZeroPath_eq_add (d : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) :
    dmsDriftedPostLastZeroPath d b t = dmsPostLastZeroPath d b t + d * t := by
  simp only [dmsDriftedPostLastZeroPath, dmsPostLastZeroPath]
  ring

/-- **Canonical conditional-law coupling** (DMS Remark 4.4 on the Wiener space). Conditional on the printed
Wiener-space clause `DMS14Remark44PrintedWiener`, every measurable `G` on path space which is `W`-almost surely the
post-last-zero path `dmsPostLastZeroPath (lqgQ γ - γ) ω` has the conditioned weak limit
`IsBMConditionedPositive (lqgQ γ - γ) (W.map G)`. This is the target's conclusion restricted to the canonical space,
derived from the printed clauses by `isBMConditionedPositive_of_remark44`. It is conditional, not a closure: the
printed clause is the input, and the transfer to an arbitrary probability space is not formalized here. -/
theorem canonical_postLastZeroLaw_of_printedWiener (hprint : DMS14Remark44PrintedWiener) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ G : ContinuousPath ℝ → ContinuousPath ℝ, Measurable G →
      (∀ᵐ ω ∂(MarkovProcess.brownianMotion 0), ∀ t : ℝ≥0,
        G ω t = dmsPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => ω s) t) →
      MatedCRT.IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ)
        (Measure.map G (MarkovProcess.brownianMotion 0)) := by
  intro γ hγ0 hγ2 G hG hid
  have hd : 0 < MatedCRTHarmonic.MatedCRT.lqgQ γ - γ :=
    MatedCRT.Proposed.lqgQ_sub_pos_of_lt_two hγ0 hγ2
  have hF : Measurable (fun ω => affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (G ω)) :=
    (measurable_affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ)).comp hG
  have hidF : ∀ᵐ ω ∂(MarkovProcess.brownianMotion 0), ∀ t : ℝ≥0,
      affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (G ω) t =
        dmsDriftedPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => ω s) t := by
    filter_upwards [hid] with ω hω t
    simp only [affinePath, ContinuousMap.coe_mk, dmsDriftedPostLastZeroPath_eq_add, hω t, zero_add]
  obtain ⟨hreal, hlaw⟩ := hprint γ hγ0 hγ2
    (fun ω => affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (G ω)) hF hidF
  have key := isBMConditionedPositive_of_remark44 (MarkovProcess.brownianMotion 0) hd
    (fun ω => affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (G ω)) hF hreal hlaw
  simpa only [affinePath_zero_inv] using key

/-! ### Conditional assembly of the numbered target from the transfer residual -/

/-- **Conditional assembly, not a closure.** The numbered target `DMS14Remark44PostLastZeroLaw` follows from the
single residual `DMS14Remark44TransferResidual` (the printed clauses on an arbitrary probability space). The proof
redrifts the measurable version `F` to `F + d·`, applies the residual, and then the coupling
`isBMConditionedPositive_of_remark44`; the target itself is not used as a premise. -/
theorem dms14Remark44PostLastZeroLaw_of_transferResidual (hT : DMS14Remark44TransferResidual) :
    DMS14Remark44PostLastZeroLaw := by
  intro γ hγ0 hγ2 Ω _ P _ B F hB hF hid
  have hd : 0 < MatedCRTHarmonic.MatedCRT.lqgQ γ - γ :=
    MatedCRT.Proposed.lqgQ_sub_pos_of_lt_two hγ0 hγ2
  have hF' : Measurable (fun ω => affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (F ω)) :=
    (measurable_affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ)).comp hF
  have hidF : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (F ω) t =
        dmsDriftedPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => B s ω) t := by
    filter_upwards [hid] with ω hω t
    simp only [affinePath, ContinuousMap.coe_mk, dmsDriftedPostLastZeroPath_eq_add, hω t, zero_add]
  obtain ⟨hreal, hlaw⟩ := hT γ hγ0 hγ2 Ω P B
    (fun ω => affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (F ω)) hB hF' hidF
  have key := isBMConditionedPositive_of_remark44 P hd
    (fun ω => affinePath 0 (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (F ω)) hF' hreal hlaw
  simpa only [affinePath_zero_inv] using key

end MatedCRT.Sec1
