import MatedCRT.Proofs.Field.WholePlaneLateralGauss
import MatedCRT.Proofs.Field.ConeLevelIntegrable

/-!
# The lateral circle averages of a whole-plane GFF: covariances (eq:gff, circle level)

For a whole-plane GFF `(hC, hcirc)` and region circles `o = (r, z)`, `o' = (r', z')` (`InLevelRegion`):

* `L_o = h_r(z) - A_o` is the lateral circle average, `A_o = ⨍_{∂B_r(z)} h_{|x|}(0)` (`latCirc`, `radAvg`);
* `Cov(h_r(z), h_s(0)) = ⨍_{∂B_r(z)} min(s, -log|x|)` (`cov_obs_radV`), so `L_o` is uncorrelated with the radial
  process (`cov_latCirc_radV`);
* `Cov(L_o, L_{o'}) = K(o, o') - S(o', o)` with `K` the whole-plane covariance and `S` the double circle average of
  `min(-log|x|, -log|y|)` (`cov_latCirc_latCirc`).

The radial process of a whole-plane GFF is the family `wpRad u = h_{e^{-max u 0}}(0)`, which satisfies
`IsRadialLevelData` (`wp_radialData`).
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric HarmonicBalls
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

/-- The span of the observables of a whole-plane GFF: a centred Gaussian space. -/
noncomputable def wpSpace {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    Submodule ℝ (Ω → ℝ) :=
  Submodule.span ℝ (Set.range fun o : GFFObservable.Admissible => fun ω => o.1.eval (hC ω) (hcirc ω))

section WP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

omit [IsProbabilityMeasure P] in
lemma wp_obs_measurable (hh : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible) :
    Measurable fun ω => o.1.eval (hC ω) (hcirc ω) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact hh.measurable_pairing φ ho
  | circle r z => exact hh.measurable_circle r z ho

omit [IsProbabilityMeasure P] in
lemma wpSpace_gaussian (hh : IsWholePlaneGFF P hC hcirc) : IsCentredGaussianSpace P (wpSpace hC hcirc) :=
  isCentredGaussianSpace_span hh.isGaussianProcess (wp_obs_measurable hh)
    (fun o => hh.integral_eq_zero o.1 o.2)

/-- The radial process of a whole-plane GFF, extended by a constant on `(-∞, 0]`. -/
noncomputable def wpRad (hcirc : ℝ → ℂ → ℝ) (u : ℝ) : ℝ := hcirc (Real.exp (-(max u 0))) 0

omit [IsProbabilityMeasure P] in
lemma wp_radial_cov (hh : IsWholePlaneGFF P hC hcirc) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    covariance (fun ω => wpRad (hcirc ω) u) (fun ω => wpRad (hcirc ω) v) P = min u v := by
  have hcov := hh.covariance_eq (.circle (Real.exp (-u)) 0) (.circle (Real.exp (-v)) 0) (Real.exp_pos _)
    (Real.exp_pos _)
  rw [wholePlaneGFFCov_circle_origin (Real.exp_pos _) 0] at hcov
  have h2 : (fun ω => wpRad (hcirc ω) u) = fun ω => hcirc ω (Real.exp (-u)) 0 := by
    funext ω
    simp only [wpRad, max_eq_left hu]
  have h3 : (fun ω => wpRad (hcirc ω) v) = fun ω => hcirc ω (Real.exp (-v)) 0 := by
    funext ω
    simp only [wpRad, max_eq_left hv]
  rw [h2, h3]
  refine hcov.trans ?_
  rw [circleAverage_radialCov _ (Real.exp_pos _), radialCov_exp_neg hv hu, min_comm]

omit [IsProbabilityMeasure P] in
/-- `wpRad` is a radial process in the sense of `IsRadialLevelData`. -/
theorem wp_radialData (hh : IsWholePlaneGFF P hC hcirc) :
    IsRadialLevelData P (fun u ω => wpRad (hcirc ω) u) (wpSpace hC hcirc) where
  meas := fun u => by
    have : (fun ω => wpRad (hcirc ω) u) = fun ω => hcirc ω (Real.exp (-(max u 0))) 0 := rfl
    rw [this]
    exact hh.measurable_circle _ _ (Real.exp_pos _)
  mem := fun u => Submodule.subset_span ⟨⟨GFFObservable.circle (Real.exp (-(max u 0))) 0, Real.exp_pos _⟩, rfl⟩
  const_nonpos := fun u hu => by
    funext ω
    simp only [wpRad, max_eq_right hu, max_self]
  cont := by
    filter_upwards [hh.ae_continuousOn_circle] with ω hω
    have hcont : Continuous fun u : ℝ => (Real.exp (-(max u 0)), (0 : ℂ)) :=
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_id.max continuous_const))).prodMk
        continuous_const
    have hmaps : ∀ u : ℝ, (Real.exp (-(max u 0)), (0 : ℂ)) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
      fun u => ⟨Real.exp_pos _, trivial⟩
    have := hω.comp_continuous hcont hmaps
    exact this
  cov := fun u v hu hv => wp_radial_cov hh hu hv

end WP

end MatedCRT.Field

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Real Metric HarmonicBalls
open MatedCRT.Field.GaussClosure MatedCRT.Field.Level MatedCRT.Field.ConeRadial
open scoped NNReal

section Cov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

lemma exp_neg_neg_log_norm {x : ℂ} (hx : x ≠ 0) : Real.exp (-(-Real.log ‖x‖)) = ‖x‖ := by
  rw [neg_neg, Real.exp_log (norm_pos_iff.2 hx)]

lemma ne_zero_of_mem_region_sphere {r : ℝ} {z x : ℂ} (hreg : InLevelRegion r z) (hx : x ∈ sphere z |r|) :
    x ≠ 0 := by
  obtain ⟨hr, hzr, -⟩ := hreg
  have h := (region_norm_bounds hr hx).1
  intro h0
  rw [h0, norm_zero] at h
  linarith [norm_nonneg z]

omit [IsProbabilityMeasure P] in
/-- `h_r(z)` against `W_u`: `Cov = ⨍_{∂B_r(z)} min(max u 0, -log|x|)` for every real `u`. -/
lemma cov_obs_W_all (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} {z : ℂ} (hreg : InLevelRegion r z) (u : ℝ) :
    covariance (fun ω => hcirc ω r z) (fun ω => wpRad (hcirc ω) u) P =
      Real.circleAverage (fun x => min (max u 0) (-Real.log ‖x‖)) z r := by
  have hL1 : ∀ v : ℝ, 0 ≤ v → covariance (fun ω => hcirc ω r z) (fun ω => wpRad (hcirc ω) v) P =
      Real.circleAverage (fun x => min v (-Real.log ‖x‖)) z r := by
    intro v hv
    have h := cov_circle_radV hh hreg.1 z v
    have hw : (fun ω => wpRad (hcirc ω) v) = fun ω => radV (hcirc ω) v := by
      funext ω
      simp only [wpRad, radV, max_eq_left hv]
    rw [hw, h]
    refine Real.circleAverage_congr_sphere (fun x hx => ?_)
    have hx0 := ne_zero_of_mem_region_sphere hreg hx
    have h2 := radialCov_exp_neg hv (neg_log_nonneg_of_mem_sphere hreg hx)
    rw [exp_neg_neg_log_norm hx0] at h2
    exact h2
  rcases le_total u 0 with hu | hu
  · have h0 : (fun ω => wpRad (hcirc ω) u) = fun ω => wpRad (hcirc ω) 0 := by
      funext ω
      simp only [wpRad, max_eq_right hu, max_self]
    rw [h0, hL1 0 le_rfl, max_eq_right hu]
  · rw [max_eq_left hu]
    exact hL1 u hu

/-- The radial circle average equals the average of `wpRad` at `-log|x|` (pointwise, for every sample). -/
lemma radAvg_eq_wpRad {r : ℝ} {z : ℂ} (hreg : InLevelRegion r z) (hcirc' : ℝ → ℂ → ℝ) :
    radAvg hcirc' r z = Real.circleAverage (fun x => wpRad hcirc' (-Real.log ‖x‖)) z r := by
  unfold radAvg
  refine Real.circleAverage_congr_sphere (fun x hx => ?_)
  have hx0 := ne_zero_of_mem_region_sphere hreg hx
  have hnn := neg_log_nonneg_of_mem_sphere hreg hx
  simp only [wpRad, max_eq_left hnn]
  rw [neg_neg, Real.exp_log (norm_pos_iff.2 hx0)]

/-- The lateral circle averages of two region circles of a whole-plane GFF are uncorrelated with the radial process,
and `Cov(L_o, L_{o'}) = K(o, o') - S(o', o)`, where `S` is the double circle average of `min(-log|x|, -log|y|)`. -/
theorem cov_latCirc_latCirc (hh : IsWholePlaneGFF P hC hcirc) {r r' : ℝ} {z z' : ℂ}
    (hreg : InLevelRegion r z) (hreg' : InLevelRegion r' z') :
    covariance (fun ω => latCirc (hcirc ω) r z) (fun ω => latCirc (hcirc ω) r' z') P =
      wholePlaneGFFCov (.circle r z) (.circle r' z') -
        Real.circleAverage (fun y => Real.circleAverage (fun x => min (-Real.log ‖y‖) (-Real.log ‖x‖)) z r) z' r' := by
  have hr : 0 < r := hreg.1
  have hzr : r < ‖z‖ := hreg.2.1
  have hr' : 0 < r' := hreg'.1
  have hzr' : r' < ‖z'‖ := hreg'.2.1
  obtain ⟨Y, Y', hYm, hYm', havg, havg', hex⟩ :=
    radial_avg_cov_pair (wp_radialData hh) (wpSpace_gaussian hh) hreg hreg'
  set M : Submodule ℝ (Ω → ℝ) := hex.choose with hMdef
  have hspec := hex.choose_spec
  have hMle : wpSpace hC hcirc ≤ M := hspec.2.1
  have hYmem : Y ∈ M := hspec.2.2.1
  have hY'mem : Y' ∈ M := hspec.2.2.2.1
  have hLF : LevelFormula P (fun u ω => wpRad (hcirc ω) u) M Y r z := hspec.2.2.2.2.2.2.1
  have hLF' : LevelFormula P (fun u ω => wpRad (hcirc ω) u) M Y' r' z' := hspec.2.2.2.2.2.2.2.1
  have hcov := hspec.2.2.2.2.2.2.2.2
  have hMem : ∀ {ρ : ℝ} {ζ : ℂ}, InLevelRegion ρ ζ → (fun ω => hcirc ω ρ ζ) ∈ M := fun {ρ} {ζ} h =>
    hMle (Submodule.subset_span ⟨⟨GFFObservable.circle ρ ζ, h.1⟩, rfl⟩)
  have hXL : ∀ {ρ : ℝ} {ζ : ℂ}, InLevelRegion ρ ζ → MemLp (fun ω => hcirc ω ρ ζ) 2 P := fun {ρ} {ζ} h =>
    (wpSpace_gaussian hh).memLp (Submodule.subset_span ⟨⟨GFFObservable.circle ρ ζ, h.1⟩, rfl⟩)
  have hXX : covariance (fun ω => hcirc ω r z) (fun ω => hcirc ω r' z') P =
      wholePlaneGFFCov (.circle r z) (.circle r' z') := hh.covariance_eq (.circle r z) (.circle r' z') hreg.1 hreg'.1
  -- the lateral parts are the observables minus the level-integral versions
  have hLA : (fun ω => latCirc (hcirc ω) r z) =ᵐ[P] (fun ω => hcirc ω r z - Y ω) := by
    filter_upwards [havg] with ω hω
    simp only [latCirc]
    rw [radAvg_eq_wpRad hreg, hω]
  have hLA' : (fun ω => latCirc (hcirc ω) r' z') =ᵐ[P] (fun ω => hcirc ω r' z' - Y' ω) := by
    filter_upwards [havg'] with ω hω
    simp only [latCirc]
    rw [radAvg_eq_wpRad hreg', hω]
  -- the covariances of the observables with the level-integral versions
  have hXY' : covariance (fun ω => hcirc ω r z) Y' P =
      Real.circleAverage (fun y => Real.circleAverage (fun x => min (-Real.log ‖y‖) (-Real.log ‖x‖)) z r) z' r' := by
    have key := hLF' (fun ω => hcirc ω r z) (hMem hreg)
      (by simp only [cov_obs_W_all hh hreg]; exact continuous_circleAverage_min_max hr hzr)
      (by
        simp only [cov_obs_W_all hh hreg]
        have hc : Continuous fun x : ℝ => Real.circleAverage
            (fun y => min (max (-Real.log ‖circleMap z' r' x‖) 0) (-Real.log ‖y‖)) z r :=
          (continuous_circleAverage_min_max hr hzr).comp (continuous_neg_log_circleMap hr' z' hzr')
        exact ((continuous_const.mul hc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
          Ioc_subset_Icc_self)
    rw [key, ← circleAverage_neg_log_eq_levelIntegral (fun u => covariance (fun ω => hcirc ω r z) (fun ω => wpRad (hcirc ω) u) P) hr' z' hzr']
    refine Real.circleAverage_congr_sphere (fun y hy => ?_)
    simp only [cov_obs_W_all hh hreg]
    rw [max_eq_left (neg_log_nonneg_of_mem_sphere hreg' hy)]
  have hMg := hspec.1
  have hYm2 : MemLp Y 2 P := hMg.memLp hYmem
  have hY'm2 : MemLp Y' 2 P := hMg.memLp hY'mem
  have hXm : MemLp (fun ω => hcirc ω r z) 2 P := hXL hreg
  have hXm' : MemLp (fun ω => hcirc ω r' z') 2 P := hXL hreg'
  have hYX : covariance Y (fun ω => hcirc ω r' z') P =
      Real.circleAverage (fun x => Real.circleAverage (fun y => min (-Real.log ‖x‖) (-Real.log ‖y‖)) z' r') z r := by
    rw [covariance_comm _ _]
    have key := hLF (fun ω => hcirc ω r' z') (hMem hreg')
      (by simp only [cov_obs_W_all hh hreg']; exact continuous_circleAverage_min_max hr' hzr')
      (by
        simp only [cov_obs_W_all hh hreg']
        have hc : Continuous fun x : ℝ => Real.circleAverage
            (fun y => min (max (-Real.log ‖circleMap z r x‖) 0) (-Real.log ‖y‖)) z' r' :=
          (continuous_circleAverage_min_max hr' hzr').comp (continuous_neg_log_circleMap hr z hzr)
        exact ((continuous_const.mul hc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
          Ioc_subset_Icc_self)
    refine key.trans ((circleAverage_neg_log_eq_levelIntegral
      (fun u => covariance (fun ω => hcirc ω r' z') (fun ω => wpRad (hcirc ω) u) P) hr z hzr).symm.trans ?_)
    refine Real.circleAverage_congr_sphere (fun x hx => ?_)
    simp only [cov_obs_W_all hh hreg']
    rw [max_eq_left (neg_log_nonneg_of_mem_sphere hreg hx)]
  have hLLcov : covariance (fun ω => latCirc (hcirc ω) r z) (fun ω => latCirc (hcirc ω) r' z') P =
      covariance (fun ω => hcirc ω r z - Y ω) (fun ω => hcirc ω r' z' - Y' ω) P :=
    covariance_congr_ae' hLA hLA'
  have hexp : covariance (fun ω => hcirc ω r z - Y ω) (fun ω => hcirc ω r' z' - Y' ω) P =
      covariance (fun ω => hcirc ω r z) (fun ω => hcirc ω r' z') P
        - covariance (fun ω => hcirc ω r z) Y' P - covariance Y (fun ω => hcirc ω r' z') P
        + covariance Y Y' P :=
    covariance_fun_sub_fun_sub hXm hYm2 hXm' hY'm2
  rw [hLLcov, hexp, hXX, hXY', hYX, hcov]
  ring

end Cov

end MatedCRT.Field
