import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseBase
import MatedCRT.FirstPass.Derived.ZeroConeEdgeCountCodeProof
import MatedCRT.FirstPass.Derived.ZeroConeQuantumCurveCovarianceProof
import LatticeProb.LQG.MassReparamBorel
import LatticeProb.LQG.AreaParametrizedCurve
import LatticeProb.Prob.FiniteOnCompactsPar

/-!
# Two quantum clocks of one curve

Let `e : ℝ → ℂ` be a proper surjective curve and `μ` a measure on `ℂ`, finite on compact sets, which parametrizes
`q = e ∘ φ` by mass: `μ (q [s, t]) = t - s`, for an increasing homeomorphism `φ` of `ℝ` fixing `0`. For a continuous
function `g` with compact support, the tilted measure `e^g μ` (`tiltArea g μ`) is parametrized in the same way by a
curve `q' = e ∘ φ'`, and the two time changes are related on the two time tails of `e`.

The signed mass clock `A` of `e` for `μ` is `φ⁻¹`, and the one for `e^g μ` is `φ'⁻¹`. Their difference is
`Δ(e [0, u]) = ∫_{e [0, u]} (e^g - 1) dμ` for `u ≥ 0` and `-Δ(e [u, 0])` for `u < 0`. Since `e` is proper, only the
times in a bounded interval visit the support of `g`, so beyond it the difference is constant, equal to the offsets
`d_+ = ∫_{e [0, ∞)} (e^g - 1) dμ` and `d_- = -∫_{e (-∞, 0]} (e^g - 1) dμ` (`clockOffset`). Consequently
`φ' (t) = φ (t - d_±)` for `±t` large, and first hits are transported by the inverse clock.

## Main declarations

* `ClockDatum`: the hypotheses (proper surjective curve, mass-parametrized by `φ`, tilt function `g`).
* `ClockDatum.exists_tilt_param`: the parametrization `φ'` of `e^g μ`, and the identities
  `massReparamCurve μ e = e ∘ φ`, `massReparamCurve (tiltArea g μ) e = e ∘ φ'`.
* `ClockDatum.eventually_tilt_param_eq`: `φ' t = φ (t - d_±)` on the two tails.
* `ClockDatum.clockOffset_true_sub_false`: `d_+ - d_- = ∫ (e^g - 1) dμ`.
* `firstHit_timeChange`: first hits of a time-changed proper curve.
* `ClockDatum.eventually_window_eq`: windows around the first hit are the same for both clocks.
* `exists_measurable_clockOffset`: the offsets are measurable functions of `(μ, e)`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open MatedCRTHarmonic.MatedCRT (firstHit)
open LatticeProb.LQG (massClock massClock_eq_symm_of_massParam image_Icc_of_reparam)

/-! ### Time changes, clock data -/

/-- The curve `e` run with the time change `v`: `t ↦ e (v t)`. -/
def timeChange (e : C(ℝ, ℂ)) (v : ℝ ≃o ℝ) : C(ℝ, ℂ) := e.comp ⟨v, v.continuous⟩

/-- Evaluation of a time-changed curve. -/
@[simp]
theorem timeChange_apply (e : C(ℝ, ℂ)) (v : ℝ ≃o ℝ) (t : ℝ) : timeChange e v t = e (v t) := rfl

/-- **Clock datum.** `e` is a proper surjective curve through `0` at time `0`, `μ` is finite on compact sets and
parametrizes `e ∘ φ` by mass (`φ` an increasing homeomorphism of `ℝ` fixing `0`), and `g` is a continuous function
with compact support. -/
structure ClockDatum (g : ℂ → ℝ) (μ : Measure ℂ) (e : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ) : Prop where
  /-- `e` is proper. -/
  proper : Tendsto e (cocompact ℝ) (cocompact ℂ)
  /-- `e` is surjective. -/
  surjective : Function.Surjective e
  /-- `e` starts at the origin. -/
  map_zero : e 0 = 0
  /-- `μ` is finite on compact sets. -/
  finiteOnCompacts : IsFiniteMeasureOnCompacts μ
  /-- `φ` fixes `0`. -/
  phi_zero : φ 0 = 0
  /-- `e ∘ φ` is parametrized by `μ`-mass. -/
  area : ∀ s t : ℝ, s ≤ t → μ ((fun u => e (φ u)) '' Icc s t) = ENNReal.ofReal (t - s)
  /-- `g` is continuous. -/
  continuous_g : Continuous g
  /-- `g` has compact support. -/
  compactSupport_g : HasCompactSupport g

/-- `φ'` parametrizes `e` by the mass of the tilted measure `e^g μ`, fixing `0`. -/
def IsTiltParam (g : ℂ → ℝ) (μ : Measure ℂ) (e : C(ℝ, ℂ)) (φ' : ℝ ≃o ℝ) : Prop :=
  φ' 0 = 0 ∧ ∀ s t : ℝ, s ≤ t → tiltArea g μ ((fun u => e (φ' u)) '' Icc s t) = ENNReal.ofReal (t - s)

/-! ### Measurability of images of intervals, properness -/

/-- The image of a compact interval under a continuous curve is measurable. -/
theorem measurableSet_image_Icc (e : C(ℝ, ℂ)) (a b : ℝ) : MeasurableSet (e '' Icc a b) :=
  (isCompact_Icc.image e.continuous).measurableSe

/-- The image of the future half-line is measurable (a countable union of compact images). -/
theorem measurableSet_image_Ici (e : C(ℝ, ℂ)) : MeasurableSet (e '' Ici 0) := by
  have h : e '' Ici 0 = ⋃ n : ℕ, e '' Icc 0 (n : ℝ) := by
    rw [← image_iUnion]
    congr 1
    ext x
    simp only [mem_Ici, mem_iUnion, mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  rw [h]
  exact MeasurableSet.iUnion fun n => measurableSet_image_Icc e 0 n

/-- The image of the past half-line is measurable (a countable union of compact images). -/
theorem measurableSet_image_Iic (e : C(ℝ, ℂ)) : MeasurableSet (e '' Iic 0) := by
  have h : e '' Iic 0 = ⋃ n : ℕ, e '' Icc (-(n : ℝ)) 0 := by
    rw [← image_iUnion]
    congr 1
    ext x
    simp only [mem_Iic, mem_iUnion, mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (-x)
      exact ⟨n, by linarith, hx⟩
    · rintro ⟨n, -, hx⟩
      exact hx
  rw [h]
  exact MeasurableSet.iUnion fun n => measurableSet_image_Icc e _ 0

/-- **Properness in terms of times.** A proper curve avoids a compact set for all times of large modulus. -/
theorem exists_radius_of_proper {e : C(ℝ, ℂ)} (he : Tendsto e (cocompact ℝ) (cocompact ℂ)) {K : Set ℂ}
    (hK : IsCompact K) : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ |t| → e t ∉ K := by
  have h : ∀ᶠ t in cocompact ℝ, e t ∈ Kᶜ := he.eventually hK.compl_mem_cocompac
  rw [cocompact_eq_atBot_atTop, eventually_sup] at h
  obtain ⟨a, ha⟩ := eventually_atBot.1 h.1
  obtain ⟨b, hb⟩ := eventually_atTop.1 h.2
  refine ⟨max (max (-a) b) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
  have h1 : -a ≤ max (max (-a) b) 1 := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : b ≤ max (max (-a) b) 1 := (le_max_right _ _).trans (le_max_left _ _)
  by_cases h0 : 0 ≤
  · rw [abs_of_nonneg h0] at h
    exact hb t (h2.trans ht)
  · rw [abs_of_neg (not_le.1 h0)] at h
    exact ha t (by linarith)

/-- The first hit of a point by a time-changed proper curve: the inverse time change of the first hit of `e`. -/
theorem firstHit_timeChange {e : C(ℝ, ℂ)} (he : Tendsto e (cocompact ℝ) (cocompact ℂ)) (v : ℝ ≃o ℝ) {z : ℂ}
    (hz : z ∈ range e) : firstHit (timeChange e v) z = v.symm (firstHit e z) := by
  have hclosed : IsClosed {t : ℝ | e t = z} := isClosed_eq e.continuous continuous_cons
  obtain ⟨R, -, hR⟩ := exists_radius_of_proper he (isCompact_singleton (x := z))
  have hbdd : BddBelow {t : ℝ | e t = z} :=
    ⟨-R, fun t ht => not_lt.1 fun h => hR t (by linarith [neg_le_abs t]) ht⟩
  obtain ⟨t₀, ht₀⟩ := hz
  have hmem : sInf {t : ℝ | e t = z} ∈ {t : ℝ | e t = z} := hclosed.csInf_mem ⟨t₀, ht₀⟩ hbdd
  have hleast : IsLeast {t : ℝ | e t = z} (sInf {t : ℝ | e t = z}) := ⟨hmem, fun t ht => csInf_le hbdd ht⟩
  have hleast' : IsLeast {t : ℝ | timeChange e v t = z} (v.symm (sInf {t : ℝ | e t = z})) := by
    refine ⟨?_, fun t ht => ?_⟩
    · show e (v (v.symm (sInf {t : ℝ | e t = z}))) = z
      rw [v.apply_symm_apply]
      exact hmem
    · rw [v.symm_apply_le]
      exact hleast.2 h
  show sInf {t : ℝ | timeChange e v t = z} = v.symm (sInf {t : ℝ | e t = z})
  exact hleast'.csInf_eq

/-! ### The tilted measure -/

section Til

variable {g : ℂ → ℝ} {μ : Measure ℂ} {e : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ}

/-- The tilted measure of a measurable set, as a set integral. -/
theorem tiltArea_apply (g : ℂ → ℝ) (μ : Measure ℂ) {s : Set ℂ} (hs : MeasurableSet s) :
    tiltArea g μ s = ∫⁻ z in s, ENNReal.ofReal (Real.exp (g z)) ∂μ :=
  withDensity_apply _ hs

/-- Upper bound for the tilted measure of a measurable set. -/
theorem tiltArea_le {M : ℝ} (hM : ∀ z, g z ≤ M) {s : Set ℂ} (hs : MeasurableSet s) :
    tiltArea g μ s ≤ ENNReal.ofReal (Real.exp M) * μ s := by
  rw [tiltArea_apply g μ hs, ← setLIntegral_const]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hM z))

/-- Lower bound for the tilted measure of a measurable set. -/
theorem le_tiltArea {m : ℝ} (hm : ∀ z, m ≤ g z) {s : Set ℂ} (hs : MeasurableSet s) :
    ENNReal.ofReal (Real.exp m) * μ s ≤ tiltArea g μ s := by
  rw [tiltArea_apply g μ hs, ← setLIntegral_const]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hm z))

/-- The tilted measure is absolutely continuous with respect to the original one. -/
theorem tiltArea_absolutelyContinuous (g : ℂ → ℝ) (μ : Measure ℂ) : tiltArea g μ ≪ μ :=
  withDensity_absolutelyContinuous _ _

/-- A continuous function with compact support is bounded. -/
theorem ClockDatum.exists_abs_le (H : ClockDatum g μ e φ) : ∃ M : ℝ, ∀ z, |g z| ≤ M := by
  obtain ⟨C, hC⟩ := H.compactSupport_g.exists_bound_of_continuous H.continuous_g
  exact ⟨C, fun z => by simpa only [Real.norm_eq_abs] using hC z⟩

/-- The tilted measure is finite on compact sets. -/
theorem ClockDatum.isFiniteMeasureOnCompacts_tiltArea (H : ClockDatum g μ e φ) :
    IsFiniteMeasureOnCompacts (tiltArea g μ) := by
  haveI := H.finiteOnCompacts
  obtain ⟨M, hM⟩ := H.exists_abs_le
  refine ⟨fun K hK => ?_⟩
  exact lt_of_le_of_lt (tiltArea_le (fun z => (le_abs_self _).trans (hM z)) hK.measurableSet)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)

/-- The image of an interval under a time change is the image of the transformed interval. -/
theorem image_Icc_symm (e : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ) (a b : ℝ) :
    (fun u => e (φ u)) '' Icc (φ.symm a) (φ.symm b) = e '' Icc a b := by
  rw [image_Icc_of_reparam e (fun u => e (φ u)) φ (fun _ => rfl)]
  simp

/-- The mass of an interval image: `μ (e [a, b]) = φ⁻¹ b - φ⁻¹ a`. -/
theorem ClockDatum.mu_image_Icc (H : ClockDatum g μ e φ) {a b : ℝ} (hab : a ≤ b) :
    μ (e '' Icc a b) = ENNReal.ofReal (φ.symm b - φ.symm a) := by
  rw [← image_Icc_symm e φ a b]
  exact H.area _ _ (φ.symm.monotone hab)

/-- Images of non-overlapping intervals of `e` meet in a `μ`-null set. -/
theorem ClockDatum.inter_null (H : ClockDatum g μ e φ) {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    μ (e '' Icc a b ∩ e '' Icc c d) = 0 := by
  rw [← image_Icc_symm e φ a b, ← image_Icc_symm e φ c d]
  exact MatedCRT.GMS310Transfer.measure_image_Icc_inter_image_Icc_eq_zero (q := fun u => e (φ u))
    (e.continuous.comp φ.continuous) H.area (φ.symm.monotone hab) (φ.symm.monotone hbc) (φ.symm.monotone hcd)

/-- Additivity of the mass of images of adjacent intervals, for measures absolutely continuous with respect to `μ`
and finite on compact sets. -/
theorem ClockDatum.measure_Icc_add (H : ClockDatum g μ e φ) {ρ : Measure ℂ} [IsFiniteMeasureOnCompacts ρ]
    (hρ : ρ ≪ μ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (ρ (e '' Icc a c)).toReal = (ρ (e '' Icc a b)).toReal + (ρ (e '' Icc b c)).toReal := by
  have hunion : e '' Icc a c = e '' Icc a b ∪ e '' Icc b c := by
    rw [← image_union, Icc_union_Icc_eq_Icc hab hbc]
  have h1 := measure_union_add_inter (μ := ρ) (e '' Icc a b) (measurableSet_image_Icc e b c)
  have h2 : ρ (e '' Icc a b ∩ e '' Icc b c) = 0 := hρ (H.inter_null hab le_rfl hbc)
  rw [h2, add_zero, ← hunion] at h1
  have hA : ρ (e '' Icc a b) ≠ ⊤ := (isCompact_Icc.image e.continuous).measure_lt_top.ne
  have hB : ρ (e '' Icc b c) ≠ ⊤ := (isCompact_Icc.image e.continuous).measure_lt_top.ne
  rw [h1, ENNReal.toReal_add hA hB]

/-- The signed mass clock has increments equal to the masses of the interval images. -/
theorem ClockDatum.massClock_sub (H : ClockDatum g μ e φ) {ρ : Measure ℂ} [IsFiniteMeasureOnCompacts ρ]
    (hρ : ρ ≪ μ) {s t : ℝ} (hst : s ≤ t) :
    massClock ρ e t - massClock ρ e s = (ρ (e '' Icc s t)).toReal := by
  unfold massClock
  by_cases hs : 0 ≤ s
  · have ht : 0 ≤ t := hs.trans hs
    simp only [hs, ht, ↓reduceIte]
    have := H.measure_Icc_add hρ hs hs
    linarith
  · by_cases ht : 0 ≤
    · simp only [hs, ht, ↓reduceIte]
      have := H.measure_Icc_add hρ (not_le.1 hs).le h
      linarith
    · simp only [hs, ht, ↓reduceIte]
      have := H.measure_Icc_add hρ hst (not_le.1 ht).le
      linarith

/-- The signed mass clock vanishes at `0`. -/
theorem ClockDatum.massClock_zero (H : ClockDatum g μ e φ) {ρ : Measure ℂ} (hρ : ρ ≪ μ) :
    massClock ρ e 0 = 0 := by
  have h0 : μ (e '' Icc 0 0) = 0 := by
    rw [H.mu_image_Icc le_rfl, sub_self, ENNReal.ofReal_zero]
  unfold massClock
  rw [if_pos le_rfl, hρ h0]
  exact ENNReal.toReal_zero

/-- `φ⁻¹ 0 = 0`. -/
theorem ClockDatum.symm_zero (H : ClockDatum g μ e φ) : φ.symm 0 = 0 := by
  rw [OrderIso.symm_apply_eq]
  exact H.phi_zero.symm

/-- Two-sided bounds for the increments of the tilted clock in terms of `φ⁻¹`. -/
theorem ClockDatum.tilt_clock_bounds (H : ClockDatum g μ e φ) {M : ℝ} (hM : ∀ z, |g z| ≤ M) {a b : ℝ}
    (hab : a ≤ b) :
    Real.exp (-M) * (φ.symm b - φ.symm a) ≤ massClock (tiltArea g μ) e b - massClock (tiltArea g μ) e a ∧
      massClock (tiltArea g μ) e b - massClock (tiltArea g μ) e a ≤ Real.exp M * (φ.symm b - φ.symm a) := by
  haveI := H.finiteOnCompacts
  haveI := H.isFiniteMeasureOnCompacts_tiltArea
  rw [H.massClock_sub (tiltArea_absolutelyContinuous g μ) hab]
  have hS := measurableSet_image_Icc e a b
  have hΔ : 0 ≤ φ.symm b - φ.symm a := sub_nonneg.2 (φ.symm.monotone hab)
  have hμ := H.mu_image_Icc hab
  have hfin : tiltArea g μ (e '' Icc a b) ≠ ⊤ := (isCompact_Icc.image e.continuous).measure_lt_top.ne
  constructor
  · have h := le_tiltArea (g := g) (μ := μ) (m := -M)
      (fun z => (neg_le_neg (hM z)).trans (neg_abs_le _)) hS
    rw [hμ] at h
    have h2 := ENNReal.toReal_mono hfin h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal hΔ] at h2
  · have h := tiltArea_le (g := g) (μ := μ) (M := M) (fun z => (le_abs_self _).trans (hM z)) hS
    rw [hμ] at h
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal hΔ] at h2

/-- **The curve reparametrized by a mass-parametrization.** If `e ∘ v` is parametrized by the mass of `ρ`, then
`massReparamCurve ρ e` is `e ∘ v`. -/
theorem massReparamCurve_eq_timeChange {ρ : Measure ℂ} {e : C(ℝ, ℂ)} {v : ℝ ≃o ℝ} (hv0 : v 0 = 0)
    (harea : ∀ s t : ℝ, s ≤ t → ρ ((fun u => e (v u)) '' Icc s t) = ENNReal.ofReal (t - s)) :
    massReparamCurve ρ e = timeChange e v := by
  have hG : IsGoodMassClock ρ e := isGoodMassClock_of_massParam (η := fun u => e (v u)) v hv0 (fun _ => rfl) harea
  ex
  rw [massReparamCurve_apply_of_good hG]
  exact LatticeProb.LQG.massReparam_eq_of_massParam ρ e (fun u => e (v u)) v hv0 (fun _ => rfl) harea

/-- **Target 1.** The tilted measure parametrizes `e` by mass through a time change `φ'`, and both mass
reparametrizations are the time changes of `e`. -/
theorem ClockDatum.exists_tilt_param (H : ClockDatum g μ e φ) :
    ∃ φ' : ℝ ≃o ℝ, IsTiltParam g μ e φ' ∧ massReparamCurve μ e = timeChange e φ ∧
      massReparamCurve (tiltArea g μ) e = timeChange e φ' := by
  haveI := H.finiteOnCompacts
  haveI := H.isFiniteMeasureOnCompacts_tiltArea
  obtain ⟨M, hM⟩ := H.exists_abs_le
  have hac := tiltArea_absolutelyContinuous g μ
  have hdiff : ∀ s t : ℝ, s ≤ t → massClock (tiltArea g μ) e t - massClock (tiltArea g μ) e s =
      (tiltArea g μ (e '' Icc s t)).toReal := fun s t hst => H.massClock_sub hac hs
  have hF0 := H.massClock_zero hac
  have hsm : StrictMono (massClock (tiltArea g μ) e) := by
    intro s t hs
    have h := (H.tilt_clock_bounds hM hst.le).1
    have hpos : 0 < Real.exp (-M) * (φ.symm t - φ.symm s) :=
      mul_pos (Real.exp_pos _) (sub_pos.2 (φ.symm.strictMono hst))
    linarith
  have key : ∀ a b : ℝ, a ≤ b →
      |massClock (tiltArea g μ) e b - massClock (tiltArea g μ) e a| ≤ Real.exp M * |φ.symm b - φ.symm a| := by
    intro a b hab
    obtain ⟨h1, h2⟩ := H.tilt_clock_bounds hM hab
    have hψ : 0 ≤ φ.symm b - φ.symm a := sub_nonneg.2 (φ.symm.monotone hab)
    have hF : 0 ≤ massClock (tiltArea g μ) e b - massClock (tiltArea g μ) e a :=
      le_trans (mul_nonneg (Real.exp_pos _).le hψ) h1
    rw [abs_of_nonneg hF, abs_of_nonneg hψ]
    exact h2
  have hcont : Continuous (massClock (tiltArea g μ) e) := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 φ.symm.continuous b (ε / Real.exp M)
      (div_pos hε (Real.exp_pos M))
    refine ⟨δ, hδ, fun a ha => ?_⟩
    have h1 := hδ' a ha
    rw [Real.dist_eq] at h1 ⊢
    have h3 : |massClock (tiltArea g μ) e a - massClock (tiltArea g μ) e b| ≤
        Real.exp M * |φ.symm a - φ.symm b| := by
      rcases le_total a b with hab | hab
      · rw [abs_sub_comm, abs_sub_comm (φ.symm a)]
        exact key a b hab
      · exact key b a hab
    calc |massClock (tiltArea g μ) e a - massClock (tiltArea g μ) e b|
        ≤ Real.exp M * |φ.symm a - φ.symm b| := h3
      _ < Real.exp M * (ε / Real.exp M) := mul_lt_mul_of_pos_left h1 (Real.exp_pos M)
      _ = ε := by field_simp
  have htop : Tendsto (massClock (tiltArea g μ) e) atTop atTop := by
    have hψ : Tendsto φ.symm atTop atTop :=
      φ.symm.monotone.tendsto_atTop_atTop fun b => ⟨φ b, by simp⟩
    refine tendsto_atTop_mono' _ ?_ (hψ.const_mul_atTop (Real.exp_pos (-M)))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t h
    have h := (H.tilt_clock_bounds hM ht).1
    rw [H.symm_zero, hF0] at h
    linarith
  have hbot : Tendsto (massClock (tiltArea g μ) e) atBot atBot := by
    have hψ : Tendsto φ.symm atBot atBot :=
      φ.symm.monotone.tendsto_atBot_atBot fun b => ⟨φ b, by simp⟩
    refine tendsto_atBot_mono' _ ?_ (hψ.const_mul_atBot (Real.exp_pos (-M)))
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t h
    have h := (H.tilt_clock_bounds hM ht).1
    rw [H.symm_zero, hF0] at h
    linarith
  have hsurj : Function.Surjective (massClock (tiltArea g μ) e) := hcont.surjective htop hbo
  let Fiso : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective _ hsm hsurj
  have hFiso : ∀ x, Fiso x = massClock (tiltArea g μ) e x := fun x => rfl
  have hφ'0 : Fiso.symm 0 = 0 := by
    rw [OrderIso.symm_apply_eq, hFiso, hF0]
  have hpar : IsTiltParam g μ e Fiso.symm := by
    refine ⟨hφ'0, fun s t hst => ?_⟩
    rw [image_Icc_of_reparam e (fun u => e (Fiso.symm u)) Fiso.symm (fun _ => rfl)]
    have h1 := hdiff (Fiso.symm s) (Fiso.symm t) (Fiso.symm.monotone hst)
    have e1 : massClock (tiltArea g μ) e (Fiso.symm s) = s := by
      rw [← hFiso]
      exact Fiso.apply_symm_apply s
    have e2 : massClock (tiltArea g μ) e (Fiso.symm t) = t := by
      rw [← hFiso]
      exact Fiso.apply_symm_apply
    have hfin : tiltArea g μ (e '' Icc (Fiso.symm s) (Fiso.symm t)) ≠ ⊤ :=
      (isCompact_Icc.image e.continuous).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin]
    congr 1
    linarith
  exact ⟨Fiso.symm, hpar, massReparamCurve_eq_timeChange H.phi_zero H.area,
    massReparamCurve_eq_timeChange hpar.1 hpar.2⟩

/-! ### The offsets of the tilted clock -/

/-- The function `e^g - 1` is integrable for a measure finite on compact sets. -/
theorem ClockDatum.integrable_tilt_sub (H : ClockDatum g μ e φ) :
    Integrable (fun z => Real.exp (g z) - 1) μ := by
  haveI := H.finiteOnCompacts
  refine Continuous.integrable_of_hasCompactSupport (by have := H.continuous_g; fun_prop) ?_
  refine HasCompactSupport.intro (K := tsupport g) H.compactSupport_g fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx]
  simp

/-- **Times visiting the support of `g`.** Beyond a radius `R`, the curve `e` does not visit the support of `g`. -/
theorem ClockDatum.exists_radius (H : ClockDatum g μ e φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ |t| → g (e t) = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_radius_of_proper H.proper (K := tsupport g) H.compactSupport_g
  exact ⟨R, hR0, fun t ht => image_eq_zero_of_notMem_tsupport (hR t ht)⟩

/-- The tilted mass of a measurable set of finite mass minus its mass is the integral of `e^g - 1`. -/
theorem ClockDatum.toReal_tilt_sub (H : ClockDatum g μ e φ) {S : Set ℂ} (hS : MeasurableSet S)
    (hfin : μ S ≠ ⊤) :
    (tiltArea g μ S).toReal - (μ S).toReal = ∫ z in S, (Real.exp (g z) - 1) ∂μ := by
  have hI1 : IntegrableOn (fun z => Real.exp (g z) - 1) S μ := H.integrable_tilt_sub.integrableOn
  have hI2 : IntegrableOn (fun _ : ℂ => (1 : ℝ)) S μ := integrableOn_const hfin
  have hmeas : Measurable fun z => Real.exp (g z) :=
    Real.measurable_exp.comp H.continuous_g.measurable
  have h1 : (tiltArea g μ S).toReal = ∫ z in S, Real.exp (g z) ∂μ := by
    rw [tiltArea_apply g μ hS]
    exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => (Real.exp_pos (g z)).le)
      hmeas.aestronglyMeasurable).symm
  have h2 : ∫ z in S, Real.exp (g z) ∂μ = (∫ z in S, (Real.exp (g z) - 1) ∂μ) + (μ S).toReal := by
    have := integral_add hI1 hI2
    simp only [sub_add_cancel] at this
    rw [this, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
  rw [h1, h2]
  ring

/-- The integral of `e^g - 1` over the image of `[0, u]` is the integral over the image of `[0, ∞)`, for `u`
beyond the times at which `e` visits the support of `g`. -/
theorem setIntegral_image_Icc_eq_Ici {R : ℝ} (hR : ∀ t : ℝ, R ≤ |t| → g (e t) = 0) {u : ℝ} (hu : R ≤ u) :
    ∫ z in e '' Icc 0 u, (Real.exp (g z) - 1) ∂μ = ∫ z in e '' Ici 0, (Real.exp (g z) - 1) ∂μ := by
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_image_Ici e) ?_ ?_
  · exact image_mono Icc_subset_Ici_self
  · rintro _ ⟨⟨r, hr, rfl⟩, hx⟩
    have hru : u < r := by
      by_contra h
      exact hx ⟨r, ⟨hr, not_lt.1 h⟩, rfl⟩
    have hr0 : 0 ≤ r := hr
    have h0 : g (e r) = 0 := hR r (by rw [abs_of_nonneg hr0]; linarith)
    simp [h0]

/-- The integral of `e^g - 1` over the image of `[u, 0]` is the integral over the image of `(-∞, 0]`, for `u`
before the times at which `e` visits the support of `g`. -/
theorem setIntegral_image_Icc_eq_Iic {R : ℝ} (hR : ∀ t : ℝ, R ≤ |t| → g (e t) = 0) {u : ℝ} (hu : u ≤ -R) :
    ∫ z in e '' Icc u 0, (Real.exp (g z) - 1) ∂μ = ∫ z in e '' Iic 0, (Real.exp (g z) - 1) ∂μ := by
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_image_Iic e) ?_ ?_
  · exact image_mono Icc_subset_Iic_self
  · rintro _ ⟨⟨r, hr, rfl⟩, hx⟩
    have hur : r < u := by
      by_contra h
      exact hx ⟨r, ⟨not_lt.1 h, hr⟩, rfl⟩
    have h0 : g (e r) = 0 := hR r (by linarith [neg_le_abs r])
    simp [h0]

/-- On the future time tail the tilted clock is the old one plus `d_+`. -/
theorem ClockDatum.massClock_tilt_sub_true (H : ClockDatum g μ e φ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t : ℝ, R ≤ |t| → g (e t) = 0) {u : ℝ} (hu : R ≤ u) :
    massClock (tiltArea g μ) e u - massClock μ e u = clockOffset g μ e true := by
  haveI := H.finiteOnCompacts
  have hu0 : 0 ≤ u := (hR0.trans_le hu).le
  have hS := measurableSet_image_Icc e 0 u
  have hfin : μ (e '' Icc 0 u) ≠ ⊤ := (isCompact_Icc.image e.continuous).measure_lt_top.ne
  unfold massClock
  rw [if_pos hu0, if_pos hu0, H.toReal_tilt_sub hS hfin]
  exact setIntegral_image_Icc_eq_Ici hR hu

/-- On the past time tail the tilted clock is the old one plus `d_-`. -/
theorem ClockDatum.massClock_tilt_sub_false (H : ClockDatum g μ e φ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ t : ℝ, R ≤ |t| → g (e t) = 0) {u : ℝ} (hu : u ≤ -R) :
    massClock (tiltArea g μ) e u - massClock μ e u = clockOffset g μ e false := by
  haveI := H.finiteOnCompacts
  have hu0 : ¬ 0 ≤ u := not_le.2 (by linarith)
  have hS := measurableSet_image_Icc e u 0
  have hfin : μ (e '' Icc u 0) ≠ ⊤ := (isCompact_Icc.image e.continuous).measure_lt_top.ne
  have h1 := H.toReal_tilt_sub hS hfin
  have h2 := setIntegral_image_Icc_eq_Iic (μ := μ) hR hu
  have h3 : clockOffset g μ e false = -∫ z in e '' Iic 0, (Real.exp (g z) - 1) ∂μ := rfl
  unfold massClock
  rw [if_neg hu0, if_neg hu0, h3]
  linarith

/-- The inverse of the tilted time change is the old one plus `d_+` on the future tail. -/
theorem ClockDatum.symm_tilt_eq_true (H : ClockDatum g μ e φ) {φ' : ℝ ≃o ℝ} (hφ' : IsTiltParam g μ e φ')
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ t : ℝ, R ≤ |t| → g (e t) = 0) {u : ℝ} (hu : R ≤ u) :
    φ'.symm u = φ.symm u + clockOffset g μ e true := by
  have h1 := massClock_eq_symm_of_massParam (tiltArea g μ) e (fun u => e (φ' u)) φ' hφ'.1 (fun _ => rfl)
    hφ'.2 u
  have h2 := massClock_eq_symm_of_massParam μ e (fun u => e (φ u)) φ H.phi_zero (fun _ => rfl) H.area u
  have h3 := H.massClock_tilt_sub_true hR0 hR hu
  linarith

/-- The inverse of the tilted time change is the old one plus `d_-` on the past tail. -/
theorem ClockDatum.symm_tilt_eq_false (H : ClockDatum g μ e φ) {φ' : ℝ ≃o ℝ} (hφ' : IsTiltParam g μ e φ')
    {R : ℝ} (hR0 : 0 < R) (hR : ∀ t : ℝ, R ≤ |t| → g (e t) = 0) {u : ℝ} (hu : u ≤ -R) :
    φ'.symm u = φ.symm u + clockOffset g μ e false := by
  have h1 := massClock_eq_symm_of_massParam (tiltArea g μ) e (fun u => e (φ' u)) φ' hφ'.1 (fun _ => rfl)
    hφ'.2 u
  have h2 := massClock_eq_symm_of_massParam μ e (fun u => e (φ u)) φ H.phi_zero (fun _ => rfl) H.area u
  have h3 := H.massClock_tilt_sub_false hR0 hR hu
  linarith

/-- **Target 2.** Beyond the times at which `e` visits the support of `g`, the tilted time change is the old one
shifted by the offsets: `φ' t = φ (t - d_±)` for `±t` large. -/
theorem ClockDatum.eventually_tilt_param_eq (H : ClockDatum g μ e φ) {φ' : ℝ ≃o ℝ}
    (hφ' : IsTiltParam g μ e φ') :
    ∃ T : ℝ, (∀ t : ℝ, T ≤ t → φ' t = φ (t - clockOffset g μ e true)) ∧
      ∀ t : ℝ, t ≤ -T → φ' t = φ (t - clockOffset g μ e false) := by
  obtain ⟨R, hR0, hR⟩ := H.exists_radius
  refine ⟨max (φ'.symm R) (-φ'.symm (-R)), fun t ht => ?_, fun t ht => ?_⟩
  · have h1 : φ'.symm R ≤ t := (le_max_left _ _).trans h
    have hu : R ≤ φ' t := by
      calc R = φ' (φ'.symm R) := (φ'.apply_symm_apply R).symm
        _ ≤ φ' t := φ'.monotone h1
    have h2 := H.symm_tilt_eq_true hφ' hR0 hR hu
    rw [φ'.symm_apply_apply] at h2
    have h3 : φ.symm (φ' t) = t - clockOffset g μ e true := by linarith
    calc φ' t = φ (φ.symm (φ' t)) := (φ.apply_symm_apply _).symm
      _ = φ (t - clockOffset g μ e true) := by rw [h3]
  · have h1 : t ≤ φ'.symm (-R) := by
      have := neg_le_neg ((le_max_right (φ'.symm R) (-φ'.symm (-R))).trans' le_rfl |>.trans (le_refl _))
      linarith [le_max_right (φ'.symm R) (-φ'.symm (-R))]
    have hu : φ' t ≤ -R := by
      calc φ' t ≤ φ' (φ'.symm (-R)) := φ'.monotone h1
        _ = -R := φ'.apply_symm_apply _
    have h2 := H.symm_tilt_eq_false hφ' hR0 hR hu
    rw [φ'.symm_apply_apply] at h2
    have h3 : φ.symm (φ' t) = t - clockOffset g μ e false := by linarith
    calc φ' t = φ (φ.symm (φ' t)) := (φ.apply_symm_apply _).symm
      _ = φ (t - clockOffset g μ e false) := by rw [h3]

/-- **Target 3.** The difference of the two offsets is the total mass of `e^g - 1`: the two time halves of `e`
cover `ℂ` and overlap in a null set. -/
theorem ClockDatum.clockOffset_true_sub_false (H : ClockDatum g μ e φ) :
    clockOffset g μ e true - clockOffset g μ e false = ∫ z, (Real.exp (g z) - 1) ∂μ := by
  haveI := H.finiteOnCompacts
  have hint := H.integrable_tilt_sub
  have hcover : e '' Ici 0 ∪ e '' Iic 0 = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨t, rfl⟩ := H.surjective z
    rcases le_total 0 t with h | h
    · exact Or.inl ⟨t, h, rfl⟩
    · exact Or.inr ⟨t, h, rfl⟩
  have hnull : μ (e '' Ici 0 ∩ e '' Iic 0) = 0 := by
    refine measure_mono_null (t := ⋃ n : ℕ, e '' Icc (-(n : ℝ)) 0 ∩ e '' Icc 0 (n : ℝ)) ?_ ?_
    · rintro _ ⟨⟨s, hs, rfl⟩, ⟨s', hs', hss'⟩⟩
      obtain ⟨n, hn⟩ := exists_nat_ge (max s (-s'))
      refine mem_iUnion.2 ⟨n, ⟨s', ⟨?_, hs'⟩, hss'⟩, ⟨s, ⟨hs, ?_⟩, rfl⟩⟩
      · linarith [le_max_right s (-s')]
      · linarith [le_max_left s (-s')]
    · exact measure_iUnion_null fun n =>
        H.inter_null (neg_nonpos.2 (Nat.cast_nonneg n)) le_rfl (Nat.cast_nonneg n)
  have h1 : ∫ z, (Real.exp (g z) - 1) ∂μ =
      ∫ z in e '' Ici 0 ∪ e '' Iic 0, (Real.exp (g z) - 1) ∂μ := by
    rw [hcover, Measure.restrict_univ]
  have ht : clockOffset g μ e true = ∫ z in e '' Ici 0, (Real.exp (g z) - 1) ∂μ := rfl
  have hf : clockOffset g μ e false = -∫ z in e '' Iic 0, (Real.exp (g z) - 1) ∂μ := rfl
  rw [ht, hf, h1, setIntegral_union₀ hnull (measurableSet_image_Iic e).nullMeasurableSet hint.integrableOn
    hint.integrableOn]
  ring

/-- **Target 5.** For every window half-length `L` there is a radius `R` such that, for a point `z` whose firs
visit by `e` is beyond `R` in the future (resp. in the past), the first hit of `z` by the tilted curve `q'` is the
first hit by `q` shifted by `d_+` (resp. `d_-`), and the curves `q'` and `q` agree on the window of half-length `L`
around their first hits of `z`. -/
theorem ClockDatum.eventually_window_eq (H : ClockDatum g μ e φ) {φ' : ℝ ≃o ℝ} (hφ' : IsTiltParam g μ e φ')
    (L : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ,
      (R ≤ firstHit e z →
        firstHit (timeChange e φ') z = firstHit (timeChange e φ) z + clockOffset g μ e true ∧
          ∀ t ∈ Icc (-L) L, timeChange e φ' (firstHit (timeChange e φ') z + t) =
            timeChange e φ (firstHit (timeChange e φ) z + t)) ∧
      (firstHit e z ≤ -R →
        firstHit (timeChange e φ') z = firstHit (timeChange e φ) z + clockOffset g μ e false ∧
          ∀ t ∈ Icc (-L) L, timeChange e φ' (firstHit (timeChange e φ') z + t) =
            timeChange e φ (firstHit (timeChange e φ) z + t)) := by
  obtain ⟨R₀, hR0, hR⟩ := H.exists_radius
  obtain ⟨T, hT₊, hT₋⟩ := H.eventually_tilt_param_eq hφ'
  refine ⟨max R₀ (max (φ (T + L - clockOffset g μ e true)) (-φ (-T - L - clockOffset g μ e false))),
    fun z => ?_⟩
  have hz : z ∈ range e := H.surjective z
  rw [firstHit_timeChange H.proper φ' hz, firstHit_timeChange H.proper φ hz]
  set τ := firstHit e z
  constructor
  · intro hτR
    have h1 : R₀ ≤ τ := (le_max_left _ _).trans hτR
    have h2 : φ (T + L - clockOffset g μ e true) ≤ τ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hτR
    have h3 : T + L - clockOffset g μ e true ≤ φ.symm τ := φ.le_symm_apply.2 h2
    have hsym := H.symm_tilt_eq_true hφ' hR0 hR h1
    refine ⟨hsym, fun t ht => ?_⟩
    simp only [timeChange_apply]
    rw [hsym, hT₊ (φ.symm τ + clockOffset g μ e true + t) (by linarith [ht.1, ht.2])]
    congr 2
    ring
  · intro hτR
    have h1 : τ ≤ -R₀ := hτR.trans (neg_le_neg (le_max_left _ _))
    have h2 : τ ≤ φ (-T - L - clockOffset g μ e false) := by
      have := neg_le_neg ((le_max_right _ _).trans (le_max_right _ _) :
        -φ (-T - L - clockOffset g μ e false) ≤ max R₀ (max (φ (T + L - clockOffset g μ e true))
          (-φ (-T - L - clockOffset g μ e false))))
      linarith
    have h3 : φ.symm τ ≤ -T - L - clockOffset g μ e false := φ.symm_apply_le.2 h2
    have hsym := H.symm_tilt_eq_false hφ' hR0 hR h1
    refine ⟨hsym, fun t ht => ?_⟩
    simp only [timeChange_apply]
    rw [hsym, hT₋ (φ.symm τ + clockOffset g μ e false + t) (by linarith [ht.1, ht.2])]
    congr 2
    ring

/-! ### Measurability of the offsets -/

/-- The tilting of a measure by a measurable function is a measurable map on measures. -/
theorem measurable_tiltArea {g : ℂ → ℝ} (hg : Measurable g) : Measurable (tiltArea g) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hf : Measurable fun z => ENNReal.ofReal (Real.exp (g z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hg)
  have h : (fun μ : Measure ℂ => tiltArea g μ s) =
      fun μ => ∫⁻ x, s.indicator (fun z => ENNReal.ofReal (Real.exp (g z))) x ∂μ := by
    funext μ
    rw [lintegral_indicator hs]
    exact withDensity_apply _ hs
  rw [h]
  exact Measure.measurable_lintegral (hf.indicator hs)

/-- The difference of the tilted and the original signed mass clocks of `e` at time `±n` (`b = true` for `+n`,
`b = false` for `-n`), computed with the finite-on-compacts parts of the measures, so that it is defined and
measurable on all pairs `(μ, e)`. -/
def clockOffsetSeq (g : ℂ → ℝ) (b : Bool) (n : ℕ) (p : Measure ℂ × C(ℝ, ℂ)) : ℝ :=
  massClock (LatticeProb.finiteOnCompactsPart (tiltArea g p.1)) p.2 (cond b (n : ℝ) (-(n : ℝ))) -
    massClock (LatticeProb.finiteOnCompactsPart p.1) p.2 (cond b (n : ℝ) (-(n : ℝ)))

/-- Each term of the sequence defining the offsets is measurable in `(μ, e)`. -/
theorem measurable_clockOffsetSeq {g : ℂ → ℝ} (hg : Measurable g) (b : Bool) (n : ℕ) :
    Measurable (clockOffsetSeq g b n) := by
  have hμ : Measurable fun p : Measure ℂ × C(ℝ, ℂ) => LatticeProb.finiteOnCompactsPart (tiltArea g p.1) :=
    LatticeProb.measurable_finiteOnCompactsPart_comp ((measurable_tiltArea hg).comp measurable_fst)
  have hμ' : Measurable fun p : Measure ℂ × C(ℝ, ℂ) => LatticeProb.finiteOnCompactsPart p.1 :=
    LatticeProb.measurable_finiteOnCompactsPart_comp measurable_fs
  have hLm : ∀ t : ℝ, Measurable fun p : Measure ℂ × C(ℝ, ℂ) => p.2 t := fun t =>
    (continuous_eval_const t).measurable.comp measurable_snd
  unfold clockOffsetSeq
  exact (LatticeProb.LQG.measurable_massClock hμ (fun _ => inferInstance) (L := fun p => ⇑p.2)
    (fun p => p.2.continuous) hLm _).sub
    (LatticeProb.LQG.measurable_massClock hμ' (fun _ => inferInstance) (L := fun p => ⇑p.2)
      (fun p => p.2.continuous) hLm _)

/-- For a clock datum, the sequence `clockOffsetSeq` is eventually equal to the offset `d_±`. -/
theorem ClockDatum.eventually_clockOffsetSeq (H : ClockDatum g μ e φ) (b : Bool) :
    ∀ᶠ n : ℕ in atTop, clockOffsetSeq g b n (μ, e) = clockOffset g μ e b := by
  haveI := H.finiteOnCompacts
  haveI := H.isFiniteMeasureOnCompacts_tiltArea
  obtain ⟨R, hR0, hR⟩ := H.exists_radius
  filter_upwards [eventually_ge_atTop ⌈R⌉₊] with n hn
  have hnR : R ≤ n := (Nat.le_ceil R).trans (by exact_mod_cast hn)
  unfold clockOffsetSeq
  simp only [LatticeProb.finiteOnCompactsPart_eq_self]
  cases b
  · exact H.massClock_tilt_sub_false hR0 hR (by simp only [cond_false]; linarith)
  · exact H.massClock_tilt_sub_true hR0 hR hnR

/-- **Target 6.** The offsets `d_±` are given on clock data by measurable functions of `(μ, e)`: the limits of the
sequences `clockOffsetSeq`, which are eventually constant. -/
theorem exists_measurable_clockOffset {g : ℂ → ℝ} (hg : Measurable g) :
    ∃ F : Bool → Measure ℂ × C(ℝ, ℂ) → ℝ, (∀ b, Measurable (F b)) ∧
      ∀ (b : Bool) (μ : Measure ℂ) (e : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ), ClockDatum g μ e φ →
        F b (μ, e) = clockOffset g μ e b := by
  refine ⟨fun b p => limsup (fun n : ℕ => clockOffsetSeq g b n p) atTop, fun b => ?_,
    fun b μ e φ H => ?_⟩
  · exact Measurable.limsup fun n => measurable_clockOffsetSeq hg b n
  · show limsup (fun n : ℕ => clockOffsetSeq g b n (μ, e)) atTop = _
    rw [limsup_congr (H.eventually_clockOffsetSeq b), limsup_const]

end Til

end MatedCRT.ZeroConePolygonal
