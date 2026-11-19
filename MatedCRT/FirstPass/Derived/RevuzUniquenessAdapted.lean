import MatedCRT.FirstPass.Derived.RevuzWindowFormula
import MatedCRT.FirstPass.Derived.RevuzOptionalClockInverse
import MatedCRT.FirstPass.Derived.RevuzPositive
import MatedCRT.FirstPass.Derived.LQGClockApproxAdapted

/-!
# Adapted versions of the window integral of a positive continuous additive functional

Let `A` be a positive continuous additive functional of planar Brownian motion and `h ≥ 0` Borel. The window integral
`A^h_t = ∫_{(0,t]} h(B_s) dĀ_s` is computed from the rational-time regularization `Ā` of `A`, which at time `t`
reads `A` at rational times larger than `t`. We prove that, for every rational time `t` and every starting point `z`,
`A^h_t` agrees `P_z`-almost surely with a functional measurable for the canonical filtration at time `t`.

The version is `ω ↦ ∫_{(0,t]} h((ω^t)_s) dĜ_s(ω^t)`, where `ω^t = ω(· ∧ t)` is the path stopped at time `t` and `Ĝ` is
the regularization of the rational family `q ↦ g_{q ∧ t}` of `F⁰_{q ∧ t}`-measurable versions of `A_{q ∧ t}`. A
function measurable for `F⁰_q`, `q ≤ t`, is invariant under stopping at time `t`, so along almost every path `Ĝ(ω^t)`
is the clock `u ↦ A_{u ∧ t}(ω)`; this clock and `u ↦ A_u(ω)` agree on `[0, t]` and therefore have the same
Lebesgue–Stieltjes measure on `(0, t]` (Revuz–Yor (1999), Chapter X, §1; Fukushima–Oshima–Takeda (2011), §5.1).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- Two continuous nondecreasing clocks that agree on `[0, t]` have the same Lebesgue–Stieltjes measure on
`(0, t]`. -/
theorem stieltjesOfNNReal_measure_restrict_Ioc_congr {a b : ℝ≥0 → ℝ≥0} (ham : Monotone a)
    (hac : Continuous a) (hbm : Monotone b) (hbc : Continuous b) {t : ℝ≥0}
    (hab : ∀ u ≤ t, a u = b u) :
    (stieltjesOfNNReal a).measure.restrict (Ioc 0 (t : ℝ)) =
      (stieltjesOfNNReal b).measure.restrict (Ioc 0 (t : ℝ)) := by
  set fa := stieltjesOfNNReal a
  set fb := stieltjesOfNNReal b
  have hval : ∀ x : ℝ, x ≤ t → fa x = fb x := fun x hx => by
    rw [stieltjesOfNNReal_apply_of_continuous ham hac, stieltjesOfNNReal_apply_of_continuous hbm hbc,
      hab _ (Real.toNNReal_le_iff_le_coe.2 hx)]
  have hIoc : ∀ u v : ℝ, (fa.measure.restrict (Ioc 0 (t : ℝ))) (Ioc u v) =
      (fb.measure.restrict (Ioc 0 (t : ℝ))) (Ioc u v) := by
    intro u v
    rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc,
      StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc]
    rcases lt_or_ge (max u 0) (min v (t : ℝ)) with h1 | h1
    · rw [hval _ (min_le_right _ _), hval _ (h1.le.trans (min_le_right _ _))]
    · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.2 (fa.mono h1)),
        ENNReal.ofReal_of_nonpos (sub_nonpos.2 (fb.mono h1))]
  have hfin : IsFiniteMeasure (fa.measure.restrict (Ioc 0 (t : ℝ))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have huniv : (fa.measure.restrict (Ioc 0 (t : ℝ))) univ = (fb.measure.restrict (Ioc 0 (t : ℝ))) univ := by
    rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    simpa only [Measure.restrict_apply_self] using hIoc 0 t
  exact Measure.ext_of_Ioc_finite _ _ huniv fun u v _ => hIoc u v

/-- The rational-time regularization only reads a functional at rational times: functionals that agree at every
rational time (along possibly different paths) have the same regularization. -/
theorem regularize_congr_nnrat {A B : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω η : ContinuousPath ℂ}
    (h : ∀ q : ℚ≥0, A q ω = B q η) (t : ℝ≥0) : regularize A t ω = regularize B t η := by
  have hc : (∀ p q : ℚ≥0, p ≤ q → A p ω ≤ A q ω) ↔ ∀ p q : ℚ≥0, p ≤ q → B p η ≤ B q η := by
    simp only [h]
  unfold regularize
  split_ifs with h1 h2 h2
  · simp only [h]
  · exact absurd (hc.1 h1) h2
  · exact absurd (hc.2 h2) h1
  · rfl

/-- **Functions of the path up to time `q` do not see stopping after `q`.** A function measurable for the natural
`σ`-field `F⁰_q` is invariant under stopping the path at any time `t ≥ q`. -/
theorem apply_stoppedPath_of_measurable_pathFiltration {q t : ℝ≥0} (hqt : q ≤ t)
    {f : ContinuousPath ℂ → ℝ≥0} (hf : Measurable[pathFiltration q] f) (ω : ContinuousPath ℂ) :
    f (ContinuousPath.stoppedPath t ω) = f ω := by
  have hle : pathFiltration q ≤
      MeasurableSpace.comap (ContinuousPath.stoppedPath (alpha := ℂ) t) inferInstance := by
    refine iSup₂_le fun s hs => ?_
    have heq : (fun ω : ContinuousPath ℂ => ω s) =
        (fun ω : ContinuousPath ℂ => ω s) ∘ ContinuousPath.stoppedPath t := by
      funext ω
      simp only [Function.comp_apply, ContinuousPath.stoppedPath_apply_of_le t ω s (hs.trans hqt)]
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (continuous_eval_const s).measurable.comap_le
  obtain ⟨S, -, hS⟩ := hle _ (hf (measurableSet_singleton (f ω)))
  have hω : ω ∈ ContinuousPath.stoppedPath t ⁻¹' S := by
    rw [hS]
    rfl
  have h2 : ContinuousPath.stoppedPath t ω ∈ ContinuousPath.stoppedPath t ⁻¹' S := by
    simpa only [mem_preimage, ContinuousPath.stoppedPath_stoppedPath, min_self] using hω
  rw [hS] at h2
  exact h2

open scoped Classical in
/-- The rational family `q ↦ g_{q ∧ t}`, extended by `0` off the rational times. -/
noncomputable def rationalStoppedClock (g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0) (t : ℚ≥0) (u : ℝ≥0)
    (ω : ContinuousPath ℂ) : ℝ≥0 :=
  if hq : ∃ q : ℚ≥0, (q : ℝ≥0) = u then g (min hq.choose t) ω else 0

theorem rationalStoppedClock_coe (g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0) (t q : ℚ≥0) (ω : ContinuousPath ℂ) :
    rationalStoppedClock g t q ω = g (min q t) ω := by
  have hq : ∃ q' : ℚ≥0, (q' : ℝ≥0) = q := ⟨q, rfl⟩
  have hc : hq.choose = q := by exact_mod_cast hq.choose_spec
  simp only [rationalStoppedClock, hq, ↓reduceDIte]
  exact congrArg (fun r => g (min r t) ω) hc

theorem measurable_rationalStoppedClock {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hg : ∀ q : ℚ≥0, Measurable[pathFiltration q] (g q)) (t : ℚ≥0) (u : ℝ≥0) :
    Measurable (rationalStoppedClock g t u) := by
  by_cases hq : ∃ q : ℚ≥0, (q : ℝ≥0) = u
  · have he : rationalStoppedClock g t u = g (min hq.choose t) := funext fun ω => by
      simp only [rationalStoppedClock, hq, ↓reduceDIte]
    rw [he]
    exact (hg _).mono ((pathFiltration_le_canonicalFiltration _).trans
      ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le _)) le_rfl
  · have he : rationalStoppedClock g t u = fun _ => 0 := funext fun ω => by
      simp only [rationalStoppedClock, hq, ↓reduceDIte]
    rw [he]
    exact measurable_const

/-- **Adapted version of the window integral.** For a PCAF `A` of planar Brownian motion, a Borel `h ≥ 0`, a
starting point `z` and a rational time `t`, the window integral `∫_{(0,t]} h(B_s) dĀ_s` agrees `P_z`-almost surely
with a functional measurable for the canonical filtration at time `t`. -/
theorem exists_canonicalFiltration_version_clockWindowIntegral {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {h : ℂ → ℝ≥0∞} (hh : Measurable h) (z : ℂ) (t : ℚ≥0) :
    ∃ Φ : ContinuousPath ℂ → ℝ≥0∞,
      Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) (t : ℝ≥0)] Φ ∧
        clockWindowIntegral A h ((t : ℝ≥0) : ℝ) =ᵐ[planarLaw z] Φ := by
  obtain ⟨g, hgm, hgA⟩ := exists_rational_versions hA z
  refine ⟨fun ω => clockWindowIntegral (rationalStoppedClock g t) h ((t : ℝ≥0) : ℝ)
      (ContinuousPath.stoppedPath (t : ℝ≥0) ω),
    (measurable_clockWindowIntegral (measurable_rationalStoppedClock hgm t) hh _).comp
      (LQGClockApproxAdapted.measurable_stoppedPath_canonicalFiltration _), ?_⟩
  have hall : ∀ᵐ ω ∂planarLaw z, ∀ q : ℚ≥0, g q ω = A q ω := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hgA q] with ω hω using hω.symm
  filter_upwards [hall, hA.path z] with ω hq hp
  obtain ⟨-, hc, hm⟩ := hp
  have hBc : Continuous fun u : ℝ≥0 => A (min u (t : ℝ≥0)) ω :=
    hc.comp (continuous_id.min continuous_const)
  have hBm : Monotone fun u : ℝ≥0 => A (min u (t : ℝ≥0)) ω := fun u v huv => hm (min_le_min_right _ huv)
  have hreg1 : (fun u => regularize (rationalStoppedClock g t) u
      (ContinuousPath.stoppedPath (t : ℝ≥0) ω)) = fun u => A (min u (t : ℝ≥0)) ω := by
    funext u
    rw [regularize_congr_nnrat (B := fun u η => A (min u (t : ℝ≥0)) η) (η := ω) (fun q => ?_) u,
      regularize_eq_of_continuous_monotone hBc hBm]
    rw [rationalStoppedClock_coe, apply_stoppedPath_of_measurable_pathFiltration
      (q := ((min q t : ℚ≥0) : ℝ≥0)) (by exact_mod_cast min_le_right q t) (hgm _), hq]
    push_cast
    rfl
  have hreg2 : (fun u => regularize A u ω) = fun u => A u ω :=
    funext (regularize_eq_of_continuous_monotone hc hm)
  show clockWindowIntegral A h ((t : ℝ≥0) : ℝ) ω = clockWindowIntegral (rationalStoppedClock g t) h
    ((t : ℝ≥0) : ℝ) (ContinuousPath.stoppedPath (t : ℝ≥0) ω)
  unfold clockWindowIntegral
  rw [hreg1, hreg2, stieltjesOfNNReal_measure_restrict_Ioc_congr hm hc hBm hBc
    (fun u hu => by simp only [min_eq_left hu])]
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [ContinuousPath.stoppedPath_apply_of_le _ _ _ (Real.toNNReal_le_iff_le_coe.2 hs.2)]

/-- **Adapted version of the difference of two window integrals.** For PCAFs `A`, `A'`, the real difference
`(A^h_t).toReal - (A'^h_t).toReal` agrees `P_z`-almost surely with a functional measurable for the canonical
filtration at the rational time `t`. -/
theorem exists_canonicalFiltration_version_clockWindowIntegral_sub {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') {h : ℂ → ℝ≥0∞} (hh : Measurable h) (z : ℂ)
    (t : ℚ≥0) :
    ∃ Ψ : ContinuousPath ℂ → ℝ,
      Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) (t : ℝ≥0)] Ψ ∧
        (fun ω => (clockWindowIntegral A h ((t : ℝ≥0) : ℝ) ω).toReal -
          (clockWindowIntegral A' h ((t : ℝ≥0) : ℝ) ω).toReal) =ᵐ[planarLaw z] Ψ := by
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_canonicalFiltration_version_clockWindowIntegral hA hh z t
  obtain ⟨Φ', hΦm', hΦ'⟩ := exists_canonicalFiltration_version_clockWindowIntegral hA' hh z t
  refine ⟨fun ω => (Φ ω).toReal - (Φ' ω).toReal, hΦm.ennreal_toReal.sub hΦm'.ennreal_toReal, ?_⟩
  filter_upwards [hΦ, hΦ'] with ω h1 h2
  simp only [h1, h2]

end MatedCRT
