import MatedCRT.Proofs.Sec3.KilledOccupation.MainOccupation

/-!
# The occupation identity of the rescaled Liouville Brownian motion from that of its clock

Let `φ = S.clock ω b` be the clock of Liouville Brownian motion along a Brownian path `b`, `σ` the exit time of `b`
from the disc `D = B_r(z)`, and `dA b` a measure on the time axis with `dA b [0, t] = φ(t ∧ σ)`, the Stieltjes measure
of the stopped clock. The median-rescaled Liouville Brownian motion is `X_t = b(φ⁻¹(m₀ t))`, with exit time
`τ = φ(σ) / m₀` from `D`, and the change of variables `s = φ⁻¹(m₀ t)` gives, path by path,
`∫_0^τ f(X_t) dt = m₀⁻¹ ∫_{[0, σ]} f(b_u) dA b (du)` (step S7 of Appendix B of the paper).

Taking the expectation over `b`, the occupation (Revuz) identity for the clock,
`E_y ∫_{[0, σ]} 1_D(b_u) g(b_u) dA b (du) = ∫_D 2 G_D(y, x) g(x) μ(dx)` with `G_D` the Green function of `D`,
gives the body of `FrozenLBMGreenOccupationRescaled`: the exit time `τ` is finite and integrable, and
`E_y ∫_0^τ f(X_t) dt = (2 / m₀) ∫_D G_D(y, x) f(x) μ(dx)` for bounded Hölder `f`.

In contrast with `rescaled_occupation_green_identity` (`MainOccupation.lean`), no base clock and no weight
appear: the identity is the one of the clock `S.clock` and of the γ-LQG measure `S.μ` themselves.

## Main results

* `rescaled_occupation_eq_clock`: the pathwise change of variables.
* `rescaled_occupation_green_identity_of_clock`: the occupation identity of the rescaled Liouville Brownian motion,
  for one environment `ω`, from the occupation identity of its clock.
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric
open HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

/-- Pathwise change of variables (step S7 of Appendix B, without weight): for a continuous path `b`, a time-change
clock `F`, the exit time `σ` of `b` from `D`, `c > 0`, and a measure `dA` on the time axis with
`dA [0, t] = F(t ∧ σ)`, the occupation `∫_{(0, τ]} f(X_t) dt` of the rescaled path `X_t = b(F⁻¹(c t))` up to its exit
time `τ` from `D` is `c⁻¹` times the difference of the integrals over `[0, σ]` against `dA` of the positive and
negative parts of `g ∘ b`, for any bounded measurable `g` equal to `f` on `D`. -/
theorem rescaled_occupation_eq_clock {F : ℝ≥0 → ℝ} {D : Set ℂ} {b : ℝ≥0 → ℂ} (hb : Continuous b)
    {σ c : ℝ≥0} (hc0 : 0 < c) (hcl : IsTimeChangeClock F) (hin : ∀ s < σ, b s ∈ D) (hout : b σ ∉ D)
    {dA : Measure ℝ≥0} (hF : ∀ t : ℝ≥0, dA (Iic t) = ENNReal.ofReal (F (min t σ)))
    (f g : ℂ → ℝ) (hfg : ∀ x ∈ D, f x = g x) (hgm : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime D (fun t : ℝ≥0 => b (clockInverse F (c * t))))).toReal,
        f (b (clockInverse F (c * t.toNNReal))) =
      (c : ℝ)⁻¹ * ((∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (max (g (b u)) 0) ∂dA).toReal -
        (∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (max (-g (b u)) 0) ∂dA).toReal) := by
  have hIcc : ∀ s : ℝ≥0, Icc (0 : ℝ≥0) s = Iic s := fun s => by
    ext u
    simp
  have hFnn : ∀ s : ℝ≥0, 0 ≤ F s := fun s => by
    rw [← hcl.map_zero]
    exact hcl.strictMono.monotone (by positivity)
  have hF' : ∀ s : ℝ≥0, s ≤ σ → F s = (∫⁻ _ in Icc (0 : ℝ≥0) s, (1 : ℝ≥0∞) ∂dA).toReal := by
    intro s hs
    rw [setLIntegral_const, one_mul, hIcc, hF s, min_eq_left hs, ENNReal.toReal_ofReal (hFnn s)]
  have hfin : ∫⁻ _ in Icc (0 : ℝ≥0) σ, (1 : ℝ≥0∞) ∂dA ≠ ⊤ := by
    rw [setLIntegral_const, one_mul, hIcc, hF σ]
    exact ENNReal.ofReal_ne_top
  have hgb : Measurable fun x : ℝ => g (b x.toNNReal) :=
    hgm.comp (hb.measurable.comp measurable_real_toNNReal)
  rw [rescaled_occupation_eq_stieltjes hc0 hcl.continuous hcl.strictMono hcl.map_zero hcl.tendsto_atTop
    hin hout f g hfg hgb,
    integral_clockMeasure_Ioc_eq_sub hcl.strictMono.monotone hcl.continuous hcl.map_zero
      (w := fun _ => 1) measurable_const hF' hfin hgb (fun x => hM _)]
  simp only [Real.toNNReal_coe, mul_one]

/-- **Occupation identity of the median-rescaled Liouville Brownian motion from that of its clock**, for one
environment `ω`. Let `dA b` be measures on the time axis with `dA b [0, t] = S.clock ω b (t ∧ σ(b))` for almost every
Brownian path `b` from `y`, where `σ(b)` is the exit time of `b` from `D = B_r(z)`. If the Green potential
`∫_D 2 G_D(y, x) μ(dx)` of `μ = S.μ ω` is finite and
`E_y ∫_{[0, σ]} 1_D(b_u) g(b_u) dA b (du) = ∫_D 2 G_D(y, x) g(x) μ(dx)` for every measurable `g ≥ 0`, then the
exit time `τ` from `D` of the rescaled Liouville Brownian motion `X` is almost surely finite and integrable, and
`E_y ∫_0^τ f(X_t) dt = (2 / m₀) ∫_D G_D(y, x) f(x) μ(dx)` for every bounded Hölder continuous `f` on `D`. The
conclusion is the body of `FrozenLBMGreenOccupationRescaled` at `ω`. -/
theorem rescaled_occupation_green_identity_of_clock {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (r : ℝ) (z y : ℂ) (σ : ContinuousPath ℂ → ℝ≥0) (hm0 : 0 < S.m₀) (ω : Ω)
    (dA : ContinuousPath ℂ → Measure ℝ≥0)
    (hclock : ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (S.clock ω b))
    (hσexit : ∀ᵐ b ∂planarBrownianMotion y, (∀ s < σ b, b s ∈ ball z r) ∧ b (σ b) ∉ ball z r)
    (hdA : ∀ᵐ b ∂planarBrownianMotion y, ∀ t : ℝ≥0,
      dA b (Iic t) = ENNReal.ofReal (S.clock ω b (min t (σ b))))
    (hmeas : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      AEMeasurable (fun b => ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA b)) (planarBrownianMotion y))
    (hfin : (∫⁻ x in ball z r, 2 * ENNReal.ofReal (greenFunction (ball z r) y x) ∂S.μ ω) < ∞)
    (hocc : ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), (ball z r).indicator g (b u) ∂(dA b) ∂planarBrownianMotion y =
        ∫⁻ x in ball z r, 2 * ENNReal.ofReal (greenFunction (ball z r) y x) * g x ∂S.μ ω) :
    (∀ᵐ b ∂planarBrownianMotion y,
        pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤) ∧
      Integrable (fun b => (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
        (planarBrownianMotion y) ∧
      ∀ f : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |f x| ≤ M) → IsHolderContinuousOn f (ball z r) →
        (∫ b, (∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
            f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) ∂planarBrownianMotion y) =
          (2 / S.m₀) * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ ω := by
  classical
  set G : ℂ → ℝ := greenFunction (ball z r) y with hG_def
  have hGm : Measurable G := measurable_greenFunction Metric.isOpen_ball y
  have hGnn : ∀ x, 0 ≤ G x := fun x => greenFunction_nonneg Metric.isBounded_ball y x
  have hc0 : 0 < S.m₀.toNNReal := Real.toNNReal_pos.mpr hm0
  have hcR : ((S.m₀.toNNReal : ℝ≥0) : ℝ) = S.m₀ := Real.coe_toNNReal _ hm0.le
  have h2G : ∀ x, 0 ≤ 2 * G x := fun x => mul_nonneg (by norm_num) (hGnn x)
  have hofR : ∀ x, ENNReal.ofReal (2 * G x) = 2 * ENNReal.ofReal (G x) := fun x => by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hQfin : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) ∂(S.μ ω) ≠ ⊤ := by
    rw [lintegral_congr fun x => hofR x]
    exact hfin.ne
  have hocc' : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), (ball z r).indicator q (b u) ∂(dA b) ∂planarBrownianMotion y =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * q x ∂S.μ ω := fun q hq => by
    rw [hocc q hq]
    exact lintegral_congr fun x => by rw [hofR x]
  have hae : ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (S.clock ω b) ∧
      (∀ s < σ b, b s ∈ ball z r) ∧ b (σ b) ∉ ball z r ∧
      ∀ t : ℝ≥0, dA b (Iic t) = ENNReal.ofReal (S.clock ω b (min t (σ b))) := by
    filter_upwards [hclock, hσexit, hdA] with b h1 h2 h3
    exact ⟨h1, h2.1, h2.2, h3⟩
  have hτ : ∀ᵐ b ∂planarBrownianMotion y,
      pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) =
        ENNReal.ofReal (S.clock ω b (σ b) / S.m₀) := by
    filter_upwards [hae] with b hb
    have h := pathExitTime_clockInverse_comp hc0 hb.1.continuous hb.1.strictMono hb.1.map_zero
      hb.1.tendsto_atTop hb.2.1 hb.2.2.1
    rw [hcR] at h
    exact h
  have hC1 : ∀ᵐ b ∂planarBrownianMotion y,
      pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤ :=
    hτ.mono fun b hb => by rw [hb]; exact ENNReal.ofReal_lt_top
  -- The expected occupation of a bounded measurable `g` vanishing outside the disc.
  have key : ∀ (f g : ℂ → ℝ) (M : ℝ), (∀ x ∈ ball z r, f x = g x) → (∀ x ∉ ball z r, g x = 0) →
      Measurable g → (∀ x, |g x| ≤ M) →
      Integrable (fun b => ∫ t in Ioc (0 : ℝ)
          (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
          f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) (planarBrownianMotion y) ∧
      ∫ b, (∫ t in Ioc (0 : ℝ)
          (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
          f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) ∂(planarBrownianMotion y) =
        S.m₀⁻¹ * ((∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω)) -
          ∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω)) := by
    intro f g M hfg hg0 hgm hgM
    set qp : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (g x) 0) with hqp_def
    set qm : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (-g x) 0) with hqm_def
    have hqpm : Measurable qp := ENNReal.measurable_ofReal.comp (hgm.max measurable_const)
    have hqmm : Measurable qm := ENNReal.measurable_ofReal.comp (hgm.neg.max measurable_const)
    have hqpi : (ball z r).indicator qp = qp := by
      funext x
      by_cases hx : x ∈ ball z r
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        simp [hqp_def, hg0 x hx]
    have hqmi : (ball z r).indicator qm = qm := by
      funext x
      by_cases hx : x ∈ ball z r
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        simp [hqm_def, hg0 x hx]
    have hpath : ∀ᵐ b ∂planarBrownianMotion y,
        (∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
          f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) =
        S.m₀⁻¹ * ((∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA b)).toReal -
          (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA b)).toReal) := by
      filter_upwards [hae] with b hb
      have h := rescaled_occupation_eq_clock (F := S.clock ω b) (D := ball z r) (b := ⇑b)
        b.continuous (c := S.m₀.toNNReal) hc0 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 f g hfg hgm hgM
      rw [hcR] at h
      exact h
    have hbdp : ∀ x, ENNReal.ofReal (max (g x) 0) ≤ ENNReal.ofReal M := fun x =>
      ENNReal.ofReal_le_ofReal (max_le ((le_abs_self _).trans (hgM x)) ((abs_nonneg _).trans (hgM x)))
    have hbdm : ∀ x, ENNReal.ofReal (max (-g x) 0) ≤ ENNReal.ofReal M := fun x =>
      ENNReal.ofReal_le_ofReal (max_le ((neg_le_abs _).trans (hgM x)) ((abs_nonneg _).trans (hgM x)))
    have hAp : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA b) ∂(planarBrownianMotion y) =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (g x) 0) ∂(S.μ ω) := by
      have h := hocc' qp hqpm
      rwa [hqpi] at h
    have hAm : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA b) ∂(planarBrownianMotion y) =
        ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (-g x) 0) ∂(S.μ ω) := by
      have h := hocc' qm hqmm
      rwa [hqmi] at h
    have hfin_p : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA b) ∂(planarBrownianMotion y) ≠ ⊤ := by
      rw [hAp]
      exact lintegral_green_mul_ne_top hQfin (k := fun x => max (g x) 0) (K := M) hbdp
    have hfin_m : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA b) ∂(planarBrownianMotion y) ≠ ⊤ := by
      rw [hAm]
      exact lintegral_green_mul_ne_top hQfin (k := fun x => max (-g x) 0) (K := M) hbdm
    have hPp : (∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA b) ∂(planarBrownianMotion y)).toReal =
        ∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω) := by
      rw [hAp, integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun x => mul_nonneg (h2G x) (le_max_right _ _))
        ((measurable_const.mul hGm).mul (hgm.max measurable_const)).aestronglyMeasurable]
      congr 1
      exact lintegral_congr fun x => (ENNReal.ofReal_mul (h2G x)).symm
    have hPm : (∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA b) ∂(planarBrownianMotion y)).toReal =
        ∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω) := by
      have hmneg : Measurable fun x => 2 * G x * max (-g x) 0 :=
        (measurable_const.mul hGm).mul (hgm.neg.max measurable_const)
      rw [hAm, integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun x => mul_nonneg (h2G x) (le_max_right _ _)) hmneg.aestronglyMeasurable]
      congr 1
      exact lintegral_congr fun x => (ENNReal.ofReal_mul (h2G x)).symm
    have hposE : ∫ b, (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA b)).toReal ∂(planarBrownianMotion y) =
        ∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω) := by
      rw [integral_toReal (hmeas qp hqpm) (ae_lt_top' (hmeas qp hqpm) hfin_p), hPp]
    have hnegE : ∫ b, (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA b)).toReal ∂(planarBrownianMotion y) =
        ∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω) := by
      rw [integral_toReal (hmeas qm hqmm) (ae_lt_top' (hmeas qm hqmm) hfin_m), hPm]
    have hintp : Integrable (fun b => (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA b)).toReal)
        (planarBrownianMotion y) :=
      integrable_toReal_of_lintegral_ne_top (hmeas qp hqpm) hfin_p
    have hintm : Integrable (fun b => (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA b)).toReal)
        (planarBrownianMotion y) :=
      integrable_toReal_of_lintegral_ne_top (hmeas qm hqmm) hfin_m
    refine ⟨((hintp.sub hintm).const_mul S.m₀⁻¹).congr (hpath.mono fun b hb => hb.symm), ?_⟩
    rw [← hposE, ← hnegE, ← integral_sub hintp hintm, ← integral_const_mul]
    exact integral_congr_ae hpath
  refine ⟨hC1, ?_, ?_⟩
  · -- The exit time is the occupation of the constant function `1`.
    have h1m : Measurable ((ball z r).indicator (1 : ℂ → ℝ)) := measurable_one.indicator measurableSet_ball
    refine (key (fun _ => 1) ((ball z r).indicator 1) 1 (fun x hx => (indicator_of_mem hx (1 : ℂ → ℝ)).symm)
      (fun x hx => indicator_of_notMem hx _) h1m (fun x => ?_)).1.congr (ae_of_all _ fun b => ?_)
    · by_cases hx : x ∈ ball z r
      · rw [indicator_of_mem hx]
        simp
      · rw [indicator_of_notMem hx]
        simp
    · simp
  · intro f hfM hfH
    obtain ⟨M, hM⟩ := hfM
    obtain ⟨C, χ, hχ0, -, hHol⟩ := hfH
    have hfcont : ContinuousOn f (ball z r) := hHol.continuousOn hχ0
    set g : ℂ → ℝ := (ball z r).piecewise f 0 with hg_def
    have hgm : Measurable g :=
      ContinuousOn.measurable_piecewise hfcont continuousOn_const measurableSet_ball
    have hg0 : ∀ x ∉ ball z r, g x = 0 := fun x hx => by
      rw [hg_def, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply]
    have hgM : ∀ x, |g x| ≤ max M 0 := by
      intro x
      by_cases hx : x ∈ ball z r
      · rw [hg_def, Set.piecewise_eq_of_mem _ _ _ hx]
        exact (hM x hx).trans (le_max_left _ _)
      · rw [hg0 x hx, abs_zero]
        exact le_max_right _ _
    have hfg : ∀ x ∈ ball z r, f x = g x := fun x hx => by
      rw [hg_def, Set.piecewise_eq_of_mem _ _ _ hx]
    have hbdp : ∀ x, ENNReal.ofReal (max (g x) 0) ≤ ENNReal.ofReal (max M 0) := fun x =>
      ENNReal.ofReal_le_ofReal (max_le ((le_abs_self _).trans (hgM x)) (le_max_right _ _))
    have hbdm : ∀ x, ENNReal.ofReal (max (-g x) 0) ≤ ENNReal.ofReal (max M 0) := fun x =>
      ENNReal.ofReal_le_ofReal (max_le ((neg_le_abs _).trans (hgM x)) (le_max_right _ _))
    have hIp_ne : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x * max (g x) 0) ∂(S.μ ω) ≠ ⊤ := by
      rw [lintegral_congr fun x => ENNReal.ofReal_mul (h2G x) (q := max (g x) 0)]
      exact lintegral_green_mul_ne_top hQfin (k := fun x => max (g x) 0) (K := max M 0) hbdp
    have hIm_ne : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x * max (-g x) 0) ∂(S.μ ω) ≠ ⊤ := by
      rw [lintegral_congr fun x => ENNReal.ofReal_mul (h2G x) (q := max (-g x) 0)]
      exact lintegral_green_mul_ne_top hQfin (k := fun x => max (-g x) 0) (K := max M 0) hbdm
    have hIp : Integrable (fun x => 2 * G x * max (g x) 0) ((S.μ ω).restrict (ball z r)) :=
      integrable_of_lintegral_ofReal_ne_top ((measurable_const.mul hGm).mul (hgm.max measurable_const))
        (fun x => mul_nonneg (h2G x) (le_max_right _ _)) hIp_ne
    have hIm : Integrable (fun x => 2 * G x * max (-g x) 0) ((S.μ ω).restrict (ball z r)) :=
      integrable_of_lintegral_ofReal_ne_top ((measurable_const.mul hGm).mul (hgm.neg.max measurable_const))
        (fun x => mul_nonneg (h2G x) (le_max_right _ _)) hIm_ne
    have hdiff : (∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω)) -
        (∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω)) =
        2 * ∫ x in ball z r, G x * f x ∂(S.μ ω) := by
      rw [← integral_sub hIp hIm, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
      have hfx : g x = f x := (hfg x hx).symm
      have hmx := max_zero_sub_max_neg_zero_eq_self (f x)
      simp only [hfx]
      linear_combination (2 * G x) * hmx
    rw [(key f g (max M 0) hfg hg0 hgm hgM).2, hdiff]
    ring

end

end MatedCRT.KilledOccupation
