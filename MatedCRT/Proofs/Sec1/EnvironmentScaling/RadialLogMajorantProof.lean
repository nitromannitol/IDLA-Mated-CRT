import MatedCRT.Defs.QuantumCone
import MatedCRT.Proofs.Sec1.EnvironmentScaling.LateralCircleMeasurability
import MatedCRT.Proofs.Sec1.EnvironmentScaling.GaussianBandProof
import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLocalIntegrability
import MarkovProcess.Examples.BrownianMotion

/-!
# Radial log majorant of a quantum cone and local integrability of its radial part

Component of `notes/env-steps/env-steps.tex:243-252`: the radial function of a quantum cone is locally integrable on
the plane, its radial log majorant (`RadialLogMajorant`) holds almost surely, and every test-function pairing with it
is integrable.

Source. For a `γ`-quantum cone `(hC, hcirc)` under a probability measure `P` (`IsQuantumCone`), the radial process
`t ↦ h_{e^{-t}}(0)` has the law `quantumConeRadialLaw γ ν` (`IsQuantumCone.radial_law`). Its first factor is
`A_t = B_t + γ t` with `B` a standard Brownian motion `brownianMotion 0`. The first coordinate `t ≥ 0` is the inward
branch, the radii `(0, 1]`. The second factor (radii `≥ 1`) is used only through its total mass.

Route, with every premise explicit.
* `IsRationalEnvelope f`: one natural `n` bounds `|f (q.toNNReal)| ≤ n (1 + max q 0)` at every rational `q`. For
  continuous `f` this is the envelope `|f u| ≤ n (1 + u)` at every `u : ℝ≥0` (`abs_le_of_isRationalEnvelope`).
* Brownian sublinearity. `brownianMotion 0` is a Brownian motion in the sense of Mathlib
  (`brownianMotion_zero_isBrownianReal`: the Markov-process notion gives Mathlib's `ProbabilityTheory.IsBrownianReal`
  through `ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw`). The producer chain
  `GaussianBandProof.ae_tendsto_div_real_of_isBrownianReal` (which assembles `BrownianSublinear`'s
  `ae_tendsto_div_real_of_gaussianBandStep`) then gives `B t / t → 0` almost surely, and for a continuous path this is
  `IsRationalEnvelope (fun u => w u + γ u)` (`ae_isRationalEnvelope_brownian`).
* Transfer through the actual radial law. The envelope set is measurable (`measurableSet_isRationalEnvelope`), and
  the first marginal of `P.map (radialProcess ∘ hcirc)` is `(brownianMotion 0).map` of the drift
  (`ae_isRationalEnvelope_innerRadial`).
* Bounded annulus. `hcirc` is continuous on `(0, ∞) × ℂ` almost surely (`ae_continuousOn_circle`), so
  `t ↦ hcirc ω t 0` is bounded on `[1, 2r]`.

Results: `radialLogMajorant_of_isQuantumCone` (`RadialLogMajorant hcirc P r` for every `r`, in particular `r > 0`) and
`ae_integrable_test_mul_radial` (on one event, every test function `φ` gives `x ↦ φ x * hcirc ω ‖x‖ 0` integrable).
The only hypotheses are `IsQuantumCone γ P hC hcirc` and `[IsProbabilityMeasure P]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open MarkovProcess HarmonicBalls

namespace MatedCRT.Sec1

/-- A function on `ℝ≥0` has a rational envelope when one natural `n` bounds `|f|` by `n (1 + t)` at every rational time
`t`, rational times being read through `Real.toNNReal`. -/
def IsRationalEnvelope (f : ℝ≥0 → ℝ) : Prop :=
  ∃ n : ℕ, ∀ q : ℚ, |f (q : ℝ).toNNReal| ≤ (n : ℝ) * (1 + max (q : ℝ) 0)

/-- For a continuous function the rational envelope is the envelope at every time `u : ℝ≥0`: the envelope inequality
is closed and holds on the dense image of `ℚ`. -/
lemma abs_le_of_isRationalEnvelope {f : ℝ≥0 → ℝ} (hf : Continuous f) (hE : IsRationalEnvelope f) :
    ∃ n : ℕ, ∀ u : ℝ≥0, |f u| ≤ (n : ℝ) * (1 + (u : ℝ)) := by
  obtain ⟨n, hn⟩ := hE
  refine ⟨n, fun u => ?_⟩
  have hclosed : IsClosed {x : ℝ | |f x.toNNReal| ≤ (n : ℝ) * (1 + max x 0)} :=
    isClosed_le (continuous_abs.comp (hf.comp continuous_real_toNNReal)) (by fun_prop)
  have h : |f (u : ℝ).toNNReal| ≤ (n : ℝ) * (1 + max (u : ℝ) 0) :=
    DenseRange.induction_on Rat.denseRange_cast (u : ℝ) hclosed hn
  rw [Real.toNNReal_coe, max_eq_left u.coe_nonneg] at h
  exact h

/-- Deterministic sublinearity: a continuous path with `w t / t → 0` as `t → ∞` has a linear envelope on `ℝ≥0`. -/
lemma exists_linear_bound_of_tendsto_div {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (hlim : Tendsto (fun t : ℝ => w t.toNNReal / t) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ≥0, |w u| ≤ C * (1 + (u : ℝ)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim) 1 one_pos)
  have hbig : ∀ u : ℝ≥0, max T 1 ≤ (u : ℝ) → |w u| ≤ (u : ℝ) := by
    intro u hu
    have hpos : (0 : ℝ) < u := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hu)
    have h1 := hT (u : ℝ) (le_trans (le_max_left _ _) hu)
    rw [Real.dist_eq, sub_zero, Real.toNNReal_coe, abs_div, abs_of_pos hpos, div_lt_one hpos] at h1
    exact h1.le
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max T 1)).exists_bound_of_continuousOn
    (hw.comp continuous_real_toNNReal).continuousOn
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun u => ?_⟩
  by_cases hu : max T 1 ≤ (u : ℝ)
  · calc |w u| ≤ (u : ℝ) := hbig u hu
      _ ≤ 1 + (u : ℝ) := by linarith
      _ ≤ max M 1 * (1 + (u : ℝ)) := le_mul_of_one_le_left (by positivity) (le_max_right _ _)
  · have hu' := not_le.mp hu
    have hmem : (u : ℝ) ∈ Icc (0 : ℝ) (max T 1) := ⟨u.coe_nonneg, hu'.le⟩
    have h1 := hM (u : ℝ) hmem
    simp only [Function.comp_apply, Real.norm_eq_abs, Real.toNNReal_coe] at h1
    calc |w u| ≤ M := h1
      _ ≤ max M 1 := le_max_left _ _
      _ ≤ max M 1 * (1 + (u : ℝ)) :=
          le_mul_of_one_le_right (le_trans zero_le_one (le_max_right _ _)) (by linarith [u.coe_nonneg])

/-- The drifted path `u ↦ w u + γ u` of a continuous path with `w t / t → 0` has a rational envelope. -/
lemma isRationalEnvelope_of_tendsto_div (γ : ℝ) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (hlim : Tendsto (fun t : ℝ => w t.toNNReal / t) atTop (𝓝 0)) :
    IsRationalEnvelope (fun u : ℝ≥0 => w u + γ * (u : ℝ)) := by
  obtain ⟨C, -, hC⟩ := exists_linear_bound_of_tendsto_div hw hlim
  refine ⟨⌈C + |γ|⌉₊, fun q => ?_⟩
  have key : ∀ u : ℝ≥0, |w u + γ * (u : ℝ)| ≤ ((⌈C + |γ|⌉₊ : ℕ) : ℝ) * (1 + (u : ℝ)) := by
    intro u
    have hn : C + |γ| ≤ ((⌈C + |γ|⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    calc |w u + γ * (u : ℝ)| ≤ |w u| + |γ * (u : ℝ)| := abs_add_le _ _
      _ = |w u| + |γ| * (u : ℝ) := by rw [abs_mul, abs_of_nonneg u.coe_nonneg]
      _ ≤ C * (1 + (u : ℝ)) + |γ| * (1 + (u : ℝ)) := by
          have h1 := hC u
          have h2 : |γ| * (u : ℝ) ≤ |γ| * (1 + (u : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg γ)
          linarith
      _ = (C + |γ|) * (1 + (u : ℝ)) := by ring
      _ ≤ ((⌈C + |γ|⌉₊ : ℕ) : ℝ) * (1 + (u : ℝ)) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
  have h := key (q : ℝ).toNNReal
  rw [Real.coe_toNNReal'] at h
  exact h

/-- `brownianMotion 0` is a Brownian motion in the sense of Mathlib. The Markov-process notion (Gaussian marginals,
independent increments, almost surely continuous paths) gives Mathlib's `ProbabilityTheory.IsBrownianReal`, because the
two notions of independent increments coincide and Mathlib's `HasIndepIncrements.isPreBrownianReal_of_hasLaw` supplies
the finite-dimensional laws. -/
lemma brownianMotion_zero_isBrownianReal :
    ProbabilityTheory.IsBrownianReal (fun (t : ℝ≥0) (w : ContinuousPath ℝ) => w t) (brownianMotion 0) := by
  have h := isBrownianReal_brownianMotion 0
  simp only [sub_zero] at h
  exact ⟨ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw h.hasLaw_eval h.hasIndepIncrements,
    h.cont⟩

/-- Almost surely under `brownianMotion 0`, the drifted coordinate path has a rational envelope. This is Brownian
sublinearity (`GaussianBandProof.ae_tendsto_div_real_of_isBrownianReal`) read through the continuous path. -/
lemma ae_isRationalEnvelope_brownian (γ : ℝ) :
    ∀ᵐ w ∂(brownianMotion 0), IsRationalEnvelope (fun u : ℝ≥0 => w u + γ * (u : ℝ)) := by
  have hae := ae_tendsto_div_real_of_isBrownianReal brownianMotion_zero_isBrownianReal
    (fun t => ContinuousPath.measurable_coordinateProcess t)
  filter_upwards [hae] with w hw
  exact isRationalEnvelope_of_tendsto_div γ (map_continuous w) hw

/-- The rational envelope is a measurable condition on `ℝ≥0 → ℝ`: it is a countable union of countable intersections of
coordinate conditions. -/
lemma measurableSet_isRationalEnvelope : MeasurableSet {f : ℝ≥0 → ℝ | IsRationalEnvelope f} := by
  have hset : {f : ℝ≥0 → ℝ | IsRationalEnvelope f} =
      ⋃ n : ℕ, ⋂ q : ℚ, {f : ℝ≥0 → ℝ | |f (q : ℝ).toNNReal| ≤ (n : ℝ) * (1 + max (q : ℝ) 0)} := by
    ext f
    simp only [IsRationalEnvelope, Set.mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [hset]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q =>
    measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _)) measurable_const

/-- The inward radial path of a cone: `u ↦ h_{e^{-u}}(0)` on `ℝ≥0`. -/
noncomputable def innerRadial {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) : Ω → (ℝ≥0 → ℝ) :=
  fun ω u => hcirc ω (Real.exp (-(u : ℝ))) 0

/-- Almost surely the inward radial path of a quantum cone has a rational envelope. The first marginal of the radial law
is `(brownianMotion 0).map` of the drift, so the envelope transfers from `brownianMotion 0` to `P`. -/
lemma ae_isRationalEnvelope_innerRadial {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, IsRationalEnvelope (innerRadial hcirc ω) := by
  obtain ⟨ν, ⟨_hνP, -⟩, hν⟩ := h.radial_law
  have hmeas : ∀ (r : ℝ), 0 < r → ∀ z : ℂ, Measurable fun ω => hcirc ω r z :=
    fun r hr z => h.measurable_circle r z hr
  have hX : Measurable (innerRadial hcirc) :=
    Measurable.of_eval fun u => hmeas _ (Real.exp_pos _) 0
  have hR : Measurable (fun ω => radialProcess (hcirc ω)) := by
    unfold radialProcess
    exact Measurable.prodMk hX (Measurable.of_eval fun s => hmeas _ (Real.exp_pos _) 0)
  have hdrift : Measurable (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ)) :=
    Measurable.of_eval fun t => (ContinuousPath.measurable_coordinateProcess t).add_const _
  unfold quantumConeRadialLaw at hν
  set μ₁ := (brownianMotion 0).map (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ))
  have hμ₁prob : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff (μ := brownianMotion 0) hdrift.aemeasurable).2 inferInstance
  have hfst : innerRadial hcirc = Prod.fst ∘ (fun ω => radialProcess (hcirc ω)) := rfl
  have hmass : P.map (innerRadial hcirc) Set.univ = 1 := by
    rw [Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hmarg : P.map (innerRadial hcirc) = μ₁ := by
    have hsec : ((ν.map (fun (w : ContinuousPath ℝ) (s : ℝ≥0) => w s - γ * (s : ℝ))) Set.univ) = 1 := by
      rw [hfst, ← Measure.map_map measurable_fst hR, hν, Measure.map_fst_prod,
        Measure.smul_apply, smul_eq_mul, measure_univ (μ := μ₁), mul_one] at hmass
      exact hmass
    rw [hfst, ← Measure.map_map measurable_fst hR, hν, Measure.map_fst_prod, hsec, one_smul]
  have hG : MeasurableSet {f : ℝ≥0 → ℝ | IsRationalEnvelope f} := measurableSet_isRationalEnvelope
  have h1 : ∀ᵐ f ∂(P.map (innerRadial hcirc)), IsRationalEnvelope f := by
    rw [hmarg]
    exact (MeasureTheory.ae_map_iff hdrift.aemeasurable hG).mpr (ae_isRationalEnvelope_brownian γ)
  exact (MeasureTheory.ae_map_iff hX.aemeasurable hG).mp h1

/-- Deterministic inward bound. If `F` is continuous on `(0, ∞)` and `u ↦ F (e^{-u})` has a rational envelope, then
`|F t| ≤ n (1 + |log t|)` on `(0, 1]`. -/
lemma inward_log_bound {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0))
    (hE : IsRationalEnvelope (fun u : ℝ≥0 => F (Real.exp (-(u : ℝ))))) :
    ∃ n : ℕ, ∀ t : ℝ, 0 < t → t ≤ 1 → |F t| ≤ (n : ℝ) * (1 + |Real.log t|) := by
  have hcont : Continuous (fun u : ℝ≥0 => F (Real.exp (-(u : ℝ)))) :=
    hF.comp_continuous (by fun_prop) (fun u => Real.exp_pos _)
  obtain ⟨n, hn⟩ := abs_le_of_isRationalEnvelope hcont hE
  refine ⟨n, fun t ht0 ht1 => ?_⟩
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have hu : (((-Real.log t).toNNReal : ℝ≥0) : ℝ) = -Real.log t :=
    Real.coe_toNNReal _ (by linarith)
  have hexp : Real.exp (-(((-Real.log t).toNNReal : ℝ≥0) : ℝ)) = t := by
    rw [hu, neg_neg, Real.exp_log ht0]
  have h : |F (Real.exp (-(((-Real.log t).toNNReal : ℝ≥0) : ℝ)))|
      ≤ (n : ℝ) * (1 + (((-Real.log t).toNNReal : ℝ≥0) : ℝ)) := hn _
  rw [hexp, hu] at h
  calc |F t| ≤ (n : ℝ) * (1 + -Real.log t) := h
    _ = (n : ℝ) * (1 + |Real.log t|) := by rw [abs_of_nonpos hlog]

/-- **Radial log majorant.** For a `γ`-quantum cone under a probability measure, `RadialLogMajorant hcirc P r` holds for
every radius `r` (in particular for `r > 0`): almost surely `|h_t(0)| ≤ C (1 + |log t|)` for all `0 < t ≤ 2 r`. -/
theorem radialLogMajorant_of_isQuantumCone {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) (r : ℝ) : RadialLogMajorant hcirc P r := by
  unfold RadialLogMajorant
  filter_upwards [h.ae_continuousOn_circle, ae_isRationalEnvelope_innerRadial h] with ω hcont hE
  have hF : ContinuousOn (fun t : ℝ => hcirc ω t 0) (Ioi 0) :=
    hcont.comp (f := fun t : ℝ => (t, (0 : ℂ))) (by fun_prop) fun t ht => ⟨ht, mem_univ _⟩
  obtain ⟨n, hn⟩ := inward_log_bound hF hE
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2 * r)).exists_bound_of_continuousOn
    (hF.mono fun t ht => lt_of_lt_of_le one_pos ht.1)
  refine ⟨max (n : ℝ) M, fun t ht0 ht2 => ?_⟩
  rcases le_total t 1 with ht1 | ht1
  · calc |hcirc ω t 0| ≤ (n : ℝ) * (1 + |Real.log t|) := hn t ht0 ht1
      _ ≤ max (n : ℝ) M * (1 + |Real.log t|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hb := hM t ⟨ht1, ht2⟩
    simp only [Real.norm_eq_abs] at hb
    calc |hcirc ω t 0| ≤ M := hb
      _ ≤ max (n : ℝ) M := le_max_right _ _
      _ ≤ max (n : ℝ) M * (1 + |Real.log t|) :=
          le_mul_of_one_le_right (le_trans (Nat.cast_nonneg n) (le_max_left _ _))
            (by linarith [abs_nonneg (Real.log t)])

/-- **Local integrability of the radial part.** For a `γ`-quantum cone under a probability measure, almost surely
`z ↦ h_{‖z‖}(0)` is locally integrable on `ℂ`. Hence on one event, for every test function `φ` (smooth, compactly
supported, `HarmonicBalls.IsTestFunction`), the pairing `x ↦ φ x * hcirc ω ‖x‖ 0` is integrable. -/
theorem ae_integrable_test_mul_radial {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Integrable (fun x : ℂ => φ x * hcirc ω ‖x‖ 0) := by
  filter_upwards [h.ae_continuousOn_circle, ae_isRationalEnvelope_innerRadial h] with ω hcont hE
  have hF : ContinuousOn (fun t : ℝ => hcirc ω t 0) (Ioi 0) :=
    hcont.comp (f := fun t : ℝ => (t, (0 : ℂ))) (by fun_prop) fun t ht => ⟨ht, mem_univ _⟩
  obtain ⟨n, hn⟩ := inward_log_bound hF hE
  have hloc : LocallyIntegrable (fun z : ℂ => hcirc ω ‖z‖ 0) volume :=
    locallyIntegrable_radial (g := fun r : ℝ => hcirc ω r 0) hF one_pos (C := (n : ℝ))
      (fun r hr0 hr1 => hn r hr0 hr1)
  intro φ hφ
  obtain ⟨hφc, hφs, -⟩ := hφ
  have hint := hloc.integrable_smul_left_of_hasCompactSupport hφc.continuous hφs
  simpa [smul_eq_mul] using hint

end MatedCRT.Sec1
