import MatedCRT.FirstPass.S4S6c.EnvInputs68
import MatedCRT.FirstPass.S4S6c.DyadicCutoff68
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma

/-!
# Field-measurable volume cutoff (Lemma 2.7 at dyadic scales, field-measurable)

Codex Q2a step 5 (`notes/fp-gaps/CODEX-idla-hOne-residuals-sol-20261110.md`, lines 140-164). The existing
`Lemma68Cutoff239.volume_lower_cutoff_measurable` gives only an ambient `Measurable` cutoff, which does not justify
`Measurable[S.fieldSigma]`. This file gives the field-measurable version, for the LQG measure `S.μ` of a valid
environment (Duplantier-Sheffield, Berestycki-Powell volume growth; Lemma 2.7 of the paper, `VolumeGrowthStmt`).

* `exists_slack_cutoff`: for `(2+γ)²/2 < b₀ < b` a deterministic `δ₀ > 0` with `δ^b ≤ (δ/8)^{b₀}` for `0 < δ < δ₀`
  (the slack `b₀ < b` absorbs the factor `8` of the dyadic interpolation).
* `volume_lower_cutoff_fieldMeasurable`: for `b > (2+γ)²/2`, a `Measurable[S.fieldSigma]` cutoff `tVol`, positive
  everywhere, with `ENNReal.ofReal (δ ^ b) ≤ S.μ ω (ball z δ)` for almost every `ω`, all `0 < δ < tVol ω` and all
  `z ∈ ball 0 (1 - δ)`.
* `volume_lower_cutoff_fieldMeasurable_vr`: the instance `b = (2+γ)²/2 + 1`, with the exponent of the first conjunct
  of `VolReady68` (LICGRCY68.lean).

Construction. `EnvInputs68.exists_fieldMeasurable_mu` gives a `Measurable[S.fieldSigma]` version `g` of `S.μ`, equal
to `S.μ` almost surely. The lower bound is taken at a countable dense set `D` of centres, so the event
`E δ = ⋂ z ∈ D ∩ ball 0 (1-δ), {ω | ofReal (δ^{b₀}) ≤ g ω (ball z δ)}` is `Measurable[S.fieldSigma]`. Its polynomially
high probability follows from `VolumeGrowthStmt` at exponent `b₀` (the two events differ by a null set).
`DyadicCutoff68.exists_dyadic_cutoff` gives a field-measurable dyadic cutoff `dd`. For `0 < δ < min (4 dd) δ₀`, a dyadic
scale `δ' ∈ [δ/8, δ/4]` with `ω ∈ E δ'` and a centre `d ∈ D` with `dist d z < δ/8` give
`μ(B_δ(z)) ≥ μ(B_{δ'}(d)) ≥ (δ/8)^{b₀} ≥ δ^b`. This is the countable-centre argument of
`BallMassLower.ballMass_lower_of_polyHighProb`, with the dyadic cutoff of `DyadicCutoff68`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT
namespace VolCutoffField68

/-- A deterministic cutoff for the slack `b₀ < b`: there is `δ₀ > 0` with `δ^b ≤ (δ/8)^{b₀}` for `0 < δ < δ₀`. -/
theorem exists_slack_cutoff {b₀ b : ℝ} (hbb₀ : b₀ < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → δ ^ b ≤ (δ / 8) ^ b₀ := by
  have hsub : 0 < b - b₀ := sub_pos.mpr hbb₀
  have h18 : 0 < (1 / 8 : ℝ) ^ b₀ := by positivity
  refine ⟨((1 / 8 : ℝ) ^ b₀) ^ (1 / (b - b₀)), by positivity, fun δ hδ hδδ₀ => ?_⟩
  have hpow : δ ^ (b - b₀) ≤ (1 / 8 : ℝ) ^ b₀ := by
    calc δ ^ (b - b₀) ≤ (((1 / 8 : ℝ) ^ b₀) ^ (1 / (b - b₀))) ^ (b - b₀) :=
          Real.rpow_le_rpow hδ.le hδδ₀.le hsub.le
      _ = (1 / 8 : ℝ) ^ b₀ := by
          rw [← Real.rpow_mul h18.le, one_div_mul_cancel hsub.ne', Real.rpow_one]
  calc δ ^ b = δ ^ b₀ * δ ^ (b - b₀) := by rw [← Real.rpow_add hδ]; congr 1; ring
    _ ≤ δ ^ b₀ * (1 / 8 : ℝ) ^ b₀ := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (δ / 8) ^ b₀ := by rw [show δ / 8 = δ * (1 / 8) by ring, Real.mul_rpow hδ.le (by norm_num)]

/-- **Volume cutoff, field-measurable (Lemma 2.7 at dyadic scales).** For a valid environment `S` of `γ ∈ (0,2)` and
`b > (2+γ)²/2`, there is a `σ(h)`-measurable random cutoff `tVol`, positive everywhere, such that almost surely
`μ_h(B_δ(z)) ≥ δ^b` for all `0 < δ < tVol` and all `z ∈ B_{1-δ}`. The cutoff is never claimed for every `ω`. -/
theorem volume_lower_cutoff_fieldMeasurable {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hb : (2 + γ) ^ 2 / 2 < b) (hVG : VolumeGrowthStmt)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ tVol : Ω → ℝ, Measurable[S.fieldSigma] tVol ∧ (∀ ω, 0 < tVol ω) ∧
      ∀ᵐ ω ∂S.P, ∀ δ : ℝ, 0 < δ → δ < tVol ω → ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ b) ≤ S.μ ω (ball z δ) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hγpos : 0 < (2 + γ) ^ 2 / 2 := by
    have : 0 < 2 + γ := by linarith
    positivity
  -- the intermediate exponent `b₀ ∈ ((2+γ)²/2, b)` and the deterministic cutoff `δ₀` of the slack
  obtain ⟨b₀, hb₀, hb₀b⟩ : ∃ b₀ : ℝ, (2 + γ) ^ 2 / 2 < b₀ ∧ b₀ < b :=
    ⟨((2 + γ) ^ 2 / 2 + b) / 2, by linarith, by linarith⟩
  have hb₀pos : 0 < b₀ := lt_trans hγpos hb₀
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_slack_cutoff hb₀b
  -- the upper exponent `βp = (2-γ)²/4 < (2-γ)²/2` of `VolumeGrowthStmt`
  have hβp : 0 < (2 - γ) ^ 2 / 4 := by
    have : 0 < 2 - γ := by linarith
    positivity
  have hβpl : (2 - γ) ^ 2 / 4 < (2 - γ) ^ 2 / 2 := by
    have : 0 < (2 - γ) ^ 2 := by
      have : 0 < 2 - γ := by linarith
      positivity
    linarith
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ := by
    unfold IsConeField
    exact ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  -- the two-sided volume-growth event of `VolumeGrowthStmt` for `S.μ`, lower exponent `b₀`
  let Emu : ℝ → Set Ω := fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
    ENNReal.ofReal (δ ^ b₀) ≤ S.μ ω (ball z δ) ∧ S.μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ ((2 - γ) ^ 2 / 4))}
  have hEmu : HarmonicBalls.PolyHighProb S.P Emu :=
    hVG γ hγ hγ2 ((2 - γ) ^ 2 / 4) b₀ hβp hβpl hb₀ Ω S.P S.hC S.hcirc S.μ hcone
  -- a field-measurable version `g` of `S.μ`, equal to `S.μ` almost surely
  obtain ⟨g, hgm, hg⟩ := EnvInputs68.exists_fieldMeasurable_mu hγ hγ2 S hS
  -- a countable dense set of centres
  obtain ⟨D, hDc, hDd⟩ : ∃ s : Set ℂ, s.Countable ∧ Dense s := TopologicalSpace.exists_countable_dense ℂ
  -- the countable-centre lower-bound event for `g`, field measurable
  let E : ℝ → Set Ω := fun δ => ⋂ z ∈ D ∩ ball (0 : ℂ) (1 - δ),
    {ω | ENNReal.ofReal (δ ^ b₀) ≤ g ω (ball z δ)}
  have hgball : ∀ (z : ℂ) (s : ℝ), Measurable[S.fieldSigma] fun ω => g ω (ball z s) :=
    fun z s => (Measure.measurable_coe measurableSet_ball).comp hgm
  have hEm : ∀ δ, MeasurableSet[S.fieldSigma] (E δ) := fun δ =>
    MeasurableSet.biInter (hDc.mono inter_subset_left) fun z _ =>
      measurableSet_le measurable_const (hgball z δ)
  -- `E δ` and `Emu δ` differ only on the null set `{S.μ ≠ g}`
  have hsub : ∀ δ, (E δ)ᶜ ⊆ (Emu δ)ᶜ ∪ {ω | ¬ S.μ ω = g ω} := by
    intro δ ω hω
    by_cases hωg : S.μ ω = g ω
    · left
      intro hωE
      apply hω
      simp only [E, mem_iInter, Set.mem_ofPred_eq]
      intro z hz
      have h1 := hωE z hz.2
      rw [← hωg]
      exact h1.1
    · right
      exact hωg
  have hN : S.P {ω | ¬ S.μ ω = g ω} = 0 := ae_iff.mp hg
  have hPHPamb : HarmonicBalls.PolyHighProb S.P E := by
    obtain ⟨p, hp, C, r₀, hr₀, hpoly⟩ := hEmu
    refine ⟨p, hp, C, r₀, hr₀, fun r hr hr₀' => ?_⟩
    calc S.P (E r)ᶜ ≤ S.P ((Emu r)ᶜ ∪ {ω | ¬ S.μ ω = g ω}) := measure_mono (hsub r)
      _ ≤ S.P (Emu r)ᶜ + S.P {ω | ¬ S.μ ω = g ω} := measure_union_le _ _
      _ = S.P (Emu r)ᶜ := by rw [hN, add_zero]
      _ ≤ ENNReal.ofReal (C * r ^ p) := hpoly r hr hr₀'
  -- `σ(h) ≤ 𝓕`, so `S.P` restricts to a probability measure on the field σ-algebra (`DyadicCutoff68` takes its
  -- measure on the σ-algebra of the cutoff); the events `E δ` are field measurable, so their complements are too
  have hle : S.fieldSigma ≤ ‹MeasurableSpace Ω› := MatedCRTEnv.fieldSigma_le S hS
  have hPF : @IsProbabilityMeasure Ω S.fieldSigma (S.P.trim hle) :=
    ⟨by rw [trim_measurableSet_eq hle MeasurableSet.univ]; exact measure_univ⟩
  have hPHPF : @HarmonicBalls.PolyHighProb Ω S.fieldSigma (S.P.trim hle) E := by
    obtain ⟨p, hp, C, r₀, hr₀, hpoly⟩ := hPHPamb
    refine ⟨p, hp, C, r₀, hr₀, fun r hr hr₀' => ?_⟩
    rw [trim_measurableSet_eq hle (hEm r).compl]
    exact hpoly r hr hr₀'
  -- the field-measurable dyadic cutoff of the countable-centre event
  obtain ⟨dd, hddm, hddpos, hdd⟩ :=
    @DyadicCutoff68.exists_dyadic_cutoff Ω S.fieldSigma (S.P.trim hle) hPF E hEm hPHPF
  refine ⟨fun ω => min (4 * dd ω) δ₀, (hddm.const_mul 4).min measurable_const,
    fun ω => lt_min (by linarith [hddpos ω]) hδ₀pos, ?_⟩
  filter_upwards [ae_of_ae_trim hle hdd, hg] with ω hωdd hωg
  intro δ hδ0 hδt z hz
  have hδ4 : δ < 4 * dd ω := lt_of_lt_of_le hδt (min_le_left _ _)
  have hδδ₀ : δ < δ₀ := lt_of_lt_of_le hδt (min_le_right _ _)
  -- a dyadic scale `δ' ∈ [δ/8, δ/4]` at which `ω` is good
  obtain ⟨δ', hδ'lo, hδ'hi, hωδ'⟩ := hωdd (δ / 4) (by positivity) (by linarith)
  -- a centre `d ∈ D` with `dist d z < δ/8`
  have hU : IsOpen (ball z (δ / 8)) := isOpen_ball
  obtain ⟨d, hdD, hdz⟩ := hDd.exists_mem_open hU ⟨z, mem_ball_self (by positivity)⟩
  rw [mem_ball] at hdz hz
  have hd : d ∈ ball (0 : ℂ) (1 - δ') := by
    rw [mem_ball]
    have := dist_triangle d z (0 : ℂ)
    linarith
  have hlow : ENNReal.ofReal (δ' ^ b₀) ≤ S.μ ω (ball d δ') := by
    rw [hωg]
    have hωE := hωδ'
    simp only [E, mem_iInter, Set.mem_ofPred_eq] at hωE
    exact hωE d ⟨hdD, hd⟩
  have hsub' : ball d δ' ⊆ ball z δ := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have := dist_triangle w d z
    linarith
  have hpow : (δ / 8) ^ b₀ ≤ δ' ^ b₀ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hb₀pos.le
  calc ENNReal.ofReal (δ ^ b) ≤ ENNReal.ofReal ((δ / 8) ^ b₀) :=
        ENNReal.ofReal_le_ofReal (hδ₀ δ hδ0 hδδ₀)
    _ ≤ ENNReal.ofReal (δ' ^ b₀) := ENNReal.ofReal_le_ofReal hpow
    _ ≤ S.μ ω (ball d δ') := hlow
    _ ≤ S.μ ω (ball z δ) := measure_mono hsub'

/-- **The instance `b = (2+γ)²/2 + 1`** of `volume_lower_cutoff_fieldMeasurable`, with the exponent of the first
conjunct of `VolReady68` (LICGRCY68.lean). For `ω` in the almost sure set, `0 < t = tVol ω` and `δ < t` give the bound
`ENNReal.ofReal (δ ^ ((2+γ)²/2 + 1)) ≤ S.μ ω (ball z δ)` for all `z ∈ ball 0 (1-δ)`. -/
theorem volume_lower_cutoff_fieldMeasurable_vr {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hVG : VolumeGrowthStmt) {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ tVol : Ω → ℝ, Measurable[S.fieldSigma] tVol ∧ (∀ ω, 0 < tVol ω) ∧
      ∀ᵐ ω ∂S.P, ∀ δ : ℝ, 0 < δ → δ < tVol ω → ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ ((2 + γ) ^ 2 / 2 + 1)) ≤ S.μ ω (ball z δ) :=
  volume_lower_cutoff_fieldMeasurable hγ hγ2 (by linarith) hVG S hS

end VolCutoffField68
end MatedCRT

#print axioms MatedCRT.VolCutoffField68.volume_lower_cutoff_fieldMeasurable
#print axioms MatedCRT.VolCutoffField68.volume_lower_cutoff_fieldMeasurable_vr
