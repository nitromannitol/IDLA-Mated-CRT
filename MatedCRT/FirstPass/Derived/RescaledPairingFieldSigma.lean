import MatedCRT.FirstPass.Derived.EnvScalingRadius
import MatedCRT.Proofs.Sec1.EnvironmentScaling
import LatticeProb.Bonanno.LQGMetric.Field.AffinePullScale

/-!
# The rescaled field `h^b` is a function of `h`

For a valid environment and `b > 0`, the pairings of the rescaled field
`h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b`, that is `φ ↦ rescaledPairing γ (h, ·) R_b b φ` with the cone scale radius `R_b`,
have a version `hC'` whose pairings are measurable for the field σ-algebra `σ(h)` and which agrees with
`rescaledPairing γ (h, ·) R_b b` almost surely, simultaneously for all test functions.

Construction: take a `σ(h)`-measurable, everywhere positive version `R` of `R_b`
(`exists_fieldSigma_measurable_coneScaleRadius`) and its dyadic upper approximants `R_k = ⌈2^k R⌉ / 2^k`, which are
countably valued, and set `hC' ω φ = limsup_k rescaledPairing γ (h, ·) R_k b φ`. On the almost sure event where the
pairings of `h` are those of the cone field `H ω` of the mating-of-trees coupling (a distribution), `r ↦ H ω (φ(r⁻¹ ·))`
is continuous on `r ≠ 0` (`LQGMetric.continuousAt_testAffinePull_scale`), so the limsup is a limit, equal to the value
at `R = R_b`.

Consequences: the measurability clause and the field σ-algebra clause `σ(h^b) ≤ σ(h)` of the rescaled cone field.
-/

open MeasureTheory Filter Set Topology HarmonicBalls MarkovProcess

namespace MatedCRT

/-- The dyadic upper approximant `⌈2^k r⌉ / 2^k` of `r`. -/
noncomputable def dyadicCeil (k : ℕ) (r : ℝ) : ℝ := (⌈(2 : ℝ) ^ k * r⌉₊ : ℝ) / 2 ^ k

lemma dyadicCeil_pos (k : ℕ) {r : ℝ} (hr : 0 < r) : 0 < dyadicCeil k r := by
  unfold dyadicCeil
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hc : 0 < ⌈(2 : ℝ) ^ k * r⌉₊ := Nat.ceil_pos.2 (mul_pos h2 hr)
  exact div_pos (by exact_mod_cast hc) h2

lemma tendsto_dyadicCeil {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun k => dyadicCeil k r) atTop (𝓝 r) := by
  have h2 : ∀ k : ℕ, (0 : ℝ) < 2 ^ k := fun k => by positivity
  have hlo : ∀ k : ℕ, r ≤ dyadicCeil k r := fun k => by
    unfold dyadicCeil
    rw [le_div_iff₀ (h2 k), mul_comm]
    exact Nat.le_ceil _
  have hhi : ∀ k : ℕ, dyadicCeil k r ≤ r + (1 / 2) ^ k := fun k => by
    unfold dyadicCeil
    rw [div_le_iff₀ (h2 k), add_mul, one_div_pow, one_div, inv_mul_cancel₀ (h2 k).ne', mul_comm r]
    exact (Nat.ceil_lt_add_one (mul_nonneg (h2 k).le hr)).le
  have hlim : Tendsto (fun k : ℕ => r + (1 / 2 : ℝ) ^ k) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo hhi

/-- Evaluating a family of measurable maps `F q` at the countably valued random index `dyadicCeil k (R ω)` is
measurable. -/
lemma measurable_comp_dyadicCeil {Ω : Type*} {m : MeasurableSpace Ω} {F : ℝ → Ω → ℝ}
    (hF : ∀ q, Measurable (F q)) {R : Ω → ℝ} (hR : Measurable R) (k : ℕ) :
    Measurable fun ω => F (dyadicCeil k (R ω)) ω := by
  have hG : Measurable fun p : Ω × ℕ => F ((p.2 : ℝ) / 2 ^ k) p.1 :=
    measurable_from_prod_countable_left fun j => by exact hF ((j : ℝ) / 2 ^ k)
  have hn : Measurable fun ω => ⌈(2 : ℝ) ^ k * R ω⌉₊ := (hR.const_mul _).nat_ceil
  exact hG.comp (measurable_id.prodMk hn)

/-- The pairings of `h` with test functions are measurable for the field σ-algebra `σ(h)`. -/
lemma MatedCRTEnv.measurable_hC_fieldSigma {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) : Measurable[S.fieldSigma] fun ω => S.hC ω φ := by
  have h : MeasurableSpace.comap (fun ω => fieldPairing 0 (S.hC ω) φ) inferInstance ≤ S.fieldSigma := by
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    exact le_iSup₂_of_le φ hφ le_rfl
  have hm : Measurable[S.fieldSigma] fun ω => fieldPairing 0 (S.hC ω) φ := measurable_iff_comap_le.2 h
  simpa [fieldPairing] using hm

/-- The dilation `x ↦ φ(q⁻¹ x)` of a test function is the test function `testAffinePull q 0 φ`. -/
lemma dilate_eq_testAffinePull (ψ : LQGMetric.TestC) {q : ℝ} (hq : q ≠ 0) :
    (fun x : ℂ => ψ ((q⁻¹ : ℂ) * x)) = ⇑(LQGMetric.testAffinePull q 0 ψ) := by
  funext x
  rw [LQGMetric.testAffinePull_apply _ _ hq]
  congr 1
  ring

/-- **The rescaled field is a function of `h`.** For a valid environment and every `b`, there is a field `hC'` whose
pairings with test functions are `σ(h)`-measurable and almost surely equal, for all test functions at once, to the
pairings `rescaledPairing γ (h, ·) R_b b` of `h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b`. -/
theorem MatedCRTEnv.IsValid.exists_fieldSigma_measurable_rescaledPairing {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hv : S.IsValid 𝒮 γ) (b : ℝ) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
      (∀ φ, IsTestFunction univ φ → Measurable[S.fieldSigma] fun ω => hC' ω φ) ∧
      ∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ := by
  obtain ⟨R, hRm, hRpos, hRae⟩ := FirstPass.Derived.exists_fieldSigma_measurable_coneScaleRadius hγ0 hγ2 S hv b
  obtain ⟨X, _, _, B, B', _, _, _, _, _, _, _, hrep⟩ := hv.matingOfTrees
  refine ⟨fun ω φ => limsup (fun k => rescaledPairing γ (S.hC ω) (dyadicCeil k (R ω)) b φ) atTop,
    fun φ hφ => ?_, ?_⟩
  · refine Measurable.limsup fun k => ?_
    refine measurable_comp_dyadicCeil (F := fun q ω => rescaledPairing γ (S.hC ω) q b φ) (fun q => ?_) hRm k
    by_cases hq : q = 0
    · subst hq
      simp only [rescaledPairing, inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        zero_add]
      exact measurable_const
    · let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, by simp⟩
      have hd : (fun x : ℂ => φ ((q⁻¹ : ℂ) * x)) = ⇑(LQGMetric.testAffinePull q 0 ψ) :=
        dilate_eq_testAffinePull ψ hq
      simp only [rescaledPairing]
      rw [hd]
      have hψ : IsTestFunction univ ⇑(LQGMetric.testAffinePull q 0 ψ) :=
        ⟨(LQGMetric.testAffinePull q 0 ψ).contDiff, (LQGMetric.testAffinePull q 0 ψ).hasCompactSupport,
          subset_univ _⟩
      exact (measurable_const.mul (S.measurable_hC_fieldSigma hψ)).add measurable_const
  · filter_upwards [hRae, hrep] with ω hRω hω
    intro φ hφ
    let ψ : LQGMetric.TestC := ⟨φ, hφ.1, hφ.2.1, by simp⟩
    let H : LQGMetric.DistC := MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))
    let g : ℝ → ℝ := fun q => (q⁻¹) ^ 2 * H (LQGMetric.testAffinePull q 0 ψ) +
      (lqgQ γ * Real.log q - γ⁻¹ * Real.log b) * ∫ x, φ x
    have hpair : ∀ q : ℝ, q ≠ 0 → rescaledPairing γ (S.hC ω) q b φ = g q := by
      intro q hq
      have hd : (fun x : ℂ => φ ((q⁻¹ : ℂ) * x)) = ⇑(LQGMetric.testAffinePull q 0 ψ) :=
        dilate_eq_testAffinePull ψ hq
      simp only [rescaledPairing, g]
      rw [hd, hω.2]
    have hR0 : R ω ≠ 0 := (hRpos ω).ne'
    have hg : ContinuousAt g (R ω) :=
      (((continuousAt_inv₀ hR0).pow 2).mul
          (H.continuous.continuousAt.comp (LQGMetric.continuousAt_testAffinePull_scale ψ 0 hR0))).add
        (((continuousAt_const.mul (Real.continuousAt_log hR0)).sub continuousAt_const).mul continuousAt_const)
    have hT : Tendsto (fun k => rescaledPairing γ (S.hC ω) (dyadicCeil k (R ω)) b φ) atTop (𝓝 (g (R ω))) :=
      (hg.tendsto.comp (tendsto_dyadicCeil (hRpos ω).le)).congr fun k =>
        (hpair _ (dyadicCeil_pos k (hRpos ω)).ne').symm
    rw [← hRω, hpair _ hR0]
    exact hT.limsup_eq

/-- **The rescaled cone field clauses from `σ(h)`.** For a valid environment and every `b`, there is a field `hC'`
with: almost surely `hC' = rescaledPairing γ (h, ·) R_b b` on all test functions; each pairing `ω ↦ hC' ω φ` is a
random variable; and for every clock and circle process, the field σ-algebra of the rescaled environment
`S.rescaleWithCircle γ b hC' clock' c` is contained in `σ(h)`. -/
theorem MatedCRTEnv.IsValid.exists_rescaledPairing_fieldSigma_le {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hv : S.IsValid 𝒮 γ) (b : ℝ) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ,
      (∀ᵐ ω ∂S.P, ∀ φ, IsTestFunction univ φ →
        hC' ω φ = rescaledPairing γ (S.hC ω) (coneScaleRadius γ (S.hcirc ω) b) b φ) ∧
      (∀ φ, IsTestFunction univ φ → Measurable fun ω => hC' ω φ) ∧
      ∀ (clock' : Ω → ContinuousPath ℂ → NNReal → ℝ) (c : Ω → ℝ → ℂ → ℝ),
        (S.rescaleWithCircle γ b hC' clock' c).fieldSigma ≤ S.fieldSigma := by
  obtain ⟨hC', hmeas, hae⟩ := hv.exists_fieldSigma_measurable_rescaledPairing hγ0 hγ2 b
  have hle : S.fieldSigma ≤ ‹MeasurableSpace Ω› := by
    simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
      simpa [fieldPairing] using hv.isQuantumCone.measurable_pairing φ hφ
    exact hm.comap_le
  refine ⟨hC', hae, fun φ hφ => (hmeas φ hφ).mono hle le_rfl, fun clock' c => ?_⟩
  show fieldSigmaAlgebra 0 hC' univ ≤ S.fieldSigma
  refine iSup₂_le fun φ hφ => ?_
  have hm : Measurable[S.fieldSigma] fun ω => fieldPairing 0 (hC' ω) φ := by
    simpa [fieldPairing] using hmeas φ hφ
  exact hm.comap_le

end MatedCRT
