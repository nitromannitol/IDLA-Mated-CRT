import MatedCRT.FirstPass.Derived.HBBallMassHolds
import HarmonicBalls.Proofs.Sec2.SingularWeight
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-!
# The quantum cone measure as a singular weight of a whole-plane LQG measure

On the coupled space `(Ω × C(ℝ≥0, ℝ), P ⊗ BM)` of `ConeGFFCoupling2.lean`, the circle average embedding of a
`γ`-quantum cone agrees on the closed unit disk with the field `h^ℂ - γ log |·|`, where `h^ℂ` is a whole-plane GFF
(`isWholePlaneGFF_coneGFF`, `isLQGMeasureOfField_coneGFF`). Let `μ₀` be the γ-LQG measure of `h^ℂ`. This file
shows that almost surely
  `μ_h(A) = ∫_A |x|^{-γ²} dμ₀(x)` for every Borel set `A ⊆ B̄_1(0)`
(`exists_coneGFF_singularWeight`). This is the representation of the cone measure used in the proof of
Berestycki-Gwynne (arXiv:2003.10320v2), Lemma A.2, p. 66.

* Off the origin, `μ_{h^ℂ - γ log|·|} = |x|^{-γ²} μ₀` is Weyl scaling (`singularWeightStep_of_weyl` with
  `Section6.lqgMeasureWeylScaling`, Harmonic-balls paper, Fact 2.1 III).
* The cone measure has no atom at the origin (`ae_coneMeasure_singleton_zero`): by Lemma A.1, eq. (A.1)
  (`frozenBerestyckiGwynneConeBallMass_holds`), `μ_h(B_δ(0)) ≤ δ^β` with `β > 0` off an event of probability
  `O(δ^p)`.
* The density `|x|^{-γ²}` vanishes at `x = 0` (`Real.zero_rpow`), so the two sides agree on sets containing `0`.
-/

open MeasureTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The quantum cone measure has no atom at the origin**, almost surely: for every `ε > 0`,
`P(μ_h({0}) > ε) ≤ P(μ_h(B_δ(0)) > δ^β) = O(δ^p)` for all small `δ`, by Berestycki-Gwynne Lemma A.1, eq. (A.1). -/
theorem ae_coneMeasure_singleton_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, μ ω {0} = 0 := by
  have h2γ : 0 < (2 - γ) ^ (2 : ℕ) := by have : 0 < 2 - γ := by linarith
                                         positivity
  set ζ : ℝ := min ((2 - γ) ^ (2 : ℕ) / 4) (1 / 2) with hζdef
  have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set β : ℝ := (2 - γ) ^ (2 : ℕ) / 2 - ζ with hβdef
  have hβ : 0 < β := by
    have : ζ ≤ (2 - γ) ^ (2 : ℕ) / 4 := min_le_left _ _
    rw [hβdef]; linarith
  obtain ⟨p, hp, C, r₀, hr₀, hbd⟩ :=
    frozenBerestyckiGwynneConeBallMass_holds Ω P γ hC hcirc μ hγ hγ2 hcone ζ hζ0 hζ1
  have hkey : ∀ δ : ℝ, 0 < δ → δ < min r₀ 1 →
      P {ω | ENNReal.ofReal (δ ^ β) < μ ω {0}} ≤ ENNReal.ofReal (C * δ ^ p) := by
    intro δ hδ hδr
    have hδ1 : δ < 1 := lt_of_lt_of_le hδr (min_le_right _ _)
    have hsub : {ω | ENNReal.ofReal (δ ^ β) < μ ω {0}} ⊆ {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ (((2 + γ) ^ (2 : ℕ)) / 2 + ζ)) ≤ μ ω (ball z δ) ∧
          μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ β)}ᶜ := by
      intro ω hω hE
      have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (1 - δ) := mem_ball_self (by linarith)
      have hle : μ ω {0} ≤ ENNReal.ofReal (δ ^ β) :=
        (measure_mono (singleton_subset_iff.2 (mem_ball_self hδ))).trans (hE 0 h0).2
      exact absurd hle (not_le.2 hω)
    exact (measure_mono hsub).trans (hbd δ hδ (lt_of_lt_of_le hδr (min_le_left _ _)))
  have hlim : ∀ c a : ℝ, 0 < a → Tendsto (fun δ : ℝ => c * δ ^ a) (𝓝[>] 0) (𝓝 0) := by
    intro c a ha
    have h := ((Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.const_mul c).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Real.zero_rpow ha.ne'] using h
  have hε : ∀ n : ℕ, P {ω | ENNReal.ofReal (1 / ((n : ℝ) + 1)) < μ ω {0}} = 0 := by
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have ht : Tendsto (fun δ : ℝ => ENNReal.ofReal (C * δ ^ p)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hlim C p hp)
    have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 1 * δ ^ β < 1 / ((n : ℝ) + 1) := hlim 1 β hβ (Iio_mem_nhds hn)
    have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 (min r₀ 1) := Ioo_mem_nhdsGT (lt_min hr₀ one_pos)
    refine le_antisymm (ge_of_tendsto ht ?_) bot_le
    filter_upwards [hev1, hev2] with δ h1 h2
    rw [one_mul] at h1
    refine le_trans (measure_mono fun ω hω => ?_) (hkey δ h2.1 h2.2)
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h1.le) hω
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hε))
  have hpos : 0 < μ ω {0} := pos_iff_ne_zero.2 hω
  obtain ⟨r, -, hr, hrb⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (ENNReal.ofReal_pos.1 hr)
  exact mem_iUnion.2 ⟨n, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hn.le) hrb⟩

/-- **The quantum cone measure as a singular weight of a whole-plane LQG measure** (the representation in the proof
of Berestycki-Gwynne, Lemma A.2). For the circle average embedding `hcirc` of a `γ`-quantum cone with LQG measure
`μ`, there are a whole-plane GFF `(hC', hcirc')` on `(Ω × C(ℝ≥0, ℝ), P ⊗ BM)` (the coupled field of
`isWholePlaneGFF_coneGFF`) and its γ-LQG measure `μ₀` such that, almost surely,
`μ(A) = ∫_A |x|^{-γ²} dμ₀(x)` for every Borel set `A ⊆ B̄_1(0)`. -/
theorem exists_coneGFF_singularWeight {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hcone : IsConeField γ P hC hcirc μ) :
    ∃ (hC' : Ω × ContinuousPath ℝ → (ℂ → ℝ) → ℝ) (hcirc' : Ω × ContinuousPath ℝ → ℝ → ℂ → ℝ)
      (μ₀ : Ω × ContinuousPath ℝ → Measure ℂ),
      IsWholePlaneGFF (P.prod (brownianMotion 0)) hC' hcirc' ∧
      IsLQGMeasureOfField (P.prod (brownianMotion 0)) γ 0 hcirc' μ₀ ∧
      ∀ᵐ q ∂(P.prod (brownianMotion 0)), ∀ s : Set ℂ, MeasurableSet s → s ⊆ closedBall 0 1 →
        μ q.1 s = ∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂(μ₀ q) := by
  have hcone' := hcone
  obtain ⟨hP, hQ, hμ⟩ := hcone
  obtain ⟨N, -, hN0, hG⟩ := isWholePlaneGFF_coneGFF hQ
  have hμ' := isLQGMeasureOfField_coneGFF hQ hμ hN0
  have hQγ : γ * (lqgQ γ - γ) = 2 - γ ^ 2 / 2 := by unfold lqgQ; field_simp; ring
  have hαQ : γ < lqgQ γ := by nlinarith
  have hQpos : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistence_derived _ γ 0 _ _ hG hγ hγ2 hQpos
  have hSW := singularWeightStep_of_weyl
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
  have hweight := hSW γ γ hγ hγ2 hαQ _ _ _ _ _ μ₀ hG hμ' hμ₀
  have hexp : -(γ * γ) = -γ ^ 2 := by ring
  rw [hexp] at hweight
  have h0 := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := brownianMotion 0)).ae
    (ae_coneMeasure_singleton_zero hγ hγ2 hcone')
  refine ⟨_, _, μ₀, hG, hμ₀, ?_⟩
  filter_upwards [hweight, h0] with q hw hq0 s hs hs1
  have hne : -γ ^ 2 ≠ 0 := by nlinarith
  rw [← coneGFFMeasure_apply_of_subset γ (circleOff N hcirc q.1) (fun t => q.2 t) (μ q.1) hs hs1]
  have hm0 : coneGFFMeasure γ (circleOff N hcirc q.1) (fun t => q.2 t) (μ q.1) {0} = 0 := by
    rw [coneGFFMeasure_apply_of_subset _ _ _ _ (measurableSet_singleton 0)
      (singleton_subset_iff.2 (mem_closedBall_self zero_le_one))]
    exact hq0
  rw [← measure_sdiff_null hm0, sdiff_eq, ← Measure.restrict_apply hs, hw, Measure.restrict_apply hs,
    withDensity_apply _ (hs.inter (measurableSet_singleton 0).compl), ← sdiff_eq,
    ← lintegral_inter_add_sdiff _ s (measurableSet_singleton (0 : ℂ))]
  have hz : ∫⁻ x in s ∩ {0}, ENNReal.ofReal (‖x‖ ^ (-γ ^ 2)) ∂(μ₀ q) = 0 := by
    rw [setLIntegral_congr_fun (hs.inter (measurableSet_singleton 0))
      (g := fun _ => (0 : ℝ≥0∞)) fun x hx => ?_]
    · simp
    · rw [hx.2, norm_zero, Real.zero_rpow hne, ENNReal.ofReal_zero]
  rw [hz, zero_add]

end MatedCRT.FirstPass.Derived
