import MatedCRT.FirstPass.Derived.TimeScaledLawField
import MatedCRT.FirstPass.Derived.ContinuousMapLimitSelection
import MatedCRT.FirstPass.Derived.ProbabilityMeasurePolish

/-!
# The field of laws of Liouville Brownian motion from Borel data of the field

Let `x ∈ X` be Polish data of the field (for instance its coordinates `LQGMetric.pairJ ⊤ h`) and let
`Q n x z ∈ 𝒫(C(ℝ≥0, ℂ))` be approximations of the law of Liouville Brownian motion from `z`, measurable in `x`
at the points of a dense sequence `zs`. The Borel limit selection `limitSelection zs Q K₀`
(`ContinuousMapLimitSelection.lean`) is a Borel map from the data to continuous fields of path laws.

* `ae_limitSelection_eq_planarBrownianPathLaw`: if almost surely `Q n (D ω) (zs j)` converges to the law
  `planarBrownianPathLaw (zs j) (lbmContinuousPath (F ω)) _` of the Liouville Brownian motion
  `t ↦ b(F_ω(b)⁻¹(t))` from `zs j` for every `j`, and almost surely this law depends continuously on the
  starting point (`hcont`, continuity of the Liouville Brownian motion law field, Berestycki–Gwynne (2020),
  Proposition 6.1 and Lemma 7.17), then almost surely the limit selection at `D ω` is that law at **every**
  starting point `z`. Agreement on the dense sequence alone would not determine the value at other points;
  the continuity of the law field is used to identify the two continuous fields.
* `rescaledLBMLawField Λ m γ x = (z ↦ (q ↦ [t ↦ q(m_γ t)])_* Λ(γ, x)(z))`, the time scaling by the median
  `m_γ` of a field of laws of Liouville Brownian motion (Berestycki–Gwynne (2020), (1.6)); it is Borel in the
  data (`measurable_rescaledLBMLawField`).
* `integral_rescaledLBMPath_eq_rescaledLBMLawField`: if in every valid environment the normalizing constant is
  `S.m₀ = m_γ` and, for a measurable version `H` of the field, almost surely `Λ(γ, R(H ω))(z)` is the law of
  Liouville Brownian motion from `z` for every `z`, then `Φ γ := rescaledLBMLawField Λ m γ` integrates every
  bounded Lipschitz path functional as the law of the rescaled Liouville Brownian motion `X_t = B_{F⁻¹(m₀ t)}`
  from each `z`: the hypothesis `hLBM` of `identification_of_reference_convergence`.
* `measurable_and_integral_rescaledLBMPath_eq_limitSelection`: the two steps combined for
  `Λ γ := limitSelection zs (Q γ) K₀`.

The law `planarBrownianPathLaw z g hg` depends on the proof `hg` of almost everywhere measurability of the
time-changed path only through proof irrelevance; hypotheses and conclusions state its existence
(`∃ hg : AEMeasurable (lbmContinuousPath (F ω)) (planarBrownianMotion z), …`).

Terminology: positive continuous additive functional (the LQG clock `F`), its right-continuous inverse and the
time change `B_{F⁻¹(t)}` of planar Brownian motion (Garban–Rhodes–Vargas, *Liouville Brownian motion*,
Definition 2.17; Berestycki, *Diffusion in planar Liouville quantum gravity*, Section 2).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

section Identification

/-- **Identification of the limit selection with the law field of Liouville Brownian motion.** Let `zs` have
dense range, and for almost every `ω` let

* (`hQ`) the approximations `Q n (D ω) (zs j)` converge, as `n → ∞`, to the law under planar Brownian motion
  from `zs j` of the Liouville Brownian motion path `t ↦ b(F_ω(b)⁻¹(t))`, for every `j`;
* (`hcont`) the law of the Liouville Brownian motion path from `z` be defined for every `z` and depend
  continuously on `z` (Berestycki–Gwynne (2020), Proposition 6.1 and Lemma 7.17).

Then almost surely, for every starting point `z`, the limit selection `limitSelection zs Q K₀ (D ω)` takes at
`z` the value of the law of Liouville Brownian motion from `z`. -/
theorem ae_limitSelection_eq_planarBrownianPathLaw {X Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Ω → X} {F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (Q : ℕ → X → ℂ → ProbabilityMeasure (ContinuousPath ℂ)) {zs : ℕ → ℂ} (hzs : DenseRange zs)
    (K₀ : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))
    (hQ : ∀ j : ℕ, ∀ᵐ ω ∂μ,
      ∃ hg : AEMeasurable (lbmContinuousPath (F ω)) (planarBrownianMotion (zs j)),
        Tendsto (fun n => Q n (D ω) (zs j)) atTop
          (𝓝 (planarBrownianPathLaw (zs j) (lbmContinuousPath (F ω)) hg)))
    (hcont : ∀ᵐ ω ∂μ, ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (F ω)) (planarBrownianMotion z),
      Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (F ω)) (hg z)) :
    ∀ᵐ ω ∂μ, ∀ z : ℂ, ∃ hg : AEMeasurable (lbmContinuousPath (F ω)) (planarBrownianMotion z),
      limitSelection zs Q K₀ (D ω) z = planarBrownianPathLaw z (lbmContinuousPath (F ω)) hg := by
  filter_upwards [ae_all_iff.2 hQ, hcont] with ω hQω hLω
  obtain ⟨hg, hc⟩ := hLω
  have hsel : limitSelection zs Q K₀ (D ω) =
      ⟨fun z => planarBrownianPathLaw z (lbmContinuousPath (F ω)) (hg z), hc⟩ :=
    limitSelection_eq hzs fun j => by
      obtain ⟨_, h⟩ := hQω j
      exact h
  exact fun z => ⟨hg z, DFunLike.congr_fun hsel z⟩

end Identification

section TimeScaling

variable {X : Type*}

/-- The time scaling by the median `m γ` of a field of laws of Liouville Brownian motion,
`Φ(γ, x)(z) = (q ↦ [t ↦ q(m_γ t)])_* Λ(γ, x)(z)` (Berestycki–Gwynne (2020), (1.6)). -/
noncomputable def rescaledLBMLawField (Λ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))
    (m : ℝ → ℝ) (γ : ℝ) (x : X) : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) :=
  timeScaleLawField (m γ).toNNReal (Λ γ x)

theorem rescaledLBMLawField_apply (Λ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))
    (m : ℝ → ℝ) (γ : ℝ) (x : X) (z : ℂ) :
    rescaledLBMLawField Λ m γ x z = (Λ γ x z).map (timeScalePath (m γ).toNNReal) := rfl

/-- The time-scaled law field is Borel measurable in the data when the law field is. -/
theorem measurable_rescaledLBMLawField [MeasurableSpace X]
    {Λ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : ∀ γ, Measurable (Λ γ))
    (m : ℝ → ℝ) (γ : ℝ) : Measurable (rescaledLBMLawField Λ m γ) :=
  (measurable_timeScaleLawField _).comp (hΛ γ)

/-- **The rescaled Liouville Brownian motion integrates against the time-scaled law field.** Let `R` map
distributions to data `X` (for instance `R = LQGMetric.pairJ ⊤`), `Λ γ` a field of path laws on the data and
`m γ` a constant such that in every valid environment `S` for `0 < γ < 2`

* (`hm`) the normalizing constant is `S.m₀ = m γ`;
* (`hΛ`) for every measurable version `H` of the field, almost surely `Λ(γ, R(H ω))(z)` is the law under planar
  Brownian motion from `z` of the Liouville Brownian motion path `t ↦ b(F_ω(b)⁻¹(t))`, for every `z`.

Then in every valid environment, for every measurable version `H` of the field, every `z` and every bounded
Lipschitz path functional `G`, almost surely the expectation of `G` of the rescaled Liouville Brownian motion
`t ↦ b(F_ω(b)⁻¹(S.m₀ t))` from `z` is the integral of `G` against `rescaledLBMLawField Λ m γ (R (H ω)) z`. -/
theorem integral_rescaledLBMPath_eq_rescaledLBMLawField {𝒮 : SpaceFillingSLEModel}
    (R : LQGMetric.DistC → X) (Λ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (m : ℝ → ℝ)
    (hm : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      S.m₀ = m γ)
    (hΛ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ᵐ ω ∂S.P, ∀ z : ℂ, ∃ hg : AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
        Λ γ (R (H ω)) z = planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) hg) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
        ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
          ∫ q, FirstPass.Derived.blPathFunctionalBCF hF q
            ∂(rescaledLBMLawField Λ m γ (R (H ω)) z : Measure (ContinuousPath ℂ)) := by
  intro γ hγ0 hγ2 Ω _ S hS H hH hrep z F hF
  filter_upwards [hΛ γ hγ0 hγ2 Ω S hS H hH hrep, hS.isLQGClock] with ω hω hclock
  obtain ⟨hg, hK⟩ := hω z
  rw [hm γ hγ0 hγ2 Ω S hS]
  exact integral_rescaledLBMPath_eq_timeScaleLawField z (m γ) (hclock z).2 hg hK hF

/-- **The field `Φ` of the random-walk-to-Liouville-Brownian-motion identification from Borel approximations.**
Let `zs` have dense range, `Q γ n x z` approximations of path laws measurable in the data `x` at the points
`zs j`, and `m γ` a constant such that in every valid environment `S` for `0 < γ < 2`

* (`hm`) the normalizing constant is `S.m₀ = m γ`;
* (`hQ`) for every measurable version `H` of the field and every `z`, almost surely `Q γ n (R (H ω)) z`
  converges as `n → ∞` to the law of Liouville Brownian motion from `z`;
* (`hcont`) almost surely the law of Liouville Brownian motion from `z` is defined for every `z` and depends
  continuously on `z` (Berestycki–Gwynne (2020), Proposition 6.1 and Lemma 7.17).

Then `Φ γ := rescaledLBMLawField (fun γ => limitSelection zs (Q γ) K₀) m γ` is Borel measurable for every `γ`
and satisfies the hypothesis `hLBM` of `identification_of_reference_convergence`. -/
theorem measurable_and_integral_rescaledLBMPath_eq_limitSelection [MeasurableSpace X]
    {𝒮 : SpaceFillingSLEModel} (R : LQGMetric.DistC → X)
    (Q : ℝ → ℕ → X → ℂ → ProbabilityMeasure (ContinuousPath ℂ)) {zs : ℕ → ℂ} (hzs : DenseRange zs)
    (K₀ : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (m : ℝ → ℝ)
    (hQm : ∀ γ n j, Measurable fun x => Q γ n x (zs j))
    (hm : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      S.m₀ = m γ)
    (hQ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ z : ℂ, ∀ᵐ ω ∂S.P, ∃ hg : AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
        Tendsto (fun n => Q γ n (R (H ω)) z) atTop
          (𝓝 (planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) hg)))
    (hcont : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ᵐ ω ∂S.P,
        ∃ hg : ∀ z : ℂ, AEMeasurable (lbmContinuousPath (S.clock ω)) (planarBrownianMotion z),
          Continuous fun z => planarBrownianPathLaw z (lbmContinuousPath (S.clock ω)) (hg z)) :
    (∀ γ, Measurable (rescaledLBMLawField (fun γ => limitSelection zs (Q γ) K₀) m γ)) ∧
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
        ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
          ∫ q, FirstPass.Derived.blPathFunctionalBCF hF q
            ∂(rescaledLBMLawField (fun γ => limitSelection zs (Q γ) K₀) m γ (R (H ω)) z :
              Measure (ContinuousPath ℂ)) := by
  refine ⟨measurable_rescaledLBMLawField (fun γ => measurable_limitSelection hzs (hQm γ)) m, ?_⟩
  refine integral_rescaledLBMPath_eq_rescaledLBMLawField R _ m hm
    fun γ hγ0 hγ2 Ω _ S hS H hH hrep => ?_
  exact ae_limitSelection_eq_planarBrownianPathLaw (μ := S.P) (D := fun ω => R (H ω)) (F := S.clock)
    (Q γ) hzs K₀ (fun j => hQ γ hγ0 hγ2 Ω S hS H hH hrep (zs j)) (hcont γ hγ0 hγ2 Ω S hS)

end TimeScaling

end MatedCRT
