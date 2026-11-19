import MatedCRT.FirstPass.Derived.NoFlatOfTendstoLaw
import MatedCRT.FirstPass.Derived.HN5OfDefinesTimeChange

/-!
# Lemma 7.4 from a continuous time change: strict monotonicity from the absence of flat intervals

Berestycki–Gwynne (2020), proof of Lemma 7.4: the limit path `X^z` is a continuous time change `B_τ` of Brownian
motion, and the last claim of Proposition 6.1 (the path is not constant on an interval) shows that the time change
is strictly increasing.  The second step is a theorem here: if `X = B ∘ τ` with `τ` continuous and nondecreasing and
the law of `X` gives mass zero to the paths that are constant on an interval of positive length, then `τ` is almost
surely strictly increasing.

* `definesTimeChangedBM_of_monotone_of_noFlat`: `DefinesTimeChangedBM P` from the nondecreasing version of its
  definition and the absence of flat intervals for every `P_z`;
* `hN5a_of_continuousTimeChange`: the binder `hN5a` of `hN5_of_defines` from the binder `hN5b` with the same
  premises and the nondecreasing time change as conclusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **A continuous nondecreasing time change of Brownian motion whose law has no flat interval is a strictly
increasing time change** (the second step of the proof of BG20, Lemma 7.4). -/
theorem definesTimeChangedBM_of_monotone_of_noFlat {P : PathLawFamily}
    (hflat : ∀ z : ℂ, ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
      {f : C(ℝ≥0, ℂ) | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0)
    (hmono : ∀ z : ℂ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
        (B X : Ω → ContinuousPath ℂ) (τ : Ω → ℝ≥0 → ℝ≥0),
      AEMeasurable B Q ∧ AEMeasurable X Q ∧ Q.map B = planarLaw z ∧
      (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ Monotone (τ ω) ∧ τ ω 0 = 0 ∧ ∀ u, X ω u = B ω (τ ω u)) ∧
      (P z : Measure (ContinuousPath ℂ)) = Q.map X) :
    DefinesTimeChangedBM P := by
  intro z
  obtain ⟨Ω, m, Q, hQ, B, X, τ, hB, hX, hlawB, hτ, hPX⟩ := hmono z
  refine ⟨Ω, m, Q, hQ, B, X, τ, hB, hX, hlawB, ?_, hPX⟩
  have hzero : Q (X ⁻¹' {f : C(ℝ≥0, ℂ) | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s}) = 0 :=
    le_antisymm ((Measure.le_map_apply hX _).trans (by rw [← hPX]; exact (hflat z).le)) bot_le
  have hnull := measure_eq_zero_iff_ae_notMem.1 hzero
  filter_upwards [hτ, hnull] with ω hω hn
  obtain ⟨hc, hm, h0, hXB⟩ := hω
  refine ⟨hc, fun a b hab => ?_, h0, hXB⟩
  by_contra hnot
  have hba : τ ω b ≤ τ ω a := not_lt.1 hnot
  refine hn ⟨a, b, hab, fun u hau hub => ?_⟩
  have hu : τ ω u = τ ω a := le_antisymm ((hm hub).trans hba) (hm hau)
  rw [hXB u, hXB a, hu]

/-- **The binder `hN5a` from the nondecreasing time change `hN5b`** (Berestycki–Gwynne (2020), Lemma 7.4): the
limit of the interpolated walk laws is a continuous nondecreasing time change of Brownian motion, and the absence
of flat intervals (`ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw`) makes it strictly
increasing. -/
theorem hN5a_of_continuousTimeChange {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (hN5b : ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (_ : IsProbabilityMeasure Q)
          (B X : Ω' → ContinuousPath ℂ) (τ : Ω' → ℝ≥0 → ℝ≥0),
        AEMeasurable B Q ∧ AEMeasurable X Q ∧ Q.map B = planarLaw z ∧
        (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ Monotone (τ ω) ∧ τ ω 0 = 0 ∧ ∀ u, X ω u = B ω (τ ω u)) ∧
        (P z : Measure (ContinuousPath ℂ)) = Q.map X) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν₂ : Measure PathLawFamily, IsProbabilityMeasure ν₂ →
      (∀ f : PathLawFamily →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) →
      ∀ᵐ P ∂ν₂, DefinesTimeChangedBM P := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw
  filter_upwards [hN5b γ hγ hγ2 Ω S hS η' hη' hae ε hε0 hε ν₂ hν₂ hlaw,
    ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU hγ hγ2
      hS hη' hae hε0 hε hlaw] with P h1 h2
  exact definesTimeChangedBM_of_monotone_of_noFlat h2 h1

end MatedCRT.FirstPass.Derived
