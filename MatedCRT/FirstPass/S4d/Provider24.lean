import MatedCRT.FirstPass.S2g.Corrected24
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S4d.GlobalMeasurable

/-!
# FIRST PASS, Lemma 2.4 in provider form and its Draft consequence (q4, fp-S4d-4-2-assembly-c, operator note chat 174)

The printed Lemma 2.4 gives, for a.e. sample, a time `T > 0`, a family `{Λ_t}_{0<t<T}` of harmonic balls stopped at
`∂B_{1/2}` at `T`, and uniqueness of that family on `(0, T)`. It does not give the stopping-time clause `T' = T` for every
other stopped family (Draft `ConeHarmonicBallsUpToFixedTimeStmt`, Draft/Section2.lean:66, clause `T' = T ∧ EqOn`).

* `coneHarmonicBallsUpToFixedTimeCorrected_of_canonical`: the provider form (`ConeHarmonicBallsUpToFixedTimeCorrectedStmt`
  of FirstPass/S2b.lean:43, stated here in the same form) from the canonical corrected Lemma 2.4 `firstPass_2_4_corrected`
  (FirstPass/S2g/Corrected24.lean:44), with `T := halfBallTime`.
* `coneHarmonicBallsUpToFixedTimeStmt_of_corrected`: the Draft statement from the provider form and the closure-inside step.
  The clause `T' = T` is NOT read off Lemma 2.4; it is the consequence of `ConeHalfBallClosureInsideStep` by
  `stopped_unique_of_closureInside_fp` (FirstPass/S2g/Draft24.lean:52), the stopping-time uniqueness of the paper's
  maximal-stopping argument (Armitage-Gardiner-free, elementary: closure containment plus monotonicity).
-/

namespace MatedCRT

open MeasureTheory Set Filter

/-- Provider form of Lemma 2.4 (the same Prop as `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`, FirstPass/S2b.lean:43):
a.s. there are `T > 0` and a family stopped at `∂B_{1/2}` at `T`, and every family with the properties on `(0, T)` agrees
with it on `(0, T)`. No stopping-time uniqueness clause. -/
def ConeHarmonicBallsProviderFP4 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∃ Λ : ℝ → Set ℂ,
    IsConeHarmonicBallFamilyOn (μ ω) Λ T ∧ IsStoppedAtHalfBall Λ T ∧
    ∀ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (μ ω) Λ' T → EqOn Λ' Λ (Ioo 0 T)

/-- **Lemma 2.4 in provider form from the canonical corrected Lemma 2.4 (q4, fp-S4d-4-2-assembly-c).** The canonical
stopping time `halfBallTime (μ ω)` is the witness `T`; its uniqueness clause is the canonical `UniqueConeFamilyOn`. -/
theorem coneHarmonicBallsProviderFP4_of_canonical (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConeHarmonicBallsProviderFP4 := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨_, Λ, _, hae⟩ := hcan γ hγ0 hγ2 Ω P hC hcirc μ hcone
  filter_upwards [hae] with ω hω
  obtain ⟨hpos, huniq, hst⟩ := hω
  exact ⟨halfBallTime (μ ω), hpos, Λ ω, huniq.1, hst, huniq.2⟩

/-- **Draft Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeStmt`) from the provider form and the closure-inside step
(q4, fp-S4d-4-2-assembly-c).** For every stopped family `Λ'` on `(0, T')`, `T' = T` by `stopped_unique_of_closureInside_fp`,
and agreement on `(0, T)` follows from `IsConeHarmonicBallFamilyOn.eqOn`. -/
theorem coneHarmonicBallsUpToFixedTimeStmt_of_provider (hprov : ConeHarmonicBallsProviderFP4)
    (hcl : ConeHalfBallClosureInsideStep) : ConeHarmonicBallsUpToFixedTimeStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [hprov γ hγ0 hγ2 Ω P hC hcirc μ hcone, hcl γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hω hcl'
  obtain ⟨T, hT, Λ, hΛ, hst, _⟩ := hω
  refine ⟨T, hT, Λ, hΛ, hst, fun T' Λ' hT' hΛ' hst' => ?_⟩
  have hTT : T = T' :=
    stopped_unique_of_closureInside_fp hT hT' hst hst' hΛ.2.1.monotoneOn hΛ'.2.1.monotoneOn (hΛ.eqOn hΛ')
      (hcl' _ _ hΛ hst) (hcl' _ _ hΛ' hst')
  refine ⟨hTT.symm, ?_⟩
  have heq := hΛ.eqOn hΛ'
  rw [hTT, min_self] at heq
  rw [hTT]
  exact heq

/-- **The existence part of the provider form (q4, fp-S4d-4-2-h24-gate-consumers).** The provider `ConeHarmonicBallsProviderFP4`
gives the existence clause `ConeStoppedBaseExistsFP4` (FirstPass/S4d/GlobalMeasurable.lean) by forgetting its uniqueness
clause. This is the conversion that the measurability steps `coneGlobalFamilyAEMeasurable_of_exists` use once the chain is
retyped to the provider form. -/
theorem coneStoppedBaseExists_of_provider (hprov : ConeHarmonicBallsProviderFP4) : ConeStoppedBaseExistsFP4 := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [hprov γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hω
  obtain ⟨T, hT, Λ, hΛ, hst, _⟩ := hω
  exact ⟨T, hT, Λ, hΛ, hst⟩

end MatedCRT
