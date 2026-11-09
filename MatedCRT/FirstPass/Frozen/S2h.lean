import MatedCRT.Defs.Setting

/-!
# First-pass frozen external inputs of the cone certificate null hull (fp-S2h, z1)

Each `def` is an EXTERNAL input of `ConeCertificateNullHullStep` (`FirstPass/S2h.lean`), used only as an explicit
hypothesis of `coneCertificateNullHull_of_steps`. Nothing here is proved. None of these statements is about clusters,
odometers, harmonic balls or IDLA processes: each concerns the quantum cone, the whole-plane GFF and the LQG measure
(operator note 2026-11-09 22:53 UTC, item (b)).
-/

namespace MatedCRT

open MeasureTheory HarmonicBalls

/-- FIRST-PASS FROZEN. Local law of the quantum cone equals the local law of the log-GFF. For `0 < γ < 2` and every
γ-quantum cone field `(P, hC, hcirc, μ)` (`IsConeField`) there is a whole-plane GFF `h^ℂ` on a probability space
`(Ω', P')` whose LQG measure of `h^ℂ − γ log|·|` (`IsLQGMeasureOfField P' γ γ hcirc' μ'`) has the same law as the cone's
measure on `B_1`, tested against any countable family of continuous compactly supported functions supported in `B_1`:
the laws of the moment vectors `ω ↦ (∫ φs k d μ_ω)_k` agree. Sources: Duplantier-Sheffield, "Liouville quantum gravity
and KPZ" (Invent. Math. 2011, arXiv:0808.1560), the quantum cone (Definition 2.1 of arXiv:2211.04891, lines 427-439)
and its restriction to `B_1`; the local equality is the restriction identity used in IDLA eq. (2.4) (arXiv:2211.04891);
GMC locality (the LQG measure on `B_1` is a measurable function of the circle averages on `B_1`, DS 2011 Section 3 /
Kahane 1985). Companion of the frozen `FrozenConeRestriction` (circle averages on `B_1`, `Steps/Sec2`). Locator:
DS 2011 and arXiv:2211.04891 eq. (2.4), exact numbering pending; truth check requested by operator. Used by:
coneCertificateNullHull_of_steps (FirstPass/S2h.lean). -/
def FrozenConeLogLocalCodeLaw : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧ IsLQGMeasureOfField P' γ γ hcirc' μ' ∧
      ∀ φs : ℕ → ℂ → ℝ, (∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ Metric.ball 0 1) →
        P.map (fun ω k => ∫ x, φs k x ∂(μ ω)) = P'.map (fun ω k => ∫ x, φs k x ∂(μ' ω))

end MatedCRT
