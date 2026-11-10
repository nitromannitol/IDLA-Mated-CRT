import MatedCRT.FirstPass.S2g

/-!
# First-pass frozen inputs of the canonical factorization (fp-S2i, z2)

EXTERNAL facts about the `γ`-quantum cone (Duplantier-Miller-Sheffield) used by the canonical factorization
`ConeCanonicalFactorStep` (`FirstPass/S2g/Canonical.lean`). They concern the law of the field, not the paper's clusters,
harmonic balls or IDLA processes.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. Uniqueness in law of the circle average process of the `γ`-quantum cone, for `0 < γ < 2`: any two
cone fields (`IsConeField`, which encodes `IsQuantumCone` and the LQG measure) have the same law of the circle average
process `circleProcess`, a random element of `(0, ∞) × ℂ → ℝ` with the product σ-algebra. The law of the radial process is
determined by the conditioned Brownian motion `ν` of `IsQuantumCone.radial_law`, the lateral part is the whole-plane GFF
(`IsQuantumCone.lateral_law`), and the circle averages are measurable functions of these two.
Source: Duplantier-Miller-Sheffield, "Liouville quantum gravity as a mating of trees" (arXiv:1409.7055v4),
quantum cone of Definition 4.10 (p. 79); conditioned Brownian motion, Remark 4.4 (pp. 74-75); radial/lateral orthogonal
decomposition, Lemma 4.9 (p. 79). The paper's cone is Definition 2.1 (paper/idla_mated_crt-corrected.tex, lines 427-439).
Not a verbatim numbered theorem of DMS: the equality of process laws is a measure-theoretic reduction to the
radial and lateral laws. Lemma 4.9 is the Hilbert-space decomposition, not a uniqueness-in-law lemma; uniqueness comes from
the sampling prescription of Definition 4.10, the conditioned-process specification and the whole-plane GFF law.
Truth check TRUE as typed (chat 180 §3; notes/fp-gaps/CHATGPT-idla-5-1-final.md, section (3)), assuming `IsConeField` is the
cone structure encoded in this development. Earlier verdicts: notes/fp-gaps/CHATGPT-idla-new-frozen-truth-2306.md (section 1);
notes/fp-gaps/CHATGPT-idla-frozen-batch.md (table row, 02:54 UTC).
Used by: coneCanonicalFactor_proved (MatedCRT/FirstPass/S2i/CanonicalFactor.lean). -/
def ConeCircleLawUniqueStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ)
      (μ' : Ω' → Measure ℂ), IsConeField γ P' hC' hcirc' μ' →
    P.map (fun ω => circleProcess (hcirc ω)) = P'.map (fun ω => circleProcess (hcirc' ω))

/-- FIRST-PASS FROZEN. Existence of a standard Borel model of the `γ`-quantum cone, for `0 < γ < 2`: there is a standard
Borel probability space carrying an `IsConeField` (the cone is a random field, realised on a Polish space of generalized
functions and its circle averages). The standard Borel structure is used only to make the image of a measurable set of
samples under the joint circle-and-family code analytic.
Source: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, quantum cone of Definition 4.10 (p. 79), which samples the cone from
a Brownian-type radial process and an independent whole-plane GFF lateral component; Duplantier-Sheffield, "Liouville quantum
gravity and KPZ" (arXiv:0808.1560v2), Proposition 1.1 (p. 5; subcritical LQG measure from the GFF) and Proposition 3.1 (p. 17;
jointly continuous modification of the circle averages). The paper's cone is Definition 2.1
(paper/idla_mated_crt-corrected.tex, lines 427-439). Not a verbatim numbered theorem: neither DS Proposition 1.1 nor
Proposition 3.1 states that a standard Borel probability space carrying an `IsConeField` exists. The standard Borel
realization (continuous path space for the radial process, a countable Gaussian-coordinate realization for the GFF, so that
their product is standard Borel) is an additional construction that must be argued, not cited.
Truth check TRUE, with the caveat above (chat 180 §3; notes/fp-gaps/CHATGPT-idla-5-1-final.md, section (3)): TRUE as typed,
but it requires an explicit canonical standard-Borel realization argument in addition to the cited numbered statements.
Earlier verdicts: notes/fp-gaps/CHATGPT-idla-new-frozen-truth-2306.md (section 2); notes/fp-gaps/CHATGPT-idla-frozen-batch.md
(table row, 02:54 UTC).
Used by: coneCanonicalFactor_proved (MatedCRT/FirstPass/S2i/CanonicalFactor.lean). -/
def ConeReferenceExistsStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ

end MatedCRT
