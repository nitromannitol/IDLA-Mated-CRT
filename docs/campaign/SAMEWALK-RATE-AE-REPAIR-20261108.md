# Audited same-walk rate repair: frozen export delta

Operator inbox entry2026-11-08 18:25 releases target3, independently audited CORRECT as a repair. Source: fleet notes/wpn-steps2/steps2-r2.tex:525-532,749-766, sha256 f52fd76aafd942d26dce5515140993cd0c55f392d965a9d9476d39aa2182a734; audit AUDIT-steps2-r2.md, Target3. The literal pointwise conclusion is false on valid null copies, including the H=0 example (491-523). The rate must hold almost surely at each mesh, with the geometric event and annulus exponent selected from the actual inputs.

Frozen evidence: MatedCRT/Draft/Section3HarmonicCorrected.lean:68-93; the offending quantifier is line85. Existing internal PointwiseSameWalkRatesStep:20 and SameWalkAssembly.lean:62 also export pointwise values. The standing no-Draft/frozen-edit rule is preserved: z1 owns new internal Ae successor modules and a checked conditional assembly/outer-probability transfer. No implication from the repaired successor to the old pointwise statement is claimed. The original qualitative convergence and annealed rate formulas are unchanged.

Exact proposed repaired export in namespace MatedCRT, with the same imports and opens as the frozen file; this is a source-backed candidate, not a new approved frozen declaration or a completed implementation:

```lean
open Classical in
def CorrectedHarmonicSameWalkRateAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ bAnn : ℝ, 0 < bAnn ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
  ∃ CE εE : ℝ, 0 ≤ CE ∧ 0 < εE ∧
    (∀ ε : ℝ, 0 < ε → ε < εE → S.P (E ε)ᶜ ≤ ENNReal.ofReal (CE * ε ^ κ)) ∧
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
    ∀ q : ℝ, 0 < q → q < min a bAnn * (χ : ℝ) →
    ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
            ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * (min a bAnn - q / χ)))) ∧
        ∀ᵐ ω ∂S.P, ω ∈ E ε → ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
          (srwLaw (S.mult ε ω) v)
            {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
              ENNReal.ofReal (C * ε ^ (ν * (min a bAnn - q / χ))) ∧
          (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
            C * (H : ℝ) *
              (if (χ : ℝ) < ν then ε ^ (min a bAnn * χ)
               else if (χ : ℝ) = ν then ε ^ (min a bAnn * ν) * (1 + |Real.log ε|)
               else ε ^ (min a bAnn * ν))
```

Only the name distinguishes this candidate and only the environment quantifier changes mathematically. Constants stay outside the per-mesh a.e. quantifier; the null set may depend on epsilon and the preceding fixed datum. The uniform exponent/event binder order, all starting labels, all three mean regimes and the annealed outer probability are retained. A future frozen successor must propagate through CorrectedLemma36Stmt and its consumers; the old frozen conclusion cannot be declared proved from this repair. The separate Brownian minimum/strict adjacency (r2:534-635), early/late exit (657-722), and admissible annulus rate implementation remain explicit, with audited written proofs now available.

Tracked in fleet ESCALATIONS.md E-SAMEWALK-RATE-AE-FROZEN-DELTA and INPUT-REQUESTS.md IR-SAMEWALK-RATE-AE-FROZEN-SUCCESSOR.

The full candidate type passes strict lc as fleet lead/checks/20261108-1810/SameWalkRateAeCandidate.lean. This checks elaboration only; it does not approve or implement a frozen statement replacement.
