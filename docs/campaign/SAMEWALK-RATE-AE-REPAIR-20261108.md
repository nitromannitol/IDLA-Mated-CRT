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


Lead verification18:41: c5305cb implements the internal a.e. successors in SameWalkRatesAe.lean and SameWalkAssemblyAe.lean, with actual assembly and annealed outer-probability transfer from `StartCellInteriorAe`. Both pinned source checks and four exported axiom checks pass. This supplies no proof of the old pointwise frozen export. The rate producer remains open. Under the operator18:45 ruling, the authoritative proof is now steps2-r3:443-766, byte-identical to r2 for this section. No extra operator ruling is needed to choose the existential E as the source's cell-size/annulus envelope; its start-cell geometric producer remains ordinary written implementation work.

Late ce894f6 source and four further axiom exports also pass. Start-cell interior geometry is now derived from the actual cell-size event and IsValid; event intersection and the min-exponent bound give the repaired conclusion from the named uniform cell target and rate core. `CellSizeTargetAeStmt` remains the exact quantitative producer to implement from audited r3 Section1; the existing weaker PolyHighProb Draft alone does not supply its uniform exponent. No new operator decision is needed for independent written proof work.


Lead19:13 checked 7e85827/ad84342: actual three-regime lintegral estimates for distance and Holder discrepancy, preserving the factor H and explicit tail/boundedness hypotheses. H=0 and the producer of the a.s. discrepancy bound remain to be connected. G1 CellSizeTargetAeStmt and G2 UniformSameWalkAeCoreStep have their exact types inventoried in GAPS-TAKEOVER-20261108; r3 Section1 and692-714 write the uniform exponent arguments. These are not new WPN. G3 cells-meet is already supplied by the freshly checked adjacentCellsMeetAeStep (AdjacentCells.lean:17), so the worker should specialize it rather than call it unproved. G4 finite exit remains an integration obligation with the finite-expectation consumer in OccupationGreen.lean:135. G5 GMS remains an explicit Proposed hypothesis with a separate canonical-scope law bridge; no promotion. The existing pointwise/a.e. frozen delta is unchanged. Operator18:55 ends future prover rounds; no new unwritten request arose here.


Late checked bd29395: sameWalkExitDiscrepancy_le_of_finite_exit and its a.s. version supply the exact bound from start-in-disk and finite-interpolated-exit hypotheses. integral_discrepancy_le_regime supplies real-valued three-regime means, including H=0, from measurability, the a.s. bound and scaled tails. Those hypotheses remain; the actual finite-exit producer and full uniform event/rate assembly are not discharged. This refines the earlier G4 implementation boundary rather than introducing new WPN. Three new embedded axiom prints use only standard axioms. Final receipts:11 pinned source versions across9 files,4 additional axiom probes,19 distinct checked exports,85-source hole scan clean.


Lead19:46 round: 7e08a81 now proves ae_adjacent_cells_meet and ae_sameWalkExitDiscrepancy_le_of_gms_adjacent; strict snapshot elaboration and standard-axiom output checked. Thus the conditional quantitative rate bound no longer has an unproved hadj premise. Uniform pre-environment kappa/nu, actual finite-exit and event/rate producers remain written implementation obligations. 944485f separated-interval Brownian minimum is checked; it does not implement the unique-minimizer paragraph or close the rate. Frozen pointwise/a.e. successor boundary is unchanged.
