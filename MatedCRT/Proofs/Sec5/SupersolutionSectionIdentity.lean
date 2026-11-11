import MatedCRT.Proofs.Sec5.CountableSupersolutionTests

/-!
# The Borel code section and its almost-sure identity

Target: `CodeSectionStmt 𝒮` (`ConeOriginNullMeasurableProof.lean`), the residual Borel obstacle code that
`coneOriginNullMeasurableStep_of_inputs` takes as a hypothesis. For every radius `R > 0` and time `t > 0` it asks for a
measurable set `𝒜 ⊆ PosCircleFns × BallFns R` whose section at almost every outcome is the set of traces of the
supersolutions of the obstacle problem for `(S.μ ω, R, t)`.

Route (no mathematics beyond the written proof):
* countable family: `φs` is the countable nonnegative `C²`-dense family of `countableC2FamilyStmt_holds`
  (residual A′, proved in `CountableSupersolutionTests`);
* punctured-disk sequence: `ps` is dense in the punctured closed disk (`exists_puncturedDisk_dense_seq`, this file);
* Borel relation: `supersolutionRelation γ t hR φs ps` is measurable (`measurableSet_supersolutionRelation`), and it is
  the code `𝒜`;
* mass identity on one event: `IsLQGMeasure` gives, almost surely, `IsLQGLimit γ (S.hcirc ω) (S.μ ω)`; with the
  circle-process agreement this yields `massLimit γ (φs j) (c ω) = ∫ φs j d(S.μ ω)` for all `j`
  (`massLimit_eq_integral`; `ae_all_iff` over the countable index `ℕ`);
* local finiteness: `S.μ ω (ball 0 R) < ⊤` from `IsLQGLimit.isLocallyFiniteMeasure`;
* section identity: `mem_supersolutionRelation_iff_of_countable` (residual B discharged there) on that event.

The LQG limit enters only through `S.IsValid.isLQGMeasure` of the environment (Duplantier-Sheffield, Berestycki-Powell
limit of dyadic approximations); the obstacle supersolutions are in the sense of Armitage-Gardiner (Green function of
the disk). No literature input is used.
-/

open HarmonicBalls

namespace MatedCRT

namespace ConeOriginNull

open MeasureTheory Filter Topology Set Metric

/-! ### 1. A punctured-disk dense sequence -/

/-- **Punctured-disk dense sequence.** For `R > 0` some sequence `ps` of points of the punctured
closed disk has dense range in it. The punctured closed disk is a subset of `ℂ`, hence separable, so it has a dense
sequence. -/
theorem exists_puncturedDisk_dense_seq {R : ℝ} (hR : 0 < R) :
    ∃ ps : ℕ → ℂ, (∀ k, ps k ∈ closedBall (0 : ℂ) R \ {0}) ∧
      ∀ x ∈ closedBall (0 : ℂ) R \ {0}, x ∈ closure (range ps) := by
  have hmem0 : ((R / 2 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) R \ {0} := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, Complex.norm_real,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ R / 2 by linarith)]
      linarith
    · intro h
      exact div_ne_zero hR.ne' two_ne_zero (Complex.ofReal_eq_zero.mp (Set.mem_singleton_iff.mp h))
  have : Nonempty ↥(closedBall (0 : ℂ) R \ {0}) := ⟨⟨((R / 2 : ℝ) : ℂ), hmem0⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ↥(closedBall (0 : ℂ) R \ {0})
  refine ⟨fun k => (u k : ℂ), fun k => (u k).2, ?_⟩
  intro x hx
  have h1 : Subtype.val '' closure (range u) ⊆ closure (Subtype.val '' range u) :=
    image_closure_subset_closure_image continuous_subtype_val
  have h2 : x ∈ Subtype.val '' closure (range u) := ⟨⟨x, hx⟩, hu ⟨x, hx⟩, rfl⟩
  have h3 := h1 h2
  rw [← Set.range_comp] at h3
  exact h3

/-! ### 2. The Borel code section -/

/-- **The Borel obstacle code from a countable `C²`-dense family.** For every space-filling SLE
model, given the countable nonnegative `C²`-dense families of residual A′ (`hfam`), the section of a measurable
relation is, at almost every outcome, the set of traces of supersolutions of the obstacle problem for the LQG measure.
The relation uses the countable family and a punctured-disk dense sequence; the mass identity holds on one almost-sure
event by `IsLQGMeasure`; the Laplacian LE residual is discharged by `CountableSupersolutionTests`. -/
theorem codeSectionStmt_of_countableC2Family (𝒮 : SpaceFillingSLEModel) (hfam : CountableC2FamilyStmt) :
    CodeSectionStmt 𝒮 := by
  intro γ _ _ Ω _ S hS c _ hcae R hR t _
  obtain ⟨φs, hφfam, hC2⟩ := hfam R hR
  obtain ⟨ps, hps, hdense⟩ := exists_puncturedDisk_dense_seq hR
  refine ⟨supersolutionRelation γ t hR φs ps,
    measurableSet_supersolutionRelation γ t hR (fun j => (hφfam j).1) ps, ?_⟩
  have hLim : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  have hmass : ∀ᵐ ω ∂S.P, ∀ j, massLimit γ (φs j) (c ω) = ∫ z, φs j z ∂(S.μ ω) := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [hLim, hcae] with ω hω hω'
    have hT := (hφfam j).1
    exact massLimit_eq_integral γ hω hT.1.continuous hT.2.1 (fun ε hε z => hω' (⟨ε, hε⟩, z))
  have hfin : ∀ᵐ ω ∂S.P, S.μ ω (ball 0 R) < ⊤ := by
    filter_upwards [hLim] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : ℂ) R).measure_lt_top
  filter_upwards [hmass, hfin] with ω hω1 hω2
  intro w
  exact mem_supersolutionRelation_iff_of_countable γ t hR hps hdense hω2 hφfam hC2 (c ω) hω1 w

/-- **The Borel code section, with no premise left.** The countable family is supplied by
`countableC2FamilyStmt_holds` (residual A′, proved in `CountableSupersolutionTests`). -/
theorem codeSectionStmt_holds (𝒮 : SpaceFillingSLEModel) : CodeSectionStmt 𝒮 :=
  codeSectionStmt_of_countableC2Family 𝒮 countableC2FamilyStmt_holds

/-- **Origin null-measurability, conditional on the Preston input only.** With the
Borel code section proved, `ConeOriginNullMeasurableStep 𝒮` is reduced to the explicit Preston input
`PrestonAnalyticUniversallyMeasurableStmt`. This is a conditional statement, not an unconditional claim of the origin
Step. -/
theorem coneOriginNullMeasurableStep_of_preston (𝒮 : SpaceFillingSLEModel)
    (hP : PrestonAnalyticUniversallyMeasurableStmt) : ConeOriginNullMeasurableStep 𝒮 :=
  coneOriginNullMeasurableStep_of_inputs 𝒮 hP (codeSectionStmt_holds 𝒮)

end ConeOriginNull

end MatedCRT
