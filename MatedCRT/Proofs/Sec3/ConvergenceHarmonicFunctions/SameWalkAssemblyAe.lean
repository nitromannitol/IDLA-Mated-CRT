import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SameWalkAssembly
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnealedTailRate
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SameWalkRatesAe

/-! # Assembly of the almost-everywhere same-walk rates (steps2-r2, Section 3)

* `sameWalkAe_clause`: for one event, the annealed component and the a.e. pointwise component give the quantitative
  clause of `CorrectedHarmonicSameWalkRateAeStmt`, the constants combined by the maximum as in the frozen assembly.
* `correctedHarmonicSameWalkRateAe_of_assemblyAe`: the assembly from `UniformSameWalkAssemblyAeStep` (the annealed
  component is the frozen named step `AnnealedSameWalkRateStep`).
* `annealedSameWalkRateStep_of_ae`: the annealed component from the a.e. quenched rate, the polynomial complement of
  the event and the start-cell interior geometry `StartCellInteriorAe`, through the a.e. outer-probability bound
  `sectionwiseOuterProb_le_of_ae_quenched_and_environment` (AnnealedTailRate.lean).
* `correctedHarmonicSameWalkRateAe_of_ae_geom`: the full repaired statement from the a.e. rate, the event with its
  polynomial complement, and the start-cell geometry, with no separate annealed input. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The quantitative clause of `CorrectedHarmonicSameWalkRateAeStmt` for one event `E`, from the annealed component
and the almost-everywhere pointwise component. Only the full-measure event of each mesh enters the quenched clause. -/
theorem sameWalkAe_clause {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {E : ℝ → Set Ω}
    {ρ a β ν κ : ℝ} (hann : AnnealedSameWalkRateStep S ρ a β ν κ)
    (hpoint : PointwiseSameWalkRatesAeStep S E ρ a β ν) :
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
    ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
    ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
            ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * (min a β - q / χ)))) ∧
        ∀ᵐ ω ∂S.P, ω ∈ E ε →
          ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
            (srwLaw (S.mult ε ω) v)
              {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
                ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) ∧
            (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
              C * (H : ℝ) *
                (if (χ : ℝ) < ν then ε ^ (min a β * χ)
                 else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
                 else ε ^ (min a β * ν)) := by
  intro r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ := hann r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C₂, δ₂, hC₂, hδ₂, h₂⟩ := hpoint r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  refine ⟨max C₁ C₂, min δ₁ δ₂, le_trans hC₁ (le_max_left _ _), lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε hsmall
  have he₁ : ε < δ₁ := hsmall.trans_le (min_le_left _ _)
  have he₂ : ε < δ₂ := hsmall.trans_le (min_le_right _ _)
  constructor
  · apply (h₁ ε hε he₁).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    positivity
  · filter_upwards [h₂ ε hε he₂] with ω hω
    intro hωE v hv
    obtain ⟨htail, hmean⟩ := hω hωE v hv
    constructor
    · apply htail.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hε.le _)
    · apply hmean.trans
      have hscale : 0 ≤ (H : ℝ) *
          (if (χ : ℝ) < ν then ε ^ (min a β * χ)
           else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
           else ε ^ (min a β * ν)) := by
        split_ifs <;> positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hscale]

/-- Assembly input with exactly the frozen uniform exponent quantifiers. The event, its polynomial complement and the
annealed component are those of `UniformSameWalkAssemblyStep`; the pointwise component is the a.e. successor. -/
def UniformSameWalkAssemblyAeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
    AnnealedSameWalkRateStep S ρ a β ν κ ∧ PointwiseSameWalkRatesAeStep S E ρ a β ν

/-- The almost-everywhere assembly: `UniformSameWalkAssemblyAeStep` implies `CorrectedHarmonicSameWalkRateAeStmt`. -/
theorem correctedHarmonicSameWalkRateAe_of_assemblyAe (𝒮 : SpaceFillingSLEModel)
    (h : UniformSameWalkAssemblyAeStep 𝒮) : CorrectedHarmonicSameWalkRateAeStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨β, hβ, h⟩ := h γ hγ hγ2
  refine ⟨β, hβ, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨ν, hν, h⟩ := h ρ hρ hρ1
  refine ⟨ν, hν, ?_⟩
  intro a ha ha'
  obtain ⟨κ, hκ, h⟩ := h a ha ha'
  refine ⟨κ, hκ, ?_⟩
  intro Ω _ S hS
  obtain ⟨E, hEm, ⟨D, δ, hD, hδ, hbad⟩, hann, hpoint⟩ := h Ω S hS
  exact ⟨E, hEm, D, δ, hD, hδ, hbad, sameWalkAe_clause hann hpoint⟩

/-- Start-cell interior geometry on the environment event. For every ball `ball z r ⊆ ball 0 ρ` and every `y` in it,
all sufficiently small meshes satisfy: `S.P`-almost surely, on `E ε`, the starting label `vertexOf ε (S.η ω) y` lies in
the interior cell set of `ball z r`. This is the cell-size input of `steps2-r2.tex` (lines 749–766): the cell of `y`
has diameter at most `ε ^ a < dist y (∂ball z r)`. The frozen event `E` does not supply it; it is a named hypothesis. -/
def StartCellInteriorAe {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (E : ℝ → Set Ω) (ρ : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → ∀ y ∈ ball z r, ∃ ε₁ : ℝ, 0 < ε₁ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∀ᵐ ω ∂S.P, ω ∈ E ε → vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r)

/-- The annealed same-walk component from the almost-everywhere quenched rate. Off `E ε`, whose complement has
probability at most `CE ε ^ κ`, the quenched bound holds at the starting label `vertexOf ε (S.η ω) y` by
`StartCellInteriorAe`. `sectionwiseOuterProb_le_of_ae_quenched_and_environment` then bounds the sectionwise outer
probability by `CE ε ^ κ + C ε ^ (ν (min a β - q/χ))`, which is the frozen annealed clause with constant `max CE C`. -/
theorem annealedSameWalkRateStep_of_ae {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    [IsProbabilityMeasure S.P] {E : ℝ → Set Ω} {ρ a β ν κ : ℝ}
    (hE : ∃ CE εE : ℝ, 0 ≤ CE ∧ 0 < εE ∧
      ∀ ε : ℝ, 0 < ε → ε < εE → S.P (E ε)ᶜ ≤ ENNReal.ofReal (CE * ε ^ κ))
    (hPt : PointwiseSameWalkRatesAeStep S E ρ a β ν) (hgeom : StartCellInteriorAe S E ρ) :
    AnnealedSameWalkRateStep S ρ a β ν κ := by
  intro r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C, ε₀, hC, hε₀, hpt⟩ := hPt r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨ε₁, hε₁, hint⟩ := hgeom r z hr hball y hy
  obtain ⟨CE, εE, hCE, hεE, hcompl⟩ := hE
  refine ⟨max CE C, min (min ε₀ ε₁) εE, le_max_of_le_left hCE, lt_min (lt_min hε₀ hε₁) hεE, ?_⟩
  intro ε hε hεs
  have h₀ : ε < ε₀ := lt_of_lt_of_le hεs ((min_le_left _ _).trans (min_le_left _ _))
  have h₁ : ε < ε₁ := lt_of_lt_of_le hεs ((min_le_left _ _).trans (min_le_right _ _))
  have hEε : ε < εE := lt_of_lt_of_le hεs (min_le_right _ _)
  have hk : 0 ≤ ε ^ κ := Real.rpow_nonneg hε.le κ
  have hn : 0 ≤ ε ^ (ν * (min a β - q / χ)) := Real.rpow_nonneg hε.le _
  have hquench : ∀ᵐ ω ∂S.P, ω ∈ E ε →
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
        {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
          ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) := by
    filter_upwards [hpt ε hε h₀, hint ε hε h₁] with ω hω₁ hω₂
    intro hωE
    exact (hω₁ hωE _ (hω₂ hωE)).1
  have hgood : ∀ᵐ ω ∂S.P, ω ∉ (E ε)ᶜ →
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
        (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℤ) | (1 + (H : ℝ)) * ε ^ q <
          sameWalkExitDiscrepancy S r z ψ ε p.1 p.2}) ≤
          ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) := by
    filter_upwards [hquench] with ω hω hωB
    exact hω (not_not.mp hωB)
  have key := sectionwiseOuterProb_le_of_ae_quenched_and_environment S.P
    (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) (fun _ => le_of_eq measure_univ)
    {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} (E ε)ᶜ
    (mul_nonneg hCE hk) (mul_nonneg hC hn) (hcompl ε hε hEε) hgood
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : CE ≤ max CE C := le_max_left _ _
  have h2 : C ≤ max CE C := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_right h1 hk, mul_le_mul_of_nonneg_right h2 hn]

/-- Assembly input without a separate annealed component: the event with its polynomial complement, the start-cell
geometry `StartCellInteriorAe`, and the a.e. pointwise rate. -/
def UniformSameWalkAeGeomStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
    StartCellInteriorAe S E ρ ∧ PointwiseSameWalkRatesAeStep S E ρ a β ν

/-- The repaired statement from the geometry-based input: the annealed component is derived by
`annealedSameWalkRateStep_of_ae`, and the quenched clause is `sameWalkAe_clause`. -/
theorem correctedHarmonicSameWalkRateAe_of_ae_geom (𝒮 : SpaceFillingSLEModel)
    (h : UniformSameWalkAeGeomStep 𝒮) : CorrectedHarmonicSameWalkRateAeStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨β, hβ, h⟩ := h γ hγ hγ2
  refine ⟨β, hβ, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨ν, hν, h⟩ := h ρ hρ hρ1
  refine ⟨ν, hν, ?_⟩
  intro a ha ha'
  obtain ⟨κ, hκ, h⟩ := h a ha ha'
  refine ⟨κ, hκ, ?_⟩
  intro Ω _ S hS
  obtain ⟨E, hEm, hbad, hgeom, hpoint⟩ := h Ω S hS
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hann : AnnealedSameWalkRateStep S ρ a β ν κ :=
    annealedSameWalkRateStep_of_ae S hbad hpoint hgeom
  obtain ⟨D, δ, hD, hδ, hbad'⟩ := hbad
  exact ⟨E, hEm, D, δ, hD, hδ, hbad', sameWalkAe_clause hann hpoint⟩

end MatedCRT

#print axioms MatedCRT.sameWalkAe_clause
#print axioms MatedCRT.correctedHarmonicSameWalkRateAe_of_assemblyAe
#print axioms MatedCRT.annealedSameWalkRateStep_of_ae
#print axioms MatedCRT.correctedHarmonicSameWalkRateAe_of_ae_geom
