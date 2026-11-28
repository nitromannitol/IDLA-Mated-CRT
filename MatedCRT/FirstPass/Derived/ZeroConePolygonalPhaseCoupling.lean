import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseBase

/-!
# Almost sure properties of the zero-cone area measure and of the curves of the coupling

For the mating-of-trees coupling `D` and `μ_ω := fieldArea γ h₀(ω)`, the Borel area map of the zero-cone field
(`ZeroConeRoot.fieldArea`), this file collects the almost sure facts used in the comparison of the two quantum clocks
(`ae_zeroConeAreaFacts`): `μ_ω` is finite on compacts and positive on nonempty open sets, the zero-cone curve `η₀` is
the Lebesgue-parametrized curve `ηL` reparametrized by `μ_ω`-mass, and `ηL` is a proper surjective curve rooted at `0`
and parametrized by Lebesgue measure.

The inputs are `ZeroConeRoot.ae_isVagueLimitC_fieldArea` (the map is the vague limit of the area approximations),
`LQGCone.ae_lqgArea_coneField_open_pos` (positivity on open sets), and the clauses `areaParam₀` and `spaceFilling` of
the coupling.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Almost sure properties of the zero-cone area measure and of the curves.** Almost surely, the area measure
`μ = fieldArea γ h₀(ω)` of the zero-cone field is finite on compacts and positive on nonempty open sets, the zero-cone
curve is `η₀ = ηL ∘ φ` for an increasing homeomorphism `φ` fixing `0` with `μ(η₀[s, t]) = t - s`, and the curve `ηL` is
surjective, proper, rooted at `0` and parametrized by Lebesgue measure. -/
theorem ae_zeroConeAreaFacts (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P,
      (∀ K : Set ℂ, IsCompact K → ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) K < ⊤) ∧
      (∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) V) ∧
      (∃ φ : ℝ ≃o ℝ, φ 0 = 0 ∧ (∀ t, η₀ ω t = ηL ω (φ t)) ∧
        ∀ s t : ℝ, s ≤ t →
          ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) (η₀ ω '' Icc s t) = ENNReal.ofReal (t - s)) ∧
      Function.Surjective (ηL ω) ∧ Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) ∧ ηL ω 0 = 0 ∧
      ∀ s t : ℝ, s ≤ t → volume (ηL ω '' Icc s t) = ENNReal.ofReal (t - s) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hQ0 : 0 < CellScaling.lqgQ γ := IGLaw.lqgQ_pos' hγ.1
  have hQ : CellScaling.lqgQ γ = QuantumZipper.Qc γ := by
    dsimp [CellScaling.lqgQ, QuantumZipper.Qc]
  have hQc : 0 < QuantumZipper.Qc γ := hQ ▸ hQ0
  have hXA := MesoModel.FrozenIdentities.indepFun_motConeRadial_of_indep γ 0
    D.bm_B₀ D.bm_B₀' D.indep_cone₀.1
  have hpos := LQGCone.ae_lqgArea_coneField_open_pos hγ.1 hγ.2 hQc D.gff₀
    D.bm_B₀ D.bm_B₀' D.indep_cone₀.2 hXA
  have hfa := ZeroConeRoot.ae_isVagueLimitC_fieldArea hγ D.gff₀ D.bm_B₀ D.bm_B₀'
    D.indep_cone₀.1 D.indep_cone₀.2
  have hfa' := ae_of_ae_map (ZeroConeRoot.aemeasurable_zeroConeFieldOf γ D.gff₀ D.bm_B₀ D.bm_B₀'
    D.indep_cone₀.2) hfa
  filter_upwards [hfa', hpos, D.areaParam₀, D.spaceFilling] with ω hv hp hpar hsf
  obtain ⟨⟨φ, hφ0, hφ⟩, hareaμ⟩ := hpar
  obtain ⟨hsurj, hprop, h0, hvol⟩ := hsf
  have hex : ∃ μ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ (zeroConeFieldOf γ X₀ B₀ B₀' ω)) μ :=
    ⟨_, hv⟩
  have hlqg := CellScaling.JointScalingO.isVagueLimitC_lqgArea_of_exists hex
  have heq : CellScaling.lqgArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) =
      ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω) :=
    LQGCoord.isVagueLimitC_unique hlqg hv
  refine ⟨fun K hK => hv.1 K hK, fun V hV hne => ?_, ⟨φ, hφ0, hφ, hareaμ _ hv⟩, hsurj, hprop, h0, hvol⟩
  rw [← heq]
  exact hp V hV hne

end MatedCRT.ZeroConePolygonal
