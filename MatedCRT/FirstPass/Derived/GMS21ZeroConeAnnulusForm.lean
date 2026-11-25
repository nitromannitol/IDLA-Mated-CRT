import MatedCRT.FirstPass.Derived.ZeroConeScalingInvariance
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfAnnulus

/-!
# The uniform-start invariance principle on annuli for the shifted zero-cone configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161, Lemma 3.5) prove Theorem 3.4 in case 1 with a `0`-quantum cone in place of
the `γ`-quantum cone and with the lattice `n⁻¹ ℤ` replaced by `n⁻¹ ℤ + n⁻¹ θ`, where `θ` is uniform on `[0, 1]` and
independent of everything else. In the proof of Theorem 3.4, case 1, this is transferred to the `γ`-quantum cone on
annuli `B_R(0) \ closedBall 0 α` avoiding the origin, where the two fields are mutually absolutely continuous.

This file states the form on annuli of Lemma 3.5 for the shifted zero-cone configuration of a mating-of-trees
coupling, in the form of the premise `hann` of `tendsto_uniformStartSelectedLPData_of_annulus`: the data at mesh
`1/n` are the zero-cone curve `η₀` read on the shifted lattice, `t ↦ η₀(t + θ/n)`, and the contour edge counts at
mesh `1/n` of the boundary-length pair `G = bm ∘ ψ` of the zero-cone curve read on the same lattice, under
`P ⊗ Unif[0, 1]`. At `n = 1` these are the data of the configuration (3.1) of arXiv:1705.11161
(`IsZeroConeConfigRealization`).

## Main definitions

* `phaseShiftedCurve`, `phaseShiftedEdgeCount`: the curve and the edge counts read on the lattice `ε ℤ + ε θ`.
* `IsZeroConeBoundaryPair`: a measurable version of the boundary-length pair of the zero-cone curve.
* `ZeroConeAnnulusLPForm`: the uniform-start invariance principle on annuli for the shifted zero-cone configuration.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

/-- The curve `t ↦ η(t + ε θ)`: the cells of `η` on the shifted lattice `ε ℤ + ε θ` are the cells of this curve at
mesh `ε`. -/
def phaseShiftedCurve (ε θ : ℝ) (η : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  η.comp ⟨fun t => t + ε * θ, continuous_id.add continuous_const⟩

/-- The contour edge counts at mesh `ε` of the boundary-length pair `G` read on the shifted lattice `ε ℤ + ε θ`. -/
def phaseShiftedEdgeCount (ε θ : ℝ) (G : Path2) : ℤ → ℤ → ℕ :=
  bmEdgeCount ε (fun t => (G (t + ε * θ)).1) (fun t => (G (t + ε * θ)).2)

section Statement

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **`G` is a measurable version of the boundary-length pair of the zero-cone curve**: `G ω t = bm ω (ψ t)` almost
surely, with `ψ` the clock of the zero cone (the first two conditions of `IsZeroConeConfigRealization`). -/
def IsZeroConeBoundaryPair (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) (G : Ω → Path2) : Prop :=
  Measurable G ∧
    ∀ᵐ ω ∂P, ∀ t, G ω t = bm ω (CellScaling.JointScalingO.clock γ
      (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) (η₀ ω) t)

/-- **The uniform-start invariance principle on annuli for the shifted zero-cone configuration**
(Gwynne–Miller–Sheffield, arXiv:1705.11161, Lemma 3.5, in the form used in the proof of Theorem 3.4, case 1). For
every measurable version `G` of the boundary-length pair of the zero-cone curve, all `0 < α < b < ρ < R`, `c > 0`
and `θ > 0`, for all large `n`, the law under `P ⊗ Unif[0, 1]` of the curve `t ↦ η₀(t + θ'/n)` and the edge counts
at mesh `1/n` of `t ↦ G(t + θ'/n)` (`θ'` the phase) gives mass at most `θ` to the failure of the Lévy–Prokhorov
comparison, at precision `c`, of the embedded walk and planar Brownian motion stopped at their exits from the annulus
`B_R(0) \ closedBall 0 α`, for starts in `closedBall 0 ρ \ B_b(0)` (`annulusSelectedLPData`). This is the premise
`hann` of `tendsto_uniformStartSelectedLPData_of_annulus` with the data of the shifted zero-cone configuration. -/
def ZeroConeAnnulusLPForm (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    ∀ α b ρ R c : ℝ, 0 < α → α < b → b < ρ → ρ < R → 0 < c → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (P.prod zeroConePhase).map (fun p => (phaseShiftedCurve (1 / (n : ℝ)) p.2 (η₀ p.1),
            phaseShiftedEdgeCount (1 / (n : ℝ)) p.2 (G p.1)))
          (annulusSelectedLPData (1 / (n : ℝ)) α b ρ R c)ᶜ ≤ ENNReal.ofReal θ

end Statement

end MatedCRT
