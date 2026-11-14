import MatedCRT.FirstPass.Derived.PathModulusPerOmega

/-!
# The path-modulus event of the quenched walk laws from the cone-rescaled environment

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Proposition 6.1 (second condition of Lemma 6.3).  The analogue for the *unstopped*
walk laws of `eqLaw_event_of_scaling`: for a fixed cone scale `b`, the probability that some vertex of
`V^ε(B_{R+1})` has a quenched walk law with path modulus more than `1 / L` at scale `δ` on `[0, L]` with
probability more than `κ + θ` is bounded by `4 θ`, away from the four events

* `R_b ≤ 4 (R + 2)`, `M < R_b` (cone-scale radius out of range),
* the exit time of the walk of the rescaled environment `S'` at mesh `ε / b` from `I^{ε/b}(B_{1/2})`, started in
  `V^{ε/b}(B_{1/4})`, is `< s b / ε` with probability `> κ` for some vertex,
* the stopped interpolated walks of `S'` from some vertex of `V^{ε/b}(B_{1/2})` have oscillation more than
  `1 / (L M)` over windows of length at most `δ` before the exit time with probability `> θ`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric LatticeProb
open scoped ENNReal NNReal
open MarkovProcess (ContinuousPath)
open MatedCRT.ExitCouplingGlue

/-- **Path-modulus event of the unstopped quenched walk laws from the cone-rescaled environment** (Berestycki–Gwynne
(2020), proof of Proposition 6.1).  See the module docstring. -/
theorem pathFailure_event_of_scaling {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {S S' : MatedCRTEnv Ω} (hS' : S'.IsValid 𝒮 γ) (hP : S'.P = S.P)
    (η' : Ω → C(ℝ, ℂ)) (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {b : ℝ} (hb : 0 < b)
    (hηs : ∀ᵐ ω ∂S.P, ∀ s : ℝ,
      S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s))
    (hbm : ∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s))
    {eps R L M κ θ s : ℝ} (δ : ℝ≥0) (hε : 0 < eps) (hL : 0 < L) (hlam : S.mε eps * (eps / b) ≤ 1)
    (hmL : S.mε eps * L ≤ (eps / b)⁻¹ * s)
    (hE1 : S.P {ω | coneScaleRadius γ (S.hcirc ω) b ≤ 4 * (R + 2)} ≤ ENNReal.ofReal θ)
    (hE2 : S.P {ω | M < coneScaleRadius γ (S.hcirc ω) b} ≤ ENNReal.ofReal θ)
    (hE3 : S'.P {ω | ∃ x : ℤ, vertexPoint (eps / b) (S'.η ω) x ∈ ball (0 : ℂ) (1 / 4) ∧
        ENNReal.ofReal κ < srwLaw (S'.mult (eps / b) ω) x
          {y | (vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) y : ℝ≥0∞) <
            ENNReal.ofReal ((eps / b)⁻¹ * s)}} ≤ ENNReal.ofReal θ)
    (hE4 : S'.P {ω | ∃ x ∈ cellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)),
        ENNReal.ofReal θ < srwLaw (S'.mult (eps / b) ω) x {X | ∃ a c : ℝ≥0,
          a ≤ ((vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) X).toNat : ℝ≥0) /
            ((eps / b)⁻¹).toNNReal ∧
          c ≤ ((vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) X).toNat : ℝ≥0) /
            ((eps / b)⁻¹).toNNReal ∧
          dist a c ≤ δ ∧ 1 / (L * M) < dist (interpPathFn (vertexPoint (eps / b) (S'.η ω))
            ((eps / b)⁻¹).toNNReal X a) (interpPathFn (vertexPoint (eps / b) (S'.η ω))
            ((eps / b)⁻¹).toNNReal X c)}} ≤ ENNReal.ofReal θ) :
    S.P {ω | ∃ j : ℤ, vertexPoint eps (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
        ENNReal.ofReal κ + ENNReal.ofReal θ <
          ((walkPathLaw S (fun ω => vertexPoint eps (⇑(η' ω))) (S.mε_nonneg eps) eps j ω :
            ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
            (pathModulusFailure (E := ℂ) L δ)} ≤ 4 * ENNReal.ofReal θ := by
  have hq : 0 < eps / b := div_pos hε hb
  have hreg := ExitCouplingEvent.ae_regular hγ hγ2 hS'
  rw [hP] at hreg hE3 hE4
  have hle : {ω | ∃ j : ℤ, vertexPoint eps (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
        ENNReal.ofReal κ + ENNReal.ofReal θ <
          ((walkPathLaw S (fun ω => vertexPoint eps (⇑(η' ω))) (S.mε_nonneg eps) eps j ω :
            ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
            (pathModulusFailure (E := ℂ) L δ)} ≤ᵐ[S.P]
      ({ω | coneScaleRadius γ (S.hcirc ω) b ≤ 4 * (R + 2)} ∪ {ω | M < coneScaleRadius γ (S.hcirc ω) b} ∪
        {ω | ∃ x : ℤ, vertexPoint (eps / b) (S'.η ω) x ∈ ball (0 : ℂ) (1 / 4) ∧
          ENNReal.ofReal κ < srwLaw (S'.mult (eps / b) ω) x
            {y | (vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) y : ℝ≥0∞) <
              ENNReal.ofReal ((eps / b)⁻¹ * s)}} ∪
        {ω | ∃ x ∈ cellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2)),
          ENNReal.ofReal θ < srwLaw (S'.mult (eps / b) ω) x {X | ∃ a c : ℝ≥0,
            a ≤ ((vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) X).toNat : ℝ≥0) /
              ((eps / b)⁻¹).toNNReal ∧
            c ≤ ((vExitTime (interiorCellVertices (eps / b) (S'.η ω) (ball (0 : ℂ) (1 / 2))) X).toNat : ℝ≥0) /
              ((eps / b)⁻¹).toNNReal ∧
            dist a c ≤ δ ∧ 1 / (L * M) < dist (interpPathFn (vertexPoint (eps / b) (S'.η ω))
              ((eps / b)⁻¹).toNNReal X a) (interpPathFn (vertexPoint (eps / b) (S'.η ω))
              ((eps / b)⁻¹).toNNReal X c)}}) := by
    filter_upwards [hηs, hae, hbm, hreg] with ω h1 h2 h3 h4 hbad
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt, not_le] at hcon
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hcon
    obtain ⟨hcont, hprop, hlf, -, hcons⟩ := h4
    have hmult : S'.mult (eps / b) ω = S.mult eps ω := MatedCRTEnv.mult_rescale S S' hb ω h3 eps
    rw [hmult] at c3 c4
    obtain ⟨j, hj, hjlt⟩ := hbad
    have hT1 := walkPathFailure_le_of_rescaled S η' ω δ hε hb c1 c2 hL (S'.η ω)
      (fun t => by rw [h1 t, h2]) hlam hmL c3
      (fun x => by
        rw [← hmult]
        exact ExitFiniteData.srwLaw_vExitTime_eq_top_null_cellVertices (hlf (eps / b) hq)
          (hcons (eps / b) hq) hq hcont hprop isBounded_ball x)
      c4 j hj
    exact absurd hjlt (not_lt.2 hT1)
  calc S.P _ ≤ _ := measure_mono_ae hle
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hE1 hE2)) hE3))
        hE4)
    _ = 4 * ENNReal.ofReal θ := by ring

end MatedCRT.FirstPass.Derived
