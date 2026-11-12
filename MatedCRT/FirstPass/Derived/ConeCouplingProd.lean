import MatedCRT.FirstPass.Derived.ConeGFFIsGFF
import MatedCRT.FirstPass.Derived.ConeCouplingOfRealization

/-!
# The quantum cone on `B_1` as `h̃ - γ log |·|` on the sample space enlarged by a Brownian motion

Let `(hC, hcirc)` be the circle average embedding of a `γ`-quantum cone under `P` (`IsQuantumCone`, Definition 2.1)
and `μ` its `γ`-LQG measure. On the enlarged sample space `Ω × C(ℝ≥0, ℝ)` under `P ⊗ BM`, the field `h̃` obtained
from the cone by replacing its radial part `h_{|x|}(0)` by `h_{|x|}(0) + γ log |x|` inside the unit disk and by the
independent Brownian motion of the second coordinate outside it (`coneCouplingPairing`, `coneGFFCircle`) is a
whole-plane GFF (`isWholePlaneGFF_coneGFF`; eq:gff, line 444, and DMS14 Definition 4.10). This file adds:

* `circle_eq_fieldCircleAverage_coneGFFCircle`: deterministically, for every circle with closure in the open unit
  disk, `h_r(z) = h̃_r(z) - γ (log |·|)_r(z)` (the remainder `coneCouplingRemainder` vanishes on the closed unit
  disk, and `coneGFFCircle` is the exact form `coneCircle_eq_addCircleAverage`);
* `exists_coneCoupling_prod`: on `Ω × C(ℝ≥0, ℝ)` under `P ⊗ BM` there are the circle average process `H` of a
  whole-plane GFF (Bonanno's `LQGDimension.IsGFFCircleAverage`) and its `γ`-LQG measure `μ̃` (DS11 Proposition 1.1,
  `LatticeProb.Gauss.IsWholePlaneGFF.exists_isLQGMeasure`), such that almost surely the cone circle averages over
  every circle in `B_1` are those of `h̃ - γ log |·|`. This is the statement of `ConeWholePlaneCouplingStep` for the
  cone read through the first coordinate of the enlarged space.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- **The cone is the coupled field minus `γ log |·|` on `B_1`.** For every circle `∂B_r(z)` with
`cl B_r(z) ⊆ B_1`, `h_r(z) = h̃_r(z) - γ (log |·|)_r(z)` for the coupled field `h̃` with circle averages
`coneGFFCircle γ hcirc w`, for every circle average process `hcirc` and every path `w`. -/
theorem circle_eq_fieldCircleAverage_coneGFFCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsub : closedBall z r ⊆ ball (0 : ℂ) 1) :
    hcirc r z = fieldCircleAverage γ (coneGFFCircle γ hcirc w) r z := by
  have hrem : Real.circleAverage (coneCouplingRemainder γ hcirc w) z r = 0 := by
    have h : EqOn (coneCouplingRemainder γ hcirc w) (fun _ => (0 : ℝ)) (sphere z |r|) := by
      intro x hx
      rw [abs_of_pos hr] at hx
      have hx' : x ∈ ball (0 : ℂ) 1 := hsub (sphere_subset_closedBall hx)
      rw [mem_ball, dist_zero_right] at hx'
      simp [coneCouplingRemainder, hx'.le]
    rw [Real.circleAverage_congr_sphere h, Real.circleAverage_const]
  simp only [fieldCircleAverage, coneGFFCircle, hrem]
  ring

/-- **The coupling of the quantum cone with a whole-plane GFF on the enlarged sample space.** For a `γ`-quantum cone
`(hC, hcirc)` under `P`, `γ ∈ (0, 2)`, there are on `Ω × C(ℝ≥0, ℝ)` under `P ⊗ BM` the circle average process `H` of
a whole-plane GFF normalized by `h̃_1(0) = 0` and its `γ`-LQG measure `μ̃` such that almost surely
`h_r(z) = h̃_r(z) - γ (log |·|)_r(z)` for every circle with `cl B_r(z) ⊆ B_1`, where `h` is read through the first
coordinate. -/
theorem exists_coneCoupling_prod {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsQuantumCone γ P hC hcirc) :
    ∃ (H : ℝ → ℂ → Ω × ContinuousPath ℝ → ℝ) (μ' : Ω × ContinuousPath ℝ → Measure ℂ),
      LQGDimension.IsGFFCircleAverage H (P.prod (brownianMotion 0)) ∧
      MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ' (P.prod (brownianMotion 0)) ∧
      ∀ᵐ x ∂(P.prod (brownianMotion 0)), ∀ (r : ℝ) (z : ℂ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 →
        hcirc x.1 r z = fieldCircleAverage γ (fun s w => H s w x) r z := by
  obtain ⟨N, _, hN0, hG⟩ := isWholePlaneGFF_coneGFF hQ
  obtain ⟨μ', hμ'⟩ := ((LPBridge.isWholePlaneGFF_iff _ _ _).1 hG).exists_isLQGMeasure hγ hγ2
  obtain ⟨H, hH, hA, hHae⟩ := MatedCRT.Field.IsWholePlaneGFF.exists_bonanno_gmc_version hG
    ((LPBridge.isLQGMeasure_iff _ γ _ μ').2 hμ')
  refine ⟨H, μ', hH, hA, ?_⟩
  have hN : ∀ᵐ ω ∂P, ω ∉ N := compl_mem_ae_iff.2 hN0
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hN, hHae] with x hx h2 r z hr hsub
  have hfun : (fun s w => H s w x) = coneGFFCircle γ (circleOff N hcirc x.1) (fun t => x.2 t) := by
    funext s w
    exact h2 s w
  rw [hfun, ← circle_eq_fieldCircleAverage_coneGFFCircle γ _ _ hr hsub, circleOff_of_notMem hx]

end MatedCRT.FirstPass.Derived
