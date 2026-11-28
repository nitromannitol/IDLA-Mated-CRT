import MatedCRT.FirstPass.Derived.LQGMeasureChartInputs
import MatedCRT.FirstPass.Derived.LQGMeasureChartPairingBound
import MatedCRT.FirstPass.Derived.LQGMeasureChartStraightenLimit
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn

/-!
# The simultaneous fixed-scale coordinate change on a disc from the two cited inputs

`sheffieldWangDiscConformal_of_inputs` proves `SheffieldWangDiscConformal`: the stated conclusion of Sheffield–Wang,
*Field-measure correspondence in Liouville quantum gravity almost surely commutes with all conformal maps
simultaneously* (arXiv:1605.06171v2), Theorem 1.4 (p. 3), on a disc and at the scales `2^{-k}`. For a zero-boundary GFF
`h` on `B(c, r)` with its continuous circle-average process, almost surely the circle approximations converge to a
measure `μ` and, for every conformal map `ψ` of the disc onto a bounded open set at once, the smooth approximations of
`h ∘ φ + Q log |φ'|`, `φ = ψ⁻¹`, at the scales `2^{-k}` converge in `ψ(B(c, r))` to the measure `A ↦ μ(φ(A))`.

The inputs are `SheffieldWangEnvelope` (Sheffield–Wang (2016), Theorem 1.1 and the envelope statement at the end of
the proof of Theorem 1.2, pp. 10-11) and `ZeroBoundaryGFFLocalRegularity` (De Nitti–Schweiger, arXiv:2301.13781v4,
Proposition 2.1, p. 9). The proof has two steps, and the almost sure event is fixed before the map `ψ` is chosen:

1. *Variable source radii.* The envelope statement for the bumps `f` and `f_{1/3}` (`log₂(1/3)` is irrational; the
   two circle limits agree since vague limits are unique) gives, for every continuous `b > 0` on the disc, the
   convergence of the smooth approximations at the radius `2^{-k} b(z)` to `μ`
   (`isVagueLimitOn_varScaleApprox_of_regularity`). The regularity input also enters here: it gives the local
   finiteness of the envelope measures, which the vague convergence `QuantumZipper.IsVagueLimitOn` (stated with
   Bochner integrals) does not carry.
2. *Straightening the bump.* With the local regularity `h ∈ C^{-1/2}_loc`, the smooth approximation of the
   pulled-back field at the fixed scale `2^{-k}` is, after the change of variables `w = ψ(z)`, the smooth approximation
   of `h` at the radius `2^{-k} |φ'(ψ z)|` up to a factor `1 + O(2^{-k/2})`
   (`isVagueLimitOn_smoothApprox_pullbackPairing`), applied with `b(z) = |φ'(ψ z)| = |ψ'(z)|⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

open LQGMeasureChart LQGMeasureChart.Straighten

/-- **The simultaneous fixed-scale coordinate change of the LQG measure on a disc** (the stated conclusion of
Sheffield–Wang (2016), Theorem 1.4, on a disc, at the scales `2^{-k}`), from the envelope statement of Sheffield–Wang
(2016) (Theorem 1.1 and the end of the proof of Theorem 1.2) and the local negative regularity of the zero-boundary
GFF (De Nitti–Schweiger, Proposition 2.1). -/
theorem sheffieldWangDiscConformal_of_inputs (hE : SheffieldWangEnvelope) (hR : ZeroBoundaryGFFLocalRegularity) :
    SheffieldWangDiscConformal := by
  intro γ hγ0 hγ2 f hf c r hr Ω _ P hP h hh hcirc hcircv
  have hf' : IsMollifier (mollDilate (1 / 3) f) := isMollifier_mollDilate hf (by norm_num) (by norm_num)
  obtain ⟨u, l, hul, hu1, hl1, hE1⟩ := hE γ hγ0 hγ2 f hf c r hr Ω P hP h hh hcirc hcircv
  obtain ⟨u', l', hul', hu1', hl1', hE2⟩ := hE γ hγ0 hγ2 _ hf' c r hr Ω P hP h hh hcirc hcircv
  filter_upwards [hE1, hE2, hR c r hr Ω P hP h hh] with ω h1 h2 h3
  obtain ⟨μ, hμ, henv⟩ := h1
  obtain ⟨μ', hμ', henv'⟩ := h2
  have hμμ' : μ' = μ := QuantumZipper.isVagueLimitOn_unique isOpen_ball hμ' hμ
  rw [hμμ'] at henv'
  refine ⟨μ, hμ, fun ψ hinj hψ _ => ?_⟩
  have hg : HasLocalRegularity (h ω) (-(1 / 2)) := fun K hK hKs => h3 (-(1 / 2)) (by norm_num) K hK hKs
  have hb : ContinuousOn (fun z => ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖) (ball c r) := by
    refine ((hψ.deriv isOpen_ball).continuousOn.norm.inv₀
      fun z hz => norm_ne_zero_iff.2 (deriv_ne_zero hψ hinj hz)).congr fun z hz => ?_
    show ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖ = ‖deriv ψ z‖⁻¹
    rw [norm_deriv_invFunOn hψ hinj (mem_image_of_mem ψ hz), invFunOn_apply hinj hz]
  have hbpos : ∀ z ∈ ball c r, 0 < ‖deriv (Function.invFunOn ψ (ball c r)) (ψ z)‖ := by
    intro z hz
    rw [norm_deriv_invFunOn hψ hinj (mem_image_of_mem ψ hz), invFunOn_apply hinj hz]
    exact inv_pos.2 (norm_pos_iff.2 (deriv_ne_zero hψ hinj hz))
  have hvar := isVagueLimitOn_varScaleApprox_of_regularity (γ := γ) hf (fun N => (hul N).1)
    (fun N => (hul N).2) (fun N => (hul' N).1) (fun N => (hul' N).2) hu1 hl1 hu1' hl1'
    (fun N hN => (henv N hN).1) (fun N hN => (henv N hN).2) (fun N hN => (henv' N hN).1)
    (fun N hN => (henv' N hN).2) h3 hb hbpos
  exact isVagueLimitOn_smoothApprox_pullbackPairing hψ hinj hγ0 hf hg hvar

end MatedCRT
