import MatedCRT.FirstPass.S5c.ThresholdField
import MatedCRT.FirstPass.S5c.ExactVersion

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), measure layer, step M3 for the field): an exact version of the least supersolution

Generic, with the frozen universal measurability `hF1` (Frozen/S1c.lean:40) as the only frozen input. For a fixed point `p`
in the closed ball of radius `R`, `ω ↦ leastSupersolution (μ ω) R 0 u p` has an `m`-measurable version (`m` the field
σ-algebra), equal to it almost surely. Proof: each rational threshold is a.s. the preimage under the moment vector of `g` of a
Borel set (`threshold_field_borel`), and `exists_measurable_version_of_thresholds` (ExactVersion.lean) takes over.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open MatedCRT

/-- **Exact version of the least supersolution** (M3 for the field). -/
theorem exists_measurable_leastSupersolution {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) {P : @Measure Ω mΩ} [IsProbabilityMeasure P] (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    {μ g : Ω → Measure ℂ} {R u : ℝ} (hR : 0 ≤ R) (hu : 0 < u)
    (hg : Measurable[m] g) (hμg : ∀ᵐ ω ∂P, μ ω = g ω)
    (hμ : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    (φs : ℕ → ℂ → ℝ) (hφs : ∀ k, φs k ∈ nonnegTest R)
    (hdense : ∀ φ ∈ nonnegTest R, ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x ∈ closedBall (0 : ℂ) R,
        |φ x - φs k x| < ε ∧ |Laplacian.laplacian φ x - Laplacian.laplacian (φs k) x| < ε)
    (hG : ∀ x ∈ ball (0 : ℂ) R, x ≠ 0 → 0 ≤ greenFunction (ball (0 : ℂ) R) 0 x)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) R)
    (hbdd : ∀ᵐ ω ∂P, BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions (μ ω) R 0 u)) :
    ∃ v' : Ω → ℝ, Measurable[m] v' ∧ ∀ᵐ ω ∂P, v' ω = leastSupersolution (μ ω) R 0 u p := by
  have hcont : ∀ k, Continuous (φs k) := fun k =>
    (contDiff_two_of_isTestFunction (hφs k).1).continuous
  have hY : Measurable[m] (fun ω => lintegralMoment φs (g ω)) :=
    measurable_lintegralMoment hg φs hcont
  refine exists_measurable_version_of_thresholds (m := m) (P := P)
    (fun ω => leastSupersolution (μ ω) R 0 u p) (fun c => ?_)
  obtain ⟨T, hT, hTω⟩ := threshold_field_borel hm hF1 hR hu hg hμg hμ φs hφs hdense hG hp hbdd (c : ℝ)
  exact ⟨(fun ω => lintegralMoment φs (g ω)) ⁻¹' T, hY hT, hTω.mono fun ω h => h.symm⟩

end MatedCRT.S5c
