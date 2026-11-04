import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.ProbabilitySubsequence
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Integral convergence against smooth test functions -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ContDiff

/-- A smooth compactly supported function is an admissible test for the
integral convergence of the Green function. -/
theorem integralConvergenceGreenFunction_smooth_test (𝒮 : SpaceFillingSLEModel)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    TendstoInProbability S.P
      (fun ε sample => (S.mε ε)⁻¹ * ∑' x : cellVertices ε (S.η sample) (ball z r),
        greenFn (S.mult ε sample) (interiorCellVertices ε (S.η sample) (ball z r))
          (vertexOf ε (S.η sample) y) x * f (vertexPoint ε (S.η sample) x))
      (fun sample => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ sample) := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by simp)
  apply h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy (fun _ => f)
  · intro x
    exact measurable_const
  · intro sample
    exact ⟨C, fun x _ => by simpa only [Real.norm_eq_abs] using hC x⟩
  · intro sample
    exact ⟨L, 1, by norm_num, le_rfl, hL.holderWith.holderOnWith _⟩

/-- Convergence in the paper's probability notation implies convergence in
measure along every deterministic mesh sequence. -/
theorem TendstoInProbability.tendstoInMeasure_sequence
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → ℝ} {Y : Ω → ℝ}
    (h : TendstoInProbability P X Y) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝[>] 0)) : TendstoInMeasure P (fun n => X (ε n)) atTop Y := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  have hlim := (h (δ / 2) (by positivity)).comp hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro sample hs
  change δ ≤ ‖X (ε n) sample - Y sample‖ at hs
  change δ / 2 < |X (ε n) sample - Y sample|
  rw [Real.norm_eq_abs] at hs
  linarith

/-- Two convergence-in-probability statements admit a common deterministic
subsequence with almost-sure convergence of both quantities. -/
theorem exists_subseq_ae_of_two_tendstoInProbability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {X Z : ℝ → Ω → ℝ} {Y W : Ω → ℝ}
    (hX : TendstoInProbability P X Y) (hZ : TendstoInProbability P Z W)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ sample ∂P,
      Tendsto (fun n => X (ε (φ n)) sample) atTop (𝓝 (Y sample)) ∧
      Tendsto (fun n => Z (ε (φ n)) sample) atTop (𝓝 (W sample)) := by
  obtain ⟨φ, hφ, hXae⟩ := (hX.tendstoInMeasure_sequence hε).exists_seq_tendsto_ae
  obtain ⟨ψ, hψ, hZae⟩ :=
    (hZ.tendstoInMeasure_sequence (hε.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
  filter_upwards [hXae, hZae] with sample hXsample hZsample
  exact ⟨hXsample.comp hψ.tendsto_atTop, hZsample⟩

/-- The degree measure and the discrete Green occupation integral converge
almost surely along a common subsequence for a fixed smooth test function. -/
theorem smooth_test_integrals_ae_subsequence (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ sample ∂S.P,
      Tendsto (fun n => ∫ x, f x ∂degreeWeightedMeasure (S.mult (ε (φ n)) sample)
        (ε (φ n)) (S.η sample) (S.μ sample)) atTop
        (𝓝 (6 * ∫ x, f x ∂S.μ sample)) ∧
      Tendsto (fun n => (S.mε (ε (φ n)))⁻¹ *
        ∑' x : cellVertices (ε (φ n)) (S.η sample) (ball z r),
          greenFn (S.mult (ε (φ n)) sample)
            (interiorCellVertices (ε (φ n)) (S.η sample) (ball z r))
            (vertexOf (ε (φ n)) (S.η sample) y) x *
              f (vertexPoint (ε (φ n)) (S.η sample) x)) atTop
        (𝓝 (S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ sample)) := by
  exact exists_subseq_ae_of_two_tendstoInProbability S.P
    (h210 γ hγ hγ2 Ω S hS f hf.continuous hfc)
    (integralConvergenceGreenFunction_smooth_test 𝒮 h34 hγ hγ2 hρ hρ1 S hS
      hr hball hy f hf hfc) ε hε

end MatedCRT
