import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShiftedRadius
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PositiveCutoff
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-! A uniform envelope for the delayed shell radii. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Before the boundary maxima stop decreasing, every shell radius is bounded
by the initial radius or by the radius chosen from the initial maximum. -/
theorem shell_radii_le_initial_envelope
    (O r : ℕ → ℝ) (K α R : ℝ) (n : ℕ)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hO : ∀ k < n, 0 ≤ O k)
    (hmono : ∀ k < n, O (k + 1) ≤ O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R) :
    ∀ k ≤ n, r k ≤ max (r 0) (max ((O 0 * K) ^ α) R) := by
  have hOupper : ∀ k ≤ n, O k ≤ O 0 := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hmono k (by omega)).trans (ih (by omega))
  intro k hk
  cases k with
  | zero => exact le_max_left _ _
  | succ k =>
    have hp : (O k * K) ^ α ≤ (O 0 * K) ^ α :=
      Real.rpow_le_rpow (mul_nonneg (hO k (by omega)) hK)
        (mul_le_mul_of_nonneg_right (hOupper k (by omega)) hK) hα
    exact (hr k (by omega)).trans ((max_le_max hp le_rfl).trans (le_max_right _ _))

/-- A vanishing deterministic envelope places every radius before the stopping
index below the field-measurable survival cutoff with high probability. -/
theorem probTendsToOne_shell_radii_le_field_cutoff
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (O r : ℝ → Ω → ℕ → ℝ) (K α R : ℝ → ℝ) (n : ℝ → Ω → ℕ)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne S.P G)
    (hdata : ∀ ε ω, ω ∈ G ε → 0 ≤ K ε ∧ 0 ≤ α ε ∧
      (∀ k < n ε ω, 0 ≤ O ε ω k) ∧
      (∀ k < n ε ω, O ε ω (k + 1) ≤ O ε ω k) ∧
      (∀ k < n ε ω, r ε ω (k + 1) ≤ max ((O ε ω k * K ε) ^ (α ε)) (R ε)))
    (scale : ℝ → ℝ) (hscale : Tendsto scale (𝓝[>] 0) (𝓝 0))
    (henvelope : ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ G ε,
      max (r ε ω 0) (max ((O ε ω 0 * K ε) ^ (α ε)) (R ε)) ≤ scale ε) :
    ProbTendsToOne S.P (fun ε => {ω | ∀ k ≤ n ε ω, r ε ω k ≤ dd ω}) := by
  have hcut := probTendsToOne_le_field_cutoff S hS dd hdd hpos scale hscale
  apply (hG.inter hcut).mono_ev
  filter_upwards [henvelope] with ε hε ω hω
  obtain ⟨hK, hα, hO, hmono, hr⟩ := hdata ε ω hω.1
  intro k hk
  exact (shell_radii_le_initial_envelope (O ε ω) (r ε ω) (K ε) (α ε) (R ε)
    (n ε ω) hK hα hO hmono hr k hk).trans ((hε ω hω.1).trans hω.2)

/-- The cutoff bound holds at each shell under monotonicity of the preceding
maxima, making it available inside the shell-contraction induction. -/
theorem probTendsToOne_shell_radius_le_field_cutoff_of_prefix
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (O r : ℝ → Ω → ℕ → ℝ) (K α R : ℝ → ℝ) (n : ℝ → Ω → ℕ)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne S.P G)
    (hdata : ∀ ε ω, ω ∈ G ε → 0 ≤ K ε ∧ 0 ≤ α ε ∧
      (∀ k < n ε ω, 0 ≤ O ε ω k) ∧
      (∀ k < n ε ω, r ε ω (k + 1) ≤ max ((O ε ω k * K ε) ^ (α ε)) (R ε)))
    (scale : ℝ → ℝ) (hscale : Tendsto scale (𝓝[>] 0) (𝓝 0))
    (henvelope : ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ G ε,
      max (r ε ω 0) (max ((O ε ω 0 * K ε) ^ (α ε)) (R ε)) ≤ scale ε) :
    ProbTendsToOne S.P (fun ε => {ω | ∀ k ≤ n ε ω,
      (∀ j < k, O ε ω (j + 1) ≤ O ε ω j) → r ε ω k ≤ dd ω}) := by
  have hcut := probTendsToOne_le_field_cutoff S hS dd hdd hpos scale hscale
  apply (hG.inter hcut).mono_ev
  filter_upwards [henvelope] with ε hε ω hω
  obtain ⟨hK, hα, hO, hr⟩ := hdata ε ω hω.1
  intro k hk hmono
  exact (shell_radii_le_initial_envelope (O ε ω) (r ε ω) (K ε) (α ε) (R ε) k
    hK hα (fun j hj => hO j (lt_of_lt_of_le hj hk)) hmono
    (fun j hj => hr j (lt_of_lt_of_le hj hk)) k le_rfl).trans ((hε ω hω.1).trans hω.2)

end MatedCRT.Sec7
