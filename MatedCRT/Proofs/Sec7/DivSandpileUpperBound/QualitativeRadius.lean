import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.QualitativeCutoff

/-! Delayed radii under qualitative initial control. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Qualitative convergence of the initial odometer scale suffices for the
field cutoff on every shell whose preceding boundary maxima decrease. -/
theorem probTendsToOne_delayedShellRadius_le_field_cutoff_of_initial
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (O : ℝ → Ω → ℕ → ℝ) (n : ℝ → Ω → ℕ)
    (K α q : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q)
    (hstart : ∀ a : ℝ, 0 < a → ProbTendsToOne S.P
      (fun ε => {ω | (O ε ω 0 * (ε * K)) ^ α ≤ a}))
    (G : ℝ → Set Ω) (hG : ProbTendsToOne S.P G)
    (hdata : ∀ ε ω, ω ∈ G ε → ∀ k < n ε ω, 0 ≤ O ε ω k) :
    ProbTendsToOne S.P (fun ε => {ω | ∀ k ≤ n ε ω,
      (∀ j < k, O ε ω (j + 1) ≤ O ε ω j) →
        delayedShellRadius (O ε ω) (ε * K) α (ε ^ q) k ≤ dd ω}) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hinit := probTendsToOne_random_le_positive_cutoff S.P dd
    (hdd.mono (S.fieldSigma_le hS) le_rfl) hpos
    (fun ε ω => (O ε ω 0 * (ε * K)) ^ α) hstart
  have hfloor := probTendsToOne_le_field_cutoff S hS dd hdd hpos
    (fun ε => ε ^ q) (tendsto_rpow_nhdsGT_zero hq)
  apply ((hG.inter hinit).inter hfloor).mono_ev
  filter_upwards [self_mem_nhdsWithin] with ε hε ω hω
  intro k hk hmono
  have hbound := shell_radii_le_initial_envelope (O ε ω)
    (delayedShellRadius (O ε ω) (ε * K) α (ε ^ q)) (ε * K) α (ε ^ q) k
    (mul_nonneg hε.le hK) hα.le
    (fun j hj => hdata ε ω hω.1.1 j (lt_of_lt_of_le hj hk))
    hmono (fun j _ => by rw [delayedShellRadius_succ]) k le_rfl
  have henv : max (delayedShellRadius (O ε ω) (ε * K) α (ε ^ q) 0)
      (max ((O ε ω 0 * (ε * K)) ^ α) (ε ^ q)) ≤ dd ω := by
    rw [← delayedShellRadius_zero, max_self, delayedShellRadius_zero]
    exact max_le hω.1.2 hω.2
  exact hbound.trans henv

end MatedCRT.Sec7
