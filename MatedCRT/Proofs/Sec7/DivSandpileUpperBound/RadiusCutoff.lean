import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusPolynomial

/-! The delayed polynomial radius fits below the field-measurable cutoff. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Under polynomial initial control, every delayed radius whose preceding
odometer maxima decrease lies below the survival cutoff with high probability. -/
theorem probTendsToOne_delayedShellRadius_le_field_cutoff
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd) (hpos : ∀ ω, 0 < dd ω)
    (O : ℝ → Ω → ℕ → ℝ) (n : ℝ → Ω → ℕ)
    (A K p α q : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hp : p < 1) (hα : 0 < α) (hq : 0 < q)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne S.P G)
    (hdata : ∀ ε ω, ω ∈ G ε → 0 ≤ O ε ω 0 ∧
      O ε ω 0 ≤ A * ε ^ (-p) ∧ ∀ k < n ε ω, 0 ≤ O ε ω k) :
    ProbTendsToOne S.P (fun ε => {ω | ∀ k ≤ n ε ω,
      (∀ j < k, O ε ω (j + 1) ≤ O ε ω j) →
        delayedShellRadius (O ε ω) (ε * K) α (ε ^ q) k ≤ dd ω}) := by
  let scale : ℝ → ℝ := fun ε => (A * K) ^ α * ε ^ ((1 - p) * α) + ε ^ q
  have hscale : Tendsto scale (𝓝[>] 0) (𝓝 0) :=
    tendsto_delayedShellRadius_polynomial_envelope A K p α q hp hα hq
  have hcut := probTendsToOne_le_field_cutoff S hS dd hdd hpos scale hscale
  apply (hG.inter hcut).mono_ev
  filter_upwards [self_mem_nhdsWithin] with ε hε ω hω
  obtain ⟨hO0, hupper, hO⟩ := hdata ε ω hω.1
  intro k hk hmono
  have hbound := shell_radii_le_initial_envelope (O ε ω)
    (delayedShellRadius (O ε ω) (ε * K) α (ε ^ q)) (ε * K) α (ε ^ q) k
    (mul_nonneg hε.le hK) hα.le (fun j hj => hO j (lt_of_lt_of_le hj hk))
    hmono (fun j _ => by rw [delayedShellRadius_succ]) k le_rfl
  have henv : max (delayedShellRadius (O ε ω) (ε * K) α (ε ^ q) 0)
      (max ((O ε ω 0 * (ε * K)) ^ α) (ε ^ q)) ≤ scale ε := by
    rw [← delayedShellRadius_zero, max_self]
    exact delayedShellRadius_initial_polynomial_bound (O ε ω) ε A K p α q
      hε hA hK hO0 hα.le hupper
  exact hbound.trans (henv.trans hω.2)

end MatedCRT.Sec7
