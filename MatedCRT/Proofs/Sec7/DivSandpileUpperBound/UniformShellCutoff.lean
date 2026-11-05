import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialShellCutoff

/-! A horizon-independent cutoff for delayed shell radii.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Qualitative initial-odometer control bounds all delayed radii on every
decreasing prefix, uniformly over the eventual choice of the horizon. -/
theorem tendsToOneOn_delayedShellRadius_le_field_cutoff_all
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (F : Set Ω) (dd : Ω → ℝ) (hdd : Measurable[S.fieldSigma] dd)
    (hpos : ∀ ω, 0 < dd ω) (O : ℝ → Ω → ℕ → ℝ)
    (K α q : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne S.P G)
    (hdata : ∀ ε ω, ω ∈ G ε → ∀ k, 0 ≤ O ε ω k)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn S.P F
      (fun ε => {ω | ε * O ε ω 0 ≤ a})) :
    TendsToOneOn S.P F (fun ε => {ω | ∀ k,
      (∀ j < k, O ε ω (j + 1) ≤ O ε ω j) →
        delayedShellRadius (O ε ω) (ε * K) α (ε ^ q) k ≤ dd ω}) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hstart := tendsToOneOn_initialRadius_of_rescaled_odometer S.P F
    (fun ε ω => O ε ω 0) K α hK hα G hG (fun ε ω hω => hdata ε ω hω 0) hsmall
  have hinit := tendsToOneOn_random_le_positive_cutoff S.P F dd
    (hdd.mono (S.fieldSigma_le hS) le_rfl) hpos
    (fun ε ω => (O ε ω 0 * (ε * K)) ^ α) hstart
  have hinit' := (probTendsToOne_compl_union_iff S.P F
    (fun ε => {ω | (O ε ω 0 * (ε * K)) ^ α ≤ dd ω})).2 hinit
  have hfloor := probTendsToOne_le_field_cutoff S hS dd hdd hpos
    (fun ε => ε ^ q) (tendsto_rpow_nhdsGT_zero hq)
  apply (probTendsToOne_compl_union_iff S.P F _).1
  apply ((hG.inter hinit').inter hfloor).mono_ev
  filter_upwards [self_mem_nhdsWithin] with ε hε ω hω
  by_cases hF : ω ∈ F
  · right
    have hinitial : (O ε ω 0 * (ε * K)) ^ α ≤ dd ω :=
      hω.1.2.resolve_left (by simpa using hF)
    intro k hmono
    have hbound := shell_radii_le_initial_envelope (O ε ω)
      (delayedShellRadius (O ε ω) (ε * K) α (ε ^ q)) (ε * K) α (ε ^ q) k
      (mul_nonneg hε.le hK) hα.le
      (fun j _ => hdata ε ω hω.1.1 j)
      hmono (fun j _ => by rw [delayedShellRadius_succ]) k le_rfl
    have henv : max (delayedShellRadius (O ε ω) (ε * K) α (ε ^ q) 0)
        (max ((O ε ω 0 * (ε * K)) ^ α) (ε ^ q)) ≤ dd ω := by
      rw [← delayedShellRadius_zero, max_self, delayedShellRadius_zero]
      exact max_le hinitial hω.2
    exact hbound.trans henv
  · exact Or.inl hF

end MatedCRT.Sec7
