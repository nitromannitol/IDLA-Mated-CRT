import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalPolynomialCertificate
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalRadius
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusChoice

/-! Budgeted shell horizons for polynomial mesh scales.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- The first delayed radius tends to zero on an event when the initial
mesh-normalized odometer tends to zero there. -/
theorem tendsToOneOn_initial_delayed_radius
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (O : ℝ → Ω → ℝ) {K α q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hq : 0 < q)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ O ε ω)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn P E (fun ε => {ω | ε * O ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → TendsToOneOn P E (fun ε => {ω |
      delayedShellRadius (fun _ => O ε ω) (ε * K) α (ε ^ q) 0 ≤ a}) := by
  have hinit := tendsToOneOn_initialRadius_of_rescaled_odometer P E O K α hK hα G hG hnonneg hsmall
  intro a ha
  have hfloor : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ^ q ≤ a :=
    ((tendsto_rpow_nhdsGT_zero hq).eventually (eventually_lt_nhds ha)).mono
      (fun _ h => h.le)
  have h := hinit a ha
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfloor] with ε hε
  apply measure_mono
  rintro ω ⟨hE, hbad⟩
  refine ⟨hE, ?_⟩
  intro hinit
  apply hbad
  change delayedShellRadius (fun _ => O ε ω) (ε * K) α (ε ^ q) 0 ≤ a
  rw [delayedShellRadius_zero]
  exact max_le hinit hε

/-- The initial odometer alone determines a budgeted dyadic horizon when the
floor and diameter bounds are fixed positive powers of the mesh. -/
theorem tendsToOneOn_budgeted_dyadic_horizon_with_mesh_scales
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : Set Ω)
    (O : ℝ → Ω → ℝ) {K b α c s T δ q d : ℝ}
    (hK : 0 < K) (hb : 0 ≤ b) (hb1 : b < 1)
    (hα : 0 < α) (hc : 0 < c) (hs : 0 < s) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hq : 0 < q) (hd : 0 < d)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ O ε ω)
    (hsmall : ∀ a : ℝ, 0 < a → TendsToOneOn P E (fun ε => {ω | ε * O ε ω ≤ a})) :
    TendsToOneOn P E (fun ε => {ω |
      let S := max (O ε ω) (ε ^ (-b))
      let x := S * (ε * K)
      let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
      let q' := (1 / 2 : ℝ) ^ α
      let r₀ := delayedShellRadius (fun _ => O ε ω) (ε * K) α (ε ^ q) 0
      ∃ N n : ℕ,
        S * (1 / 2 : ℝ) ^ N ≤ ε ^ (-b) ∧
        let H := (N : ℝ) * (2 / s + 2) *
          (1 + |Real.log a| + |Real.log q'| * (N : ℝ)) ^ 2
        H < (n : ℝ) ∧ r₀ + (x ^ α * (2 / s + 2) *
          ((1 + |Real.log a| + |Real.log q'|) ^ 2 * T) + ε ^ q * H) +
          (H + 1) * (2 * ε ^ d) ≤ δ}) := by
  have hr₀ := tendsToOneOn_initial_delayed_radius P E O hK.le hα hq G hG hnonneg hsmall
  have hpoly : TendsToOneOn P E (fun ε => {ω : Ω |
      0 ≤ ε ^ q ∧ ε ^ q ≤ (1 : ℝ) * ε ^ q ∧
      0 ≤ ε ^ d ∧ ε ^ d ≤ (1 : ℝ) * ε ^ d}) := by
    unfold TendsToOneOn
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hp : 0 < ε := hε
    simp [Real.rpow_nonneg hp.le]
  exact tendsToOneOn_budgeted_dyadic_horizon_of_polynomial_errors P E O
    (fun ε ω => delayedShellRadius (fun _ => O ε ω) (ε * K) α (ε ^ q) 0)
    (fun ε _ => ε ^ q) (fun ε _ => ε ^ d) hK hb hb1 hα hc hs hT hδ hq hd
    hsmall hr₀ hpoly

end MatedCRT.Sec7
