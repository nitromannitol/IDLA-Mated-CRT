import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestFiniteCover

/-!
# Measurable covers by a countable family of tests (E-c2-9)

For a countable family of deterministic tests `g j` and a countable set `Q` of points in the ball, the
events `{ω | ∀ q ∈ Q, |f ω q - g j q| < δ}` are measurable, and if every environment is `δ`-close to some
test on `Q`, finitely many of them cover all but any prescribed probability. Together with
`abs_sub_le_of_forall_lt_on_dense` (a bound on the whole ball from the bound on a dense countable set) and
`tendstoInProbability_of_finite_cover`, this is the approximation layer of E-c2-9 in `GAPS-SEC3.md`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- The event that an environment-dependent test is `δ`-close to `g` on a countable set `Q` is measurable,
provided each `ω ↦ f ω x` is measurable. -/
theorem measurableSet_forall_abs_sub_lt {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℂ → ℝ}
    (hf : ∀ x, Measurable fun ω => f ω x) {Q : Set ℂ} (hQ : Q.Countable) (g : ℂ → ℝ) (δ : ℝ) :
    MeasurableSet {ω | ∀ q ∈ Q, |f ω q - g q| < δ} := by
  have h : {ω | ∀ q ∈ Q, |f ω q - g q| < δ} = ⋂ q ∈ Q, {ω | |f ω q - g q| < δ} := by
    ext ω
    simp
  rw [h]
  exact MeasurableSet.biInter hQ fun q _ =>
    measurableSet_lt (continuous_abs.measurable.comp ((hf q).sub_const (g q))) measurable_const

/-- **Finite cover by countably many approximation events.** If every environment is `δ`-close on `Q` to
some member of a countable family `g : ℕ → ℂ → ℝ`, then for every `κ > 0` finitely many of the events
`{ω | ∀ q ∈ Q, |f ω q - g j q| < δ}` cover all but probability `κ`. -/
theorem exists_finite_cover_of_countable_family {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℂ → ℝ} (hf : ∀ x, Measurable fun ω => f ω x)
    {Q : Set ℂ} (hQ : Q.Countable) (g : ℕ → ℂ → ℝ) (δ : ℝ)
    (hcov : ∀ ω, ∃ j, ∀ q ∈ Q, |f ω q - g j q| < δ) (κ : ℝ≥0∞) (hκ : 0 < κ) :
    ∃ J : ℕ, P ((⋃ j ∈ Finset.range J, {ω | ∀ q ∈ Q, |f ω q - g j q| < δ})ᶜ) < κ := by
  set A : ℕ → Set Ω := fun j => {ω | ∀ q ∈ Q, |f ω q - g j q| < δ} with hA
  have hAm : ∀ j, MeasurableSet (A j) := fun j => measurableSet_forall_abs_sub_lt hf hQ (g j) δ
  set V : ℕ → Set Ω := fun J => (⋃ j ∈ Finset.range J, A j)ᶜ with hV
  have hVm : ∀ J, MeasurableSet (V J) := fun J =>
    (Finset.measurableSet_biUnion _ fun j _ => hAm j).compl
  have hanti : Antitone V := fun J K hJK => compl_subset_compl.2
    (biUnion_subset_biUnion_left fun j hj => Finset.mem_range.2 ((Finset.mem_range.1 hj).trans_le hJK))
  have hinter : (⋂ J, V J) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    obtain ⟨j, hj⟩ := hcov ω
    have hωA : ω ∈ A j := hj
    exact (mem_iInter.1 hω (j + 1)) (mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_self j), hωA⟩)
  have hlim : Tendsto (fun J => P (V J)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (fun J => (hVm J).nullMeasurableSet) hanti
      ⟨0, measure_ne_top P _⟩
    rw [hinter, measure_empty] at h
    exact h
  obtain ⟨J, hJ⟩ := (hlim.eventually_lt_const hκ).exists
  exact ⟨J, hJ⟩

/-- **Bound on the ball from a dense set.** If `F` and `G` are continuous on the ball `B(z, r)` and
`|F q - G q| < δ` on a set `Q ⊆ B(z, r)` whose closure contains the ball, then `|F x - G x| ≤ δ` on the
whole ball. This converts the bound on a countable dense set into the bound used in the pathwise
comparison of the truncated occupation integrals. -/
theorem abs_sub_le_of_forall_lt_on_dense {F G : ℂ → ℝ} {z : ℂ} {r : ℝ} {Q : Set ℂ}
    (hQB : Q ⊆ Metric.ball z r) (hQd : Metric.ball z r ⊆ closure Q)
    (hF : ContinuousOn F (Metric.ball z r)) (hG : ContinuousOn G (Metric.ball z r)) {δ : ℝ}
    (h : ∀ q ∈ Q, |F q - G q| < δ) : ∀ x ∈ Metric.ball z r, |F x - G x| ≤ δ := by
  intro x hx
  have hc : ContinuousOn (fun y => |F y - G y|) (Metric.ball z r) := (hF.sub hG).abs
  obtain ⟨u, huQ, hu⟩ := mem_closure_iff_seq_limit.1 (hQd hx)
  have hu' : Tendsto u atTop (𝓝[Metric.ball z r] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall fun n => hQB (huQ n)⟩
  have hlim : Tendsto (fun n => |F (u n) - G (u n)|) atTop (𝓝 |F x - G x|) :=
    (hc x hx).tendsto.comp hu'
  exact le_of_tendsto hlim (Eventually.of_forall fun n => (h (u n) (huQ n)).le)

end MatedCRT
