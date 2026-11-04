import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundary
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialMeasurable

/-! Probability control for a continuous random function near a ball boundary. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Pointwise measurability and almost-sure continuity give a deterministic
boundary layer on which a random function vanishing at the boundary is small
with arbitrarily high probability. -/
theorem boundary_layer_small_in_probability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {z : ℂ} {r : ℝ} (hr : 0 < r) (F : Ω → ℂ → ℝ)
    (hF : ∀ x ∈ closedBall z r, AEMeasurable (fun ω => F ω x) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (F ω) (closedBall z r) ∧
      ∀ x ∈ sphere z r, F ω x = 0)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      P {ω | ∃ x ∈ closedBall z r \ closedBall z r', t < |F ω x|} ≤ e := by
  let K := closedBall z r
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable D := hDc.to_subtype
  let R : ℕ → ℝ := fun n => r - 1 / ((n : ℝ) + 1)
  let A : ℕ → Set Ω := fun n => {ω | ∃ x : D, R n < dist x.1.1 z ∧ t < |F ω x|}
  have hAmeas : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    have hA : A n = ⋃ x : D, if R n < dist x.1.1 z then
        {ω | t < |F ω x|} else ∅ := by
      ext ω
      simp only [A, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨x, hx, hfx⟩
        exact ⟨x, by simpa [hx] using hfx⟩
      · rintro ⟨x, hx⟩
        by_cases hR : R n < dist x.1.1 z
        · exact ⟨x, hR, by simpa [hR] using hx⟩
        · simp [hR] at hx
    rw [hA]
    apply NullMeasurableSet.iUnion
    intro x
    split_ifs
    · exact nullMeasurableSet_lt aemeasurable_const ((hF x x.1.property).abs)
    · exact MeasurableSet.empty.nullMeasurableSet
  have hR : Monotone R := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [R]
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : 1 / ((n + 1 : ℕ) + 1 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hden
      push_cast
      linarith
    linarith
  have hanti : Antitone A := by
    intro n m hnm ω hω
    obtain ⟨x, hx, hfx⟩ := hω
    exact ⟨x, (hR hnm).trans_lt hx, hfx⟩
  have hRlim : Tendsto R atTop (𝓝 r) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat)
  have hinter : P (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hcont)
    intro ω hω hc
    obtain ⟨r', hr'0, hr'r, hrsmall⟩ :=
      exists_boundary_layer_of_continuousOn hr hc.1 hc.2 ht
    obtain ⟨n, hn⟩ := (hRlim.eventually (eventually_gt_nhds hr'r)).exists
    obtain ⟨x, hx, hfx⟩ := mem_iInter.mp hω n
    have hxlayer : (x : ℂ) ∈ closedBall z r \ closedBall z r' := by
      refine ⟨x.1.property, ?_⟩
      rw [mem_closedBall]
      exact not_le_of_gt (hn.trans hx)
    exact (not_lt_of_ge (hrsmall x hxlayer).le) hfx
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    simpa only [hinter, Function.comp_def] using
      (tendsto_measure_iInter_atTop hAmeas hanti ⟨0, measure_ne_top P _⟩)
  have hsmall := ENNReal.tendsto_nhds_zero.1 hlim e he
  have hpos := hRlim.eventually (eventually_gt_nhds hr)
  obtain ⟨n, hn, hnpos⟩ := (hsmall.and hpos).exists
  have hnlt : R n < r := by
    dsimp [R]
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  refine ⟨R n, hnpos, hnlt, ?_⟩
  calc
    P {ω | ∃ x ∈ closedBall z r \ closedBall z (R n), t < |F ω x|} ≤ P (A n) := by
      apply measure_mono_ae
      filter_upwards [hcont] with ω hω
      rintro ⟨x, hx, hfx⟩
      have hc : Continuous (fun x : K => F ω x) :=
        continuousOn_iff_continuous_domRestrict.mp hω.1
      let U : Set K := {x | R n < dist x.1 z ∧ t < |F ω x|}
      have hU : IsOpen U :=
        (isOpen_lt continuous_const (continuous_subtype_val.dist continuous_const)).inter
          (isOpen_lt continuous_const hc.abs)
      have hxU : (⟨x, hx.1⟩ : K) ∈ U := by
        exact ⟨lt_of_not_ge hx.2, hfx⟩
      obtain ⟨y, hyD, hyU⟩ := hDd.exists_mem_open hU ⟨_, hxU⟩
      exact ⟨⟨y, hyD⟩, hyU.1, hyU.2⟩
    _ ≤ e := hn

/-- The continuum part of the boundary estimate in Lemma 3.7, conditional
on the continuity part of the potential-identification step. -/
theorem normalizedExitGreenPotential_boundary_small
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hpot : NormalizedExitPotentialStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        t < |normalizedExitGreenPotential S r z ω x|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply boundary_layer_small_in_probability S.P hr (normalizedExitGreenPotential S r z) _ _ ht he
  · intro x hx
    by_cases hxi : x ∈ ball z r
    · exact normalizedExitGreenPotential_aemeasurable 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hxi
    · have hz : (fun ω => normalizedExitGreenPotential S r z ω x) = fun _ => 0 := by
        funext ω
        exact normalizedExitGreenPotential_eq_zero_of_not_mem S hxi ω
      rw [hz]
      exact aemeasurable_const
  · filter_upwards [hpot γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball] with ω hω
    exact ⟨hω.1, hω.2.2⟩

end MatedCRT
