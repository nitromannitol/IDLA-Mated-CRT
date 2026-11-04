import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BrownianExitTail
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Median

/-! Annealed exit-time bounds from the clock and Brownian exit probabilities. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

/-- A bound on the early annealed exit distribution in terms of the clock and the
Brownian exit probability. -/
theorem MatedCRTEnv.IsValid.annealedExitCDF_le_clock_add_brownian
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (r q : ℝ≥0) :
    (∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ∂S.P) ≤
    (∫⁻ ω, planarBrownianMotion 0 {b | S.clock ω b r ≤ (q : ℝ)} ∂S.P) +
      planarBrownianMotion 0 {b | ∃ s ≤ r, b s ∉ ball 0 (1 / 2)} := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let A := {b : ContinuousPath ℂ | ∃ s ≤ r, b s ∉ ball 0 (1 / 2)}
  let F : Ω → ℝ≥0∞ := fun ω => planarBrownianMotion 0 {b | S.clock ω b r ≤ (q : ℝ)}
  have hbound : ∀ᵐ ω ∂S.P, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ≤
        F ω + planarBrownianMotion 0 A := by
    filter_upwards [hS.isLQGClock] with ω hclock
    have hbad : planarBrownianMotion 0 {b | ¬ IsTimeChangeClock (S.clock ω b)} = 0 :=
      ae_iff.mp (hclock 0).2
    calc
      _ ≤ planarBrownianMotion 0
          ({b | ¬ IsTimeChangeClock (S.clock ω b)} ∪
           {b | Real.toNNReal (S.clock ω b r) ≤ q} ∪ A) :=
        measure_mono (lbmExitTime_event_subset r q)
      _ ≤ (planarBrownianMotion 0 {b | ¬ IsTimeChangeClock (S.clock ω b)} +
          planarBrownianMotion 0 {b | Real.toNNReal (S.clock ω b r) ≤ q}) +
          planarBrownianMotion 0 A := by
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = F ω + planarBrownianMotion 0 A := by
        simp only [hbad, zero_add, F, Real.toNNReal_le_iff_le_coe]
  calc
    _ ≤ ∫⁻ ω, (F ω + planarBrownianMotion 0 A) ∂S.P := lintegral_mono_ae hbound
    _ = (∫⁻ ω, F ω ∂S.P) + planarBrownianMotion 0 A := by
      rw [lintegral_add_right _ measurable_const]
      simp

/-- The annealed exit distribution is below one half at a positive time. -/
theorem MatedCRTEnv.IsValid.exists_small_annealedExitCDF
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ δ : ℝ, 0 < δ ∧ (∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal δ} ∂S.P) < 1 / 2 := by
  have hearly : ∀ᶠ n : ℕ in atTop, planarBrownianMotion 0
      {b | ∃ s : ℝ≥0, s ≤ ⟨1 / ((n : ℝ) + 1), by positivity⟩ ∧
        b s ∉ ball 0 (1 / 2)} < (1 / 8 : ℝ≥0∞) :=
    (tendsto_order.1 planarBrownianMotion_early_exit_tendsto_zero).2 (1 / 8 : ℝ≥0∞) (ENNReal.div_pos (by simp) (by simp))
  obtain ⟨n, hn⟩ := hearly.exists
  let r : ℝ≥0 := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hr : 0 < r := by change 0 < 1 / ((n : ℝ) + 1); positivity
  have hclock : ∀ᶠ m : ℕ in atTop, (∫⁻ ω, planarBrownianMotion 0
      {b | S.clock ω b r ≤ 1 / ((m : ℝ) + 1)} ∂S.P) < (1 / 8 : ℝ≥0∞) :=
    (tendsto_order.1 (hS.annealed_clock_lower_tail_tendsto_zero hr)).2 (1 / 8 : ℝ≥0∞) (ENNReal.div_pos (by simp) (by simp))
  obtain ⟨m, hm⟩ := hclock.exists
  let q : ℝ≥0 := ⟨1 / ((m : ℝ) + 1), by positivity⟩
  have hq : (0 : ℝ) < q := by change 0 < 1 / ((m : ℝ) + 1); positivity
  refine ⟨q, hq, ?_⟩
  have hbound := hS.annealedExitCDF_le_clock_add_brownian r q
  have hsum : (∫⁻ ω, planarBrownianMotion 0 {b | S.clock ω b r ≤ (q : ℝ)} ∂S.P) +
      planarBrownianMotion 0 {b | ∃ s ≤ r, b s ∉ ball 0 (1 / 2)} < (1 / 2 : ℝ≥0∞) := by
    calc
      _ ≤ (1 / 8 : ℝ≥0∞) + 1 / 8 := add_le_add hm.le hn.le
      _ < 1 / 2 := by
        have hnum : ((1 / 8 + 1 / 8 : ℝ≥0) : ℝ≥0∞) < ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast (show (1 / 8 : ℝ≥0) + 1 / 8 < 1 / 2 by norm_num)
        simpa using hnum
  simpa using hbound.trans_lt hsum

/-- A measurable envelope for the upper clock tail bounds the complement of the
annealed exit distribution. -/
theorem MatedCRTEnv.IsValid.one_le_annealedExitCDF_add_clock_add_brownian
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (r q : ℝ≥0) (E : Ω → ℝ≥0∞)
    (hE : Measurable E) (hbound : ∀ᵐ ω ∂S.P,
      planarBrownianMotion 0 {b | (q : ℝ) ≤ S.clock ω b r} ≤ E ω) :
    1 ≤ (∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ∂S.P) +
      (∫⁻ ω, E ω ∂S.P) +
      planarBrownianMotion 0 {b | ∀ s ≤ r, b s ∈ ball 0 (1 / 2)} := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let A := {b : ContinuousPath ℂ | ∀ s ≤ r, b s ∈ ball 0 (1 / 2)}
  let F : Ω → ℝ≥0∞ := fun ω => planarBrownianMotion 0
    {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)}
  have hpoint : ∀ᵐ ω ∂S.P, 1 ≤ (F ω + E ω) + planarBrownianMotion 0 A := by
    filter_upwards [hS.isLQGClock, hbound] with ω hclock hEω
    have hbad : planarBrownianMotion 0 {b | ¬ IsTimeChangeClock (S.clock ω b)} = 0 :=
      ae_iff.mp (hclock 0).2
    have hlate : planarBrownianMotion 0
        {b | (q : ℝ≥0∞) < lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b} ≤
        E ω + planarBrownianMotion 0 A := by
      calc
        _ ≤ planarBrownianMotion 0
            ({b | ¬ IsTimeChangeClock (S.clock ω b)} ∪
             {b | q < Real.toNNReal (S.clock ω b r)} ∪ A) :=
          measure_mono (lbmExitTime_late_event_subset r q)
        _ ≤ (planarBrownianMotion 0 {b | ¬ IsTimeChangeClock (S.clock ω b)} +
            planarBrownianMotion 0 {b | q < Real.toNNReal (S.clock ω b r)}) +
            planarBrownianMotion 0 A := by
          exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
        _ ≤ E ω + planarBrownianMotion 0 A := by
          simp only [hbad, zero_add]
          refine add_le_add ?_ le_rfl
          calc
            _ ≤ planarBrownianMotion 0 {b | (q : ℝ) ≤ S.clock ω b r} := by
              apply measure_mono
              intro b hb
              exact (Real.lt_toNNReal_iff_coe_lt.mp hb).le
            _ ≤ E ω := hEω
    have hpart : 1 ≤ F ω + planarBrownianMotion 0
        {b | (q : ℝ≥0∞) < lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b} := by
      calc
        1 = planarBrownianMotion 0 univ := by simp
        _ ≤ planarBrownianMotion 0
            ({b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ∪
             {b | (q : ℝ≥0∞) < lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b}) := by
          apply measure_mono
          intro b hb
          exact le_total (lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b) (q : ℝ≥0∞) |>.elim
            (fun h => Or.inl h) (fun h => by
              by_cases he : lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b = (q : ℝ≥0∞)
              · exact Or.inl he.le
              · exact Or.inr (lt_of_le_of_ne h (Ne.symm he)))
        _ ≤ _ := measure_union_le _ _
    exact hpart.trans (by simpa [add_assoc] using add_le_add le_rfl hlate)
  have hint : (∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂S.P) ≤
      ∫⁻ ω, (F ω + E ω) + planarBrownianMotion 0 A ∂S.P := lintegral_mono_ae hpoint
  rw [lintegral_add_right _ measurable_const, lintegral_add_right _ hE] at hint
  simpa [F, A] using hint

/-- The annealed exit distribution reaches one half at a finite time. -/
theorem MatedCRTEnv.IsValid.exists_large_annealedExitCDF
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ M : ℝ, 0 ≤ M ∧ (1 / 2 : ℝ≥0∞) ≤ ∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal M} ∂S.P := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hlate : ∀ᶠ n : ℕ in atTop, planarBrownianMotion 0
      {b | ∀ s : ℝ≥0, s ≤ (n : ℝ≥0) → b s ∈ ball 0 (1 / 2)} < (1 / 8 : ℝ≥0∞) :=
    (tendsto_order.1 planarBrownianMotion_late_exit_tendsto_zero).2
      (1 / 8 : ℝ≥0∞) (ENNReal.div_pos (by simp) (by simp))
  obtain ⟨k, hk, hkpos⟩ := (hlate.and (eventually_ge_atTop 1)).exists
  let r : ℝ≥0 := k
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkpos)
  obtain ⟨E, hEmeas, hEsand⟩ := hS.exists_measurable_upper_clock_tail_envelopes r
  have hElim : ∀ᵐ ω ∂S.P, Tendsto (fun n => E n ω) atTop (𝓝 0) := by
    filter_upwards [hEsand, hS.ae_clock_tail_limits] with ω hE ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (ht r hr).2
      (Eventually.of_forall fun _ => bot_le) ?_
    apply Eventually.of_forall
    intro n
    calc
      E n ω ≤ planarBrownianMotion 0 {b | (n : ℝ) + 1 ≤ S.clock ω b r} := (hE n).2
      _ ≤ planarBrownianMotion 0 {b | (n : ℝ) ≤ S.clock ω b r} := by
        apply measure_mono
        intro b hb
        change (n : ℝ) + 1 ≤ S.clock ω b r at hb
        change (n : ℝ) ≤ S.clock ω b r
        linarith
  have hEbound : ∀ n, E n ≤ᵐ[S.P] fun _ => (1 : ℝ≥0∞) := by
    intro n
    filter_upwards [hEsand] with ω hE
    calc
      E n ω ≤ planarBrownianMotion 0 {b | (n : ℝ) + 1 ≤ S.clock ω b r} := (hE n).2
      _ ≤ planarBrownianMotion 0 univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hEint := tendsto_lintegral_of_dominated_convergence (fun _ => 1) hEmeas hEbound
    (by simp) hElim
  have hEint' : Tendsto (fun n => ∫⁻ ω, E n ω ∂S.P) atTop (𝓝 0) := by
    simpa using hEint
  have hsmall : ∀ᶠ n : ℕ in atTop, (∫⁻ ω, E n ω ∂S.P) < (1 / 8 : ℝ≥0∞) :=
    (tendsto_order.1 hEint').2 _ (ENNReal.div_pos (by simp) (by simp))
  obtain ⟨n, hn⟩ := hsmall.exists
  let q : ℝ≥0 := ⟨3 * ((n : ℝ) + 1), by positivity⟩
  have hq : (0 : ℝ) ≤ q := q.property
  refine ⟨q, hq, ?_⟩
  have henv : ∀ᵐ ω ∂S.P, planarBrownianMotion 0
      {b | (q : ℝ) ≤ S.clock ω b r} ≤ E n ω := by
    filter_upwards [hEsand] with ω hE
    exact (hE n).1
  have hbound := hS.one_le_annealedExitCDF_add_clock_add_brownian r q (E n) (hEmeas n) henv
  have hnum : (1 / 2 : ℝ≥0∞) + 1 / 8 + 1 / 8 < 1 := by
    have hnum' : ((1 / 2 + 1 / 8 + 1 / 8 : ℝ≥0) : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast (show (1 / 2 : ℝ≥0) + 1 / 8 + 1 / 8 < 1 by norm_num)
    simpa using hnum'
  have hresult : (1 / 2 : ℝ≥0∞) ≤ ∫⁻ ω, planarBrownianMotion 0
      {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ (q : ℝ≥0∞)} ∂S.P := by
    by_contra hc
    have hc' := le_of_not_ge hc
    have hcontra : (1 : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0∞) + 1 / 8 + 1 / 8 :=
      hbound.trans (add_le_add (add_le_add hc' hn.le) hk.le)
    exact (not_le_of_gt hnum) hcontra
  simpa using hresult

/-- The normalizing constant is strictly positive in every valid environment. -/
theorem matedCRTScalingConstantPositive (𝒮 : SpaceFillingSLEModel) :
    MatedCRTScalingConstantPositiveStep 𝒮 := by
  intro γ _ _ Ω _ S hS
  obtain ⟨δ, hδ, hsmall⟩ := hS.exists_small_annealedExitCDF
  obtain ⟨M, hM, hlarge⟩ := hS.exists_large_annealedExitCDF
  exact scalingConstantPositive_of_two_exit_bounds S hδ hM hsmall hlarge

end MatedCRT
