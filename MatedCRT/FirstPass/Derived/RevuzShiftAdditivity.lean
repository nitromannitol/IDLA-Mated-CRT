import MatedCRT.FirstPass.Derived.RevuzFormula

/-!
# Additivity of a clock at a fixed time, for all later times at once

A positive continuous additive functional `A` of the canonical planar path is additive at a fixed time `t`,
`A (t + s) = A t + A s ∘ θ_t`, only almost surely for each `s` separately (Revuz–Yor (1999), X.1.1, raw form).
Along a path where `A` is continuous and nondecreasing, additivity at all rational `s` determines the clock of
the shifted path at rational times, hence its rational-time regularization at every time. This gives, almost
surely, for all `s` simultaneously,

`A (t + s) ω = A t ω + Ã s (θ_t ω)`,

where `Ã = regularize A` (`ae_add_regularize_pathShift`), and the corresponding shift identity for the right
inverse of a good clock, `τ_{A_t + r} = t + τ̃_r ∘ θ_t` (`ae_clockInverse_add_eq_pathShift`).

The regularization on the shifted side is essential: the raw clock `A` need not be regular along the shifted
path on a measurable event, since its regularity is only an almost sure property of each starting law.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **Additivity at all times from additivity at rational times.** If `A` is continuous and nondecreasing along
`ω` and `A (t + q) ω = A t ω + A q ω'` for every rational `q ≥ 0`, then `A (t + s) ω = A t ω + Ã s ω'` for every
`s`, where `Ã` is the rational-time regularization of `A`. -/
theorem add_regularize_of_forall_nnrat {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω ω' : ContinuousPath ℂ}
    {t : ℝ≥0} (hc : Continuous fun u => A u ω) (hm : Monotone fun u => A u ω)
    (hq : ∀ q : ℚ≥0, A (t + (q : ℝ≥0)) ω = A t ω + A (q : ℝ≥0) ω') (s : ℝ≥0) :
    A (t + s) ω = A t ω + regularize A s ω' := by
  have hne := nonempty_regularize_index s
  have hcond : ∀ p q : ℚ≥0, p ≤ q → A p ω' ≤ A q ω' := fun p q hpq => by
    have h := hm (show t + (p : ℝ≥0) ≤ t + (q : ℝ≥0) by gcongr)
    simp only [hq] at h
    exact le_of_add_le_add_left h
  unfold regularize
  split_ifs
  refine le_antisymm ?_ ?_
  · rw [← tsub_le_iff_left]
    refine le_ciInf fun q => ?_
    rw [tsub_le_iff_left, ← hq]
    exact hm (show t + s ≤ t + (q.1 : ℝ≥0) by gcongr; exact q.2.le)
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc' => ?_
    have hU : {u | A u ω < c} ∈ 𝓝 (t + s) := hc.continuousAt.eventually (gt_mem_nhds hc')
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (nhdsWithin_le_nhds hU)
    have hsu : s < u - t := lt_tsub_iff_left.2 hu
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal hsu
    have hmem : t + (q : ℝ≥0) ∈ Ioo (t + s) u :=
      ⟨by gcongr, lt_tsub_iff_left.1 hq2⟩
    calc A t ω + ⨅ q' : {q : ℚ≥0 // s < (q : ℝ≥0)}, A (q'.1 : ℝ≥0) ω'
        ≤ A t ω + A (q : ℝ≥0) ω' := by
          gcongr
          exact ciInf_le (OrderBot.bddBelow _) (⟨q, hq1⟩ : {q : ℚ≥0 // s < (q : ℝ≥0)})
      _ = A (t + (q : ℝ≥0)) ω := (hq q).symm
      _ ≤ c := (hsub hmem).le

/-- **Additivity of a positive continuous additive functional at a fixed time, for all later times at once.**
For every starting point `z` and time `t`, almost surely, `A (t + s) ω = A t ω + Ã s (θ_t ω)` for every `s`,
where `Ã` is the rational-time regularization of `A` and `θ_t` the time shift. -/
theorem ae_add_regularize_pathShift {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (z : ℂ) (t : ℝ≥0) :
    ∀ᵐ ω ∂W z, ∀ s, A (t + s) ω = A t ω + regularize A s (LatticeProb.pathShift ω t) := by
  have hrat : ∀ᵐ ω ∂W z, ∀ q : ℚ≥0,
      A (t + (q : ℝ≥0)) ω = A t ω + A (q : ℝ≥0) (LatticeProb.pathShift ω t) :=
    ae_all_iff.2 fun q => hA.add z q t
  filter_upwards [hA.path z, hrat] with ω hp hq s
  exact add_regularize_of_forall_nnrat hp.2.1 hp.2.2 hq s

/-- **Additivity of the regularized clock at a fixed time.** For every starting point `z` and time `t`, almost
surely, `Ã (t + s) ω = Ã t ω + Ã s (θ_t ω)` for every `s`. -/
theorem ae_regularize_add_pathShift {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (z : ℂ) (t : ℝ≥0) :
    ∀ᵐ ω ∂W z, ∀ s,
      regularize A (t + s) ω = regularize A t ω + regularize A s (LatticeProb.pathShift ω t) := by
  filter_upwards [hA.path z, ae_add_regularize_pathShift hA z t] with ω hp hadd s
  rw [regularize_eq_of_continuous_monotone hp.2.1 hp.2.2,
    regularize_eq_of_continuous_monotone hp.2.1 hp.2.2, hadd s]

/-- **Shift of the right inverse of a clock.** If `A` is nondecreasing along `ω`, `A (t + s) ω = A t ω + B s ω'`
for every `s`, and `A` exceeds `A t ω + r` along `ω`, then the right inverse of `A` at level `A t ω + r` is `t`
plus the right inverse of `B` at level `r` along `ω'`. -/
theorem clockInverse_add_eq_of_shift {A B : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω ω' : ContinuousPath ℂ}
    {t r : ℝ≥0} (hm : Monotone fun u => A u ω) (hshift : ∀ s, A (t + s) ω = A t ω + B s ω')
    (hne : ∃ u, A t ω + r < A u ω) :
    clockInverse A (A t ω + r) ω = t + clockInverse B r ω' := by
  unfold clockInverse
  have hS : {s | r < B s ω'} = {s | A t ω + r < A (t + s) ω} := by
    ext s
    simp only [Set.mem_ofPred_eq, hshift s, add_lt_add_iff_left]
  have himg : (fun s => t + s) '' {s | A t ω + r < A (t + s) ω} = {u | A t ω + r < A u ω} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hu
      have htu : t ≤ u := by
        by_contra h
        exact absurd hu (not_lt.2 ((hm (not_le.1 h).le).trans le_self_add))
      refine ⟨u - t, ?_, add_tsub_cancel_of_le htu⟩
      simpa only [Set.mem_ofPred_eq, add_tsub_cancel_of_le htu] using hu
  have hSne : {s | A t ω + r < A (t + s) ω}.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    have hmem : u ∈ (fun s => t + s) '' {s | A t ω + r < A (t + s) ω} := by
      rw [himg]
      exact hu
    obtain ⟨s, hs, -⟩ := hmem
    exact ⟨s, hs⟩
  rw [hS, ← himg]
  exact (Monotone.map_csInf_of_continuousAt (f := fun s : ℝ≥0 => t + s) (by fun_prop : Continuous fun s : ℝ≥0 => t + s).continuousAt
    (fun a b (h : a ≤ b) => (add_le_add_iff_left t).2 h) hSne (OrderBot.bddBelow _)).symm

/-- **Shift of the right inverse of a good clock at a fixed time.** For a positive continuous additive functional
`A` with a good clock, every starting point `z` and time `t`, almost surely, for every level `r`,
`τ_{A_t + r} = t + τ̃_r ∘ θ_t`, where `τ` is the right inverse of `A` and `τ̃` that of its rational-time
regularization. -/
theorem ae_clockInverse_add_eq_pathShift {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (hG : GoodClock W A) (z : ℂ) (t : ℝ≥0) :
    ∀ᵐ ω ∂W z, ∀ r, clockInverse A (A t ω + r) ω =
      t + clockInverse (regularize A) r (LatticeProb.pathShift ω t) := by
  filter_upwards [hA.path z, hG z, ae_add_regularize_pathShift hA z t] with ω hp hg hadd r
  exact clockInverse_add_eq_of_shift hp.2.2 hadd ((hg.2.eventually_gt_atTop (A t ω + r)).exists)

end MatedCRT
