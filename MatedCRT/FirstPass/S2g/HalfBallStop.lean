import Mathlib

/-!
# The half-ball time from a continuous radius (fp-S2g, q1)

Deterministic part of CHATGPT-q1-open-steps.md Section 3, steps H4-H5 (the stopping predicate of the canonical half-ball
time). For a family of sets `Λ_t`, let `R(t)` be the radius of the closure of `Λ_t`, the supremum of `|z|` over
`closure Λ_t`. The half-ball time is the supremum `T` of the times `t > 0` with `R(t) ≤ a` (here `a = 1/2`). If `R` is
continuous on `(0, ∞)`, then `R(T) = a`, and for every `r < a` some `t ∈ (0, T)` has `r < R(t)`.
The continuity of `R` (Hausdorff continuity of the clusters) is an explicit hypothesis of the consumers, not proved here.
-/

namespace MatedCRT

open Set Filter Topology

/-- The level-set supremum of a continuous radius (CHATGPT-q1-open-steps.md H4-H5). With `S = {t > 0 | R t ≤ a}` nonempty
and bounded above, `T = sSup S` is positive, `R T = a`, and for every `r < a` some `t ∈ (0, T)` satisfies `r < R t`. -/
theorem sup_level_radius_eq {R : ℝ → ℝ} {a : ℝ}
    (hR : ∃ U : ℝ, sSup {t : ℝ | 0 < t ∧ R t ≤ a} < U ∧ ContinuousOn R (Ioo 0 U))
    (hne : ∃ s : ℝ, 0 < s ∧ R s ≤ a) (hbdd : BddAbove {t : ℝ | 0 < t ∧ R t ≤ a}) :
    0 < sSup {t : ℝ | 0 < t ∧ R t ≤ a} ∧ R (sSup {t : ℝ | 0 < t ∧ R t ≤ a}) = a ∧
      ∀ r < a, ∃ t ∈ Ioo 0 (sSup {t : ℝ | 0 < t ∧ R t ≤ a}), r < R t := by
  set S : Set ℝ := {t : ℝ | 0 < t ∧ R t ≤ a} with hS
  set T : ℝ := sSup S with hT
  obtain ⟨s0, hs0, hRs0⟩ := hne
  have hSne : S.Nonempty := ⟨s0, hs0, hRs0⟩
  have hTS : ∀ t ∈ S, t ≤ T := fun t ht => le_csSup hbdd ht
  have hTpos : 0 < T := lt_of_lt_of_le hs0 (hTS s0 ⟨hs0, hRs0⟩)
  obtain ⟨U, hTU, hRU⟩ := hR
  have hcont : ContinuousAt R T := hRU.continuousAt (Ioo_mem_nhds hTpos hTU)
  -- `R T ≤ a`: otherwise `R > a` near `T`, but `S` has points arbitrarily close to `T` from below.
  have hle : R T ≤ a := by
    by_contra h
    have h' : a < R T := not_le.mp h
    have hev : ∀ᶠ t in 𝓝 T, a < R t := Filter.Tendsto.eventually hcont (lt_mem_nhds h')
    obtain ⟨ε, _, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨s, hsS, hsT⟩ := exists_lt_of_lt_csSup hSne (show T - ε < T by linarith)
    have hdist : dist s T < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith
      · linarith [hTS s hsS]
    exact (not_le.mpr (hball hdist)) hsS.2
  -- `a ≤ R T`: otherwise `R < a` near `T`, and `T + ε/2` would lie in `S`, contradicting the supremum.
  have hge : a ≤ R T := by
    by_contra h
    have h' : R T < a := not_le.mp h
    have hev : ∀ᶠ t in 𝓝 T, R t < a := Filter.Tendsto.eventually hcont (gt_mem_nhds h')
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hdist : dist (T + ε / 2) T < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hmem : T + ε / 2 ∈ S := ⟨by linarith, (hball hdist).le⟩
    linarith [hTS _ hmem]
  have hRT : R T = a := le_antisymm hle hge
  refine ⟨hTpos, hRT, fun r hr => ?_⟩
  -- Left continuity at `T` gives times `t < T` with `R t > r`.
  have hev : ∀ᶠ t in 𝓝 T, r < R t := Filter.Tendsto.eventually hcont (lt_mem_nhds (show r < R T by rw [hRT]; exact hr))
  have hev' : ∀ᶠ t in 𝓝[<] T, r < R t := eventually_nhdsWithin_of_eventually_nhds hev
  obtain ⟨t, ht1, ht2⟩ := (hev'.and (Ioo_mem_nhdsLT hTpos)).exists
  exact ⟨t, ht2, ht1⟩

end MatedCRT
