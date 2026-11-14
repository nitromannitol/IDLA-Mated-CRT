import MatedCRT.Defs.Setting

/-!
# Uniqueness of the LQG clock

The LQG clock `F` of a path law `Q x` for a field with circle averages `h_ε` is the limit in `Q x`-probability,
uniformly on compact time intervals, of the approximating clocks `A_k(t) = ∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds` along
`ε = 2^{-k}` (`IsLQGClock`, line 517 of the paper; Garban-Rhodes-Vargas 2016, Theorem 2.7 (2)). Two such limits
`F, G` agree `Q x`-almost surely at all times: for `T ≥ 0` and `η > 0`,
`Q x {∃ t ≤ T, |F_t - G_t| ≥ η} ≤ Q x {∃ t ≤ T, |A_k(t) - F_t| ≥ η/2} + Q x {∃ t ≤ T, |A_k(t) - G_t| ≥ η/2}`,
which tends to `0` as `k → ∞`, and the exceptional sets for integer horizons `T` and levels `η = 1/(n+1)` form a
countable family. No measurability of the clocks is used: the estimate only needs monotonicity and subadditivity
of the (outer) measure.

* `isLQGClock_ae_eq`: two LQG clocks of the same path law and field agree almost surely at all times.
* `MatedCRTEnv.IsValid.ae_clock_eq_of_isLQGClock`: in a valid environment, almost surely in the environment and
  for every starting point `z`, an LQG clock of planar Brownian motion for the field agrees with the clock of the
  environment almost surely in the Brownian path, at all times.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- If `|F - G| ≥ η` at some time `t ≤ T`, then at that time the clock `A` is at distance at least `η/2` from `F`
or from `G`. -/
theorem setOf_exists_le_abs_sub_subset {α : Type*} (A F G : α → ℝ≥0 → ℝ) (T : ℝ≥0) (η : ℝ) :
    {b | ∃ t ≤ T, η ≤ |F b t - G b t|} ⊆
      {b | ∃ t ≤ T, η / 2 ≤ |A b t - F b t|} ∪ {b | ∃ t ≤ T, η / 2 ≤ |A b t - G b t|} := by
  rintro b ⟨t, ht, hη⟩
  by_contra hb
  rw [mem_union, not_or] at hb
  have h1 : |A b t - F b t| < η / 2 := lt_of_not_ge fun h => hb.1 ⟨t, ht, h⟩
  have h2 : |A b t - G b t| < η / 2 := lt_of_not_ge fun h => hb.2 ⟨t, ht, h⟩
  have h3 := abs_sub_le (F b t) (A b t) (G b t)
  rw [abs_sub_comm (F b t) (A b t)] at h3
  linarith

/-- **Uniqueness of the LQG clock.** Two LQG clocks `F, G` of the path law `Q x` for the same field agree
`Q x`-almost surely at all times. -/
theorem isLQGClock_ae_eq {Q : Kernel ℂ (ContinuousPath ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock Q γ hε x F) (hG : IsLQGClock Q γ hε x G) :
    ∀ᵐ b ∂(Q x), ∀ t : ℝ≥0, F b t = G b t := by
  have hnull : ∀ (T : ℝ≥0) (η : ℝ), 0 < η → Q x {b | ∃ t ≤ T, η ≤ |F b t - G b t|} = 0 := by
    intro T η hη
    have hη2 : 0 < η / 2 := half_pos hη
    have hlim := (hF T (η / 2) hη2).add (hG T (η / 2) hη2)
    rw [add_zero] at hlim
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim fun k => ?_)
    exact (measure_mono (setOf_exists_le_abs_sub_subset (lqgClockApprox γ hε (dyadicScale k)) F G T η)).trans
      (measure_union_le _ _)
  have hU : Q x (⋃ N : ℕ, ⋃ n : ℕ,
      {b | ∃ t ≤ (N : ℝ≥0), 1 / ((n : ℝ) + 1) ≤ |F b t - G b t|}) = 0 :=
    measure_iUnion_null fun N => measure_iUnion_null fun n => hnull _ _ Nat.one_div_pos_of_nat
  rw [ae_iff]
  refine measure_mono_null (fun b hb => ?_) hU
  have hb' : ¬ ∀ t : ℝ≥0, F b t = G b t := hb
  obtain ⟨t, ht⟩ := not_forall.1 hb'
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 ht))
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact mem_iUnion.2 ⟨N, mem_iUnion.2 ⟨n, ⟨t, hN, hn.le⟩⟩⟩

/-- In a valid environment, almost surely in the environment and for every starting point `z`, an LQG clock `G ω`
of planar Brownian motion for the field `h` agrees with the clock of the environment almost surely in the
Brownian path, at all times. -/
theorem MatedCRTEnv.IsValid.ae_clock_eq_of_isLQGClock {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hG : ∀ᵐ ω ∂S.P, ∀ z : ℂ, IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (G ω)) :
    ∀ᵐ ω ∂S.P, ∀ z : ℂ, ∀ᵐ b ∂(planarBrownianMotion z), ∀ t, G ω b t = S.clock ω b t := by
  filter_upwards [hS.isLQGClock, hG] with ω hω hGω z
  exact isLQGClock_ae_eq (hGω z) (hω z).1

end MatedCRT
