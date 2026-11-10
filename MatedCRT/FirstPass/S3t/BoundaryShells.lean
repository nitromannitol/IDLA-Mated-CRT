import HarmonicBalls.Defs.LBM

/-!
# Truncated quenched laws, Step 6 (pathwise part): boundary shells (fp-S3t-truncated-continuum, z10)

Source: notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md, Step 6. The disk `D = B_r(z)` is exhausted by the
concentric disks `D_n = B_{r - a/(n+1)}(z)`, which increase to `D`. The shell functional
`shellTime D_n D T w = min(T, τ_D w) - min(T, τ_{D_n} w)` is the time in `[0, T]` that the path `w` spends before
exiting `D` but after leaving `D_n`. This file proves the pathwise statements: exit times from an increasing open
exhaustion converge to the exit time from the union, for continuous paths; the shell functional is nonnegative,
at most `T`, and tends to `0`. The probabilistic limit uses Step 5.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- The concentric exhaustion `D_n = B_{r - a/(n+1)}(z)` of `B_r(z)` (Step 6, `δ_n = a/(n+1)`). -/
def ballExhaustion (z : ℂ) (r a : ℝ) (n : ℕ) : Set ℂ :=
  ball z (r - a / ((n : ℝ) + 1))

/-- The truncated shell functional (Step 6): the time in `[0, T]` that the path spends in `D` after leaving `Dn`. -/
noncomputable def shellTime (Dn D : Set ℂ) (T : ℝ) (w : ℝ≥0 → ℂ) : ℝ :=
  (min (ENNReal.ofReal T) (pathExitTime D w)).toReal -
    (min (ENNReal.ofReal T) (pathExitTime Dn w)).toReal

/-- A larger domain is exited no earlier: `U ⊆ V` gives `τ_U ≤ τ_V`. -/
theorem pathExitTime_mono_domain {U V : Set ℂ} (hUV : U ⊆ V) (w : ℝ≥0 → ℂ) :
    pathExitTime U w ≤ pathExitTime V w := by
  unfold pathExitTime
  apply sInf_le_sInf
  rintro s ⟨t, rfl, hw⟩
  exact ⟨t, rfl, fun hU => hw (hUV hU)⟩

/-- Exit times from a monotone open exhaustion of `V` converge to the exit time from `V`, for a continuous path. -/
theorem pathExitTime_tendsto_of_exhaustion {U : ℕ → Set ℂ} {V : Set ℂ} (hmono : Monotone U)
    (hopen : ∀ n, IsOpen (U n)) (hsub : ∀ n, U n ⊆ V) (hcover : V ⊆ ⋃ n, U n) {w : ℝ≥0 → ℂ}
    (hw : Continuous w) :
    Tendsto (fun n => pathExitTime (U n) w) atTop (𝓝 (pathExitTime V w)) := by
  have hmonoτ : Monotone (fun n => pathExitTime (U n) w) :=
    fun n m h => pathExitTime_mono_domain (hmono h) w
  have hge : pathExitTime V w ≤ ⨆ n, pathExitTime (U n) w := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    -- the path stays in `V` on `[0, r]`, since `pathExitTime V w > r`
    have hK : w '' Icc (0 : ℝ≥0) r ⊆ V := by
      rintro _ ⟨t, ht, rfl⟩
      by_contra hV
      have h1 : pathExitTime V w ≤ (t : ℝ≥0∞) := sInf_le ⟨t, rfl, hV⟩
      exact absurd hr (not_lt.2 (h1.trans (ENNReal.coe_le_coe.2 ht.2)))
    -- compactness: the compact image lies in some `U N`
    obtain ⟨N, hN⟩ := (isCompact_Icc.image hw).elim_directed_cover U hopen (hK.trans hcover)
      hmono.directed_le
    have hτN : (r : ℝ≥0∞) ≤ pathExitTime (U N) w := by
      unfold pathExitTime
      refine le_sInf ?_
      rintro s ⟨t, rfl, hwt⟩
      rcases le_or_gt r t with h | h
      · exact ENNReal.coe_le_coe.2 h
      · exact absurd (hN ⟨t, ⟨zero_le, h.le⟩, rfl⟩) hwt
    exact hτN.trans (le_iSup (fun n => pathExitTime (U n) w) N)
  have hsup : (⨆ n, pathExitTime (U n) w) = pathExitTime V w :=
    le_antisymm (iSup_le fun n => pathExitTime_mono_domain (hsub n) w) hge
  rw [← hsup]
  exact tendsto_atTop_iSup hmonoτ

/-- Truncation at a finite level `c` is continuous along a convergent sequence of exit times. -/
theorem truncExit_tendsto {c : ℝ≥0∞} (hc : c ≠ ⊤) {τ : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (h : Tendsto τ atTop (𝓝 L)) :
    Tendsto (fun n => (min c (τ n)).toReal) atTop (𝓝 (min c L).toReal) := by
  have h1 : Tendsto (fun n => min c (τ n)) atTop (𝓝 (min c L)) := tendsto_const_nhds.min h
  exact (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hc (min_le_left _ _))).comp h1

/-- **Step 6, pathwise.** For a continuous path, the shell functional of a monotone open exhaustion of `V` tends to
`0`. -/
theorem shellTime_tendsto_zero {U : ℕ → Set ℂ} {V : Set ℂ} (hmono : Monotone U) (hopen : ∀ n, IsOpen (U n))
    (hsub : ∀ n, U n ⊆ V) (hcover : V ⊆ ⋃ n, U n) {T : ℝ} {w : ℝ≥0 → ℂ} (hw : Continuous w) :
    Tendsto (fun n => shellTime (U n) V T w) atTop (𝓝 0) := by
  have h := truncExit_tendsto (c := ENNReal.ofReal T) ENNReal.ofReal_ne_top
    (pathExitTime_tendsto_of_exhaustion hmono hopen hsub hcover hw)
  have h2 := (tendsto_const_nhds (x := (min (ENNReal.ofReal T) (pathExitTime V w)).toReal)).sub h
  rw [sub_self] at h2
  exact h2

/-- The shell functional is nonnegative for nested domains. -/
theorem shellTime_nonneg {Dn D : Set ℂ} (hDD : Dn ⊆ D) (T : ℝ) (w : ℝ≥0 → ℂ) :
    0 ≤ shellTime Dn D T w := by
  unfold shellTime
  rw [sub_nonneg]
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _))
    (min_le_min_left _ (pathExitTime_mono_domain hDD w))

/-- The shell functional is at most `T` (for `T ≥ 0`). -/
theorem shellTime_le {Dn D : Set ℂ} {T : ℝ} (hT : 0 ≤ T) (w : ℝ≥0 → ℂ) : shellTime Dn D T w ≤ T := by
  unfold shellTime
  have h1 : (min (ENNReal.ofReal T) (pathExitTime D w)).toReal ≤ T := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left (ENNReal.ofReal T) (pathExitTime D w))
    rwa [ENNReal.toReal_ofReal hT] at this
  have h2 : 0 ≤ (min (ENNReal.ofReal T) (pathExitTime Dn w)).toReal := ENNReal.toReal_nonneg
  linarith

/-- The concentric disks `ballExhaustion z r a n` increase in `n` (for `a ≥ 0`). -/
theorem ballExhaustion_monotone (z : ℂ) (r : ℝ) {a : ℝ} (ha : 0 ≤ a) : Monotone (ballExhaustion z r a) := by
  intro n m hnm
  unfold ballExhaustion
  apply ball_subset_ball
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have : a / ((m : ℝ) + 1) ≤ a / ((n : ℝ) + 1) := by gcongr
  linarith

/-- The concentric disks `ballExhaustion z r a n` lie in `B_r(z)` (for `a ≥ 0`). -/
theorem ballExhaustion_subset (z : ℂ) (r : ℝ) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ballExhaustion z r a n ⊆ ball z r := by
  unfold ballExhaustion
  apply ball_subset_ball
  have : 0 ≤ a / ((n : ℝ) + 1) := by positivity
  linarith

/-- The concentric disks `ballExhaustion z r a n` exhaust `B_r(z)` (for every `a`). -/
theorem ball_subset_iUnion_ballExhaustion (z : ℂ) (r a : ℝ) :
    ball z r ⊆ ⋃ n, ballExhaustion z r a n := by
  intro x hx
  rw [mem_ball] at hx
  have hpos : 0 < r - dist x z := sub_pos.2 hx
  obtain ⟨n, hn⟩ := exists_nat_gt (a / (r - dist x z))
  rw [div_lt_iff₀ hpos] at hn
  simp only [mem_iUnion]
  refine ⟨n, ?_⟩
  unfold ballExhaustion
  rw [mem_ball]
  have h1 : a / ((n : ℝ) + 1) < r - dist x z := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- A point at distance `< r - a` from the centre lies in every disk of the exhaustion (for `a ≥ 0`). -/
theorem mem_ballExhaustion_of_dist_lt (z y : ℂ) (r : ℝ) {a : ℝ} (ha : 0 ≤ a) (hy : dist y z < r - a) (n : ℕ) :
    y ∈ ballExhaustion z r a n := by
  unfold ballExhaustion
  rw [mem_ball]
  have : a / ((n : ℝ) + 1) ≤ a := div_le_self ha (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  linarith

end MatedCRT.TruncatedLaws
