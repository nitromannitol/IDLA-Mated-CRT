import MatedCRT.FirstPass.Derived.HarnackUnionBound

/-!
# From the single-ball bound to all balls: the grid union bound

Gwynne–Miller–Sheffield (2019), Proposition 2.9, as used in Berestycki–Gwynne (2020), Lemma 5.3, Step 3.
The single-ball estimate (a fixed ball `B_r(z) ⊆ B_{ρ'}` of radius `r ≥ ε^{β₀}` has cell size sum
`∑ deg(k) (diam H_k)² ≤ A r²` except on an event of probability at most `C ε^{α₀}`) is upgraded to
polynomially high probability for all balls `B_r(z) ⊆ B_ρ` with `r ≥ ε^β` simultaneously, `β = min β₀ (α₀ / 6)`.

* `MatedCRT.exists_gridBall_cover`: every ball of radius `r ∈ [ε^β, (1 - ρ) / 20]` inside `B_ρ` lies in a grid ball
  `B_{(√2)^a}(h (m + n i))` of radius at most `3 r` inside `B_{(1+ρ)/2}` (grid of `HarnackGridCount`).
* `MatedCRT.hball_of_pointwise`: the union bound over the `125 ε^{-5β}` grid balls plus one ball `B_ρ` for the
  radii above `(1 - ρ) / 20`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace MatedCRT

/-- **Grid cover of a ball.**  For `ε^β ≤ r ≤ (1 - ρ) / 20` and `B_r(z) ⊆ B_ρ`, the lattice point `h (m + n i)`
nearest to `z` (`h = ε^{2β}`) and a radius `(√2)^a ∈ [2 r, 3 r)` give a grid ball containing `B_r(z)` and
contained in `B_{(1+ρ)/2}`, with index in `gridIndexBox`. -/
theorem exists_gridBall_cover {ε β β₀ ρ : ℝ} {z : ℂ} {r : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β)
    (hββ₀ : β ≤ β₀) (hεr : ε ^ β ≤ r) (hsub : ball z r ⊆ ball 0 ρ) (hr : r ≤ (1 - ρ) / 20) :
    ∃ i ∈ gridIndexBox (ε ^ (2 * β)) (ε ^ β),
      ‖latticePt (ε ^ (2 * β)) i.1 i.2.1‖ + sqrt2Pow i.2.2 ≤ (1 + ρ) / 2 ∧ ε ^ β₀ ≤ sqrt2Pow i.2.2 ∧
        ball z r ⊆ ball (latticePt (ε ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2) ∧ sqrt2Pow i.2.2 ≤ 3 * r := by
  have hs₀ : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 β
  have hr0 : 0 < r := hs₀.trans_le hεr
  have hh : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
  have hhs : ε ^ (2 * β) ≤ ε ^ β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have hβ₀ : ε ^ β₀ ≤ ε ^ β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hββ₀
  have hzρ : ‖z‖ < ρ := by
    have := hsub (Metric.mem_ball_self hr0)
    simpa using this
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  set h : ℝ := ε ^ (2 * β) with hh_def
  have hre : |z.re - h * (round (z.re / h) : ℤ)| ≤ h / 2 := by
    have h1 := abs_sub_round (z.re / h)
    have e : z.re - h * (round (z.re / h) : ℤ) = h * (z.re / h - round (z.re / h)) := by field_simp
    rw [e, abs_mul, abs_of_pos hh]
    nlinarith
  have him : |z.im - h * (round (z.im / h) : ℤ)| ≤ h / 2 := by
    have h1 := abs_sub_round (z.im / h)
    have e : z.im - h * (round (z.im / h) : ℤ) = h * (z.im / h - round (z.im / h)) := by field_simp
    rw [e, abs_mul, abs_of_pos hh]
    nlinarith
  set m : ℤ := round (z.re / h) with hm
  set n : ℤ := round (z.im / h) with hn
  have hdist : ‖z - latticePt h m n‖ ≤ h := by
    have e1 : (z - latticePt h m n).re = z.re - h * m := by simp [latticePt]
    have e2 : (z - latticePt h m n).im = z.im - h * n := by simp [latticePt]
    have := Complex.norm_le_abs_re_add_abs_im (z - latticePt h m n)
    rw [e1, e2] at this
    linarith
  have hlp : ‖latticePt h m n‖ < ρ + r := by
    have : ‖latticePt h m n‖ ≤ ‖z‖ + ‖z - latticePt h m n‖ := by
      calc ‖latticePt h m n‖ = ‖z - (z - latticePt h m n)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖z‖ + ‖z - latticePt h m n‖ := norm_sub_le _ _
    linarith
  obtain ⟨n₀, hn₀⟩ := exists_mem_Ioc_zpow (x := 2 * r) (y := Real.sqrt 2) (by positivity) one_lt_sqrt_two
  have hsq : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsq0 : 0 < Real.sqrt 2 := by positivity
  have hR : sqrt2Pow (n₀ + 1) = Real.sqrt 2 ^ n₀ * Real.sqrt 2 := zpow_add_one₀ hsq0.ne' n₀
  have hR2 : 2 * r ≤ sqrt2Pow (n₀ + 1) := hn₀.2
  have hR3 : sqrt2Pow (n₀ + 1) ≤ 3 * r := by
    rw [hR]
    have := mul_lt_mul_of_pos_right hn₀.1 hsq0
    nlinarith
  have hR1 : sqrt2Pow (n₀ + 1) ≤ 1 := by linarith
  refine ⟨(m, n, n₀ + 1), mem_gridIndexBox hh hs₀ (by linarith) (by linarith) hR1, ?_, ?_, ?_, hR3⟩
  · show ‖latticePt h m n‖ + sqrt2Pow (n₀ + 1) ≤ (1 + ρ) / 2
    linarith
  · show ε ^ β₀ ≤ sqrt2Pow (n₀ + 1)
    linarith
  · show ball z r ⊆ ball (latticePt h m n) (sqrt2Pow (n₀ + 1))
    refine Metric.ball_subset_ball' ?_
    rw [dist_eq_norm]
    linarith

/-- **The grid union bound** (GMS19, Proposition 2.9, ball form).  The pointwise single-ball estimate `hsingle`
implies the estimate for all balls simultaneously with polynomially high probability: this is the `hball`
hypothesis of the inverse-square cell sum. -/
theorem hball_of_pointwise {𝒮 : SpaceFillingSLEModel}
    (hsingle : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (z : ℂ) (r : ℝ), ε ^ β₀ ≤ r → ball z r ⊆ ball 0 ρ' →
          S.P {ω | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
            ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2} ≤
              ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z r ⊆ ball 0 ρ →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2} := by
  intro γ hγ hγ2
  obtain ⟨β₀, α₀, hβ₀, hα₀, hpt⟩ := hsingle γ hγ hγ2
  set β : ℝ := min β₀ (α₀ / 6) with hβdef
  have hβ : 0 < β := lt_min hβ₀ (by linarith)
  have hββ₀ : β ≤ β₀ := min_le_left _ _
  have h5 : 5 * β < α₀ := by
    have : β ≤ α₀ / 6 := min_le_right _ _
    linarith
  refine ⟨β, hβ, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨A, hA, hAP⟩ := hpt ((1 + ρ) / 2) (by linarith) (by linarith)
  have hq : 0 < 1 - ρ := by linarith
  refine ⟨A * (9 + 400 / (1 - ρ) ^ 2), by positivity, fun Ω _ S hS => ?_⟩
  obtain ⟨C, hC⟩ := hAP Ω S hS
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCle : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (C * ε ^ α₀) ≤ ENNReal.ofReal (C' * ε ^ α₀) :=
    fun ε hε => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _))
  -- the grid balls
  have hG : PolyHighProb S.P fun ε => {ω | ∀ i ∈ gridIndexBox (ε ^ (2 * β)) (ε ^ β),
      (‖latticePt (ε ^ (2 * β)) i.1 i.2.1‖ + sqrt2Pow i.2.2 ≤ (1 + ρ) / 2 ∧ ε ^ β₀ ≤ sqrt2Pow i.2.2) →
      ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω)
          (ball (latticePt (ε ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2))) →
        ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * sqrt2Pow i.2.2 ^ 2} := by
    refine Gauss.polyHighProb_forall_mem_finset S.P (fun ε => gridIndexBox (ε ^ (2 * β)) (ε ^ β))
      (fun ε i => {ω | (‖latticePt (ε ^ (2 * β)) i.1 i.2.1‖ + sqrt2Pow i.2.2 ≤ (1 + ρ) / 2 ∧
          ε ^ β₀ ≤ sqrt2Pow i.2.2) →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω)
            (ball (latticePt (ε ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2))) →
          ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * sqrt2Pow i.2.2 ^ 2})
      (K := 125) (c := 5 * β) (C := C') (α := α₀) (by norm_num) hC'0 h5
      (fun r hr hr1 => card_gridIndexBox_rpow_le hβ hr hr1) (fun r hr hr1 i _ => ?_)
    by_cases hok : ‖latticePt (r ^ (2 * β)) i.1 i.2.1‖ + sqrt2Pow i.2.2 ≤ (1 + ρ) / 2 ∧
        r ^ β₀ ≤ sqrt2Pow i.2.2
    · refine (measure_mono ?_).trans ((hC r hr hr1 (latticePt (r ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2)
        hok.2 ?_).trans (hCle r hr))
      · intro ω hω hall
        exact hω fun _ => hall
      · refine Metric.ball_subset_ball' ?_
        rw [dist_zero_right]
        linarith [hok.1]
    · have hempty : ({ω | (‖latticePt (r ^ (2 * β)) i.1 i.2.1‖ + sqrt2Pow i.2.2 ≤ (1 + ρ) / 2 ∧
          r ^ β₀ ≤ sqrt2Pow i.2.2) →
        ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices r (S.η ω)
            (ball (latticePt (r ^ (2 * β)) i.1 i.2.1) (sqrt2Pow i.2.2))) →
          ∑ k ∈ T, (mdeg (S.mult r ω) k : ℝ) * diam (cell r (S.η ω) k) ^ 2 ≤ A * sqrt2Pow i.2.2 ^ 2} :
            Set Ω)ᶜ = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun ω hω => hω ?_
        exact fun h => absurd h hok
      rw [hempty, measure_empty]
      exact zero_le
  -- the one large ball
  have hF : PolyHighProb S.P fun ε => {ω | ∀ T : Finset ℤ,
      (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball 0 ρ)) →
        ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * ρ ^ 2} := by
    obtain ⟨r₁, hr₁, hr₁h⟩ := exists_rpow_le_of_small hβ₀ hρ
    refine ⟨α₀, hα₀, C', min r₁ 1, lt_min hr₁ one_pos, fun r hr hrr => ?_⟩
    have hr1 : r < 1 := hrr.trans_le (min_le_right _ _)
    have hrb : r ^ β₀ ≤ ρ := hr₁h r hr (hrr.trans_le (min_le_left _ _))
    refine (measure_mono ?_).trans ((hC r hr hr1 0 ρ hrb
      (Metric.ball_subset_ball (by linarith))).trans (hCle r hr))
    intro ω hω hall
    exact hω hall
  refine polyHighProb_mono_of_small (polyHighProb_inter hG hF) (r₁ := 1) one_pos ?_
  intro ε hε hε1 ω ⟨hGω, hFω⟩ z r hεr hsub T hT
  have hmono : ∀ {D D' : Set ℂ}, D ⊆ D' → ∀ k, k ∈ cellVertices ε (S.η ω) D →
      k ∈ cellVertices ε (S.η ω) D' := fun hD k ⟨x, hx1, hx2⟩ => ⟨x, hx1, hD hx2⟩
  have hs₀ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hr0 : 0 < r := hs₀.trans_le hεr
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  by_cases hrs : r ≤ (1 - ρ) / 20
  · obtain ⟨i, hi, hok1, hok2, hsub', hR⟩ :=
      exists_gridBall_cover hε hε1 hβ hββ₀ hεr hsub hrs
    have h1 := hGω i hi ⟨hok1, hok2⟩ T (fun k hk => hmono hsub' k (hT k hk))
    have h2 : sqrt2Pow i.2.2 ^ 2 ≤ 9 * r ^ 2 := by
      have : 0 ≤ sqrt2Pow i.2.2 := by unfold sqrt2Pow; positivity
      nlinarith
    calc _ ≤ A * sqrt2Pow i.2.2 ^ 2 := h1
      _ ≤ A * (9 * r ^ 2) := mul_le_mul_of_nonneg_left h2 hA.le
      _ ≤ A * (9 + 400 / (1 - ρ) ^ 2) * r ^ 2 := by
          have : 0 ≤ A * (400 / (1 - ρ) ^ 2) * r ^ 2 := by positivity
          nlinarith
  · rw [not_le] at hrs
    have h1 := hFω T (fun k hk => hmono hsub k (hT k hk))
    have h3 : 1 < 400 / (1 - ρ) ^ 2 * r ^ 2 := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      nlinarith
    have h4 : ρ ^ 2 ≤ 1 := by nlinarith
    calc _ ≤ A * ρ ^ 2 := h1
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left h4 hA.le
      _ ≤ A * (400 / (1 - ρ) ^ 2 * r ^ 2) := mul_le_mul_of_nonneg_left h3.le hA.le
      _ ≤ A * (9 + 400 / (1 - ρ) ^ 2) * r ^ 2 := by
          have : 0 ≤ A * 9 * r ^ 2 := by positivity
          nlinarith

end MatedCRT
