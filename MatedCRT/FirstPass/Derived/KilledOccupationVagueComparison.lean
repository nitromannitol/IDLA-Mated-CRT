import MatedCRT.FirstPass.Derived.KilledPotentialComparison
import MatedCRT.FirstPass.Derived.KilledOccupationDiscSplit

/-!
# Occupation functionals of two vaguely convergent families of rates

Let `f_n` and `g_k` be Borel rates such that `f_n(y) dy` and `g_k(y) dy` converge vaguely on every closed disc
`B̄(0, r)`, `r < 1`, to the same measure `ν₀`, with, on each disc `B(0, r)`, eventually a common upper power growth
`∫_{B(z, s)} f_n, ∫_{B(z, s)} g_k, ν₀(B(z, s)) ≤ s^β`, and eventually a common mass bound on the unit disc. Then for
Brownian motion from `0` killed on exiting the unit disc, the probability that the occupation functionals of `f_n` and
`g_k` differ by more than `η` at some time tends to `0` as `n, k → ∞`
(`tendsto_measure_exists_lt_abs_killedOccupationGapUpTo`).

Given `ε > 0`, choose `r < 1` with `π⁻¹ log(1/r)` small against the masses, then `δ > 0` small: eventually the killed
potentials of `f_n` and of `g_k` on `B(0, r)` are within `δ` of `2 G_{B(0, r)} ν₀`, which is bounded on the closed
disc (`eventually_forall_killedPotential_ball_near`, `exists_forall_greenPotential_ball_le`), and the disc splitting
bound `measure_exists_lt_abs_killedOccupationGapUpTo_ball_one_le` applies (Armitage–Gardiner, §4.3, for the Green
potentials; Fukushima–Oshima–Takeda (2011), §5.1, for the comparison of additive functionals through their potentials).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess HarmonicBalls

/-- A property that holds eventually along a shifted sequence holds eventually. -/
theorem eventually_atTop_of_eventually_shift {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ n in atTop, P (n + N)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨a + N, fun n hn => ?_⟩
  have h1 := ha (n - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at h1

/-- **Killed potentials of vaguely convergent rates, with eventual bounds.** The conclusion of
`eventually_forall_killedPotential_ball_near` when the power growth and the mass bound of the rates hold only
eventually. -/
theorem eventually_forall_killedPotential_ball_near_of_eventually {R r₀ β m : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀)
    (hβ : 0 < β) (hm : 0 ≤ m) {f : ℕ → ℂ → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) {ν₀ : Measure ℂ}
    (hup : ∀ᶠ n in atTop, (∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume.withDensity (f n) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
        volume.withDensity (f n) (ball 0 R) ≤ ENNReal.ofReal m)
    (hup₀ : ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) R, ν₀ (ball z s) ≤ ENNReal.ofReal (s ^ β))
    (hmass₀ : ν₀ (ball 0 R) ≤ ENNReal.ofReal m)
    (hvague : ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 R →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity (f n))) atTop (𝓝 (∫ y, F y ∂ν₀)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ x ∈ ball (0 : ℂ) R,
      killedPotential (ball 0 R) (f n) x ≤
          ENNReal.ofReal (2 * greenPotential (ball 0 R) ν₀ x) + ENNReal.ofReal δ ∧
        ENNReal.ofReal (2 * greenPotential (ball 0 R) ν₀ x) ≤
          killedPotential (ball 0 R) (f n) x + ENNReal.ofReal δ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hup
  refine eventually_atTop_of_eventually_shift N ?_
  exact eventually_forall_killedPotential_ball_near hR hr₀ hβ hm (f := fun n => f (n + N))
    (fun n => hf (n + N)) (fun n => (hN (n + N) (Nat.le_add_left N n)).1)
    (fun n => (hN (n + N) (Nat.le_add_left N n)).2) hup₀ hmass₀
    (fun F hF hFs => (tendsto_add_atTop_iff_nat
      (f := fun n => ∫ y, F y ∂(volume.withDensity (f n))) N).2 (hvague F hF hFs)) hδ

/-- **Occupation functionals of two vaguely convergent families of rates.** Let `f_n(y) dy` and `g_k(y) dy` converge
vaguely to `ν₀` on every closed disc `B̄(0, r)`, `r < 1`; for each `r < 1` let `f_n`, `g_k` (eventually) and `ν₀` have
a common upper power growth `s^β` for discs `B(z, s)`, `z ∈ B(0, r)`, `s < r₀`; and let the masses of `f_n`, `g_k`
(eventually) and `ν₀` on the unit disc be at most `m`. Then for every `η > 0`, the probability that the occupation
functionals of `f_n` and `g_k` along Brownian motion from `0` killed on exiting the unit disc differ by more than `η`
at some time tends to `0` as `(n, k) → ∞`. -/
theorem tendsto_measure_exists_lt_abs_killedOccupationGapUpTo {f g : ℕ → ℂ → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n)) {ν₀ : Measure ℂ}
    (hpow : ∀ r, r < 1 → ∃ β > (0 : ℝ), ∃ r₀ > (0 : ℝ),
      (∀ᶠ n in atTop, ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
        volume.withDensity (f n) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
      (∀ᶠ n in atTop, ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
        volume.withDensity (g n) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
      ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r, ν₀ (ball z s) ≤ ENNReal.ofReal (s ^ β))
    {m : ℝ} (hfm : ∀ᶠ n in atTop, volume.withDensity (f n) (ball 0 1) ≤ ENNReal.ofReal m)
    (hgm : ∀ᶠ n in atTop, volume.withDensity (g n) (ball 0 1) ≤ ENNReal.ofReal m)
    (hνm : ν₀ (ball 0 1) ≤ ENNReal.ofReal m)
    (hfv : ∀ r, r < 1 → ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity (f n))) atTop (𝓝 (∫ y, F y ∂ν₀)))
    (hgv : ∀ r, r < 1 → ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity (g n))) atTop (𝓝 (∫ y, F y ∂ν₀)))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun p : ℕ × ℕ => planarBrownianMotion 0
      {b | ∃ t : ℝ, η < |killedOccupationGapUpTo (ball 0 1) (f p.1) (g p.2) b t|}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · refine Eventually.of_forall fun _ => ?_
    rw [hεtop]
    exact le_top
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = ε.toReal := ⟨_, rfl⟩
  have he : 0 < e := by
    rw [he_def]
    exact ENNReal.toReal_pos hε.ne' hεtop
  have hεe : ε = ENNReal.ofReal e := by rw [he_def, ENNReal.ofReal_toReal hεtop]
  obtain ⟨m', hm', hmm'⟩ : ∃ m' : ℝ, 0 ≤ m' ∧ ENNReal.ofReal m ≤ ENNReal.ofReal m' :=
    ⟨max m 0, le_max_right _ _, ENNReal.ofReal_le_ofReal (le_max_left _ _)⟩
  -- the radius `r = exp(-π c)`, with `π⁻¹ log(1/r) = c` small against the masses
  obtain ⟨c, hc, hcA⟩ : ∃ c > (0 : ℝ), 3 / η * (c * (m' + m')) < e / 2 := by
    have hcont : Continuous fun c : ℝ => 3 / η * (c * (m' + m')) := by fun_prop
    have hev := (hcont.tendsto 0).eventually (gt_mem_nhds
      (show 3 / η * ((0 : ℝ) * (m' + m')) < e / 2 by rw [zero_mul, mul_zero]; exact half_pos he))
    obtain ⟨ρ, hρ, hP⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨ρ / 2, half_pos hρ, hP (y := ρ / 2) ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hρ)]
    exact half_lt_self hρ
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = Real.exp (-(Real.pi * c)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr_def]
    exact Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr_def]
    exact Real.exp_lt_one_iff.2 (neg_lt_zero.2 (mul_pos Real.pi_pos hc))
  have hlog : Real.pi⁻¹ * Real.log r⁻¹ = c := by
    rw [hr_def, Real.exp_neg, inv_inv, Real.log_exp, inv_mul_cancel_left₀ Real.pi_ne_zero]
  obtain ⟨β, hβ, r₀, hr₀, hfpow, hgpow, hνpow⟩ := hpow r hr1
  have hball : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1.le
  have hνr : ν₀ (ball 0 r) ≤ ENNReal.ofReal m' := (measure_mono hball).trans (hνm.trans hmm')
  obtain ⟨M₀, hM₀⟩ := exists_forall_greenPotential_ball_le hr0 hr₀ hβ hm' hνpow hνr
  obtain ⟨M, hM, hM₀M⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall (0 : ℂ) r, greenPotential (ball 0 r) ν₀ x ≤ M :=
    ⟨max M₀ 0, le_max_right _ _, fun x hx => (hM₀ x hx).trans (le_max_left _ _)⟩
  -- the closeness `δ` of the potentials
  obtain ⟨δ, hδ, hδA⟩ : ∃ δ > (0 : ℝ), 9 / η ^ 2 * (32 * (δ + δ) * (2 * M + δ)) < e / 2 := by
    have hcont : Continuous fun δ : ℝ => 9 / η ^ 2 * (32 * (δ + δ) * (2 * M + δ)) := by fun_prop
    have hev := (hcont.tendsto 0).eventually (gt_mem_nhds
      (show 9 / η ^ 2 * (32 * ((0 : ℝ) + 0) * (2 * M + 0)) < e / 2 by
        simp only [add_zero, mul_zero, zero_mul]; exact half_pos he))
    obtain ⟨ρ, hρ, hP⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨ρ / 2, half_pos hρ, hP (y := ρ / 2) ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hρ)]
    exact half_lt_self hρ
  have hfR : ∀ᶠ n in atTop, (∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
      volume.withDensity (f n) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
        volume.withDensity (f n) (ball 0 r) ≤ ENNReal.ofReal m' :=
    hfpow.and (hfm.mono fun n hn => (measure_mono hball).trans (hn.trans hmm'))
  have hgR : ∀ᶠ n in atTop, (∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
      volume.withDensity (g n) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
        volume.withDensity (g n) (ball 0 r) ≤ ENNReal.ofReal m' :=
    hgpow.and (hgm.mono fun n hn => (measure_mono hball).trans (hn.trans hmm'))
  have hfnear := eventually_forall_killedPotential_ball_near_of_eventually hr0 hr₀ hβ hm' hf hfR hνpow hνr
    (hfv r hr1) hδ
  have hgnear := eventually_forall_killedPotential_ball_near_of_eventually hr0 hr₀ hβ hm' hg hgR hνpow hνr
    (hgv r hr1) hδ
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := tendsto_fst.mono_left prod_atTop_atTop_eq.ge
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := tendsto_snd.mono_left prod_atTop_atTop_eq.ge
  filter_upwards [hfst.eventually (hfnear.and hfm), hsnd.eventually (hgnear.and hgm)] with p hp1 hp2
  obtain ⟨hfn, hfmn⟩ := hp1
  obtain ⟨hgk, hgmk⟩ := hp2
  have hG : ∀ y ∈ ball (0 : ℂ) r,
      ENNReal.ofReal (2 * greenPotential (ball 0 r) ν₀ y) ≤ ENNReal.ofReal (2 * M) := fun y hy =>
    ENNReal.ofReal_le_ofReal (by linarith [hM₀M y (ball_subset_closedBall hy)])
  have hbound := measure_exists_lt_abs_killedOccupationGapUpTo_ball_one_le (hf p.1) (hg p.2) hr0 hr1.le
    (M := ENNReal.ofReal (2 * M) + ENNReal.ofReal δ) (δ := ENNReal.ofReal δ + ENNReal.ofReal δ)
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
    (fun y hy => (hfn y hy).1.trans (add_le_add (hG y hy) le_rfl))
    (fun y hy => (hgk y hy).1.trans (add_le_add (hG y hy) le_rfl))
    (fun y hy => (hfn y hy).1.trans (by rw [← add_assoc]; exact add_le_add (hgk y hy).2 le_rfl))
    (fun y hy => (hgk y hy).1.trans (by rw [← add_assoc]; exact add_le_add (hfn y hy).2 le_rfl)) hη
  have hIf : ∫⁻ y in ball (0 : ℂ) 1, f p.1 y ≤ ENNReal.ofReal m' := by
    have h := hfmn.trans hmm'
    rwa [withDensity_apply _ measurableSet_ball] at h
  have hIg : ∫⁻ y in ball (0 : ℂ) 1, g p.2 y ≤ ENNReal.ofReal m' := by
    have h := hgmk.trans hmm'
    rwa [withDensity_apply _ measurableSet_ball] at h
  have hA₁ : 0 ≤ 9 / η ^ 2 * (32 * (δ + δ) * (2 * M + δ)) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
  have hA₂ : 0 ≤ 3 / η * (c * (m' + m')) :=
    mul_nonneg (div_nonneg (by norm_num) hη.le) (mul_nonneg hc.le (by linarith))
  have h1 : ENNReal.ofReal (9 / η ^ 2) * (32 * (ENNReal.ofReal δ + ENNReal.ofReal δ) *
      (ENNReal.ofReal (2 * M) + ENNReal.ofReal δ)) =
      ENNReal.ofReal (9 / η ^ 2 * (32 * (δ + δ) * (2 * M + δ))) := by
    rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ 2 * M) hδ.le,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 / η ^ 2),
      ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 32 * (δ + δ)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32), ENNReal.ofReal_ofNat]
  have h2 : ENNReal.ofReal (3 / η) * (ENNReal.ofReal c *
      ((∫⁻ y in ball (0 : ℂ) 1, f p.1 y) + ∫⁻ y in ball (0 : ℂ) 1, g p.2 y)) ≤
      ENNReal.ofReal (3 / η * (c * (m' + m'))) := by
    rw [ENNReal.ofReal_mul (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) hη.le), ENNReal.ofReal_mul hc.le,
      ENNReal.ofReal_add hm' hm']
    gcongr
  refine hbound.trans ?_
  rw [hlog, h1, hεe]
  calc _ ≤ ENNReal.ofReal (9 / η ^ 2 * (32 * (δ + δ) * (2 * M + δ))) +
        ENNReal.ofReal (3 / η * (c * (m' + m'))) := add_le_add le_rfl h2
    _ = ENNReal.ofReal (9 / η ^ 2 * (32 * (δ + δ) * (2 * M + δ)) + 3 / η * (c * (m' + m'))) :=
        (ENNReal.ofReal_add hA₁ hA₂).symm
    _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Finite potentials at the centre.** If `f_n(y) dy → ν₀` vaguely on `B̄(0, r)`, `0 < r ≤ 1`, with eventually a
common upper power growth on `B(0, r)` and a common mass bound on the unit disc, then eventually the potential
`u_{f_n}(0)` for Brownian motion killed on exiting the unit disc is finite: `u^{B(0,1)}_{f_n}(0)` exceeds
`u^{B(0,r)}_{f_n}(0)`, which is close to `2 G_{B(0,r)} ν₀(0)`, by at most `π⁻¹ log(1/r) ∫_{B(0,1)} f_n`. -/
theorem eventually_killedPotential_ball_one_zero_ne_top {r r₀ β m : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr₀ : 0 < r₀)
    (hβ : 0 < β) {f : ℕ → ℂ → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) {ν₀ : Measure ℂ}
    (hup : ∀ᶠ n in atTop, ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
      volume.withDensity (f n) (ball z s) ≤ ENNReal.ofReal (s ^ β))
    (hfm : ∀ᶠ n in atTop, volume.withDensity (f n) (ball 0 1) ≤ ENNReal.ofReal m)
    (hup₀ : ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r, ν₀ (ball z s) ≤ ENNReal.ofReal (s ^ β))
    (hνm : ν₀ (ball 0 1) ≤ ENNReal.ofReal m)
    (hvague : ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity (f n))) atTop (𝓝 (∫ y, F y ∂ν₀))) :
    ∀ᶠ n in atTop, killedPotential (ball 0 1) (f n) 0 ≠ ⊤ := by
  have hball : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1
  obtain ⟨m', hm', hmm'⟩ : ∃ m' : ℝ, 0 ≤ m' ∧ ENNReal.ofReal m ≤ ENNReal.ofReal m' :=
    ⟨max m 0, le_max_right _ _, ENNReal.ofReal_le_ofReal (le_max_left _ _)⟩
  have hupm : ∀ᶠ n in atTop, (∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
      volume.withDensity (f n) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
        volume.withDensity (f n) (ball 0 r) ≤ ENNReal.ofReal m' :=
    hup.and (hfm.mono fun n hn => (measure_mono hball).trans (hn.trans hmm'))
  have hνr : ν₀ (ball 0 r) ≤ ENNReal.ofReal m' := (measure_mono hball).trans (hνm.trans hmm')
  have hnear := eventually_forall_killedPotential_ball_near_of_eventually hr hr₀ hβ hm' hf hupm hup₀ hνr
    hvague one_pos
  filter_upwards [hnear, hfm] with n hn hmn
  have h0 := (hn 0 (mem_ball_self hr)).1
  have hsplit := tsub_le_iff_left.1 (killedPotential_ball_one_sub_le hr (hf n))
  have hI : ∫⁻ y in ball (0 : ℂ) 1, f n y ≠ ⊤ := by
    have h := hmn
    rw [withDensity_apply _ measurableSet_ball] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ?_ h0,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI⟩) hsplit
  exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩

end MatedCRT
