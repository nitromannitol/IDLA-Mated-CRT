import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S6r.GoodAnnulus
import MatedCRT.FirstPass.S6r.Window
import MatedCRT.FirstPass.S6p

/-!
# Prevalence bridge for the good-annulus event (Lemma 6.8 window; fp-S6r-prevalence-bridge)

Sources: `notes/fp-gaps/CHATGPT-idla-6-4-6-5-fidelity.md` l.1-43 (the [C5] event is the positive part of
`log (R/|u-v|) + 1`; the factor-4 kernel of the redesign is not literally the Lean event), and
`notes/fp-gaps/CHATGPT-idla-6-8-redesign.md` l.165-214 (S2.3, short-window prevalence).

* (i) `scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent`: the [C5] event `IsGoodAnnulusEvent` (Defs/Setting.lean)
  implies the scale-covariant event `ScaleCovGoodAnnulusEvent` (kernel `log (4R/|u-v|) + 1`, S6r/GoodAnnulus.lean:74)
  with the constants `c₀ ↦ 3 c₀` and `C ↦ (1 + N log 4) C`. The kernel is not switched: the factor `4` is absorbed by
  `log 4 · μ(𝔸)`, and `μ(𝔸) ≤ N · sup_v ∫_𝔸 (log (R/|u-v|)+1)_+ dμ` by a finite cover of the annulus by `N` balls of
  radius `R` (`annulus_cover_uniform`, a count uniform in `(R, z)`). The sup over the closed annulus is reduced to the
  open one by Fatou's lemma (`lintegral_covKernel_le_of_mem_closure`).
  Side conditions, all named: positive ball masses `0 < inf_w μ(B(w, c₀R))`, local finiteness `μ(B(z, 3R)) < ⊤`, and
  no atoms on `𝔸` (the paper's kernel is `+∞` on the diagonal; the Lean [C5] integrand is `1` there).
* (ii) `scaleCovUniformPrevalenceStmt_of_c5`: `ScaleCovUniformPrevalenceStmt` from the all-scales uniform [C5]
  prevalence `C5AllScalesPrevalenceStmt` (named) and a.s. non-degeneracy `AnnulusNondegenerateAe` (named).
* (iii) deterministic part of S2.3: a seven-adic `7^{-n} ∈ [d, d^a]` is a window candidate `winCand`, and the first
  good candidate `winSelect` is good (`winSelect_good_of_seven_adic`). The probability bound (S2.3, the short-window
  prevalence) is owned by z12 (`MatedCRT/FirstPass/S6r/ShortWindow.lean`, `ShortWindowGoodRadiusPrevalenceStmt`), not
  duplicated here; the restricted (ii) above is the cone-field input of that chain.

Terminology: LQG measure (Duplantier-Sheffield), good annuli (Berestycki-Powell, Armstrong-Kuusi-Mourrat),
log kernels and their positive parts (Armitage-Gardiner).
-/

open MeasureTheory Set Metric HarmonicBalls Filter Topology
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Window

/-! ### 1. A covering count for the annulus, uniform in `(R, z)` -/

/-- The open unit annulus `{1 < |x| < 2}` is covered by finitely many balls of radius `1` centred in it. By scaling and
translation, `𝔸_{R,2R}(z)` is covered by the same number of balls of radius `R` centred in `𝔸_{R,2R}(z)`. -/
lemma annulus_cover_uniform :
    ∃ N : ℕ, ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧
      (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧ annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R := by
  set A : Set ℂ := {x : ℂ | 1 < ‖x‖ ∧ ‖x‖ < 2} with hA
  have hbd : TotallyBounded A :=
    (isCompact_closedBall (0 : ℂ) 2).totallyBounded.subset fun x hx => by
      simpa [mem_closedBall, dist_zero_right] using hx.2.le
  obtain ⟨t₀, ht₀sub, ht₀fin, hcov⟩ :=
    totallyBounded_iff_subset.1 hbd _ (Metric.dist_mem_uniformity one_pos)
  refine ⟨ht₀fin.toFinset.card, fun R z hR => ⟨ht₀fin.toFinset.image (fun y => z + (R : ℂ) * y),
    Finset.card_image_le.trans le_rfl, ?_, ?_⟩⟩
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hyA : 1 < ‖y‖ ∧ ‖y‖ < 2 := ht₀sub (ht₀fin.mem_toFinset.1 hy)
    rw [mem_annulus_iff, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    constructor <;> nlinarith [hyA.1, hyA.2]
  · intro u hu
    obtain ⟨hu1, hu2⟩ := mem_annulus_iff.1 hu
    have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    set x : ℂ := (u - z) / (R : ℂ) with hx
    have hxn : ‖x‖ = ‖u - z‖ / R := by
      rw [hx, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
    have hxA : x ∈ A := by
      refine ⟨?_, ?_⟩
      · rw [hxn, lt_div_iff₀ hR]; linarith
      · rw [hxn, div_lt_iff₀ hR]; linarith
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxA)
    have hdist : dist x y < 1 := hxy
    refine Set.mem_iUnion₂.2 ⟨z + (R : ℂ) * y,
      Finset.mem_image.2 ⟨y, ht₀fin.mem_toFinset.2 hy, rfl⟩, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have heq : u - (z + (R : ℂ) * y) = (R : ℂ) * (x - y) := by
      rw [hx]; field_simp; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, ← dist_eq_norm]
    nlinarith [hdist]

/-! ### 2. Kernel comparisons -/

/-- The [C5] integrand `(log (R/|u-v|) + 1)_+` is at least `1` on the ball `B(v, R)` (on the diagonal the Lean value is
`1`, since `log 0 = 0`). -/
lemma one_le_ofReal_log_div {R : ℝ} {v u : ℂ} (hd : ‖u - v‖ < R) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) := by
  rcases eq_or_ne u v with rfl | hne
  · simp
  · have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hlog : 0 ≤ Real.log (R / ‖u - v‖) := Real.log_nonneg ((one_le_div hpos).2 hd.le)
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) := ENNReal.ofReal_le_ofReal (by linarith)

/-- The scale-covariant kernel is at most the [C5] kernel plus `log 4`, off the diagonal:
`log (4R/|u-v|) + 1 = (log (R/|u-v|) + 1) + log 4`. -/
lemma covKernel_le_add {R : ℝ} (hR : 0 < R) {v u : ℂ} (hne : u ≠ v) :
    covKernel R v u ≤ ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) + ENNReal.ofReal (Real.log 4) := by
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hlog : Real.log (4 * R / ‖u - v‖) = Real.log (R / ‖u - v‖) + Real.log 4 := by
    rw [mul_div_assoc, Real.log_mul (by norm_num) (div_pos hR hpos).ne', add_comm]
  unfold covKernel
  simp only [hne, ↓reduceIte]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  rw [hlog]; linarith

/-! ### 3. Measure bounds from the [C5] supremum -/

/-- `μ(𝔸 ∩ B(v, R))` is at most the [C5] integral at `v ∈ 𝔸`. -/
lemma measure_annulus_inter_ball_le {μ : Measure ℂ} {R : ℝ} {z v : ℂ}
    {S : ℝ≥0∞} (hS : ∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ S) :
    μ (annulus z R (2 * R) ∩ ball v R) ≤ S := by
  have hA : MeasurableSet (annulus z R (2 * R)) := measurableSet_ball.diff measurableSet_closedBall
  have hB : MeasurableSet (ball v R) := measurableSet_ball
  rw [Set.inter_comm, ← Measure.restrict_apply hB, ← lintegral_indicator_one (μ := μ.restrict (annulus z R (2 * R))) hB]
  refine le_trans (setLIntegral_mono' hA fun u _ => ?_) hS
  by_cases hub : u ∈ ball v R
  · rw [Set.indicator_of_mem hub]
    exact one_le_ofReal_log_div (by rwa [mem_ball, dist_eq_norm] at hub)
  · rw [Set.indicator_of_notMem hub]
    exact zero_le

/-- Covering bound: `μ(𝔸_{R,2R}(z)) ≤ N · S` when every [C5] integral at a centre `v ∈ 𝔸` is at most `S`. -/
lemma measure_annulus_le_of_cover {μ : Measure ℂ} {N : ℕ} {R : ℝ} {z : ℂ}
    (hcov : ∃ t : Finset ℂ, t.card ≤ N ∧ (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧
      annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R)
    {S : ℝ≥0∞}
    (hS : ∀ v ∈ annulus z R (2 * R),
      ∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ S) :
    μ (annulus z R (2 * R)) ≤ N * S := by
  obtain ⟨t, htN, htA, hsub⟩ := hcov
  calc μ (annulus z R (2 * R))
      ≤ μ (⋃ v ∈ t, annulus z R (2 * R) ∩ ball v R) := by
        refine measure_mono fun u hu => ?_
        obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.1 (hsub hu)
        exact Set.mem_iUnion₂.2 ⟨v, hv, hu, huv⟩
    _ ≤ ∑ v ∈ t, μ (annulus z R (2 * R) ∩ ball v R) := measure_biUnion_finset_le t _
    _ ≤ ∑ _v ∈ t, S := Finset.sum_le_sum fun v hv =>
        measure_annulus_inter_ball_le (hS v (htA v hv))
    _ = (t.card : ℝ≥0∞) * S := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ≥0∞) * S := by gcongr

/-- The scale-covariant integral at a centre `v ∈ 𝔸` (where `μ{v} = 0`) is at most the [C5] integral plus
`log 4 · μ(𝔸)`. -/
lemma lintegral_covKernel_le_of_mem {μ : Measure ℂ} {R : ℝ} {z v : ℂ} (hR : 0 < R) (hv : μ {v} = 0)
    {S : ℝ≥0∞} (hS : ∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ S) :
    ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ
      ≤ S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R)) := by
  have hae : ∀ᵐ u ∂μ, u ≠ v := by
    rw [ae_iff]; simpa using hv
  calc ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ
      ≤ ∫⁻ u in annulus z R (2 * R),
          (ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) + ENNReal.ofReal (Real.log 4)) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hae] with u hu
        exact covKernel_le_add hR hu
    _ = (∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ)
          + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R)) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R)) := add_le_add hS le_rfl

/-- Fatou's lemma: the scale-covariant integral at a centre in the closed annulus is bounded by the bound on the open
annulus (the kernel is continuous in the centre off the diagonal, and `u ∈ 𝔸` is never on the boundary). -/
lemma lintegral_covKernel_le_of_mem_closure {μ : Measure ℂ} {R : ℝ} {z v : ℂ} (hR : 0 < R) {B : ℝ≥0∞}
    (hB : ∀ w ∈ annulus z R (2 * R), ∫⁻ u in annulus z R (2 * R), covKernel R w u ∂μ ≤ B)
    (hv : v ∈ closure (annulus z R (2 * R))) :
    ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ ≤ B := by
  by_cases hvA : v ∈ annulus z R (2 * R)
  · exact hB v hvA
  obtain ⟨x, hxA, hxv⟩ := mem_closure_iff_seq_limit.1 hv
  have hA : MeasurableSet (annulus z R (2 * R)) := measurableSet_ball.diff measurableSet_closedBall
  have hpt : ∀ u ∈ annulus z R (2 * R),
      Tendsto (fun n => covKernel R (x n) u) atTop (𝓝 (covKernel R v u)) := by
    intro u hu
    have hne : u ≠ v := fun h => hvA (h ▸ hu)
    have hev : ∀ᶠ n in atTop, u ≠ x n := by
      filter_upwards [hxv.eventually_ne (Ne.symm hne)] with n hn
      exact Ne.symm hn
    have hd : ‖u - v‖ ≠ 0 := (norm_pos_iff.2 (sub_ne_zero.2 hne)).ne'
    have hreal : ContinuousAt (fun w : ℂ => Real.log (4 * R / ‖u - w‖) + 1) v := by
      refine ContinuousAt.add (ContinuousAt.log ?_ (div_ne_zero (mul_pos (by norm_num) hR).ne' hd)) continuousAt_const
      exact continuousAt_const.div (continuous_norm.comp (continuous_const.sub continuous_id)).continuousAt hd
    have hcont : ContinuousAt (fun w : ℂ => covKernel R w u) v := by
      have : (fun w : ℂ => covKernel R w u) =ᶠ[𝓝 v] fun w => ENNReal.ofReal (Real.log (4 * R / ‖u - w‖) + 1) := by
        filter_upwards [isOpen_ne.mem_nhds (Ne.symm hne)] with w hw
        simp only [covKernel, Ne.symm hw, ↓reduceIte]
      exact ((ENNReal.continuous_ofReal.continuousAt).comp hreal).congr this.symm
    have hlim := hcont.tendsto.comp hxv
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hev] with n hn
    simp [Function.comp, covKernel, hn]
  have hfat := lintegral_liminf_le (u := atTop) (μ := μ.restrict (annulus z R (2 * R)))
    (fun n => measurable_covKernel R (x n))
  have hlim_int : ∫⁻ u in annulus z R (2 * R), covKernel R v u ∂μ
      = ∫⁻ u in annulus z R (2 * R), liminf (fun n => covKernel R (x n) u) atTop ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hA] with u hu
    exact ((hpt u hu).liminf_eq).symm
  rw [hlim_int]
  refine le_trans hfat (Filter.liminf_le_of_frequently_le' ?_)
  refine (Eventually.of_forall fun n => ?_).frequently
  exact hB (x n) (hxA n)

/-- The scale-covariant supremum `covN` is bounded by the [C5] constant times the ball-mass infimum, with the explicit
constant `(1 + N log 4)`: the proof of `ScaleCovGoodAnnulusEvent` for `μ` from `IsGoodAnnulusEvent`. -/
lemma covN_le_of_isGoodAnnulusEvent {μ : Measure ℂ} {N : ℕ} {c₀ C R : ℝ} {z : ℂ} (hR : 0 < R)
    (hcov : ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧
      (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧ annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R)
    (hgood : IsGoodAnnulusEvent μ c₀ C R z) (hatom : ∀ v ∈ annulus z R (2 * R), μ {v} = 0) :
    covN R z μ ≤ ENNReal.ofReal ((1 + N * Real.log 4) * C) *
      ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R)) := by
  set S : ℝ≥0∞ := ⨆ v ∈ annulus z R (2 * R),
    ∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ with hSdef
  have hS : ∀ v ∈ annulus z R (2 * R),
      ∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ S :=
    fun v hv => le_iSup₂ (f := fun v _ =>
      ∫⁻ u in annulus z R (2 * R), ENNReal.ofReal (Real.log (R / ‖u - v‖) + 1) ∂μ) v hv
  have hSL : S ≤ ENNReal.ofReal C * ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R)) := hgood
  have hB : ∀ w ∈ annulus z R (2 * R), ∫⁻ u in annulus z R (2 * R), covKernel R w u ∂μ
      ≤ S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R)) :=
    fun w hw => lintegral_covKernel_le_of_mem hR (hatom w hw) (hS w hw)
  have hcovN : covN R z μ ≤ S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R)) :=
    iSup₂_le fun v hv => lintegral_covKernel_le_of_mem_closure hR hB hv
  have hmass : μ (annulus z R (2 * R)) ≤ N * S := measure_annulus_le_of_cover (hcov R z hR) hS
  have hpos : (0 : ℝ) ≤ 1 + N * Real.log 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hBS : S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R))
      ≤ ENNReal.ofReal (1 + N * Real.log 4) * S := by
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))),
      ENNReal.ofReal_one, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, add_mul, one_mul]
    calc S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R))
        ≤ S + ENNReal.ofReal (Real.log 4) * ((N : ℝ≥0∞) * S) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass zero_le)
      _ = S + (N * ENNReal.ofReal (Real.log 4)) * S := by ring
  calc covN R z μ ≤ S + ENNReal.ofReal (Real.log 4) * μ (annulus z R (2 * R)) := hcovN
    _ ≤ ENNReal.ofReal (1 + N * Real.log 4) * S := hBS
    _ ≤ ENNReal.ofReal (1 + N * Real.log 4) *
          (ENNReal.ofReal C * ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R))) :=
          by gcongr
    _ = ENNReal.ofReal ((1 + N * Real.log 4) * C) * ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R)) := by
          rw [ENNReal.ofReal_mul hpos, mul_assoc]

/-! ### 4. The bump mass `m_R^φ` (with `c₀ ↦ 3 c₀`) -/

lemma bumpPhi_le_one (x : ℂ) : bumpPhi x ≤ 1 := by
  unfold bumpPhi
  exact max_le zero_le_one (min_le_left _ _)

lemma bumpPhi_eq_one_of_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : bumpPhi x = 1 := by
  unfold bumpPhi
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The bump mass is at least the mass of the ball of radius `c₀ R` around a point at distance `< c₀ R / 2`
(`φ = 1` on `|x| ≤ 1/2`, and the rescaling uses `3 c₀`). -/
lemma measure_ball_le_bumpMass {μ : Measure ℂ} {c₀ R : ℝ} (hc₀ : 0 < c₀) (hR : 0 < R) {w w' : ℂ}
    (hw : dist w w' < c₀ * R / 2) :
    μ (ball w' (c₀ * R)) ≤ bumpMass (3 * c₀) R μ w := by
  unfold bumpMass
  have hden : (0 : ℝ) < 3 * c₀ * R := by have := mul_pos hc₀ hR; linarith
  rw [← lintegral_indicator_one (μ := μ) measurableSet_ball]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ ball w' (c₀ * R)
  · rw [Set.indicator_of_mem hu]
    have hu' : ‖u - w'‖ < c₀ * R := by rwa [mem_ball, dist_eq_norm] at hu
    have hw' : ‖w' - w‖ < c₀ * R / 2 := by rw [← dist_eq_norm, dist_comm]; exact hw
    have htri : ‖u - w‖ ≤ ‖u - w'‖ + ‖w' - w‖ := norm_sub_le_norm_sub_add_norm_sub u w' w
    have hnorm : ‖(u - w) / ((3 * c₀ * R : ℝ) : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hden.le, div_le_iff₀ hden]
      linarith
    rw [bumpPhi_eq_one_of_le hnorm]
    simp
  · rw [Set.indicator_of_notMem hu]
    exact zero_le

/-- The bump mass at `w` is at most the mass of the ball of radius `9 c₀ R / 4` (`φ = 0` on `|x| ≥ 3/4`). -/
lemma bumpMass_le_measure_ball {μ : Measure ℂ} {c₀ R : ℝ} (hc₀ : 0 < c₀) (hR : 0 < R) (w : ℂ) :
    bumpMass (3 * c₀) R μ w ≤ μ (ball w (9 / 4 * c₀ * R)) := by
  unfold bumpMass
  have hden : (0 : ℝ) < 3 * c₀ * R := by have := mul_pos hc₀ hR; linarith
  rw [← lintegral_indicator_one (μ := μ) measurableSet_ball]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ ball w (9 / 4 * c₀ * R)
  · rw [Set.indicator_of_mem hu]
    exact ENNReal.ofReal_le_one.2 (bumpPhi_le_one _)
  · rw [Set.indicator_of_notMem hu]
    have hu' : 9 / 4 * c₀ * R ≤ ‖u - w‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hu; exact hu
    have h34 : 3 / 4 ≤ ‖(u - w) / ((3 * c₀ * R : ℝ) : ℂ)‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hden.le, le_div_iff₀ hden]
      linarith
    rw [bumpPhi_eq_zero h34]
    simp

/-- The bump mass infimum dominates the [C5] ball-mass infimum: `0 < inf_{𝔸} μ(B(·, c₀R)) ≤ m_R^φ(z; μ)` for the
rescaled bump with `3 c₀`. -/
lemma inf_ball_le_massBumpR {μ : Measure ℂ} {c₀ R : ℝ} {z : ℂ} (hc₀ : 0 < c₀) (hR : 0 < R) :
    (⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R))) ≤ massBumpR (3 * c₀) R z μ := by
  unfold massBumpR
  refine le_iInf₂ fun w hw => ?_
  obtain ⟨w', hw', hdist⟩ := Metric.mem_closure_iff.1 hw (c₀ * R / 2) (div_pos (mul_pos hc₀ hR) two_pos)
  exact le_trans (iInf₂_le w' hw') (measure_ball_le_bumpMass hc₀ hR hdist)

/-- `m_R^φ(z; μ) < ∞` as soon as `μ(B(z, 3R)) < ∞` (the infimum is at most the value at `z + (3/2) R ∈ 𝔸`). -/
lemma massBumpR_lt_top {μ : Measure ℂ} {c₀ R : ℝ} {z : ℂ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hR : 0 < R)
    (hfin : μ (ball z (3 * R)) ≠ ⊤) : massBumpR (3 * c₀) R z μ < ⊤ := by
  set w₀ : ℂ := z + ((3 / 2 * R : ℝ) : ℂ) with hw₀
  have hdist : dist w₀ z = 3 / 2 * R := by
    rw [hw₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hw₀A : w₀ ∈ annulus z R (2 * R) := by
    rw [mem_annulus_iff, ← dist_eq_norm, hdist]
    constructor <;> linarith
  have hcR : c₀ * R < R / 5 := by nlinarith
  unfold massBumpR
  refine lt_of_le_of_lt (le_trans (iInf₂_le w₀ (subset_closure hw₀A))
    (bumpMass_le_measure_ball hc₀ hR w₀)) ?_
  refine lt_of_le_of_lt (measure_mono fun u hu => ?_) (lt_top_iff_ne_top.2 hfin)
  rw [mem_ball] at hu ⊢
  have htri := dist_triangle u w₀ z
  linarith

/-! ### 5. Main comparison (i) -/

/-- **(i) Comparison of the good-annulus events.** The [C5] event `IsGoodAnnulusEvent` (Defs/Setting.lean; kernel
`(log (R/|u-v|)+1)_+`) implies the scale-covariant event `ScaleCovGoodAnnulusEvent` (S6r/GoodAnnulus.lean; kernel
`log (4R/|u-v|)+1`) at the constants `c₀ ↦ 3 c₀` and `C ↦ (1 + N log 4) C`, under the named side conditions:
positive ball masses on the annulus, `μ(B(z,3R)) < ⊤`, and no atoms on the annulus. -/
theorem scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent {μ : Measure ℂ} {N : ℕ}
    (hN : ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧
      (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧ annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R)
    {c₀ C R : ℝ} {z : ℂ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hR : 0 < R)
    (hgood : IsGoodAnnulusEvent μ c₀ C R z)
    (hpos : 0 < ⨅ w ∈ annulus z R (2 * R), μ (ball w (c₀ * R)))
    (hfin : μ (ball z (3 * R)) ≠ ⊤) (hatom : ∀ v ∈ annulus z R (2 * R), μ {v} = 0) :
    ScaleCovGoodAnnulusEvent (3 * c₀) ((1 + N * Real.log 4) * C) R z μ := by
  refine ⟨lt_of_lt_of_le hpos (inf_ball_le_massBumpR hc₀ hR), massBumpR_lt_top hc₀ hc₀' hR hfin, ?_⟩
  exact le_trans (covN_le_of_isGoodAnnulusEvent hR hN hgood hatom)
    (mul_le_mul_of_nonneg_left (inf_ball_le_massBumpR hc₀ hR) zero_le)

/-! ### 6. Uniform prevalence (ii) -/

/-- **Named input, not proved (all-scales form of [C5]).** `p ≤ P(IsGoodAnnulusEvent)` for all `R > 0` and all centres
`z ∈ ℂ`. `annulusHit_uniform` (S6p.lean:44) gives this only for `𝔸_{r/3,3r}(z) ⊆ B_ρ`, `ρ < 1`, and
`r/100 ≤ infDist 0 𝔸`; the all-scales statement is the paper's invariance step (paper line 2716, corrected tex) through
`WholePlaneLQGCoordinateChangeStep` and `WholePlaneGoodAnnulusTightnessStep` (Steps/Sec6/AnnulusHit.lean). -/
def C5AllScalesPrevalenceStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ) (c₀ C : ℝ) :
    Prop :=
  ∃ p : ℝ≥0∞, 0 < p ∧ ∀ R : ℝ, 0 < R → ∀ z : ℂ, p ≤ P {ω | IsGoodAnnulusEvent (μ ω) c₀ C R z}

/-- **Named input, not proved (a.s. non-degeneracy at one annulus).** Positive ball masses on `𝔸_{R,2R}(z)`, local
finiteness on `B(z, 3R)`, and no atoms on `𝔸_{R,2R}(z)`. These are properties of the LQG measure `μ_h` (full support,
Rhodes-Vargas; diffuseness), not consequences of `IsLQGMeasure` as defined in the Harmonic-Balls package. -/
def AnnulusNondegenerateAe {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ) (c₀ R : ℝ)
    (z : ℂ) : Prop :=
  ∀ᵐ ω ∂P, 0 < (⨅ w ∈ annulus z R (2 * R), μ ω (ball w (c₀ * R))) ∧ μ ω (ball z (3 * R)) ≠ ⊤ ∧
    ∀ v ∈ annulus z R (2 * R), μ ω {v} = 0

/-- Transfer of a probability lower bound from the [C5] event to the scale-covariant event, at one annulus, under the
a.s. non-degeneracy `AnnulusNondegenerateAe`. -/
lemma scaleCov_prob_of_isGood {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ) {N : ℕ}
    (hN : ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧
      (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧ annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R)
    {c₀ C R : ℝ} {z : ℂ} {p : ℝ≥0∞} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5) (hR : 0 < R)
    (hp : p ≤ P {ω | IsGoodAnnulusEvent (μ ω) c₀ C R z}) (hnd : AnnulusNondegenerateAe P μ c₀ R z) :
    p ≤ P {ω | ScaleCovGoodAnnulusEvent (3 * c₀) ((1 + N * Real.log 4) * C) R z (μ ω)} := by
  have hnull : P {ω | ¬ (0 < (⨅ w ∈ annulus z R (2 * R), μ ω (ball w (c₀ * R))) ∧
      μ ω (ball z (3 * R)) ≠ ⊤ ∧ ∀ v ∈ annulus z R (2 * R), μ ω {v} = 0)} = 0 :=
    ae_iff.1 hnd
  calc p ≤ P {ω | IsGoodAnnulusEvent (μ ω) c₀ C R z} := hp
    _ ≤ P ({ω | ScaleCovGoodAnnulusEvent (3 * c₀) ((1 + N * Real.log 4) * C) R z (μ ω)} ∪
          {ω | ¬ (0 < (⨅ w ∈ annulus z R (2 * R), μ ω (ball w (c₀ * R))) ∧
            μ ω (ball z (3 * R)) ≠ ⊤ ∧ ∀ v ∈ annulus z R (2 * R), μ ω {v} = 0)}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hND : 0 < (⨅ w ∈ annulus z R (2 * R), μ ω (ball w (c₀ * R))) ∧
            μ ω (ball z (3 * R)) ≠ ⊤ ∧ ∀ v ∈ annulus z R (2 * R), μ ω {v} = 0
        · exact Or.inl (scaleCovGoodAnnulusEvent_of_isGoodAnnulusEvent hN hc₀ hc₀' hR hω hND.1 hND.2.1
            hND.2.2)
        · exact Or.inr hND
    _ ≤ P {ω | ScaleCovGoodAnnulusEvent (3 * c₀) ((1 + N * Real.log 4) * C) R z (μ ω)} +
          P {ω | ¬ (0 < (⨅ w ∈ annulus z R (2 * R), μ ω (ball w (c₀ * R))) ∧
            μ ω (ball z (3 * R)) ≠ ⊤ ∧ ∀ v ∈ annulus z R (2 * R), μ ω {v} = 0)} :=
        measure_union_le _ _
    _ = P {ω | ScaleCovGoodAnnulusEvent (3 * c₀) ((1 + N * Real.log 4) * C) R z (μ ω)} := by
        rw [hnull, add_zero]

/-- **(ii) Uniform prevalence of the scale-covariant event (all scales; not derived).** From the all-scales [C5]
prevalence and a.s. non-degeneracy, `ScaleCovUniformPrevalenceStmt` holds at `c₀ ↦ 3 c₀`, `C ↦ (1 + N log 4) C`.
The hypothesis `hC5` is not available from the Lean inputs (see `C5AllScalesPrevalenceStmt`). -/
theorem scaleCovUniformPrevalenceStmt_of_c5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) {N : ℕ}
    (hN : ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧
      (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧ annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R)
    {c₀ C : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5)
    (hC5 : C5AllScalesPrevalenceStmt P μ c₀ C)
    (hnd : ∀ R : ℝ, 0 < R → ∀ z : ℂ, AnnulusNondegenerateAe P μ c₀ R z) :
    ScaleCovUniformPrevalenceStmt P μ (3 * c₀) ((1 + N * Real.log 4) * C) := by
  obtain ⟨p, hp, hA⟩ := hC5
  exact ⟨p, hp, fun R hR z => scaleCov_prob_of_isGood P μ hN hc₀ hc₀' hR (hA R hR z) (hnd R hR z)⟩

/-- Complement form of a lower bound: `P Aᶜ ≤ 1 - p` gives `p ≤ P A` for a probability measure. -/
lemma ofReal_le_measure_of_compl_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Set Ω} {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (h : P Aᶜ ≤ ENNReal.ofReal (1 - p)) :
    ENNReal.ofReal p ≤ P A := by
  have h1 : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    rw [← measure_univ (μ := P), ← Set.union_compl_self A]
    exact measure_union_le _ _
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hsum : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp.le (by linarith)]
    simp
  have h2 : P A + ENNReal.ofReal (1 - p) < 1 := by
    rw [← hsum]
    exact ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hlt
  have h3 : (1 : ℝ≥0∞) ≤ P A + ENNReal.ofReal (1 - p) := le_trans h1 (add_le_add le_rfl h)
  exact absurd h2 (not_lt.2 h3)

/-- **(ii), restricted range (proved from the uniform Lemma 6.5 of S6p).** For cone fields, `AnnulusHitUniformStmt`
(S6p.lean:44-ish, the uniform form of Lemma 6.5 with `C = C(p)`) gives `P[E_R(z; C)] ≥ p` for the annuli of the paper's
range: `𝔸_{R/3,3R}(z) ⊆ B_ρ` with `ρ < 1` and `R/100 ≤ dist(0, 𝔸_{R/3,3R}(z))`. Together with (i) and the a.s.
non-degeneracy, the scale-covariant event has probability at least `p` on that range, with constant
`C' = (1 + N log 4) C(p)`. This is the range used by the paper's Lemma 6.4 (lattice points in `B_{ρ-3√δ} \ B_{10√δ}`,
scales `R ∈ [δ, √δ]`), not the all-scales `ScaleCovUniformPrevalenceStmt`. -/
theorem scaleCov_restricted_prevalence_of_annulusHit
    (hA : MatedCRT.FirstPass64.AnnulusHitUniformStmt) {N : ℕ}
    (hN : ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧
      (∀ v ∈ t, v ∈ annulus z R (2 * R)) ∧ annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      (∀ (R : ℝ), 0 < R → ∀ z : ℂ, AnnulusNondegenerateAe P μ c₀ R z) →
      ∀ (R : ℝ) (z : ℂ), 0 < R → annulus z (R / 3) (3 * R) ⊆ ball 0 ρ →
        R / 100 ≤ infDist 0 (annulus z (R / 3) (3 * R)) →
        ENNReal.ofReal p ≤ P {ω | ScaleCovGoodAnnulusEvent (3 * c₀) C' R z (μ ω)} := by
  obtain ⟨C, hC, hAC⟩ := hA γ hγ0 hγ2 c₀ hc₀ hc₀' p hp hp1
  have hlog : (0 : ℝ) ≤ N * Real.log 4 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  refine ⟨(1 + N * Real.log 4) * C, mul_pos (by linarith) hC, ?_⟩
  intro ρ hρ hρ1 Ω _ P hC' hcirc μ hcone hnd R z hR hsub hdist
  have : IsProbabilityMeasure P := hcone.1
  have hbad := hAC ρ hρ hρ1 Ω P hC' hcirc μ hcone R z hR hsub hdist
  have hgood : ENNReal.ofReal p ≤ P {ω | IsGoodAnnulusEvent (μ ω) c₀ C R z} :=
    ofReal_le_measure_of_compl_le P hp hp1.le hbad
  exact scaleCov_prob_of_isGood P μ hN hc₀ hc₀' hR hgood (hnd R hR z)

/-! ### 7. Short window (S2.2-S2.3): the deterministic part -/

/-- A seven-adic scale `7^{-n}` in the short window `[d, d^a]`, `a = shortExp ζ`, is a window candidate `winCand`. -/
lemma exists_winCand_of_seven_adic {d ζ : ℝ} (hd : 0 < d) {n : ℤ}
    (h1 : d ≤ (7 : ℝ) ^ (-n)) (h2 : (7 : ℝ) ^ (-n) ≤ d ^ shortExp ζ) :
    ∃ k : ℕ, k < winNum d ζ ∧ winCand d ζ k = (7 : ℝ) ^ (-n) := by
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h1' := Real.log_le_log hd h1
  rw [Real.log_zpow] at h1'
  have h2' := Real.log_le_log (zpow_pos (by norm_num) _) h2
  rw [Real.log_zpow, Real.log_rpow hd] at h2'
  push_cast at h1' h2'
  have hnhi : n ≤ winHi d := Int.le_floor.2 (by rw [le_div_iff₀ hlog7]; linarith)
  have hlo : winLo d ζ ≤ n := Int.ceil_le.2 (by rw [div_le_iff₀ hlog7]; nlinarith)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n - winLo d ζ by omega)
  refine ⟨k, ?_, ?_⟩
  · rw [winNum, Int.lt_toNat]
    omega
  · unfold winCand
    congr 1
    omega

open Classical in
/-- The first-good selection `winSelect` (S6r/Window.lean) picks an index `k < winNum` whose good event holds, and
`winSelect` equals the candidate `winCand d ζ k`. -/
lemma winSelect_spec {d ζ : ℝ} (good : ℕ → Prop) (h : ∃ k, k < winNum d ζ ∧ good k) :
    ∃ k, k < winNum d ζ ∧ good k ∧ winSelect d ζ good = winCand d ζ k := by
  unfold winSelect
  split_ifs
  exact ⟨_, (Nat.find_spec h).1, (Nat.find_spec h).2, rfl⟩

/-- **Deterministic part of (iii).** If some seven-adic scale `7^{-n} ∈ [d, d^a]` is good (for the predicate `Good`
of a radius), then the radius selected by `winSelect` is good. This discharges the good-hypothesis of the selection
once the window prevalence is available pointwise. -/
lemma winSelect_good_of_seven_adic {d ζ : ℝ} (hd : 0 < d) (Good : ℝ → Prop)
    (h : ∃ n : ℤ, d ≤ (7 : ℝ) ^ (-n) ∧ (7 : ℝ) ^ (-n) ≤ d ^ shortExp ζ ∧ Good ((7 : ℝ) ^ (-n))) :
    Good (winSelect d ζ (fun k => Good (winCand d ζ k))) := by
  obtain ⟨n, h1, h2, hg⟩ := h
  obtain ⟨k, hk, hck⟩ := exists_winCand_of_seven_adic (ζ := ζ) hd h1 h2
  obtain ⟨k', _, hg', heq⟩ := winSelect_spec (fun k => Good (winCand d ζ k))
    ⟨k, hk, by rw [hck]; exact hg⟩
  rw [heq]
  exact hg'

end Lemma68Window

end MatedCRT
