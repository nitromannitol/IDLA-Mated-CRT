import MatedCRT.Defs.Setting

/-!
# The good annulus event through countably many integrals (proof of IR-c4-6, deterministic part)

The event `E_r(z; C)` of eq:good-annulus-event (`IsGoodAnnulusEvent`, with the scale-invariant integrand of [C5]) is a
property of the measure `μ` involving a supremum over `v ∈ 𝔸_{r,2r}(z)` and an infimum over `w ∈ 𝔸_{r,2r}(z)`. For a
locally finite `μ` it is a measurable condition on countably many integrals `∫ g_j dμ` of continuous compactly
supported functions `g_j` supported in `𝔸_{r/3,3r}(z)` (`isGoodAnnulusEvent_iff_countable`):

* the supremum over `v` may be taken over a countable dense set, because `v ↦ ∫_{𝔸} (log (r/|u - v|) + 1)⁺ dμ(u)` is
  lower semicontinuous (Fatou's lemma);
* `∫_{𝔸} (log (r/|u - v|) + 1)⁺ dμ(u) = sup_n ∫ χ_{𝔸,n}(u) ℓ_{v,n}(u) dμ(u)` for continuous cutoffs `χ_{𝔸,n} ↑ 1_𝔸` and
  continuous `ℓ_{v,n}` eventually equal to the integrand at each point;
* `μ(B_ρ(w)) = sup_l ∫ χ_{B_ρ(w),l} dμ`;
* the infimum over `w` of `μ(B_ρ(w))` over a compact `K` equals `sup_n inf {μ(B_{ρ - 2δ_n}(w')) : w' ∈ D, dist(w', K) < δ_n}`
  for a countable dense `D` and `δ_n ↓ 0` (compactness), and `𝔸_{r,2r}(z)` is a countable union of compact annuli.
-/

namespace MatedCRT

namespace AnnulusEventCountable

open MeasureTheory Set Metric Filter Topology HarmonicBalls
open scoped ENNReal

/-! ### Cutoffs -/

/-- `χ_{V,n}(u) = min(1, (n + 1) dist(u, Vᶜ))`. -/
noncomputable def cutoff (V : Set ℂ) (n : ℕ) (u : ℂ) : ℝ := min 1 (((n : ℝ) + 1) * infDist u Vᶜ)

lemma continuous_cutoff (V : Set ℂ) (n : ℕ) : Continuous (cutoff V n) :=
  continuous_const.min (continuous_const.mul (continuous_infDist_pt _))

lemma cutoff_nonneg (V : Set ℂ) (n : ℕ) (u : ℂ) : 0 ≤ cutoff V n u :=
  le_min zero_le_one (mul_nonneg (by positivity) infDist_nonneg)

lemma cutoff_le_one (V : Set ℂ) (n : ℕ) (u : ℂ) : cutoff V n u ≤ 1 := min_le_left _ _

lemma cutoff_eq_zero {V : Set ℂ} {u : ℂ} (hu : u ∉ V) (n : ℕ) : cutoff V n u = 0 := by
  rw [cutoff, infDist_zero_of_mem (show u ∈ Vᶜ from hu), mul_zero, min_eq_right zero_le_one]

lemma tsupport_cutoff_subset (V : Set ℂ) (n : ℕ) : tsupport (cutoff V n) ⊆ closure V :=
  closure_mono (Function.support_subset_iff'.2 fun _ hu => cutoff_eq_zero hu n)

lemma hasCompactSupport_cutoff {V : Set ℂ} (hV : Bornology.IsBounded V) (n : ℕ) :
    HasCompactSupport (cutoff V n) :=
  hV.isCompact_closure.of_isClosed_subset (isClosed_tsupport _) (tsupport_cutoff_subset V n)

/-- On an open set `V` with `Vᶜ ≠ ∅`, `χ_{V,n} = 1` eventually at each point of `V`. -/
lemma eventually_cutoff_eq_one {V : Set ℂ} (hV : IsOpen V) (hVc : Vᶜ.Nonempty) {u : ℂ} (hu : u ∈ V) :
    ∀ᶠ n in atTop, cutoff V n u = 1 := by
  have hpos : 0 < infDist u Vᶜ :=
    (hV.isClosed_compl.notMem_iff_infDist_pos hVc).1 fun h => h hu
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist u Vᶜ)
  refine eventually_atTop.2 ⟨N, fun n hn => min_eq_left ?_⟩
  have h1 : 1 < N * infDist u Vᶜ := by
    rwa [div_lt_iff₀ hpos] at hN
  have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (N : ℝ) * infDist u Vᶜ ≤ n * infDist u Vᶜ := mul_le_mul_of_nonneg_right h2 hpos.le
  have h4 : ((n : ℝ) + 1) * infDist u Vᶜ = n * infDist u Vᶜ + infDist u Vᶜ := by ring
  linarith

/-! ### A Fatou-type limit -/

/-- If `F_n ≤ f` and `F_n(u) = f(u)` eventually at each `u`, then `∫⁻ f = sup_n ∫⁻ F_n`. -/
lemma lintegral_eq_iSup_of_eventually_eq {m : Measure ℂ} {F : ℕ → ℂ → ℝ≥0∞} {f : ℂ → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) (hle : ∀ n u, F n u ≤ f u) (hev : ∀ u, ∀ᶠ n in atTop, F n u = f u) :
    ∫⁻ u, f u ∂m = ⨆ n, ∫⁻ u, F n u ∂m := by
  refine le_antisymm ?_ (iSup_le fun n => lintegral_mono (hle n))
  have hlim : ∀ u, liminf (fun n => F n u) atTop = f u := fun u => by
    rw [liminf_congr (hev u), liminf_const]
  calc ∫⁻ u, f u ∂m = ∫⁻ u, liminf (fun n => F n u) atTop ∂m := by simp_rw [hlim]
    _ ≤ liminf (fun n => ∫⁻ u, F n u ∂m) atTop := lintegral_liminf_le hF
    _ ≤ ⨆ n, ∫⁻ u, F n u ∂m := by
      rw [liminf_eq_iSup_iInf_of_nat]
      exact iSup_mono fun n => iInf₂_le n le_rfl

/-- `∫⁻ ofReal g dm = ofReal (∫ g dm)` for continuous compactly supported `g ≥ 0` and locally finite `m`. -/
lemma lintegral_ofReal_eq {m : Measure ℂ} [IsLocallyFiniteMeasure m] {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) :
    ∫⁻ u, ENNReal.ofReal (g u) ∂m = ENNReal.ofReal (∫ u, g u ∂m) :=
  (ofReal_integral_eq_lintegral_ofReal (hg.integrable_of_hasCompactSupport hgc)
    (Eventually.of_forall hg0)).symm

/-- **Measure of an open bounded set through cutoffs**: `m(V) = sup_l ofReal (∫ χ_{V,l} dm)`. -/
lemma measure_eq_iSup_cutoff {m : Measure ℂ} [IsLocallyFiniteMeasure m] {V : Set ℂ} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hVc : Vᶜ.Nonempty) :
    m V = ⨆ l, ENNReal.ofReal (∫ u, cutoff V l u ∂m) := by
  have h := lintegral_eq_iSup_of_eventually_eq (m := m) (F := fun l u => ENNReal.ofReal (cutoff V l u))
    (f := V.indicator 1) (fun l => (continuous_cutoff V l).measurable.ennreal_ofReal) (fun l u => ?_) (fun u => ?_)
  · rw [lintegral_indicator_one hV.measurableSet] at h
    rw [h]
    exact iSup_congr fun l => lintegral_ofReal_eq (continuous_cutoff V l) (hasCompactSupport_cutoff hVb l)
      (cutoff_nonneg V l)
  · by_cases hu : u ∈ V
    · rw [indicator_of_mem hu, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (cutoff_le_one V l u)
    · rw [cutoff_eq_zero hu, ENNReal.ofReal_zero]
      exact zero_le
  · by_cases hu : u ∈ V
    · filter_upwards [eventually_cutoff_eq_one hV hVc hu] with l hl
      rw [hl, ENNReal.ofReal_one, indicator_of_mem hu, Pi.one_apply]
    · exact Eventually.of_forall fun l => by
        rw [cutoff_eq_zero hu, ENNReal.ofReal_zero, indicator_of_notMem hu]

/-! ### The logarithmic integrand -/

/-- The integrand `(log (r / |u - v|) + 1)⁺` of `E_r(z)` ([C5]), in `[0, ∞)`. -/
noncomputable def logKernel (r : ℝ) (v u : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1)

/-- Continuous approximants `ℓ_{v,n}(u) = min((log (r / max(|u - v|, 1/(n+1))) + 1)⁺, 1 + (n+1)|u - v|)`. -/
noncomputable def logApprox (r : ℝ) (v : ℂ) (n : ℕ) (u : ℂ) : ℝ :=
  min (max 0 (Real.log (r / max ‖u - v‖ ((n : ℝ) + 1)⁻¹) + 1)) (1 + ((n : ℝ) + 1) * ‖u - v‖)

lemma logApprox_nonneg (r : ℝ) (v : ℂ) (n : ℕ) (u : ℂ) : 0 ≤ logApprox r v n u :=
  le_min (le_max_left _ _) (by positivity)

lemma continuous_logApprox {r : ℝ} (hr : 0 < r) (v : ℂ) (n : ℕ) : Continuous (logApprox r v n) := by
  have hmax : Continuous fun u : ℂ => max ‖u - v‖ ((n : ℝ) + 1)⁻¹ :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).max continuous_const
  have hpos : ∀ u : ℂ, 0 < max ‖u - v‖ ((n : ℝ) + 1)⁻¹ :=
    fun u => lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hdiv : Continuous fun u : ℂ => r / max ‖u - v‖ ((n : ℝ) + 1)⁻¹ :=
    continuous_const.div hmax fun u => (hpos u).ne'
  have hlog : Continuous fun u : ℂ => Real.log (r / max ‖u - v‖ ((n : ℝ) + 1)⁻¹) :=
    Real.continuousOn_log.comp_continuous hdiv fun u => (div_pos hr (hpos u)).ne'
  exact (continuous_const.max (hlog.add continuous_const)).min
    (continuous_const.add (continuous_const.mul (continuous_norm.comp (continuous_id.sub continuous_const))))

lemma ofReal_max_zero (a : ℝ) : ENNReal.ofReal (max 0 a) = ENNReal.ofReal a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_left h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_right h]

lemma logKernel_self (r : ℝ) (v : ℂ) : logKernel r v v = 1 := by
  simp [logKernel]

lemma ofReal_logApprox_le {r : ℝ} (hr : 0 < r) (v : ℂ) (n : ℕ) (u : ℂ) :
    ENNReal.ofReal (logApprox r v n u) ≤ logKernel r v u := by
  by_cases huv : u = v
  · subst huv
    rw [logKernel_self, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans ?_)
    simp
  · have hd : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
    rw [logKernel, ← ofReal_max_zero (Real.log (r / ‖u - v‖) + 1)]
    refine ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (max_le_max le_rfl ?_))
    have hm : 0 < max ‖u - v‖ ((n : ℝ) + 1)⁻¹ := lt_of_lt_of_le hd (le_max_left _ _)
    have : r / max ‖u - v‖ ((n : ℝ) + 1)⁻¹ ≤ r / ‖u - v‖ :=
      div_le_div_of_nonneg_left hr.le hd (le_max_left _ _)
    linarith [Real.log_le_log (div_pos hr hm) this]

lemma eventually_ofReal_logApprox_eq {r : ℝ} (hr : 0 < r) (v u : ℂ) :
    ∀ᶠ n in atTop, ENNReal.ofReal (logApprox r v n u) = logKernel r v u := by
  by_cases huv : u = v
  · subst huv
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / r)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    rw [logKernel_self, ← ENNReal.ofReal_one]
    congr 1
    have hn' : (1 : ℝ) / r < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hrn : 1 ≤ r * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hr] at hn'
      linarith
    have e : max ‖u - u‖ ((n : ℝ) + 1)⁻¹ = ((n : ℝ) + 1)⁻¹ := by
      rw [sub_self, norm_zero]
      exact max_eq_right (by positivity)
    have hlog : 0 ≤ Real.log (r / ((n : ℝ) + 1)⁻¹) := by
      rw [div_inv_eq_mul]
      exact Real.log_nonneg hrn
    unfold logApprox
    rw [e, sub_self, norm_zero, mul_zero, add_zero, max_eq_right (by linarith),
      min_eq_right (by linarith)]
  · have hd : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖u - v‖) (max 0 (Real.log (r / ‖u - v‖) + 1) / ‖u - v‖))
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hn' : max (1 / ‖u - v‖) (max 0 (Real.log (r / ‖u - v‖) + 1) / ‖u - v‖) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : ((n : ℝ) + 1)⁻¹ ≤ ‖u - v‖ := by
      rw [inv_le_comm₀ (by positivity) hd, ← one_div]
      exact (le_max_left _ _).trans hn'.le
    have h2 : max 0 (Real.log (r / ‖u - v‖) + 1) ≤ 1 + ((n : ℝ) + 1) * ‖u - v‖ := by
      have := (le_max_right _ _).trans hn'.le
      rw [div_le_iff₀ hd] at this
      linarith
    rw [logKernel, ← ofReal_max_zero (Real.log (r / ‖u - v‖) + 1)]
    simp only [logApprox, max_eq_left h1]
    rw [min_eq_left h2]

lemma measurable_logKernel (r : ℝ) (v : ℂ) : Measurable (logKernel r v) := by
  unfold logKernel
  fun_prop

lemma liminf_le_iSup_nat (f : ℕ → ℝ≥0∞) : liminf f atTop ≤ ⨆ n, f n := by
  rw [liminf_eq_iSup_iInf_of_nat]
  exact iSup_mono fun n => iInf₂_le n le_rfl

/-- `∫_V (log (r / |u - v|) + 1)⁺ dm(u) = sup_n ofReal (∫ χ_{V,n} ℓ_{v,n} dm)`. -/
lemma setLIntegral_logKernel_eq_iSup {m : Measure ℂ} [IsLocallyFiniteMeasure m] {V : Set ℂ} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (hVc : Vᶜ.Nonempty) {r : ℝ} (hr : 0 < r) (v : ℂ) :
    ∫⁻ u in V, logKernel r v u ∂m = ⨆ n, ENNReal.ofReal (∫ u, cutoff V n u * logApprox r v n u ∂m) := by
  rw [← lintegral_indicator hV.measurableSet]
  have h := lintegral_eq_iSup_of_eventually_eq (m := m)
    (F := fun n u => ENNReal.ofReal (cutoff V n u * logApprox r v n u)) (f := V.indicator (logKernel r v))
    (fun n => ((continuous_cutoff V n).mul (continuous_logApprox hr v n)).measurable.ennreal_ofReal)
    (fun n u => ?_) (fun u => ?_)
  · rw [h]
    exact iSup_congr fun n => lintegral_ofReal_eq ((continuous_cutoff V n).mul (continuous_logApprox hr v n))
      ((hasCompactSupport_cutoff hVb n).mul_right)
      fun u => mul_nonneg (cutoff_nonneg V n u) (logApprox_nonneg r v n u)
  · by_cases hu : u ∈ V
    · rw [indicator_of_mem hu]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_logApprox_le hr v n u)
      exact mul_le_of_le_one_left (logApprox_nonneg r v n u) (cutoff_le_one V n u)
    · rw [cutoff_eq_zero hu, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
  · by_cases hu : u ∈ V
    · filter_upwards [eventually_cutoff_eq_one hV hVc hu, eventually_ofReal_logApprox_eq hr v u] with n h1 h2
      rw [h1, one_mul, h2, indicator_of_mem hu]
    · exact Eventually.of_forall fun n => by
        rw [cutoff_eq_zero hu, zero_mul, ENNReal.ofReal_zero, indicator_of_notMem hu]

/-! ### The supremum over `v`: lower semicontinuity -/

lemma one_le_logKernel {r : ℝ} {u v : ℂ} (h : ‖u - v‖ ≤ r) : 1 ≤ logKernel r v u := by
  by_cases huv : u = v
  · rw [huv, logKernel_self]
  · have hd : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
    rw [logKernel, ENNReal.one_le_ofReal]
    have : 0 ≤ Real.log (r / ‖u - v‖) := Real.log_nonneg ((one_le_div hd).2 h)
    linarith

lemma tendsto_logKernel {r : ℝ} (hr : 0 < r) {u v : ℂ} (huv : u ≠ v) {vs : ℕ → ℂ}
    (hvs : Tendsto vs atTop (𝓝 v)) : Tendsto (fun j => logKernel r (vs j) u) atTop (𝓝 (logKernel r v u)) := by
  have hd : ‖u - v‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 huv)
  have hn : ContinuousAt (fun v' : ℂ => ‖u - v'‖) v :=
    (continuous_norm.comp (continuous_const.sub continuous_id)).continuousAt
  have hdiv : ContinuousAt (fun v' : ℂ => r / ‖u - v'‖) v := continuousAt_const.div hn hd
  have hlog : ContinuousAt (fun v' : ℂ => Real.log (r / ‖u - v'‖) + 1) v :=
    (ContinuousAt.comp (f := fun v' : ℂ => r / ‖u - v'‖) (Real.continuousAt_log (div_ne_zero hr.ne' hd))
      hdiv).add continuousAt_const
  exact (ENNReal.continuous_ofReal.continuousAt.comp hlog).tendsto.comp hvs

/-- **Lower semicontinuity in `v`** (Fatou): for `v ∈ V` open and `w` dense, the integral at `v` is at most the
supremum of the integrals at the points `w_i ∈ V`. -/
lemma setLIntegral_logKernel_le_iSup_dense {m : Measure ℂ} {V : Set ℂ} (hV : IsOpen V) {r : ℝ} (hr : 0 < r)
    {v : ℂ} (hv : v ∈ V) {w : ℕ → ℂ} (hw : DenseRange w) :
    ∫⁻ u in V, logKernel r v u ∂m ≤ ⨆ i, ⨆ (_ : w i ∈ V), ∫⁻ u in V, logKernel r (w i) u ∂m := by
  have hex : ∀ j : ℕ, ∃ i, w i ∈ V ∩ ball v (1 / ((j : ℝ) + 1)) := fun j =>
    hw.exists_mem_open (hV.inter isOpen_ball) ⟨v, hv, mem_ball_self (by positivity)⟩
  choose i hi using hex
  have hlim : Tendsto (fun j => w (i j)) atTop (𝓝 v) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun j => dist_nonneg)
      (fun j => (mem_ball.1 (hi j).2).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  have hpt : ∀ u, logKernel r v u ≤ liminf (fun j => logKernel r (w (i j)) u) atTop := by
    intro u
    by_cases huv : u = v
    · subst huv
      rw [logKernel_self]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hlim.eventually (ball_mem_nhds u hr)] with j hj
      refine one_le_logKernel ?_
      rw [← dist_eq_norm, dist_comm]
      exact (mem_ball.1 hj).le
    · exact ((tendsto_logKernel hr huv hlim).liminf_eq).ge
  calc ∫⁻ u in V, logKernel r v u ∂m
      ≤ ∫⁻ u in V, liminf (fun j => logKernel r (w (i j)) u) atTop ∂m := lintegral_mono hpt
    _ ≤ liminf (fun j => ∫⁻ u in V, logKernel r (w (i j)) u ∂m) atTop :=
        lintegral_liminf_le fun j => measurable_logKernel r _
    _ ≤ ⨆ j, ∫⁻ u in V, logKernel r (w (i j)) u ∂m := liminf_le_iSup_nat _
    _ ≤ ⨆ i, ⨆ (_ : w i ∈ V), ∫⁻ u in V, logKernel r (w i) u ∂m :=
        iSup_le fun j => le_iSup₂_of_le (f := fun i (_ : w i ∈ V) => ∫⁻ u in V, logKernel r (w i) u ∂m)
          (i j) (hi j).1 le_rfl

/-- The supremum over `v ∈ V` equals the supremum over the points of a dense sequence lying in `V`. -/
lemma iSup_setLIntegral_logKernel_eq_dense {m : Measure ℂ} {V : Set ℂ} (hV : IsOpen V) {r : ℝ} (hr : 0 < r)
    {w : ℕ → ℂ} (hw : DenseRange w) :
    ⨆ v ∈ V, ∫⁻ u in V, logKernel r v u ∂m = ⨆ i, ⨆ (_ : w i ∈ V), ∫⁻ u in V, logKernel r (w i) u ∂m :=
  le_antisymm (iSup₂_le fun _ hv => setLIntegral_logKernel_le_iSup_dense hV hr hv hw)
    (iSup₂_le fun i hi => le_iSup₂_of_le (f := fun v (_ : v ∈ V) => ∫⁻ u in V, logKernel r v u ∂m)
      (w i) hi le_rfl)

/-! ### The infimum over `w`: compactness -/

/-- **Infimum of ball masses over a compact set through a dense sequence.** With `δ_n = δ₀/(n+1)`,
`inf_{x ∈ K} m(B_ρ(x)) = sup_n inf {m(B_{ρ - 2δ_n}(w_i)) : dist(w_i, K) < δ_n}`. -/
lemma iInf_measure_ball_eq {m : Measure ℂ} {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) (ρ : ℝ)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {w : ℕ → ℂ} (hw : DenseRange w) :
    ⨅ x ∈ K, m (ball x ρ) =
      ⨆ n : ℕ, ⨅ i, ⨅ (_ : infDist (w i) K < δ₀ / ((n : ℝ) + 1)),
        m (ball (w i) (ρ - 2 * (δ₀ / ((n : ℝ) + 1)))) := by
  set δ : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδanti : ∀ {n k : ℕ}, n ≤ k → δ k ≤ δ n := fun {n k} hnk => by
    have : (n : ℝ) ≤ k := by exact_mod_cast hnk
    exact div_le_div_of_nonneg_left hδ₀.le (by positivity) (by linarith)
  refine le_antisymm ?_ (iSup_le fun n => le_iInf₂ fun x hx => ?_)
  swap
  · obtain ⟨i, hi⟩ := hw.exists_mem_open isOpen_ball ⟨x, mem_ball_self (hδpos n)⟩
    refine iInf₂_le_of_le i ((infDist_le_dist_of_mem hx).trans_lt (mem_ball.1 hi)) (measure_mono ?_)
    refine ball_subset_ball' ?_
    have := mem_ball.1 hi
    have := hδpos n
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs1, hs2⟩ := exists_between hcon
  have hn : ∀ n, ∃ i, infDist (w i) K < δ n ∧ m (ball (w i) (ρ - 2 * δ n)) < s := by
    intro n
    have h := (le_iSup (fun n : ℕ => ⨅ i, ⨅ (_ : infDist (w i) K < δ n), m (ball (w i) (ρ - 2 * δ n))) n).trans_lt hs1
    obtain ⟨i, hi⟩ := iInf_lt_iff.1 h
    obtain ⟨hc, hlt⟩ := iInf_lt_iff.1 hi
    exact ⟨i, hc, hlt⟩
  choose i hic his using hn
  have hy : ∀ n, ∃ y ∈ K, dist (w (i n)) y < δ n := fun n => (infDist_lt_iff hKne).1 (hic n)
  choose y hyK hyd using hy
  obtain ⟨y₀, hy₀K, φ, hφ, hφlim⟩ := hK.tendsto_subseq hyK
  -- every ball `B_{ρ - 3δ_N}(y₀)` has mass less than `s`
  have hN : ∀ N : ℕ, m (ball y₀ (ρ - 3 * δ N)) ≤ s := by
    intro N
    have h1 : ∀ᶠ j in atTop, dist (y (φ j)) y₀ < δ N / 2 :=
      (tendsto_iff_dist_tendsto_zero.1 hφlim).eventually (gt_mem_nhds (by linarith [hδpos N]))
    have h2 : ∀ᶠ j in atTop, 2 * N + 1 ≤ φ j := hφ.tendsto_atTop.eventually_ge_atTop _
    obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
    have hδj : δ (φ j) ≤ δ N / 2 := by
      have := hδanti hj2
      have e : δ (2 * N + 1) = δ N / 2 := by
        simp only [hδdef]
        push_cast
        field_simp
        ring
      linarith
    have hdj : dist y₀ (w (i (φ j))) < δ N := by
      have h3 := hyd (φ j)
      have h4 := dist_triangle y₀ (y (φ j)) (w (i (φ j)))
      rw [dist_comm (y (φ j)) (w (i (φ j)))] at h4
      rw [dist_comm] at hj1
      linarith
    refine (measure_mono (ball_subset_ball' ?_)).trans (his (φ j)).le
    have := hδpos N
    linarith
  have hU : ball y₀ ρ = ⋃ N : ℕ, ball y₀ (ρ - 3 * δ N) := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun N => ball_subset_ball (by linarith [hδpos N]))
    have hx' : 0 < ρ - dist x y₀ := by rw [mem_ball] at hx; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (3 * δ₀ / (ρ - dist x y₀))
    refine mem_iUnion.2 ⟨N, mem_ball.2 ?_⟩
    have h1 : 3 * δ₀ < N * (ρ - dist x y₀) := by rwa [div_lt_iff₀ hx'] at hN
    have h2 : 3 * δ N < ρ - dist x y₀ := by
      simp only [hδdef]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      have e : (ρ - dist x y₀) * ((N : ℝ) + 1) = N * (ρ - dist x y₀) + (ρ - dist x y₀) := by ring
      linarith
    linarith
  have hmono : Monotone fun N : ℕ => ball y₀ (ρ - 3 * δ N) := fun N N' hNN' =>
    ball_subset_ball (by linarith [hδanti hNN'])
  have hball : m (ball y₀ ρ) ≤ s := by
    rw [hU]
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hN
  exact absurd ((iInf₂_le y₀ hy₀K).trans hball) (not_le.2 hs2)

/-! ### The countable criterion -/

lemma ball_compl_nonempty (x : ℂ) (s : ℝ) : (ball x s)ᶜ.Nonempty := by
  refine ⟨x + ((|s| + 1 : ℝ) : ℂ), fun h => ?_⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
  linarith [le_abs_self s]

/-- The compact annuli `K_k = {r + r/(k+3) ≤ |x - z| ≤ 2r - r/(k+3)}` exhausting `𝔸_{r,2r}(z)`. -/
def compactAnnulus (z : ℂ) (r : ℝ) (k : ℕ) : Set ℂ :=
  closedBall z (2 * r - r / ((k : ℝ) + 3)) \ ball z (r + r / ((k : ℝ) + 3))

lemma isCompact_compactAnnulus (z : ℂ) (r : ℝ) (k : ℕ) : IsCompact (compactAnnulus z r k) :=
  (isCompact_closedBall z _).diff isOpen_ball

lemma compactAnnulus_nonempty (z : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) : (compactAnnulus z r k).Nonempty := by
  have hk : (3 : ℝ) ≤ (k : ℝ) + 3 := by
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have hη : r / ((k : ℝ) + 3) ≤ r / 3 := div_le_div_of_nonneg_left hr.le (by norm_num) hk
  refine ⟨z + ((3 * r / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith

lemma iUnion_compactAnnulus (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ⋃ k, compactAnnulus z r k = annulus z r (2 * r) := by
  refine Subset.antisymm (iUnion_subset fun k x hx => ?_) fun x hx => ?_
  · have hη : 0 < r / ((k : ℝ) + 3) := by positivity
    obtain ⟨h1, h2⟩ := hx
    rw [mem_closedBall] at h1
    rw [mem_ball, not_lt] at h2
    refine ⟨mem_ball.2 (by linarith), fun h => ?_⟩
    rw [mem_closedBall] at h
    linarith
  · obtain ⟨h1, h2⟩ := hx
    rw [mem_ball] at h1
    rw [mem_closedBall, not_le] at h2
    have hm : 0 < min (dist x z - r) (2 * r - dist x z) := lt_min (by linarith) (by linarith)
    obtain ⟨k, hk⟩ := exists_nat_gt (r / min (dist x z - r) (2 * r - dist x z))
    have hk' : r / ((k : ℝ) + 3) < min (dist x z - r) (2 * r - dist x z) := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hm] at hk
      have : min (dist x z - r) (2 * r - dist x z) * (k : ℝ) ≤
          min (dist x z - r) (2 * r - dist x z) * ((k : ℝ) + 3) := by
        have := hm.le
        nlinarith
      linarith
    refine mem_iUnion.2 ⟨k, mem_closedBall.2 ?_, fun h => ?_⟩
    · linarith [min_le_right (dist x z - r) (2 * r - dist x z)]
    · rw [mem_ball] at h
      linarith [min_le_left (dist x z - r) (2 * r - dist x z)]

/-- The countable index set: `inl (i, n)` for the supremum part, `inr (i, n, l)` for the infimum part. -/
abbrev Index : Type := (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ)

/-- The dense sequence of centres. -/
noncomputable abbrev pt (i : ℕ) : ℂ := TopologicalSpace.denseSeq ℂ i

open Classical in
/-- The test functions `g_j`: `χ_{𝔸,n} ℓ_{w_i,n}` (if `w_i ∈ 𝔸_{r,2r}(z)`) and `χ_{B(w_i, c₀r - 2δ_n), l}` (if
`B̄(w_i, c₀ r) ⊆ 𝔸_{r/3,3r}(z)`), with `δ_n = r/(10(n+1))`. -/
noncomputable def testFn (z : ℂ) (r c₀ : ℝ) : Index → ℂ → ℝ
  | .inl (i, n) => if pt i ∈ annulus z r (2 * r) then
      fun u => cutoff (annulus z r (2 * r)) n u * logApprox r (pt i) n u else 0
  | .inr (i, n, l) => if closedBall (pt i) (c₀ * r) ⊆ annulus z (r / 3) (3 * r) then
      cutoff (ball (pt i) (c₀ * r - 2 * (r / 10 / ((n : ℝ) + 1)))) l else 0

/-- The supremum part of the criterion. -/
noncomputable def supPart (q : Index → ℝ) : ℝ≥0∞ := ⨆ i, ⨆ n, ENNReal.ofReal (q (.inl (i, n)))

/-- The infimum part of the criterion. -/
noncomputable def infPart (z : ℂ) (r : ℝ) (q : Index → ℝ) : ℝ≥0∞ :=
  ⨅ k, ⨆ n : ℕ, ⨅ i, ⨅ (_ : infDist (pt i) (compactAnnulus z r k) < r / 10 / ((n : ℝ) + 1)),
    ⨆ l, ENNReal.ofReal (q (.inr (i, n, l)))

/-- The criterion set. -/
def criterion (z : ℂ) (r C : ℝ) : Set (Index → ℝ) := {q | supPart q ≤ ENNReal.ofReal C * infPart z r q}

lemma measurableSet_criterion (z : ℂ) (r C : ℝ) : MeasurableSet (criterion z r C) := by
  have hS : Measurable supPart :=
    Measurable.iSup fun i => Measurable.iSup fun n =>
      ENNReal.measurable_ofReal.comp (measurable_pi_apply (Sum.inl (i, n)))
  have hI : Measurable (infPart z r) :=
    Measurable.iInf fun k => Measurable.iSup fun n => Measurable.iInf fun i => Measurable.iInf_Prop _
      (Measurable.iSup fun l => ENNReal.measurable_ofReal.comp (measurable_pi_apply (Sum.inr (i, n, l))))
  exact measurableSet_le hS (measurable_const.mul hI)

lemma closure_annulus_subset (z : ℂ) (r : ℝ) :
    closure (annulus z r (2 * r)) ⊆ closedBall z (2 * r) \ ball z r :=
  closure_minimal (fun _ hx => ⟨ball_subset_closedBall hx.1, fun h => hx.2 (ball_subset_closedBall h)⟩)
    (isClosed_closedBall.sdiff isOpen_ball)

lemma closedBall_subset_of_infDist {z : ℂ} {r c₀ : ℝ} (hr : 0 < r) (hc₀' : c₀ < 1 / 5) {k n i : ℕ}
    (h : infDist (pt i) (compactAnnulus z r k) < r / 10 / ((n : ℝ) + 1)) :
    closedBall (pt i) (c₀ * r) ⊆ annulus z (r / 3) (3 * r) := by
  have hδ : r / 10 / ((n : ℝ) + 1) ≤ r / 10 := div_le_self (by positivity) (by linarith [n.cast_nonneg (α := ℝ)])
  obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff (compactAnnulus_nonempty z hr k)).1 h
  have hη : 0 < r / ((k : ℝ) + 3) := by positivity
  obtain ⟨hy1, hy2⟩ := hy
  rw [mem_closedBall] at hy1
  rw [mem_ball, not_lt] at hy2
  have hc : c₀ * r < r / 5 := by nlinarith
  intro x hx
  rw [mem_closedBall] at hx
  have t1 := dist_triangle x (pt i) z
  have t2 := dist_triangle (pt i) y z
  have t3 := dist_triangle y (pt i) z
  have t4 := dist_triangle y x z
  rw [dist_comm y (pt i)] at t3
  have t5 := dist_triangle (pt i) x z
  rw [dist_comm (pt i) x] at t5
  refine ⟨mem_ball.2 (by linarith), fun h' => ?_⟩
  rw [mem_closedBall] at h'
  linarith

/-- **The countable criterion for `E_r(z; C)`.** For locally finite `m`, `E_r(z; C)` occurs for `m` iff the family of
integrals `(∫ g_j dm)_j` lies in the measurable set `criterion z r C`. -/
theorem isGoodAnnulusEvent_iff_criterion {r c₀ : ℝ} (hr : 0 < r) (hc₀' : c₀ < 1 / 5) (C : ℝ) (z : ℂ)
    (m : Measure ℂ) [IsLocallyFiniteMeasure m] :
    IsGoodAnnulusEvent m c₀ C r z ↔ (fun j => ∫ u, testFn z r c₀ j u ∂m) ∈ criterion z r C := by
  set A := annulus z r (2 * r) with hAdef
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAb : Bornology.IsBounded A := isBounded_ball.subset sdiff_subset
  have hAc : Aᶜ.Nonempty := ⟨z, fun h => h.2 (mem_closedBall_self hr.le)⟩
  have hw : DenseRange pt := TopologicalSpace.denseRange_denseSeq ℂ
  -- the supremum part
  have hS : supPart (fun j => ∫ u, testFn z r c₀ j u ∂m) =
      ⨆ v ∈ A, ∫⁻ u in A, logKernel r v u ∂m := by
    rw [iSup_setLIntegral_logKernel_eq_dense hAo hr hw]
    refine iSup_congr fun i => ?_
    by_cases hi : pt i ∈ A
    · rw [iSup_pos hi, setLIntegral_logKernel_eq_iSup hAo hAb hAc hr]
      refine iSup_congr fun n => ?_
      simp only [testFn, ← hAdef, hi, ↓reduceIte]
    · rw [iSup_neg hi]
      simp only [testFn, ← hAdef, hi, ↓reduceIte, Pi.zero_apply, integral_zero, ENNReal.ofReal_zero,
        iSup_const, bot_eq_zero]
  -- the infimum part
  have hI : infPart z r (fun j => ∫ u, testFn z r c₀ j u ∂m) = ⨅ x ∈ A, m (ball x (c₀ * r)) := by
    rw [hAdef, ← iUnion_compactAnnulus z hr, iInf_iUnion]
    refine iInf_congr fun k => ?_
    rw [iInf_measure_ball_eq (isCompact_compactAnnulus z r k) (compactAnnulus_nonempty z hr k) (c₀ * r)
      (by positivity : (0 : ℝ) < r / 10) hw]
    refine iSup_congr fun n => iInf_congr fun i => iInf_congr fun hc => ?_
    have hsub := closedBall_subset_of_infDist hr hc₀' hc
    rw [measure_eq_iSup_cutoff isOpen_ball isBounded_ball (ball_compl_nonempty _ _)]
    refine iSup_congr fun l => ?_
    simp only [testFn, hsub, ↓reduceIte]
  unfold IsGoodAnnulusEvent
  rw [← hAdef]
  show _ ↔ supPart _ ≤ ENNReal.ofReal C * infPart z r _
  rw [hS, hI]
  exact Iff.rfl

lemma testFn_properties {r c₀ : ℝ} (hr : 0 < r) (z : ℂ) (j : Index) :
    Continuous (testFn z r c₀ j) ∧ HasCompactSupport (testFn z r c₀ j) ∧
      tsupport (testFn z r c₀ j) ⊆ annulus z (r / 3) (3 * r) := by
  have hAb : Bornology.IsBounded (annulus z r (2 * r)) := isBounded_ball.subset sdiff_subset
  rcases j with ⟨i, n⟩ | ⟨i, n, l⟩
  · by_cases hi : pt i ∈ annulus z r (2 * r)
    · simp only [testFn, hi, ↓reduceIte]
      refine ⟨(continuous_cutoff _ n).mul (continuous_logApprox hr _ n),
        (hasCompactSupport_cutoff hAb n).mul_right, ?_⟩
      refine (tsupport_mul_subset_left).trans ((tsupport_cutoff_subset _ n).trans
        ((closure_annulus_subset z r).trans fun x hx => ?_))
      obtain ⟨h1, h2⟩ := hx
      rw [mem_closedBall] at h1
      rw [mem_ball, not_lt] at h2
      refine ⟨mem_ball.2 (by linarith), fun h => ?_⟩
      rw [mem_closedBall] at h
      linarith
    · simp only [testFn, hi, ↓reduceIte]
      exact ⟨continuous_zero, HasCompactSupport.zero, by simp⟩
  · by_cases hi : closedBall (pt i) (c₀ * r) ⊆ annulus z (r / 3) (3 * r)
    · simp only [testFn, hi, ↓reduceIte]
      refine ⟨continuous_cutoff _ l, hasCompactSupport_cutoff isBounded_ball l,
        (tsupport_cutoff_subset _ l).trans (closure_ball_subset_closedBall.trans
          ((closedBall_subset_closedBall ?_).trans hi))⟩
      have : 0 ≤ r / 10 / ((n : ℝ) + 1) := by positivity
      linarith
    · simp only [testFn, hi, ↓reduceIte]
      exact ⟨continuous_zero, HasCompactSupport.zero, by simp⟩

end AnnulusEventCountable

end MatedCRT
