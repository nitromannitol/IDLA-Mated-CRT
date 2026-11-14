import MatedCRT.FirstPass.Derived.BrownianTemplateEvent
import MatedCRT.FirstPass.Derived.BrownianDiscPoissonExit
import MatedCRT.FirstPass.Derived.BrownianExitPointRestart

/-!
# The template tube at dyadic scales

Step (A6) of the Brownian disconnection estimate behind the invariance principle of
Gwynne-Miller-Sheffield (Lemma 3.14 (a)).

Let `r_k = 4^{-k}` (`templateRadius k`) and `p₀ = templateTubeConst`. For planar Brownian motion
started from `0`, the events `exitTemplateTube r_k` (after its exit time `τ_k` from the disc of
radius `r_k`, the path follows the template moved to radius `r_k` for a time `r_k²`) all fail
for `k = j, ..., j + n - 1` with probability at most `(1 - p₀)^n`.

* `measurableSet_templateTube`: the template tube is a Borel event of the path.
* `planarBrownianMotion_templateTube_compl_le`: from a point of the circle of radius `r`, the
  tube fails with probability at most `1 - p₀` (the tube estimate at the start point).
* `planarBrownianMotion_inter_shift_preimage_le`: the strong Markov property at a stopping time
  `τ`, in the form of a bound: for an event `H` of the stopped σ-algebra, the probability that
  `H` holds, `τ` is finite and the path restarted at `τ` lies in `B` is at most `c · P(H)` when
  `P_x(B) ≤ c` at every possible position `x` of the path at time `τ`.
* `planarBrownianMotion_inter_exitTemplateTube_compl_le`: one scale costs the factor `1 - p₀`
  against every event of the stopped σ-algebra at `τ_r`.
* `planarBrownianMotion_iInter_exitTemplateTube_compl_le`: the bound `(1 - p₀)^n` for `n`
  consecutive scales, by induction from the smallest scale outwards: the template tubes of the
  smaller discs are events of the stopped σ-algebra at the exit time of a larger disc (step A5).
* `planarBrownianMotion_iInter_templatePieceEvent_compl_le`: the template-piece events at the
  scales `r_1, ..., r_K` all fail with probability at most `(1 - p₀)^K` (step A4).

Step (A7): with `K(δ) = ⌊log₄ (3 / (4δ))⌋` (`templateScaleCount δ`, at least `1` for
`0 < δ < 3/16`, and `δ ≤ 3 r_k / 4` for `1 ≤ k ≤ K(δ)`), the robust disconnection event
`templateDisconnectionEvent δ` (`E_δ`: a template piece at some scale `r_k`, `1 ≤ k ≤ K(δ)`)
has probability at least `1 - (1 - p₀)^{K(δ)}` under planar Brownian motion from `0`
(`one_sub_le_planarBrownianMotion_templateDisconnectionEvent`, no measurability of `E_δ` needed),
which tends to `1` as `δ → 0⁺` (`tendsto_planarBrownianMotion_templateDisconnectionEvent`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6
open MatedCRTHarmonic.CellularEmbedding

namespace MatedCRT

/-- The template tube is a Borel event of the path. -/
theorem measurableSet_templateTube (r : ℝ≥0) : MeasurableSet (templateTube r) := by
  unfold templateTube
  refine measurableSet_forall_le_lt_of_continuous _ (r ^ 2)
    (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) =>
      ‖ω t - movedTemplate 0 r (Complex.arg (ω 0)) ((t : ℝ) / (r : ℝ) ^ 2)‖)
    (fun t _ => ?_) (fun ω => ?_) _
  · have h1 : Measurable fun ω : ContinuousPath ℂ => ω t := (continuous_eval_const t).measurable
    have h0 : Measurable fun ω : ContinuousPath ℂ => ω 0 := (continuous_eval_const 0).measurable
    have h2 : Measurable fun ω : ContinuousPath ℂ =>
        movedTemplate 0 r (Complex.arg (ω 0)) ((t : ℝ) / (r : ℝ) ^ 2) :=
      ((continuous_movedTemplate_left 0 r _).measurable.comp Complex.measurable_arg).comp h0
    exact (h1.sub h2).norm
  · exact (ω.continuous.sub ((continuous_movedTemplate_right 0 r _).comp
      (NNReal.continuous_coe.div_const _))).norm

/-- **One scale, from the circle.** From a point of the circle of radius `r > 0` about `0`,
planar Brownian motion leaves the template tube with probability at most
`1 - templateTubeConst`. -/
theorem planarBrownianMotion_templateTube_compl_le {r : ℝ≥0} (hr : 0 < r) {x : ℂ}
    (hx : ‖x‖ = r) :
    planarBrownianMotion x (templateTube r)ᶜ ≤ 1 - templateTubeConst := by
  rw [prob_compl_eq_one_sub (measurableSet_templateTube r)]
  refine tsub_le_tsub_left ?_ 1
  refine (templateTubeConst_le_planarBrownianMotion hr hx).trans (measure_mono_ae ?_)
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω hω h
  intro t ht
  rw [hω]
  exact h t ht

/-- **Restart bound at a stopping time** (strong Markov property). Let `τ` be a stopping time of
the canonical filtration and `H` an event of its stopped σ-algebra. If planar Brownian motion
started from any point of `S` lies in `B` with probability at most `c`, and the path started
from `y` is almost surely in `S` at time `τ`, then the probability that `H` holds, `τ` is finite
and the path restarted at `τ` lies in `B` is at most `c · P_y(H)`. -/
theorem planarBrownianMotion_inter_shift_preimage_le {y : ℂ}
    {τ : ContinuousPath ℂ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) τ)
    {H : Set (ContinuousPath ℂ)} (hH : MeasurableSet[hτ.measurableSpace] H)
    {B : Set (ContinuousPath ℂ)} (hB : MeasurableSet B) {S : Set ℂ} {c : ℝ≥0∞}
    (hS : ∀ x ∈ S, planarBrownianMotion x B ≤ c)
    (hpt : ∀ᵐ ω ∂(planarBrownianMotion y), ω ((τ ω).untopD 0) ∈ S) :
    planarBrownianMotion y (H ∩ {ω | τ ω < ⊤} ∩
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' B) ≤
      c * planarBrownianMotion y H := by
  have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      y τ hτ H hH
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m B) hrestart
  rw [Measure.map_apply hshift hB, Measure.restrict_apply (hshift hB),
    Measure.bind_apply hB (Kernel.aemeasurable _)] at happ
  simp only [Kernel.comap_apply] at happ
  calc
    planarBrownianMotion y (H ∩ {ω | τ ω < ⊤} ∩
        (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' B)
        = planarBrownianMotion y ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' B ∩
          (H ∩ {ω | τ ω < ⊤})) := by rw [inter_comm]
    _ = ∫⁻ ω, planarBrownianMotion (ω ((τ ω).untopD 0)) B
          ∂((planarBrownianMotion y).restrict (H ∩ {ω | τ ω < ⊤})) := happ
    _ ≤ ∫⁻ _, c ∂((planarBrownianMotion y).restrict (H ∩ {ω | τ ω < ⊤})) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_of_ae hpt] with ω h1
      exact hS _ h1
    _ = c * planarBrownianMotion y (H ∩ {ω | τ ω < ⊤}) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ c * planarBrownianMotion y H := by
      gcongr
      exact inter_subset_left

/-- **One scale at its exit time.** For `r > 0` and an event `H` of the stopped σ-algebra at the
exit time `τ_r` of the disc of radius `r`, planar Brownian motion from `0` satisfies `H` and fails
the template tube at `τ_r` with probability at most `(1 - templateTubeConst) · P_0(H)`. -/
theorem planarBrownianMotion_inter_exitTemplateTube_compl_le {r : ℝ≥0} (hr : 0 < r)
    {H : Set (ContinuousPath ℂ)}
    (hH : MeasurableSet[(isStoppingTime_discExitTime r).measurableSpace] H) :
    planarBrownianMotion 0 (H ∩ (exitTemplateTube r)ᶜ) ≤
      (1 - templateTubeConst) * planarBrownianMotion 0 H := by
  have hr' : (0 : ℝ) < r := hr
  have hae := ae_planarBrownian_disc_exitPoint_mem_sphere (c := 0) (y := 0) (r := r)
    (mem_ball_self hr')
  have hstep := planarBrownianMotion_inter_shift_preimage_le (isStoppingTime_discExitTime r) hH
    (measurableSet_templateTube r).compl (S := sphere 0 r) (c := 1 - templateTubeConst)
    (fun x hx => planarBrownianMotion_templateTube_compl_le hr (mem_sphere_zero_iff_norm.mp hx))
    (hae.mono fun ω hω => hω.2)
  refine le_trans (measure_mono_ae ?_) hstep
  filter_upwards [hae] with ω hω h
  obtain ⟨hH', hc⟩ := h
  have hlt : discExitTime r ω < ⊤ := lt_top_iff_ne_top.mpr hω.1
  exact ⟨⟨hH', hlt⟩, fun hT => hc ⟨hlt, hT⟩⟩

/-- The dyadic radii `r_k = 4^{-k}` of the template scales. -/
noncomputable def templateRadius (k : ℕ) : ℝ≥0 :=
  (4 : ℝ≥0)⁻¹ ^ k

theorem templateRadius_pos (k : ℕ) : 0 < templateRadius k :=
  pow_pos (inv_pos.mpr (by norm_num)) k

theorem coe_templateRadius (k : ℕ) : (templateRadius k : ℝ) = (1 / 4 : ℝ) ^ k := by
  simp [templateRadius]

/-- A smaller template scale fits, with its tube, inside a larger one: for `j < k`,
`11 r_k / 10 + r_k / 2000 ≤ r_j`. -/
theorem templateRadius_le_of_lt {j k : ℕ} (hjk : j < k) :
    11 / 10 * (templateRadius k : ℝ) + templateRadius k / 2000 ≤ templateRadius j := by
  rw [coe_templateRadius, coe_templateRadius]
  have h1 : (1 / 4 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ (j + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_of_lt hjk)
  have h2 : (1 / 4 : ℝ) ^ (j + 1) = (1 / 4 : ℝ) ^ j / 4 := by
    rw [pow_succ]; ring
  have h0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
  rw [h2] at h1
  linarith

/-- **(A6) The template tube fails at `n` consecutive scales with probability at most
`(1 - p₀)^n`.** For planar Brownian motion from `0` and all `j, n`, the events
`exitTemplateTube r_k`, `j ≤ k < j + n`, all fail with probability at most
`(1 - templateTubeConst)^n`. -/
theorem planarBrownianMotion_iInter_exitTemplateTube_compl_le (j n : ℕ) :
    planarBrownianMotion 0
        (⋂ k ∈ Finset.Ico j (j + n), (exitTemplateTube (templateRadius k))ᶜ) ≤
      (1 - templateTubeConst) ^ n := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    have hset : (⋂ k ∈ Finset.Ico j (j + (n + 1)), (exitTemplateTube (templateRadius k))ᶜ) =
        (⋂ k ∈ Finset.Ico (j + 1) (j + 1 + n), (exitTemplateTube (templateRadius k))ᶜ) ∩
          (exitTemplateTube (templateRadius j))ᶜ := by
      ext ω
      simp only [mem_iInter, Finset.mem_Ico, mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun k hk => h k ⟨by omega, by omega⟩, h j ⟨le_rfl, by omega⟩⟩
      · rintro ⟨h, hj⟩ k hk
        rcases eq_or_lt_of_le hk.1 with rfl | hlt
        · exact hj
        · exact h k ⟨by omega, by omega⟩
    have hH : MeasurableSet[(isStoppingTime_discExitTime (templateRadius j)).measurableSpace]
        (⋂ k ∈ Finset.Ico (j + 1) (j + 1 + n), (exitTemplateTube (templateRadius k))ᶜ) := by
      refine Finset.measurableSet_biInter _ fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      exact (measurableSet_exitTemplateTube (templateRadius_le_of_lt (by omega))).compl
    rw [hset, pow_succ']
    calc _ ≤ (1 - templateTubeConst) * planarBrownianMotion 0
          (⋂ k ∈ Finset.Ico (j + 1) (j + 1 + n), (exitTemplateTube (templateRadius k))ᶜ) :=
          planarBrownianMotion_inter_exitTemplateTube_compl_le (templateRadius_pos j) hH
      _ ≤ (1 - templateTubeConst) * (1 - templateTubeConst) ^ n := by
          gcongr
          exact ih (j + 1)

/-- **(A6) at the scales `r_1, ..., r_K`.** -/
theorem planarBrownianMotion_iInter_Icc_exitTemplateTube_compl_le (K : ℕ) :
    planarBrownianMotion 0
        (⋂ k ∈ Finset.Icc 1 K, (exitTemplateTube (templateRadius k))ᶜ) ≤
      (1 - templateTubeConst) ^ K := by
  have hI : Finset.Ico 1 (1 + K) = Finset.Icc 1 K := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [← hI]
  exact planarBrownianMotion_iInter_exitTemplateTube_compl_le 1 K

/-- **The template-piece events fail at the scales `r_1, ..., r_K` with probability at most
`(1 - p₀)^K`**, by step (A4): for `k ≥ 1`, `r_k ≤ 1/4`, so the template tube at `τ_{r_k}` gives
the template-piece event at scale `r_k`. -/
theorem planarBrownianMotion_iInter_templatePieceEvent_compl_le (K : ℕ) :
    planarBrownianMotion 0
        (⋂ k ∈ Finset.Icc 1 K, (templatePieceEvent (templateRadius k))ᶜ) ≤
      (1 - templateTubeConst) ^ K := by
  refine le_trans (measure_mono ?_) (planarBrownianMotion_iInter_Icc_exitTemplateTube_compl_le K)
  refine iInter₂_mono fun k hk => compl_subset_compl.mpr ?_
  rw [Finset.mem_Icc] at hk
  refine exitTemplateTube_subset_templatePieceEvent (templateRadius_pos k) ?_
  rw [coe_templateRadius]
  exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)

/-- **Number of template scales** for the inner radius `δ`: `K(δ) = ⌊log₄ (3 / (4δ))⌋`. -/
noncomputable def templateScaleCount (δ : ℝ) : ℕ :=
  ⌊Real.logb 4 (3 / (4 * δ))⌋₊

/-- For `0 < δ < 3/16` there is at least one template scale. -/
theorem one_le_templateScaleCount {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 / 16) :
    1 ≤ templateScaleCount δ := by
  apply Nat.le_floor
  rw [Nat.cast_one, Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one,
    le_div_iff₀ (by positivity)]
  linarith

/-- The template scales stay outside the inner disc: `δ ≤ 3 r_k / 4` for `1 ≤ k ≤ K(δ)`. -/
theorem le_templateRadius_of_le_templateScaleCount {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ templateScaleCount δ) : δ ≤ 3 / 4 * (templateRadius k : ℝ) := by
  rw [templateScaleCount, Nat.le_floor_iff' (by omega),
    Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast,
    le_div_iff₀ (by positivity)] at hk
  rw [coe_templateRadius, one_div_pow,
    show (3 : ℝ) / 4 * (1 / 4 ^ k) = 3 / (4 * 4 ^ k) by ring, le_div_iff₀ (by positivity)]
  calc δ * (4 * 4 ^ k) = 4 ^ k * (4 * δ) := by ring
    _ ≤ 3 := hk

/-- **The robust disconnection event** `E_δ`: at some scale `r_k`, `1 ≤ k ≤ K(δ)`, a piece of the
path, before it leaves the disc of radius `1/2`, follows the polar template moved to radius `r_k`
within Fréchet distance `r_k / 2000`. -/
def templateDisconnectionEvent (δ : ℝ) : Set (ContinuousPath ℂ) :=
  ⋃ k ∈ Finset.Icc 1 (templateScaleCount δ), templatePieceEvent (templateRadius k)

/-- **(A7) Lower bound for the robust disconnection event.** Planar Brownian motion from `0` lies
in `E_δ` with (outer) probability at least `1 - (1 - templateTubeConst)^{K(δ)}`. -/
theorem one_sub_le_planarBrownianMotion_templateDisconnectionEvent (δ : ℝ) :
    1 - (1 - templateTubeConst) ^ templateScaleCount δ ≤
      planarBrownianMotion 0 (templateDisconnectionEvent δ) := by
  set E := templateDisconnectionEvent δ with hE
  have hc : Eᶜ = ⋂ k ∈ Finset.Icc 1 (templateScaleCount δ),
      (templatePieceEvent (templateRadius k))ᶜ := by
    simp only [hE, templateDisconnectionEvent, compl_iUnion]
  have h1 : (1 : ℝ≥0∞) ≤ planarBrownianMotion 0 E + planarBrownianMotion 0 Eᶜ := by
    calc (1 : ℝ≥0∞) = planarBrownianMotion 0 (E ∪ Eᶜ) := by rw [union_compl_self, measure_univ]
      _ ≤ _ := measure_union_le _ _
  rw [tsub_le_iff_right]
  calc 1 ≤ planarBrownianMotion 0 E + planarBrownianMotion 0 Eᶜ := h1
    _ ≤ planarBrownianMotion 0 E + (1 - templateTubeConst) ^ templateScaleCount δ := by
      gcongr
      rw [hc]
      exact planarBrownianMotion_iInter_templatePieceEvent_compl_le _

/-- **(A7) The robust disconnection event is almost sure in the limit**: its probability under
planar Brownian motion from `0` tends to `1` as `δ → 0⁺`. -/
theorem tendsto_planarBrownianMotion_templateDisconnectionEvent :
    Filter.Tendsto (fun δ : ℝ => planarBrownianMotion 0 (templateDisconnectionEvent δ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hlt : 1 - templateTubeConst < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero templateTubeConst_pos.ne'
  have h1 : Filter.Tendsto (fun δ : ℝ => 3 / (4 * δ)) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
    refine ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
      (show (0 : ℝ) < 3 / 4 by norm_num)).congr fun δ => ?_
    ring
  have hK : Filter.Tendsto templateScaleCount (nhdsWithin 0 (Ioi 0)) Filter.atTop :=
    tendsto_nat_floor_atTop.comp ((Real.tendsto_logb_atTop (by norm_num)).comp h1)
  have hpow : Filter.Tendsto (fun δ : ℝ => (1 - templateTubeConst) ^ templateScaleCount δ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt).comp hK
  have hlow : Filter.Tendsto (fun δ : ℝ => 1 - (1 - templateTubeConst) ^ templateScaleCount δ)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hpow (Or.inl ENNReal.one_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun δ => one_sub_le_planarBrownianMotion_templateDisconnectionEvent δ) (fun _ => prob_le_one)

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.measurableSet_templateTube
#print axioms MatedCRT.planarBrownianMotion_templateTube_compl_le
#print axioms MatedCRT.planarBrownianMotion_inter_shift_preimage_le
#print axioms MatedCRT.planarBrownianMotion_inter_exitTemplateTube_compl_le
#print axioms MatedCRT.planarBrownianMotion_iInter_exitTemplateTube_compl_le
#print axioms MatedCRT.planarBrownianMotion_iInter_Icc_exitTemplateTube_compl_le
#print axioms MatedCRT.planarBrownianMotion_iInter_templatePieceEvent_compl_le
#print axioms MatedCRT.one_le_templateScaleCount
#print axioms MatedCRT.le_templateRadius_of_le_templateScaleCount
#print axioms MatedCRT.one_sub_le_planarBrownianMotion_templateDisconnectionEvent
#print axioms MatedCRT.tendsto_planarBrownianMotion_templateDisconnectionEvent
