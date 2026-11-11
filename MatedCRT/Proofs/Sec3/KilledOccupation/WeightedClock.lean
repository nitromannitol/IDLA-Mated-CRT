import Mathlib
import MarkovProcess.Path.Basic

/-!
# The weighted clock `Φ` and its quenched mean (Appendix B, step S4)

Source: `paper/appendix-occupation-C16.tex`, eq:occ-weightedclock (line 275), eq:occ-weightedmean
(lines 277-281), and the continuity and monotonicity paragraph (lines 283-290).

Notation: `dA` is the clock measure (the Lebesgue-Stieltjes measure of the base clock `A` of
Lemma lem:occ-base), `B` is a planar Brownian path, `σ` is its exit time from `D`, and
`μ_h = |x|^{-γ²} ν` on `B_1` (eq:occ-weight, step S2) is taken as the hypothesis `hweight`.
The Green function `G` of `D` is a parameter with `G ≥ 0` on `D` (`hGnn`).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

/-- The weight `x ↦ |x|^{-γ²}` of eq:occ-weightedclock, as an `ℝ≥0∞`-valued function. At `x = 0`
Lean's real power takes the junk value `0`; this is harmless, because the clock measure charges no
time at which the path is `0` (lem:occ-base with `q = 1_{0}`, paper line 275-276). -/
noncomputable def gammaWeight (γ : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖x‖ ^ (-(γ ^ 2)))

/-- The weighted clock `Φ(s) = ∫_0^{s ∧ σ} w(B_u) dA(u)` (paper eq:occ-weightedclock, line 275).
`dA` is the clock measure, `w` is the weight evaluated along the path, `σ` is the exit time. -/
noncomputable def weightedClock (dA : Measure ℝ≥0) (w : ℝ≥0 → ℝ≥0∞) (σ s : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (min s σ), w u ∂dA

theorem measurable_gammaWeight (γ : ℝ) : Measurable (gammaWeight γ) :=
  ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)

/-- `Φ(0) = 0` (paper line 283-290: no clock atom at `0`). -/
theorem weightedClock_zero {dA : Measure ℝ≥0} [NullSingletonClass dA] (w : ℝ≥0 → ℝ≥0∞) (σ : ℝ≥0) :
    weightedClock dA w σ 0 = 0 := by
  unfold weightedClock
  rw [min_eq_left (zero_le), Icc_self]
  exact setLIntegral_measure_zero _ _ (measure_singleton 0)

/-- `Φ` is nondecreasing in the time `s` (paper line 283-290). -/
theorem weightedClock_mono (dA : Measure ℝ≥0) (w : ℝ≥0 → ℝ≥0∞) (σ : ℝ≥0) :
    Monotone (weightedClock dA w σ) := fun _ _ hst =>
  lintegral_mono_set (Icc_subset_Icc le_rfl (min_le_min hst le_rfl))

/-- `Φ` is continuous when `dA` has no atoms and `Φ(σ) < ∞` (paper line 283-290: `dΦ` is absolutely
continuous with respect to the atomless measure `dA`). Proof: dominated convergence for the indicators
`1_{[0, s ∧ σ]} w`, which converge off the single point `s ∧ σ`. -/
theorem weightedClock_continuous {dA : Measure ℝ≥0} [NullSingletonClass dA] {w : ℝ≥0 → ℝ≥0∞}
    (hw : Measurable w) (σ : ℝ≥0) (hfin : weightedClock dA w σ σ ≠ ⊤) :
    Continuous (weightedClock dA w σ) := by
  have key : ∀ t, weightedClock dA w σ t = ∫⁻ u, (Icc 0 (min t σ)).indicator w u ∂dA := by
    intro t
    unfold weightedClock
    rw [lintegral_indicator measurableSet_Icc]
  have hbd : ∫⁻ u, (Icc 0 σ).indicator w u ∂dA ≠ ⊤ := by
    have h := key σ
    rw [min_self] at h
    rw [← h]
    exact hfin
  have hcont : Continuous fun t : ℝ≥0 => min t σ := continuous_id.min continuous_const
  have hfun : weightedClock dA w σ = fun t => ∫⁻ u, (Icc 0 (min t σ)).indicator w u ∂dA := funext key
  refine continuous_iff_continuousAt.2 fun s => ?_
  unfold ContinuousAt
  rw [hfun]
  dsimp only
  refine tendsto_lintegral_filter_of_dominated_convergence (l := 𝓝 s) (fun u => (Icc 0 σ).indicator w u)
    (Eventually.of_forall fun t => hw.indicator measurableSet_Icc) ?_ hbd ?_
  · refine Eventually.of_forall fun t => ae_of_all _ fun u => ?_
    exact indicator_le_indicator_of_subset (Icc_subset_Icc le_rfl (min_le_right _ _))
      (fun _ => zero_le) u
  · have hae : ∀ᵐ u ∂dA, u ≠ min s σ := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with u hu
    rcases lt_or_gt_of_ne hu with h | h
    · have hev : ∀ᶠ t in 𝓝 s, u < min t σ := (hcont.tendsto s).eventually_const_lt h
      have hev' : (fun t : ℝ≥0 => (Icc (0 : ℝ≥0) (min t σ)).indicator w u) =ᶠ[𝓝 s]
          fun _ => w u := by
        filter_upwards [hev] with t ht
        exact indicator_of_mem (show u ∈ Icc (0 : ℝ≥0) (min t σ) from ⟨zero_le, ht.le⟩) w
      have hs : (Icc (0 : ℝ≥0) (min s σ)).indicator w u = w u :=
        indicator_of_mem (show u ∈ Icc (0 : ℝ≥0) (min s σ) from ⟨zero_le, h.le⟩) w
      rw [hs]
      exact tendsto_const_nhds.congr' hev'.symm
    · have hev : ∀ᶠ t in 𝓝 s, min t σ < u := (hcont.tendsto s).eventually_lt_const h
      have hev' : (fun t : ℝ≥0 => (Icc (0 : ℝ≥0) (min t σ)).indicator w u) =ᶠ[𝓝 s]
          fun _ => 0 := by
        filter_upwards [hev] with t ht
        exact indicator_of_notMem (show u ∉ Icc (0 : ℝ≥0) (min t σ) from
          fun hm => absurd hm.2 (not_le.2 ht)) w
      have hs : (Icc (0 : ℝ≥0) (min s σ)).indicator w u = 0 :=
        indicator_of_notMem (show u ∉ Icc (0 : ℝ≥0) (min s σ) from
          fun hm => absurd hm.2 (not_le.2 h)) w
      rw [hs]
      exact tendsto_const_nhds.congr' hev'.symm

/-- `⨆_n min(a, n) = a` in `ℝ≥0∞`, the monotone limit of the bounded truncations. -/
theorem iSup_min_natCast (a : ℝ≥0∞) : (⨆ n : ℕ, min a (n : ℝ≥0∞)) = a := by
  have h : (⨆ n : ℕ, (n : ℝ≥0∞)) = ⊤ := ENNReal.iSup_natCast
  calc (⨆ n : ℕ, min a (n : ℝ≥0∞)) = ⨆ n : ℕ, (n : ℝ≥0∞) ⊓ a := by
        congr 1
        funext n
        exact min_comm _ _
    _ = (⨆ n : ℕ, (n : ℝ≥0∞)) ⊓ a := (iSup_inf_eq (fun n : ℕ => (n : ℝ≥0∞)) a).symm
    _ = a := by rw [h, top_inf_eq]

/-- **Quenched mean of the weighted clock** (paper eq:occ-weightedmean, lines 277-281):
`E_y[Φ(σ) | g] = 2 ∫_D G_D(y,x) μ_h(dx)`. Here `PB` is the Brownian law from `y`, `dA ω b` the clock
measure of the path `b` in environment `ω`, `μ ω = μ_h`, `ν ω = μ_g` (the base measure, so that
`μ_h = |x|^{-γ²} ν` on `B_1`), and `G` the Green function of `D`.

Inputs (explicit hypotheses):
* `hbase`: Lemma lem:occ-base (paper lines 140-151, eq:occ-base), for every bounded Borel `q`, on one
  event of full field probability;
* `hmeas`: measurability in the path of the clock functional (implicit in lem:occ-base);
* `hweight`: eq:occ-weight (step S2, paper lines 256-258), tested on measurable subsets of `B_1`. -/
theorem weightedClock_quenchedMean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (PB : Measure (ContinuousPath ℂ))
    (γ : ℝ) (D : Set ℂ) (hDm : MeasurableSet D) (hD : D ⊆ ball 0 1)
    (G : ℂ → ℝ) (hGm : Measurable G)
    (μ ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    (hbase : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∫⁻ b, ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b) ∂PB =
        ∫⁻ x in D, ENNReal.ofReal (2 * G x) * q x ∂(ν ω))
    (hmeas : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc 0 (σ b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂P, ∀ S : Set ℂ, MeasurableSet S → S ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, g x ∂(μ ω) = ∫⁻ x in S, g x * gammaWeight γ x ∂(ν ω)) :
    ∀ᵐ ω ∂P, ∫⁻ b, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) ∂PB =
      ∫⁻ x in D, ENNReal.ofReal (2 * G x) ∂(μ ω) := by
  filter_upwards [hbase, hmeas, hweight] with ω hbω hmω hwω
  have hW := measurable_gammaWeight γ
  let q : ℕ → ℂ → ℝ≥0∞ := fun n x => min (gammaWeight γ x) (n : ℝ≥0∞)
  have hqm : ∀ n, Measurable (q n) := fun n => hW.min measurable_const
  have hqb : ∀ n, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q n x ≤ M := fun n =>
    ⟨n, ENNReal.natCast_ne_top n, fun x => min_le_right _ _⟩
  have hqmono : ∀ x, Monotone fun n => q n x := fun x m n hmn =>
    min_le_min le_rfl (Nat.cast_le.2 hmn)
  have hgm : Measurable fun x => ENNReal.ofReal (2 * G x) :=
    ENNReal.measurable_ofReal.comp (hGm.const_mul 2)
  -- the truncated clocks, as functions of the Brownian path
  let I : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun n b =>
    ∫⁻ u in Icc 0 (σ b), q n (b u) ∂(dA ω b)
  have hIm : ∀ n, Measurable (I n) := fun n => hmω (q n) (hqm n)
  have hImono : Monotone I := fun m n hmn b =>
    lintegral_mono fun u => min_le_min le_rfl (Nat.cast_le.2 hmn)
  -- Φ(σ) is the monotone limit of the truncated clocks, for each path
  have hLHS : ∀ b, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) =
      ⨆ n, I n b := by
    intro b
    have hpt : (∫⁻ u in Icc 0 (σ b), gammaWeight γ (b u) ∂(dA ω b)) =
        ∫⁻ u in Icc 0 (σ b), ⨆ n : ℕ, q n (b u) ∂(dA ω b) :=
      lintegral_congr fun u => (iSup_min_natCast _).symm
    rw [weightedClock, min_self, hpt,
      lintegral_iSup (f := fun n u => q n (b u)) (fun n => (hqm n).comp b.continuous.measurable)
        (fun m n hmn u => min_le_min le_rfl (Nat.cast_le.2 hmn))]
  calc ∫⁻ b, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) ∂PB
      = ∫⁻ b, ⨆ n, I n b ∂PB := lintegral_congr fun b => hLHS b
    _ = ⨆ n, ∫⁻ b, I n b ∂PB := lintegral_iSup (fun n => hIm n) hImono
    _ = ⨆ n, ∫⁻ x in D, ENNReal.ofReal (2 * G x) * q n x ∂(ν ω) :=
        iSup_congr fun n => hbω (q n) (hqm n) (hqb n)
    _ = ∫⁻ x in D, ⨆ n, ENNReal.ofReal (2 * G x) * q n x ∂(ν ω) :=
        (lintegral_iSup (fun n => hgm.mul (hqm n))
          (fun m n hmn x => show ENNReal.ofReal (2 * G x) * q m x ≤ ENNReal.ofReal (2 * G x) * q n x from
            mul_le_mul_of_nonneg_left (min_le_min le_rfl (Nat.cast_le.2 hmn)) zero_le)).symm
    _ = ∫⁻ x in D, ENNReal.ofReal (2 * G x) * gammaWeight γ x ∂(ν ω) := by
        refine lintegral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [q]
        rw [← ENNReal.mul_iSup, iSup_min_natCast]
    _ = ∫⁻ x in D, ENNReal.ofReal (2 * G x) ∂(μ ω) :=
        (hwω D hDm hD _ hgm).symm

end MatedCRT.KilledOccupation
