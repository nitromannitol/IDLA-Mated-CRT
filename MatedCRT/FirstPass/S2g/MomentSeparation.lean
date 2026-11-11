import MatedCRT.FirstPass.S2g.GoodSetReduction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Countable determination of locally finite measures on `B_{3/4}`

Proves `CandidateMomentSeparation` (`S2g/GoodSetReduction.lean`): there is a countable family `φs` of continuous
compactly supported functions with support in `B_1` such that two locally finite measures on `ℂ` with the same moment
vector (`momentVec`, `S2g/GoodSetMoments.lean`) agree on `B_{3/4}`. This is general measure theory (Riesz uniqueness of
Radon measures, separability of `C(K)` for compact metric `K`); no paper-specific input.

Argument.
1. For `R_n = 1 - 1/(n+2) < 1`, the continuous functions vanishing outside `B̄_{R_n}` have a countable sup-norm dense
   sequence `Ψ n` (`exists_dense_momSep`: a subset of the second countable space `C(B̄_{R_n}, ℝ)`).
2. Equal integrals against all `Ψ n j` give equal integrals against every continuous `g` vanishing outside `B̄_ρ`,
   `ρ < 1` (`exists_momSep_family`): pick `n` with `ρ < R_n`, approximate `g` uniformly by `Ψ n k` within `ε`, and bound
   the error by `ε · ν(B̄_{R_n})`; then `δ`-argument.
3. Equal integrals against all continuous `g` vanishing outside `B̄_{3/4}` give equal restrictions to `B_{3/4}`
   (`restrict_ball_eq_of_det`): the cutoffs `min(1, n(3/4 - |x|))⁺` increase to the indicator of `B_{3/4}`; the finite
   measures `ν_i.restrict B_{3/4}` are determined by their bounded continuous integrals
   (`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`); dominated convergence.

Terminology: Riesz uniqueness of Radon measures, Parthasarathy (1967) Thm II.6.6 for the countable determining class.
-/

namespace MatedCRT

open MeasureTheory Set Metric TopologicalSpace Filter Topology

/-- The sup-norm restriction to `B̄_R` of a continuous function vanishing outside `B̄_R`. -/
def momSepRestr (R : ℝ) (h : {h : ℂ → ℝ // Continuous h ∧ ∀ x, x ∉ closedBall (0 : ℂ) R → h x = 0}) :
    C(closedBall (0 : ℂ) R, ℝ) :=
  ⟨fun x => h.1 x.1, h.2.1.comp continuous_subtype_val⟩

/-- Countable sup-norm density on `ℂ` for the continuous functions vanishing outside `B̄_R`: the restrictions to `B̄_R` form
a subset of the second countable space `C(B̄_R, ℝ)`, which has a countable dense sequence in itself; a function vanishing
outside `B̄_R` is uniformly close on `ℂ` as soon as its restriction is close on `B̄_R`. -/
theorem exists_dense_momSep (R : ℝ) :
    ∃ ψ : ℕ → ℂ → ℝ, (∀ k, Continuous (ψ k) ∧ ∀ x, x ∉ closedBall (0 : ℂ) R → ψ k x = 0) ∧
      ∀ h : ℂ → ℝ, Continuous h → (∀ x, x ∉ closedBall (0 : ℂ) R → h x = 0) →
        ∀ ε : ℝ, 0 < ε → ∃ k, ∀ x, |h x - ψ k x| < ε := by
  classical
  have hne : Nonempty ↥(range (momSepRestr R)) :=
    ⟨⟨momSepRestr R ⟨0, continuous_const, fun _ _ => rfl⟩, ⟨_, rfl⟩⟩⟩
  obtain ⟨u, hu⟩ := exists_dense_seq ↥(range (momSepRestr R))
  have hex : ∀ k, ∃ h : {h : ℂ → ℝ // Continuous h ∧ ∀ x, x ∉ closedBall (0 : ℂ) R → h x = 0},
      momSepRestr R h = (u k : C(closedBall (0 : ℂ) R, ℝ)) :=
    fun k => (u k).2
  choose ψ hψ using hex
  refine ⟨fun k => (ψ k).1, fun k => (ψ k).2, ?_⟩
  intro h hcont hvan ε hε
  have hmem : momSepRestr R ⟨h, hcont, hvan⟩ ∈ range (momSepRestr R) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hu ⟨_, hmem⟩ ε hε
  have hd : dist (momSepRestr R ⟨h, hcont, hvan⟩) (momSepRestr R (ψ k)) < ε := by
    rw [hψ k]
    exact hk
  refine ⟨k, fun x => ?_⟩
  show |h x - (ψ k).1 x| < ε
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · have h1 := ContinuousMap.dist_apply_le_dist (⟨x, hx⟩ : closedBall (0 : ℂ) R)
      (f := momSepRestr R ⟨h, hcont, hvan⟩) (g := momSepRestr R (ψ k))
    rw [Real.dist_eq] at h1
    exact lt_of_le_of_lt h1 hd
  · rw [hvan x hx, (ψ k).2.2 x hx]
    simpa using hε

/-- Radii `R_n = 1 - 1/(n+2)` of the countable family. -/
noncomputable def momSepRad (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem momSepRad_lt_one (n : ℕ) : momSepRad n < 1 := by
  unfold momSepRad
  have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  linarith

/-- The cutoffs `min(1, n (3/4 - |x|))⁺`, which increase to the indicator of the open ball `B_{3/4}`. -/
noncomputable def momSepCut (n : ℕ) (x : ℂ) : ℝ := max 0 (min 1 ((n : ℝ) * (3 / 4 - ‖x‖)))

theorem momSepCut_continuous (n : ℕ) : Continuous (momSepCut n) :=
  continuous_const.max (continuous_const.min (continuous_const.mul (continuous_const.sub continuous_norm)))

theorem momSepCut_nonneg (n : ℕ) (x : ℂ) : 0 ≤ momSepCut n x :=
  le_max_left _ _

theorem momSepCut_le_one (n : ℕ) (x : ℂ) : momSepCut n x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem momSepCut_eq_zero (n : ℕ) {x : ℂ} (hx : 3 / 4 ≤ ‖x‖) : momSepCut n x = 0 := by
  unfold momSepCut
  have h1 : (n : ℝ) * (3 / 4 - ‖x‖) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
  rw [min_eq_right (by linarith), max_eq_left h1]

theorem momSepCut_tendsto_one {x : ℂ} (hx : ‖x‖ < 3 / 4) :
    Tendsto (fun n => momSepCut n x) atTop (𝓝 1) := by
  have hc : 0 < 3 / 4 - ‖x‖ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (3 / 4 - ‖x‖))
  have hev : ∀ᶠ n : ℕ in atTop, momSepCut n x = 1 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hc] at hN
    have h2 := mul_le_mul_of_nonneg_right hNn hc.le
    have h1 : 1 < (n : ℝ) * (3 / 4 - ‖x‖) := by linarith
    unfold momSepCut
    rw [min_eq_left h1.le, max_eq_right zero_le_one]
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

theorem three_quarters_le_of_not_mem {x : ℂ} (hx : x ∉ closedBall (0 : ℂ) (3 / 4)) : 3 / 4 ≤ ‖x‖ := by
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact hx.le

/-- Supports: a continuous function vanishing outside `B̄_R`, `R < 1`, is continuous with compact support and `tsupport`
inside `B_1`. -/
theorem momSep_family_props {R : ℝ} (hR : R < 1) {ψ : ℂ → ℝ} (hc : Continuous ψ)
    (hv : ∀ x, x ∉ closedBall (0 : ℂ) R → ψ x = 0) :
    Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball (0 : ℂ) 1 := by
  have hsupp : Function.support ψ ⊆ closedBall (0 : ℂ) R := fun x hx => by
    by_contra hxc
    exact Function.mem_support.1 hx (hv x hxc)
  refine ⟨hc, HasCompactSupport.intro (isCompact_closedBall _ _) hv, ?_⟩
  exact (closure_minimal hsupp isClosed_closedBall).trans (closedBall_subset_ball hR)

/-- **Countable determining family.** There is a countable family `φs` of continuous compactly supported
functions with `tsupport ⊆ B_1` such that: for every `ρ < 1` and every continuous `g` vanishing outside `B̄_ρ`, equal
integrals of the `φs k` against two locally finite measures force equal integrals of `g`. -/
theorem exists_momSep_family :
    ∃ φs : ℕ → ℂ → ℝ,
      (∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ ball (0 : ℂ) 1) ∧
      ∀ ρ : ℝ, ρ < 1 → ∀ g : ℂ → ℝ, Continuous g → (∀ x, x ∉ closedBall (0 : ℂ) ρ → g x = 0) →
        ∀ ν₁ ν₂ : Measure ℂ, IsLocallyFiniteMeasure ν₁ → IsLocallyFiniteMeasure ν₂ →
          (∀ k, ∫ x, φs k x ∂ν₁ = ∫ x, φs k x ∂ν₂) → ∫ x, g x ∂ν₁ = ∫ x, g x ∂ν₂ := by
  choose Ψ hΨ using fun n => exists_dense_momSep (momSepRad n)
  refine ⟨fun k => Ψ (Nat.unpair k).1 (Nat.unpair k).2, ?_, ?_⟩
  · intro k
    have hk := (hΨ (Nat.unpair k).1).1 (Nat.unpair k).2
    exact momSep_family_props (momSepRad_lt_one _) hk.1 hk.2
  · intro ρ hρ g hg hgv ν₁ ν₂ h₁ h₂ hEq
    have := h₁
    have := h₂
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - ρ))
    have hpos : 0 < 1 - ρ := by linarith
    have h1 : 1 < (N : ℝ) * (1 - ρ) := by
      rw [div_lt_iff₀ hpos] at hN
      exact hN
    have h2 : 1 / ((N : ℝ) + 2) < 1 - ρ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hρN : ρ < momSepRad N := by
      unfold momSepRad
      linarith
    have hgN : ∀ x, x ∉ closedBall (0 : ℂ) (momSepRad N) → g x = 0 := fun x hx =>
      hgv x (fun hb => hx (closedBall_subset_closedBall hρN.le hb))
    have hKc : IsCompact (closedBall (0 : ℂ) (momSepRad N)) := isCompact_closedBall _ _
    have hgcs : HasCompactSupport g := HasCompactSupport.intro hKc hgN
    have hgi₁ : Integrable g ν₁ := hg.integrable_of_hasCompactSupport hgcs
    have hgi₂ : Integrable g ν₂ := hg.integrable_of_hasCompactSupport hgcs
    have hCpos : 0 < (ν₁ (closedBall (0 : ℂ) (momSepRad N))).toReal +
        (ν₂ (closedBall (0 : ℂ) (momSepRad N))).toReal + 1 := by
      have := ENNReal.toReal_nonneg (a := ν₁ (closedBall (0 : ℂ) (momSepRad N)))
      have := ENNReal.toReal_nonneg (a := ν₂ (closedBall (0 : ℂ) (momSepRad N)))
      linarith
    -- the error bound for a single measure
    have hbd : ∀ (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] (ε : ℝ) (ψ : ℂ → ℝ), Continuous ψ →
        (∀ x, x ∉ closedBall (0 : ℂ) (momSepRad N) → ψ x = 0) →
        (∀ x, |g x - ψ x| < ε) →
        |∫ x, (g x - ψ x) ∂ν| ≤ ε * (ν (closedBall (0 : ℂ) (momSepRad N))).toReal := by
      intro ν _ ε ψ hψc hψv hψε
      have hF : ∀ x, ‖g x - ψ x‖ ≤ (closedBall (0 : ℂ) (momSepRad N)).indicator (fun _ => ε) x := by
        intro x
        by_cases hx : x ∈ closedBall (0 : ℂ) (momSepRad N)
        · rw [indicator_of_mem hx, Real.norm_eq_abs]
          exact (hψε x).le
        · rw [indicator_of_notMem hx, hgN x hx, hψv x hx]
          simp
      have hint : Integrable ((closedBall (0 : ℂ) (momSepRad N)).indicator (fun _ => ε)) ν :=
        (integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const hKc.measure_lt_top.ne)
      calc |∫ x, (g x - ψ x) ∂ν| = ‖∫ x, (g x - ψ x) ∂ν‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, (closedBall (0 : ℂ) (momSepRad N)).indicator (fun _ => ε) x ∂ν :=
            norm_integral_le_of_norm_le hint (ae_of_all _ hF)
        _ = ν.real (closedBall (0 : ℂ) (momSepRad N)) • ε :=
            integral_indicator_const ε measurableSet_closedBall
        _ = ε * (ν (closedBall (0 : ℂ) (momSepRad N))).toReal := by
            rw [Measure.real, smul_eq_mul, mul_comm]
    have key : ∀ δ : ℝ, 0 < δ → |∫ x, g x ∂ν₁ - ∫ x, g x ∂ν₂| ≤ δ := by
      intro δ hδ
      have hεpos : 0 < δ / ((ν₁ (closedBall (0 : ℂ) (momSepRad N))).toReal +
          (ν₂ (closedBall (0 : ℂ) (momSepRad N))).toReal + 1) := div_pos hδ hCpos
      obtain ⟨k, hk⟩ := (hΨ N).2 g hg hgN _ hεpos
      have hψc : Continuous (Ψ N k) := ((hΨ N).1 k).1
      have hψv : ∀ x, x ∉ closedBall (0 : ℂ) (momSepRad N) → Ψ N k x = 0 := ((hΨ N).1 k).2
      have hψi₁ : Integrable (Ψ N k) ν₁ :=
        hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc hψv)
      have hψi₂ : Integrable (Ψ N k) ν₂ :=
        hψc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc hψv)
      have hpair : ∫ x, Ψ N k x ∂ν₁ = ∫ x, Ψ N k x ∂ν₂ := by
        have := hEq (Nat.pair N k)
        simpa only [Nat.unpair_pair] using this
      have e1 := hbd ν₁ _ (Ψ N k) hψc hψv hk
      have e2 := hbd ν₂ _ (Ψ N k) hψc hψv hk
      have hsplit : ∫ x, g x ∂ν₁ - ∫ x, g x ∂ν₂
          = ∫ x, (g x - Ψ N k x) ∂ν₁ - ∫ x, (g x - Ψ N k x) ∂ν₂ := by
        rw [integral_sub hgi₁ hψi₁, integral_sub hgi₂ hψi₂, hpair]
        ring
      rw [hsplit]
      set C := (ν₁ (closedBall (0 : ℂ) (momSepRad N))).toReal +
        (ν₂ (closedBall (0 : ℂ) (momSepRad N))).toReal + 1 with hCdef
      set ε := δ / C with hεdef
      calc |∫ x, (g x - Ψ N k x) ∂ν₁ - ∫ x, (g x - Ψ N k x) ∂ν₂|
          ≤ |∫ x, (g x - Ψ N k x) ∂ν₁| + |∫ x, (g x - Ψ N k x) ∂ν₂| := abs_sub _ _
        _ ≤ ε * (ν₁ (closedBall (0 : ℂ) (momSepRad N))).toReal +
            ε * (ν₂ (closedBall (0 : ℂ) (momSepRad N))).toReal := add_le_add e1 e2
        _ = ε * ((ν₁ (closedBall (0 : ℂ) (momSepRad N))).toReal +
            (ν₂ (closedBall (0 : ℂ) (momSepRad N))).toReal) := by ring
        _ ≤ ε * C := mul_le_mul_of_nonneg_left (by rw [hCdef]; linarith) hεpos.le
        _ = δ := by rw [hεdef, div_mul_cancel₀ δ hCpos.ne']
    exact eq_of_forall_dist_le fun δ hδ => by
      rw [Real.dist_eq]
      exact key δ hδ

/-- **Equal restrictions to `B_{3/4}`.** Two locally finite measures on `ℂ` that integrate every continuous
function vanishing outside `B̄_{3/4}` to the same value have equal restrictions to the open ball `B_{3/4}`. -/
theorem restrict_ball_eq_of_det {ν₁ ν₂ : Measure ℂ} [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂]
    (hdet : ∀ g : ℂ → ℝ, Continuous g → (∀ x, x ∉ closedBall (0 : ℂ) (3 / 4) → g x = 0) →
      ∫ x, g x ∂ν₁ = ∫ x, g x ∂ν₂) :
    ν₁.restrict (ball (0 : ℂ) (3 / 4)) = ν₂.restrict (ball (0 : ℂ) (3 / 4)) := by
  have : IsFiniteMeasure (ν₁.restrict (ball (0 : ℂ) (3 / 4))) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall _ _).measure_lt_top⟩
  have : IsFiniteMeasure (ν₂.restrict (ball (0 : ℂ) (3 / 4))) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall _ _).measure_lt_top⟩
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  -- the cutoff integrals converge to the restricted integrals (dominated convergence)
  have hlim : ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
      Tendsto (fun n => ∫ x, momSepCut n x * f x ∂ν) atTop
        (𝓝 (∫ x, (ball (0 : ℂ) (3 / 4)).indicator (fun x => f x) x ∂ν)) := by
    intro ν _
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : ℂ) (3 / 4)).indicator (fun _ => ‖f‖)) ?_ ?_ ?_ ?_
    · intro n
      exact ((momSepCut_continuous n).mul f.continuous).aestronglyMeasurable
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
    · intro n
      refine ae_of_all _ (fun x => ?_)
      by_cases hx : x ∈ closedBall (0 : ℂ) (3 / 4)
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_of_nonneg (momSepCut_nonneg n x)]
        have hfx : |f x| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
        calc momSepCut n x * |f x| ≤ 1 * ‖f‖ :=
              mul_le_mul (momSepCut_le_one n x) hfx (abs_nonneg _) zero_le_one
          _ = ‖f‖ := one_mul _
      · rw [indicator_of_notMem hx, momSepCut_eq_zero n (three_quarters_le_of_not_mem hx)]
        simp
    · refine ae_of_all _ (fun x => ?_)
      by_cases hx : ‖x‖ < 3 / 4
      · rw [indicator_of_mem (mem_ball_zero_iff.2 hx)]
        have := (momSepCut_tendsto_one hx).mul_const (f x)
        rw [one_mul] at this
        exact this
      · have hx' : 3 / 4 ≤ ‖x‖ := not_lt.1 hx
        have hz : ∀ n, momSepCut n x * f x = 0 := fun n => by
          rw [momSepCut_eq_zero n hx', zero_mul]
        rw [indicator_of_notMem (fun h => hx (mem_ball_zero_iff.1 h))]
        exact tendsto_const_nhds.congr (fun n => (hz n).symm)
  have h1 := hlim ν₁ inferInstance
  have h2 := hlim ν₂ inferInstance
  have heq : (fun n => ∫ x, momSepCut n x * f x ∂ν₁) = (fun n => ∫ x, momSepCut n x * f x ∂ν₂) := by
    funext n
    refine hdet _ ((momSepCut_continuous n).mul f.continuous) (fun x hx => ?_)
    show momSepCut n x * f x = 0
    rw [momSepCut_eq_zero n (three_quarters_le_of_not_mem hx), zero_mul]
  rw [heq] at h1
  have hu := tendsto_nhds_unique h1 h2
  rw [integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at hu
  exact hu

/-- **`CandidateMomentSeparation` is proved.** The countable family of `exists_momSep_family` separates the
moment vectors of locally finite measures on `B_{3/4}`. -/
theorem candidateMomentSeparation_proved : CandidateMomentSeparation := by
  obtain ⟨φs, hφs, hdet⟩ := exists_momSep_family
  refine ⟨φs, hφs, fun ν₁ ν₂ h₁ h₂ hmom => ?_⟩
  have := h₁
  have := h₂
  apply restrict_ball_eq_of_det
  intro g hg hgv
  refine hdet (3 / 4) (by norm_num) g hg hgv ν₁ ν₂ h₁ h₂ (fun k => ?_)
  have hk : intG (φs k) ν₁ = intG (φs k) ν₂ := congrFun hmom k
  rwa [intG_eq_integral (hφs k).1 (hφs k).2.1 ν₁, intG_eq_integral (hφs k).1 (hφs k).2.1 ν₂] at hk

/-- **Good-set reduction without the separation input.** `coneHalfBallGood_of_source` with
`CandidateMomentSeparation` discharged by `candidateMomentSeparation_proved`. The remaining hypotheses are the open
`SourceHalfBallPathwiseStep`, the candidate `CandidateConeLogLocalCodeLawStd` (not frozen), and the frozen
`FrozenUniversalMeasurabilityOfAnalytic` and `FrozenLQGTestIntegralMeasurable`. -/
theorem coneHalfBallGood_of_source_sep (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hsrc : SourceHalfBallPathwiseStep) (hstd : CandidateConeLogLocalCodeLawStd) :
    ConeHalfBallGoodMeasureLawStep :=
  coneHalfBallGood_of_source hU hmeasT hsrc hstd candidateMomentSeparation_proved

end MatedCRT
