import HarmonicBalls.Defs.LBM
import MatedCRT.FirstPass.S3t.ContinuumUnderDiscrete
import MatedCRT.Proofs.LBM.TimeChangeContinuity
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit

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

/-- The exhaustion radius of Step 6: `a = (r - |y - z|)/2 > 0` for `y ∈ B_r(z)`. -/
theorem exhaustion_radius_pos {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) : 0 < (r - dist y z) / 2 := by
  rw [mem_ball] at hy
  linarith

/-- The disks `ballExhaustion z r a n` are open. -/
theorem isOpen_ballExhaustion (z : ℂ) (r a : ℝ) (n : ℕ) : IsOpen (ballExhaustion z r a n) :=
  isOpen_ball

/-- The starting point `y` of the walk lies in every disk `D_n` of the Step 6 exhaustion. -/
theorem mem_ballExhaustion_of_mem {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) (n : ℕ) :
    y ∈ ballExhaustion z r ((r - dist y z) / 2) n := by
  rw [mem_ball] at hy
  exact mem_ballExhaustion_of_dist_lt z y r (exhaustion_radius_pos (mem_ball.2 hy)).le (by linarith) n

/-- **Step 6, pathwise (concrete data).** For `y ∈ B_r(z)`, the shell functionals of the Step 6 exhaustion
`D_n = B_{r - δ_n}(z)`, `δ_n = a/(n+1)`, `a = (r - |y - z|)/2`, tend to `0` along every continuous path. -/
theorem shellTime_ballExhaustion_tendsto {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) (T : ℝ) {w : ℝ≥0 → ℂ}
    (hw : Continuous w) :
    Tendsto (fun n => shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T w) atTop (𝓝 0) :=
  shellTime_tendsto_zero (ballExhaustion_monotone z r (exhaustion_radius_pos hy).le)
    (isOpen_ballExhaustion z r _) (fun n => ballExhaustion_subset z r (exhaustion_radius_pos hy).le n)
    (ball_subset_iUnion_ballExhaustion z r _) hw

/-! ### Probabilistic layer (Step 6): the shell functionals converge in probability -/

/-- The stopped occupation with the constant integrand `1` is the truncated exit time. -/
theorem stoppedOccupation_one (D : Set ℂ) (T : ℝ) (w : ℝ≥0 → ℂ) :
    stoppedOccupation D T (fun _ => 1) w = (min (ENNReal.ofReal T) (pathExitTime D w)).toReal := by
  simp only [stoppedOccupation, setIntegral_const, smul_eq_mul, mul_one]
  rw [Real.volume_real_Ioc_of_le ENNReal.toReal_nonneg, sub_zero]

/-- The shell functional is the difference of two stopped occupations with integrand `1`. -/
theorem shellTime_eq_sub (Dn D : Set ℂ) (T : ℝ) (w : ℝ≥0 → ℂ) :
    shellTime Dn D T w = stoppedOccupation D T (fun _ => 1) w - stoppedOccupation Dn T (fun _ => 1) w := by
  rw [stoppedOccupation_one D, stoppedOccupation_one Dn]
  rfl

/-- Convergence in probability is preserved by differences. -/
theorem tendstoInProbability_sub_of {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X X' : ℝ → Ω → ℝ}
    {Y Y' : Ω → ℝ} (h : TendstoInProbability P X Y) (h' : TendstoInProbability P X' Y') :
    TendstoInProbability P (fun ε ω => X ε ω - X' ε ω) (fun ω => Y ω - Y' ω) := by
  intro δ hδ
  have hA := h (δ / 2) (half_pos hδ)
  have hB := h' (δ / 2) (half_pos hδ)
  have hsub : ∀ ε : ℝ, {ω | δ < |X ε ω - X' ε ω - (Y ω - Y' ω)|} ⊆
      {ω | δ / 2 < |X ε ω - Y ω|} ∪ {ω | δ / 2 < |X' ε ω - Y' ω|} := by
    intro ε ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    have h1 : X ε ω - X' ε ω - (Y ω - Y' ω) = (X ε ω - Y ω) - (X' ε ω - Y' ω) := by ring
    rw [h1] at hω
    have h2 := abs_sub (X ε ω - Y ω) (X' ε ω - Y' ω)
    linarith [hc.1, hc.2]
  have hup : Tendsto (fun ε : ℝ => P {ω | δ / 2 < |X ε ω - Y ω|} + P {ω | δ / 2 < |X' ε ω - Y' ω|})
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_zero] using hA.add hB
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun ε => (measure_mono (hsub ε)).trans (measure_union_le _ _))

/-- A bounded almost-everywhere measurable function on a finite measure space is integrable. -/
theorem integrable_of_ae_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    {C : ℝ} (hf : AEStronglyMeasurable f μ) (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf hC

/-- **Step 6, probabilistic.** For the Step 6 exhaustion `D_n = B_{r - a/(n+1)}(z)` of `D = B_r(z)` with
`a = (r - |y - z|)/2`: the shell functionals converge in probability under the discrete law (difference of two
applications of Step 5, to `D` and `D_n`), and their continuum limits tend to `0` almost surely as `n → ∞`
(dominated convergence with bound `T`, and the pathwise shell limit `shellTime_ballExhaustion_tendsto` along the a.s.
continuous paths `rescaledLBMPath (S.clock ω) S.m₀ b`). Named inputs: `hcont` (Steps 3–4, continuity at the regular exits)
and `hmeas` (measurability of the LBM exit functionals in the Brownian path; not provided by `IsValid`). -/
theorem shell_tendsto_discrete {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) {y z : ℂ} {r T : ℝ} (hy : y ∈ ball z r) (hT : 0 ≤ T)
    (hcont : ∀ s : ℝ, y ∈ ball z s → ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      PathFunctionalContinuousAt (stoppedOccupation (ball z s) T (fun _ => 1))
        (rescaledLBMPath (S.clock ω) S.m₀ b))
    (hmeas : ∀ s : ℝ, ∀ᵐ ω ∂S.P, AEStronglyMeasurable
      (fun b => stoppedOccupation (ball z s) T (fun _ => 1) (rescaledLBMPath (S.clock ω) S.m₀ b))
      (planarBrownianMotion y)) :
    (∀ n : ℕ, TendstoInProbability S.P
      (fun ε ω => ∫ q, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y)) ∧
    (∀ᵐ ω ∂S.P, Tendsto (fun n : ℕ => ∫ b, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) atTop (𝓝 0)) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have ha : 0 ≤ (r - dist y z) / 2 := (exhaustion_radius_pos hy).le
  -- Step 5 for every disk containing `y`
  have hstep5 : ∀ s : ℝ, y ∈ ball z s → TendstoInProbability S.P
      (fun ε ω => ∫ q, stoppedOccupation (ball z s) T (fun _ => 1)
        (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, stoppedOccupation (ball z s) T (fun _ => 1)
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) :=
    fun s hs => stoppedOccupation_tendsto_discrete h211 hγ0 hγ2 Ω S hS hs hT continuous_const
      (M := 1) (fun x => by simp) (hcont s hs)
  have hbd : ∀ (s : ℝ) (w : ℝ≥0 → ℂ), ‖stoppedOccupation (ball z s) T (fun _ => 1) w‖ ≤ T := by
    intro s w
    have h := abs_stoppedOccupation_le (D := ball z s) (g := fun _ => (1 : ℝ)) (M := 1)
      (fun x => by simp) hT w
    rw [Real.norm_eq_abs]
    linarith
  -- the discrete shell functional is the difference of the two stopped occupations
  have hdisc : ∀ (n : ℕ) (ε : ℝ) (ω : Ω),
      ∫ q, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) =
        (∫ q, stoppedOccupation (ball z r) T (fun _ => 1)
            (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
        ∫ q, stoppedOccupation (ballExhaustion z r ((r - dist y z) / 2) n) T (fun _ => 1)
            (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) := by
    intro n ε ω
    have h1 : Integrable (fun q : ℕ → ℤ => stoppedOccupation (ball z r) T (fun _ => 1)
        (interpolatedWalk ε (S.η ω) (S.mε ε) q)) (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) :=
      integrable_of_ae_bound
        (aestronglyMeasurable_stoppedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε) z r T continuous_const)
        (Eventually.of_forall fun q => hbd r _)
    have h2 : Integrable (fun q : ℕ → ℤ => stoppedOccupation (ballExhaustion z r ((r - dist y z) / 2) n) T
        (fun _ => 1) (interpolatedWalk ε (S.η ω) (S.mε ε) q)) (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) :=
      integrable_of_ae_bound
        (aestronglyMeasurable_stoppedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε)
          z (r - (r - dist y z) / 2 / ((n : ℝ) + 1)) T continuous_const)
        (Eventually.of_forall fun q => hbd _ _)
    rw [← integral_sub h1 h2]
    congr 1
    funext q
    exact shellTime_eq_sub _ _ T _
  -- continuum side: the shell integral is the difference of the two occupation integrals, a.s.
  have hcontin : ∀ n : ℕ, ∀ᵐ ω ∂S.P,
      (∫ b, stoppedOccupation (ball z r) T (fun _ => 1) (rescaledLBMPath (S.clock ω) S.m₀ b)
          ∂planarBrownianMotion y) -
        ∫ b, stoppedOccupation (ballExhaustion z r ((r - dist y z) / 2) n) T (fun _ => 1)
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y =
      ∫ b, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y := by
    intro n
    filter_upwards [hmeas r, hmeas (r - (r - dist y z) / 2 / ((n : ℝ) + 1))] with ω h1 h2
    have i1 : Integrable (fun b => stoppedOccupation (ball z r) T (fun _ => 1)
        (rescaledLBMPath (S.clock ω) S.m₀ b)) (planarBrownianMotion y) :=
      integrable_of_ae_bound h1 (Eventually.of_forall fun b => hbd r _)
    have i2 : Integrable (fun b => stoppedOccupation (ballExhaustion z r ((r - dist y z) / 2) n) T
        (fun _ => 1) (rescaledLBMPath (S.clock ω) S.m₀ b)) (planarBrownianMotion y) :=
      integrable_of_ae_bound h2 (Eventually.of_forall fun b => hbd _ _)
    rw [← integral_sub i1 i2]
    congr 1
    funext b
    exact (shellTime_eq_sub _ _ T _).symm
  -- measurability of the continuum shell functionals, a.s.
  have hmeasShell : ∀ n : ℕ, ∀ᵐ ω ∂S.P, AEStronglyMeasurable
      (fun b => shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b)) (planarBrownianMotion y) := by
    intro n
    filter_upwards [hmeas r, hmeas (r - (r - dist y z) / 2 / ((n : ℝ) + 1))] with ω h1 h2
    exact (h1.sub h2).congr (Eventually.of_forall fun b => (shellTime_eq_sub _ _ T _).symm)
  refine ⟨fun n => ?_, ?_⟩
  · -- convergence in probability: Step 5 for `D` and for `D_n`, then the difference
    have key := tendstoInProbability_sub_of (hstep5 r hy)
      (hstep5 (r - (r - dist y z) / 2 / ((n : ℝ) + 1)) (mem_ballExhaustion_of_mem hy n))
    have hY : (fun ω => (∫ b, stoppedOccupation (ball z r) T (fun _ => 1)
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) -
        ∫ b, stoppedOccupation (ball z (r - (r - dist y z) / 2 / ((n : ℝ) + 1))) T (fun _ => 1)
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y)
        =ᵐ[S.P] (fun ω => ∫ b, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) :=
      (hcontin n).mono fun ω h => h
    have hX : (fun ε ω => ∫ q, shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
          (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) =
        (fun ε ω => (∫ q, stoppedOccupation (ball z r) T (fun _ => 1)
            (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          ∫ q, stoppedOccupation (ball z (r - (r - dist y z) / 2 / ((n : ℝ) + 1))) T (fun _ => 1)
            (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) :=
      funext fun ε => funext fun ω => hdisc n ε ω
    rw [hX]
    exact key.congr_ae hY
  · -- almost sure limit: dominated convergence in the Brownian path, pathwise shell limit
    filter_upwards [hS.isLQGClock, ae_all_iff.2 hmeasShell] with ω hω hmeasω
    have hcb : ∀ᵐ b ∂planarBrownianMotion y, Continuous (rescaledLBMPath (S.clock ω) S.m₀ b) :=
      (hω y).2.mono fun b hb => continuous_rescaledLBMPath hb
    have hdct := tendsto_integral_of_dominated_convergence (μ := planarBrownianMotion y)
      (F := fun n b => shellTime (ballExhaustion z r ((r - dist y z) / 2) n) (ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b))
      (f := fun _ => (0 : ℝ)) (fun _ => T) hmeasω (integrable_const T)
      (fun n => Eventually.of_forall fun b => by
        have h1 := shellTime_nonneg (ballExhaustion_subset z r ha n) T (rescaledLBMPath (S.clock ω) S.m₀ b)
        have h2 := shellTime_le (Dn := ballExhaustion z r ((r - dist y z) / 2) n) (D := ball z r) hT
          (rescaledLBMPath (S.clock ω) S.m₀ b)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
      (hcb.mono fun b hb => shellTime_ballExhaustion_tendsto hy T hb)
    simpa only [integral_zero] using hdct
end MatedCRT.TruncatedLaws
