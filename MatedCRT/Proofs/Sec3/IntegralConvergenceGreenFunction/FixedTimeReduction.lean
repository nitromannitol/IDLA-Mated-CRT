import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Final
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.BallHolderFamily
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.NullFiniteCover
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedDiscreteBound
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestFiniteCover
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestCover
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableTruncated

/-!
# Lemma 3.4: reduction of the truncated fixed-time step

`truncatedOccupationFixedTimeStep_of_det` proves `TruncatedOccupationFixedTimeStep 𝒮` (the step of Lemma 3.4 for
environment-dependent test functions) from two named steps:
* `TruncatedDetFixedTimeStep 𝒮` (D1): the convergence in probability of the discrete truncated occupation to the
  continuum one for deterministic bounded continuous Hölder test functions on the ball (the route of
  PROOF-REPAIRS-G §G4: sandwich of the discrete exit between exits from the disks of radii `r ± δ`); open;
* `TruncatedFixedTimeIntegrableStep 𝒮` (H2): for environment-dependent Hölder test functions, the truncated path
  functionals of the rescaled Liouville Brownian path are almost surely strongly measurable in the Brownian variable
  and integrable in time; the real-truncation form of `LBMTruncatedOccupationMeasurableStep`; open.

The proof is a finite net over one countable family of Hölder test functions (`exists_holder_family_ball`, levels
`m` and indices `j`, enumerated by `Nat.unpair`), null-measurable events from the environment σ-algebra, continuity
from above (`exists_finite_cover_nullMeasurable`), the discrete pathwise bound (`truncatedDiscreteOccupation_sub_le`)
and the continuum pathwise bound (`abs_pathFunctional_sub_le`). The cited scaling input `MepsScalingInput 𝒮`
(External/SLE.lean) gives `mε ≥ C⁻¹ ε⁻¹ > 0` for small `ε`.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The truncated path functional of the test function `F` along the rescaled Liouville Brownian path of the
environment `ω` (the summand of `truncatedLBMOccupation`): a.s. strongly measurable in the Brownian variable, and
integrable in time for almost every Brownian path. -/
def TruncatedPathIntegrable {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (z y : ℂ) (r T : ℝ)
    (F : Ω → ℂ → ℝ) (ω : Ω) : Prop :=
  AEStronglyMeasurable (fun b => ∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
      (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal), F ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal))
    (planarBrownianMotion y) ∧
  ∀ᵐ b ∂(planarBrownianMotion y), IntegrableOn
    (fun t : ℝ => F ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal))
    (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal))

/-- **Deterministic fixed-time step (D1)**: for a deterministic bounded continuous Hölder test function `g` on the ball,
the discrete truncated occupation `(mε)⁻¹ Σ_{n < ⌊T mε⌋} g(η(X_n)) 1{n < τ^ε_int}` converges in probability to the
continuum truncated occupation `∫_{(0, T ∧ τ_B]} g(B^{LBM}_t) dt`. Open (route: PROOF-REPAIRS-G §G4). -/
def TruncatedDetFixedTimeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ g : ℂ → ℝ, Continuous g → (∃ M : ℝ, ∀ x, |g x| ≤ M) →
  (∃ (C χ : ℝ≥0), 0 < χ ∧ HolderOnWith C χ g (ball z r)) →
  ∀ T : ℝ, 0 < T → TendstoInProbability S.P
    (fun ε ω => truncatedDiscreteOccupation S (ball z r) y (fun _ => g) ⌊T * S.mε ε⌋₊ ε ω)
    (truncatedLBMOccupation S (ball z r) y (fun _ => g) T)

/-- **Integrability of the truncated path functionals (H2)**: for environment-dependent test functions that are
measurable in the environment, bounded and Hölder on the ball, the truncated path functionals are a.s. strongly
measurable in the Brownian variable and integrable in time. Open (with the real truncation `T`). -/
def TruncatedFixedTimeIntegrableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ f : Ω → ℂ → ℝ, (∀ x, Measurable[S.envSigma] fun ω => f ω x) →
    (∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M) → (∀ ω, IsHolderContinuousOn (f ω) (ball z r)) →
  ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂S.P, TruncatedPathIntegrable S z y r T f ω

/-- A point `w t` of the path with `0 < t` before the truncated exit time lies in the ball. -/
lemma path_mem_ball_of_lt_truncation {w : ℝ≥0 → ℂ} {z : ℂ} {r T t : ℝ} (ht0 : 0 < t)
    (ht : t < min T (pathExitTime (ball z r) w).toReal) : w t.toNNReal ∈ ball z r := by
  have hτ : t < (pathExitTime (ball z r) w).toReal := lt_of_lt_of_le ht (min_le_right _ _)
  have hτtop : pathExitTime (ball z r) w ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hτ
    linarith
  have hlt : ENNReal.ofReal t < pathExitTime (ball z r) w :=
    (ENNReal.ofReal_lt_iff_lt_toReal ht0.le hτtop).2 hτ
  exact mem_of_lt_pathExitTime hlt

/-- One-dimensional bound: an integral over `(0, a]` of a function bounded by `M` a.e. is at most `M a`. -/
theorem abs_setIntegral_Ioc_le_ae {F : ℝ → ℝ} {a M : ℝ} (ha : 0 ≤ a) (_hM : 0 ≤ M)
    (h : ∀ᵐ t : ℝ, t ∈ Ioc (0 : ℝ) a → |F t| ≤ M) :
    |∫ t in Ioc (0 : ℝ) a, F t| ≤ M * a := by
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)), ‖F t‖ ≤ M := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h] with t ht ht'
    rw [Real.norm_eq_abs]
    exact ht ht'
  have h2 := norm_integral_le_of_norm_le_const h1
  rw [Real.norm_eq_abs] at h2
  simpa [Real.volume_Ioc, ENNReal.toReal_ofReal ha, Measure.real] using h2

/-- One-dimensional difference bound on `(0, a]`, almost everywhere. -/
theorem abs_setIntegral_Ioc_sub_le_ae {F G : ℝ → ℝ} {a δ : ℝ} (ha : 0 ≤ a)
    (hF : IntegrableOn F (Ioc (0 : ℝ) a)) (hG : IntegrableOn G (Ioc (0 : ℝ) a)) (hδ : 0 ≤ δ)
    (h : ∀ᵐ t : ℝ, t ∈ Ioc (0 : ℝ) a → |F t - G t| ≤ δ) :
    |(∫ t in Ioc (0 : ℝ) a, F t) - ∫ t in Ioc (0 : ℝ) a, G t| ≤ δ * a := by
  rw [← integral_sub hF hG]
  exact abs_setIntegral_Ioc_le_ae (F := fun t => F t - G t) ha hδ h

/-- The truncated path functional of a function bounded by `M` on the ball is bounded by `M T`. -/
theorem abs_pathFunctional_le {w : ℝ≥0 → ℂ} {z : ℂ} {r T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    {F : ℂ → ℝ} (hF : ∀ q ∈ ball z r, |F q| ≤ M) :
    |∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal), F (w t.toNNReal)| ≤ M * T := by
  have hm0 : 0 ≤ min T (pathExitTime (ball z r) w).toReal := le_min hT ENNReal.toReal_nonneg
  refine (abs_setIntegral_Ioc_le_ae hm0 hM ?_).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hM)
  have hne : ∀ᵐ t : ℝ, t ∉ ({min T (pathExitTime (ball z r) w).toReal} : Set ℝ) :=
    (Set.countable_singleton _).ae_notMem volume
  filter_upwards [hne] with t ht htI
  have ht' : t < min T (pathExitTime (ball z r) w).toReal :=
    lt_of_le_of_ne htI.2 (fun h => ht (Set.mem_singleton_iff.2 h))
  exact hF _ (path_mem_ball_of_lt_truncation htI.1 ht')

/-- **Continuum pathwise bound.** If `F` and `G` are `δ`-close on the ball, the truncated path functionals of `F` and
`G` along a path differ by at most `δ T`. -/
theorem abs_pathFunctional_sub_le {w : ℝ≥0 → ℂ} {z : ℂ} {r T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    {F G : ℂ → ℝ} (hFG : ∀ q ∈ ball z r, |F q - G q| ≤ δ)
    (hF : IntegrableOn (fun t : ℝ => F (w t.toNNReal)) (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal)))
    (hG : IntegrableOn (fun t : ℝ => G (w t.toNNReal)) (Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal))) :
    |(∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal), F (w t.toNNReal)) -
      ∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r) w).toReal), G (w t.toNNReal)| ≤ δ * T := by
  have hm0 : 0 ≤ min T (pathExitTime (ball z r) w).toReal := le_min hT ENNReal.toReal_nonneg
  refine (abs_setIntegral_Ioc_sub_le_ae hm0 hF hG hδ ?_).trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hδ)
  have hne : ∀ᵐ t : ℝ, t ∉ ({min T (pathExitTime (ball z r) w).toReal} : Set ℝ) :=
    (Set.countable_singleton _).ae_notMem volume
  filter_upwards [hne] with t ht htI
  have ht' : t < min T (pathExitTime (ball z r) w).toReal :=
    lt_of_le_of_ne htI.2 (fun h => ht (Set.mem_singleton_iff.2 h))
  exact hFG _ (path_mem_ball_of_lt_truncation htI.1 ht')

/-- A bound in probability of a difference of two integrals of a family of functions of the Brownian variable. -/
theorem abs_integral_sub_le_of_ae {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsProbabilityMeasure μ]
    {Φ Ψ : β → ℝ} {c : ℝ} (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ μ) (h : ∀ᵐ b ∂μ, |Φ b - Ψ b| ≤ c) :
    |(∫ b, Φ b ∂μ) - ∫ b, Ψ b ∂μ| ≤ c := by
  rw [← integral_sub hΦ hΨ]
  have h2 := norm_integral_le_of_norm_le_const (μ := μ) (f := fun b => Φ b - Ψ b) (C := c)
    (by
      filter_upwards [h] with b hb
      rw [Real.norm_eq_abs]
      exact hb)
  rw [Real.norm_eq_abs] at h2
  simpa using h2

/-- Convergence in probability along `𝓝[>] 0` only depends on the functions for small positive `ε`. -/
theorem tendstoInProbability_congr_nhdsGT {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' : ℝ → Ω → ℝ} {Y : Ω → ℝ} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, X' ε ω = X ε ω) :
    TendstoInProbability P X' Y ↔ TendstoInProbability P X Y := by
  have key : ∀ {A B : ℝ → Ω → ℝ}, (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, A ε ω = B ε ω) →
      TendstoInProbability P A Y → TendstoInProbability P B Y := by
    intro A B hAB hA η hη
    refine (hA η hη).congr' ?_
    filter_upwards [hAB] with ε hε
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, hε ω]
  exact ⟨key h, key (h.mono fun ε hε ω => (hε ω).symm)⟩

/-- **Reduction of the truncated fixed-time step (E1).** Given the deterministic step D1 and the continuum integrability
H2 (and the cited scaling input `MepsScalingInput 𝒮`), the environment-dependent convergence
`TruncatedOccupationFixedTimeStep 𝒮` holds. -/
theorem truncatedOccupationFixedTimeStep_of_det {𝒮 : SpaceFillingSLEModel}
    (hscale : MepsScalingInput 𝒮) (H1 : TruncatedDetFixedTimeStep 𝒮)
    (H2 : TruncatedFixedTimeIntegrableStep 𝒮) : TruncatedOccupationFixedTimeStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy f hfmeas hfbound hfcont T hT
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨C, hC1, hCS⟩ := hscale γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hCS Ω S hS
  -- one countable family of Hölder test functions: level m (accuracy 1/(m+1)) and index j
  choose G hG hGapp using fun m : ℕ =>
    exists_holder_family_ball z hr (δ := 1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨Ξ, hΞdef⟩ : ∃ Ξ : ℕ → ℂ → ℝ, ∀ n, Ξ n = G (Nat.unpair n).1 (Nat.unpair n).2 :=
    ⟨fun n => G (Nat.unpair n).1 (Nat.unpair n).2, fun n => rfl⟩
  have hΞprop : ∀ n, Continuous (Ξ n) ∧ (∃ M : ℝ, ∀ x, |Ξ n x| ≤ M) ∧
      ∃ (C χ : ℝ≥0), 0 < χ ∧ χ ≤ 1 ∧ HolderOnWith C χ (Ξ n) (ball z r) := by
    intro n
    rw [hΞdef n]
    exact hG _ _
  have hΞpair : ∀ m j, Ξ (Nat.pair m j) = G m j := by
    intro m j
    rw [hΞdef, Nat.unpair_pair]
  have hfcontOn : ∀ ω, ContinuousOn (f ω) (ball z r) := fun ω => by
    obtain ⟨C', χ', hχ', -, hH'⟩ := hfcont ω
    exact hH'.continuousOn hχ'
  have hae_f : ∀ᵐ ω ∂S.P, TruncatedPathIntegrable S z y r T f ω :=
    H2 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f hfmeas hfbound hfcont T hT
  have hae_n : ∀ n, ∀ᵐ ω ∂S.P, TruncatedPathIntegrable S z y r T (fun _ => Ξ n) ω := by
    intro n
    obtain ⟨MΞ, hMΞ⟩ := (hΞprop n).2.1
    obtain ⟨C', χ', hχ', hχ1, hH'⟩ := (hΞprop n).2.2
    exact H2 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy (fun _ => Ξ n) (fun x => measurable_const)
      (fun _ => ⟨MΞ, fun x _ => hMΞ x⟩) (fun _ => ⟨C', χ', hχ', hχ1, hH'⟩) T hT
  -- the good event: continuity of the curve and the path integrability hypotheses
  set Good : Set Ω := {ω | Continuous (S.η ω) ∧ TruncatedPathIntegrable S z y r T f ω ∧
    ∀ n, TruncatedPathIntegrable S z y r T (fun _ => Ξ n) ω} with hGooddef
  have hgood : ∀ᵐ ω ∂S.P, ω ∈ Good := by
    filter_upwards [hS.isAreaParametrized, hae_f, ae_all_iff.2 hae_n] with ω h1 h2 h3
    exact ⟨h1.1, h2, h3⟩
  have hGoodnull : S.P {ω | ¬ ω ∈ Good} = 0 := ae_iff.1 hgood
  -- the scaled functionals, and their versions valid for `0 < ε < ε₀`
  set Xf : ℝ → Ω → ℝ := fun ε ω => truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω with hXf
  set Xj : ℕ → ℝ → Ω → ℝ := fun n ε ω =>
    truncatedDiscreteOccupation S (ball z r) y (fun _ => Ξ n) ⌊T * S.mε ε⌋₊ ε ω with hXj
  set Yf : Ω → ℝ := truncatedLBMOccupation S (ball z r) y f T with hYf
  set Yj : ℕ → Ω → ℝ := fun n => truncatedLBMOccupation S (ball z r) y (fun _ => Ξ n) T with hYj
  set X' : ℝ → Ω → ℝ := fun ε ω => if 0 < ε ∧ ε < ε₀ then Xf ε ω else 0 with hX'
  set Xj' : ℕ → ℝ → Ω → ℝ := fun n ε ω => if 0 < ε ∧ ε < ε₀ then Xj n ε ω else 0 with hXj'
  have hevf : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, X' ε ω = Xf ε ω := by
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε ω
    have hεmem : 0 < ε ∧ ε < ε₀ := ⟨hε.1, hε.2⟩
    show (if 0 < ε ∧ ε < ε₀ then Xf ε ω else 0) = Xf ε ω
    simp [hεmem]
  have hevn : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Xj' n ε ω = Xj n ε ω := by
    intro n
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε ω
    have hεmem : 0 < ε ∧ ε < ε₀ := ⟨hε.1, hε.2⟩
    show (if 0 < ε ∧ ε < ε₀ then Xj n ε ω else 0) = Xj n ε ω
    simp [hεmem]
  have hconv : ∀ n, TendstoInProbability S.P (Xj' n) (Yj n) := by
    intro n
    obtain ⟨C', χ', hχ', -, hH'⟩ := (hΞprop n).2.2
    have h1 := H1 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy (Ξ n) (hΞprop n).1 (hΞprop n).2.1
      ⟨C', χ', hχ', hH'⟩ T hT
    exact (tendstoInProbability_congr_nhdsGT (hevn n)).2 h1
  have hcov : ∀ b : ℝ, 0 < b → ∀ κ : ℝ≥0∞, 0 < κ → ∃ (J : ℕ) (A : ℕ → Set Ω),
      (∀ j ∈ Finset.range J, ∀ ε : ℝ, ∀ ω ∈ A j, |X' ε ω - Xj' j ε ω| ≤ b ∧ |Yf ω - Yj j ω| ≤ b) ∧
      S.P ((⋃ j ∈ Finset.range J, A j)ᶜ) < κ := by
    intro b hb κ hκ
    set δ : ℝ := b / T with hδdef
    have hδ : 0 < δ := div_pos hb hT
    obtain ⟨Dq, hDqc, hDqd⟩ := TopologicalSpace.exists_countable_dense ℂ
    set Q : Set ℂ := Dq ∩ ball z r with hQdef
    have hQc : Q.Countable := hDqc.mono inter_subset_left
    set A0 : ℕ → Set Ω := fun n => {ω | ∀ q ∈ Q, |f ω q - Ξ n q| < δ} with hA0def
    have hA0m : ∀ n, NullMeasurableSet (A0 n) S.P := fun n =>
      hS.nullMeasurableSet_of_envSigma
        (@measurableSet_forall_abs_sub_lt Ω S.envSigma f hfmeas Q hQc (Ξ n) δ)
    have hcov0 : ∀ ω, ∃ n, ω ∈ A0 n := by
      intro ω
      obtain ⟨C', χ', hχ', -, hH'⟩ := hfcont ω
      set m : ℕ := ⌈1 / δ⌉₊ with hmdef
      obtain ⟨j, hj⟩ := hGapp m (f ω) ⟨C', χ', hχ', hH'⟩
      refine ⟨Nat.pair m j, fun q hq => ?_⟩
      rw [hΞpair m j]
      have hlev : 1 / ((m : ℝ) + 1) ≤ δ := by
        have h1 : 1 / δ ≤ (m : ℝ) := Nat.le_ceil _
        rw [div_le_iff₀ hδ] at h1
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      exact lt_of_lt_of_le (hj q hq.2) hlev
    obtain ⟨J, hJ⟩ := exists_finite_cover_nullMeasurable S.P A0 hA0m hcov0 hκ
    refine ⟨J, fun n => A0 n ∩ Good, ?_, ?_⟩
    · intro n _ ε ω hω
      obtain ⟨hωA, hωG⟩ := hω
      obtain ⟨hηc, hTf, hTΞ⟩ := hωG
      have hFG : ∀ q ∈ ball z r, |f ω q - Ξ n q| ≤ δ :=
        abs_sub_le_of_lt_on_dense_inter_ball hDqd (hfcontOn ω) (hΞprop n).1.continuousOn hωA
      obtain ⟨Mf, hMf⟩ := hfbound ω
      obtain ⟨MΞ, hMΞ⟩ := (hΞprop n).2.1
      -- continuum bound (independent of ε)
      have hcontbound : |Yf ω - Yj n ω| ≤ b := by
        obtain ⟨hΦm, hΦi⟩ := hTf
        obtain ⟨hΨm, hΨi⟩ := hTΞ n
        have hΦint : Integrable (fun b => ∫ t in Ioc (0 : ℝ)
            (min T (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
            f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) (planarBrownianMotion y) :=
          Integrable.mono' (integrable_const (max Mf 0 * T)) hΦm
            (ae_of_all _ fun b => by
              rw [Real.norm_eq_abs]
              exact abs_pathFunctional_le hT.le (le_max_right _ _)
                (fun q hq => (hMf q hq).trans (le_max_left _ _)))
        have hΨint : Integrable (fun b => ∫ t in Ioc (0 : ℝ)
            (min T (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
            Ξ n (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) (planarBrownianMotion y) :=
          Integrable.mono' (integrable_const (max MΞ 0 * T)) hΨm
            (ae_of_all _ fun b => by
              rw [Real.norm_eq_abs]
              exact abs_pathFunctional_le hT.le (le_max_right _ _)
                (fun q _ => (hMΞ q).trans (le_max_left _ _)))
        have key := abs_integral_sub_le_of_ae hΦint hΨint (c := δ * T) (by
          filter_upwards [hΦi, hΨi] with b h1 h2
          exact abs_pathFunctional_sub_le hT.le hδ.le hFG h1 h2)
        have h4 : δ * T = b := by
          rw [hδdef]
          field_simp
        rw [h4] at key
        exact key
      refine ⟨?_, hcontbound⟩
      by_cases hε : 0 < ε ∧ ε < ε₀
      · have hmpos : 0 < S.mε ε := by
          have h1 := (hmε ε hε.1 hε.2).1
          have hCpos : (0 : ℝ) < C⁻¹ := inv_pos.2 (by linarith)
          have h2 : 0 < C⁻¹ * ε⁻¹ := mul_pos hCpos (inv_pos.2 hε.1)
          linarith
        have hFM : ∀ q ∈ ball z r, |f ω q| ≤ max (max Mf MΞ) 0 := fun q hq =>
          (hMf q hq).trans ((le_max_left _ _).trans (le_max_left _ _))
        have hGM : ∀ q ∈ ball z r, |(fun _ => Ξ n) ω q| ≤ max (max Mf MΞ) 0 := fun q _ =>
          (hMΞ q).trans ((le_max_right _ _).trans (le_max_left _ _))
        have hM0 : 0 ≤ max (max Mf MΞ) 0 := le_max_right _ _
        have hdisc := truncatedDiscreteOccupation_sub_le S y z f (fun _ => Ξ n) ⌊T * S.mε ε⌋₊ hε.1
          hmpos ω hηc hM0 hFM hGM hδ.le hFG
        have hN : ((⌊T * S.mε ε⌋₊ : ℕ) : ℝ) ≤ T * S.mε ε :=
          Nat.floor_le (mul_nonneg hT.le hmpos.le)
        have hbound : (S.mε ε)⁻¹ * (((⌊T * S.mε ε⌋₊ : ℕ) : ℝ) * δ) ≤ b := by
          have h2 : ((⌊T * S.mε ε⌋₊ : ℕ) : ℝ) * δ ≤ (T * S.mε ε) * δ :=
            mul_le_mul_of_nonneg_right hN hδ.le
          have h3 : (S.mε ε)⁻¹ * (((⌊T * S.mε ε⌋₊ : ℕ) : ℝ) * δ)
              ≤ (S.mε ε)⁻¹ * ((T * S.mε ε) * δ) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hmpos.le)
          have h4 : (S.mε ε)⁻¹ * ((T * S.mε ε) * δ) = b := by
            rw [hδdef]
            field_simp
          linarith
        have hdiff : X' ε ω - Xj' n ε ω = truncatedDiscreteOccupation S (ball z r) y f
            ⌊T * S.mε ε⌋₊ ε ω - truncatedDiscreteOccupation S (ball z r) y (fun _ => Ξ n)
            ⌊T * S.mε ε⌋₊ ε ω := by
          simp only [hX', hXj', hXf, hXj, hε, and_self, ↓reduceIte]
        rw [hdiff]
        exact hdisc.trans hbound
      · have hz : X' ε ω - Xj' n ε ω = 0 := by
          show (if 0 < ε ∧ ε < ε₀ then Xf ε ω else 0) - (if 0 < ε ∧ ε < ε₀ then Xj n ε ω else 0) = 0
          have h1 : (if 0 < ε ∧ ε < ε₀ then Xf ε ω else 0) = 0 :=
            ite_eq_right_iff.2 (fun h => absurd h hε)
          have h2 : (if 0 < ε ∧ ε < ε₀ then Xj n ε ω else 0) = 0 :=
            ite_eq_right_iff.2 (fun h => absurd h hε)
          rw [h1, h2, sub_self]
        rw [hz, abs_zero]
        exact hb.le
    · show S.P ((⋃ j ∈ Finset.range J, A0 j ∩ Good)ᶜ) < κ
      have hsub : (⋃ j ∈ Finset.range J, A0 j ∩ Good)ᶜ ⊆
          (⋃ j ∈ Finset.range J, A0 j)ᶜ ∪ {ω | ¬ ω ∈ Good} := by
        intro ω hω
        by_cases hG : ω ∈ Good
        · left
          intro hmem
          apply hω
          obtain ⟨j, hj, hωA⟩ := Set.mem_iUnion₂.1 hmem
          exact Set.mem_iUnion₂.2 ⟨j, hj, hωA, hG⟩
        · right
          exact hG
      calc S.P ((⋃ j ∈ Finset.range J, A0 j ∩ Good)ᶜ)
          ≤ S.P ((⋃ j ∈ Finset.range J, A0 j)ᶜ ∪ {ω | ¬ ω ∈ Good}) := measure_mono hsub
        _ ≤ S.P ((⋃ j ∈ Finset.range J, A0 j)ᶜ) + S.P {ω | ¬ ω ∈ Good} := measure_union_le _ _
        _ = S.P ((⋃ j ∈ Finset.range J, A0 j)ᶜ) := by rw [hGoodnull, add_zero]
        _ < κ := hJ
  have hTP : TendstoInProbability S.P X' Yf :=
    tendstoInProbability_of_finite_cover S.P X' Yf Xj' Yj hconv hcov
  exact (tendstoInProbability_congr_nhdsGT hevf).1 hTP

end MatedCRT
