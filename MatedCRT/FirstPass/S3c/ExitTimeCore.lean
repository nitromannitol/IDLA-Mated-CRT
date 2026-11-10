import MatedCRT.FirstPass.S3c.ExitTimeBridge
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitMonotone
import MatedCRT.Proofs.Infra.Setting

/-!
# Exit-time bridge, core (task fp-S3c-3-1-fidelity-fix, route A; z12)

`normExitTime ≤ expectedExitTime` (`ofReal_normExitTime_le_expectedExitTime'`), and the deterministic core
`exitTimeClauses_of_events` of the second clause of `ExitTimeUpperBoundStmt` (Draft Lemma 2.18) from the first
clause at two radii and the volume-growth lower bound (audit §2.3).
-/

namespace MatedCRT

open MeasureTheory Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace S3cBridge

/-- The normalized Green kernel is dominated by the Green function (`g = G / deg`, `deg ≥ 1` or junk `0`). -/
theorem greenKernel_le_greenFn' (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) :
    greenKernel m A a b ≤ greenFn m A a b := by
  unfold greenKernel
  have hnn := greenFn_nonnegative m A a b
  rcases Nat.eq_zero_or_pos (mdeg m b) with h | h
  · simp [h, hnn]
  · exact div_le_self hnn (Nat.one_le_cast.mpr h)

/-- `q_A(a) ≤ Q_A(a)`: the normalized exit time is at most the expected exit time (Lemma 2.18, second clause). -/
theorem ofReal_normExitTime_le_expectedExitTime' (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) :
    ENNReal.ofReal (normExitTime m A a) ≤ expectedExitTime m A a := by
  have hk : ∀ b : A, ENNReal.ofReal (greenKernel m A a b) ≤ ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a := by
    intro b
    calc ENNReal.ofReal (greenKernel m A a b) ≤ ENNReal.ofReal (greenFn m A a b) :=
          ENNReal.ofReal_le_ofReal (greenKernel_le_greenFn' m A a b)
      _ = ENNReal.ofReal (∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a).toReal := rfl
      _ ≤ ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a := ENNReal.ofReal_toReal_le
  have hsum : ∑' b : A, ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a =
      ∫⁻ x, MatedCRT.ConstantOrderDiv.visitCount A A x ∂srwLaw m a := by
    rw [← lintegral_tsum fun b : A => (MatedCRT.ConstantOrderDiv.measurable_visitsBeforeExit A b).aemeasurable]
    exact lintegral_congr fun x => MatedCRT.ConstantOrderDiv.tsum_visitsBeforeExit A A x
  have hle : ∫⁻ x, MatedCRT.ConstantOrderDiv.visitCount A A x ∂srwLaw m a ≤ expectedExitTime m A a := by
    unfold expectedExitTime
    exact lintegral_mono fun x => MatedCRT.ConstantOrderDiv.visitCount_le A A x
  unfold normExitTime
  by_cases hs : Summable (fun b : A => greenKernel m A a b)
  · have hnn : ∀ b : A, 0 ≤ greenKernel m A a b := fun b => by
      unfold greenKernel
      exact div_nonneg (greenFn_nonnegative m A a b) (Nat.cast_nonneg _)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hs]
    calc ∑' b : A, ENNReal.ofReal (greenKernel m A a b)
        ≤ ∑' b : A, ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a := ENNReal.tsum_le_tsum hk
      _ = ∫⁻ x, MatedCRT.ConstantOrderDiv.visitCount A A x ∂srwLaw m a := hsum
      _ ≤ expectedExitTime m A a := hle
  · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
    exact zero_le

/-- The first clause of `ExitTimeUpperBoundStmt` at the scale `ε` (exit-time moments of the interior cells of every
measurable `D ⊆ B_ρ` with `μ(D) ≥ ε^α`), with the constant `C`. -/
def ExitMomentClause (m : ℤ → ℤ → ℕ) (μ : Measure ℂ) (η : ℝ → ℂ) (ε α C ρ : ℝ) : Prop :=
  ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ μ D →
    ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
      exitTimeMoment m (interiorCellVertices ε η D) a N ≤
        ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
          (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ^ N

/-- Deterministic core of the second clause of Lemma 2.18 (audit §2.3). For `0 < ε` small, `D ⊆ B_ρ`, `a ∈ V^ε(D)`:
the killed set of `D` is contained in the killed set of `D' = B_{ε^{2α}}(D)`, whose mass is at least `ε^{α₀}`
(volume growth at the point `x₀ ∈ D`), and the first moment on `D'` is bounded by the first clause at the radius `ρ'`. -/
theorem second_clause_of_events (m : ℤ → ℤ → ℕ) (μ : Measure ℂ) (η : ℝ → ℂ) (hη : Continuous η)
    {ε α α₀ b C₂ ρ ρ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hα : 0 < α) (h2α : 2 * α < α₀)
    (h2αb : 2 * α * b ≤ α₀) (hρ'1 : ρ' < 1) (hδ : ε ^ (2 * α) < ρ' - ρ)
    (hα_half : ε ^ α ≤ 1 / 2)
    (hC₂ : ExitMomentClause m μ η ε α₀ C₂ ρ') (hvol : ∀ z ∈ ball (0 : ℂ) (1 - ε ^ (2 * α)),
      ENNReal.ofReal ((ε ^ (2 * α)) ^ b) ≤ μ (ball z (ε ^ (2 * α))))
    (D : Set ℂ) (hDρ : D ⊆ ball 0 ρ) (a : ℤ) (ha : a ∈ cellVertices ε η D) :
    expectedExitTime m (interiorCellVertices ε η D) a ≤
      ENNReal.ofReal (C₂ * ε⁻¹) *
        largestExitTimeRV μ (thickening (ε ^ α) D) := by
  obtain ⟨x₀, hx₀c, hx₀D⟩ := ha
  set δ : ℝ := ε ^ (2 * α) with hδ_def
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hε0 _
  have hεα : δ = ε ^ α * ε ^ α := by rw [hδ_def, show 2 * α = α + α by ring, Real.rpow_add hε0]
  have hεα0 : ε ^ α₀ ≤ δ := by
    rw [hδ_def]; exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le h2α.le
  have hpos : 0 ≤ ε ^ α := Real.rpow_nonneg hε0.le _
  have hle : ε ^ α₀ + δ ≤ ε ^ α := by nlinarith [mul_nonneg hpos (sub_nonneg.mpr hα_half)]
  set D' : Set ℂ := thickening δ D with hD'_def
  have hD'meas : MeasurableSet D' := isOpen_thickening.measurableSet
  have hDD' : D ⊆ D' := self_subset_thickening hδpos D
  have hD'ρ : D' ⊆ ball 0 ρ' := by
    intro x hx
    obtain ⟨z, hzD, hxz⟩ := mem_thickening_iff.mp hx
    have hz : ‖z‖ < ρ := mem_ball_zero_iff.mp (hDρ hzD)
    have hxz' : ‖x - z‖ < δ := by rw [← dist_eq_norm]; exact hxz
    rw [mem_ball_zero_iff]
    linarith [norm_sub_norm_le x z]
  have hvolx0 : x₀ ∈ ball (0 : ℂ) (1 - δ) := by
    have h := mem_ball_zero_iff.mp (hDρ hx₀D)
    rw [mem_ball_zero_iff]
    linarith
  have hmass : ENNReal.ofReal (ε ^ α₀) ≤ μ D' := by
    have h1 : ENNReal.ofReal (ε ^ α₀) ≤ ENNReal.ofReal (δ ^ b) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hδ_def, ← Real.rpow_mul hε0.le]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le h2αb
    have h2 : ENNReal.ofReal (δ ^ b) ≤ μ (ball x₀ δ) := hvol x₀ hvolx0
    have h3 : μ (ball x₀ δ) ≤ μ D' :=
      measure_mono fun x hx => mem_thickening_iff.mpr ⟨x₀, hx₀D, mem_ball.mp hx⟩
    exact h1.trans (h2.trans h3)
  have hmom := hC₂ D' hD'meas hD'ρ hmass a ⟨x₀, hx₀c, hDD' hx₀D⟩ 1
  have hmono : expectedExitTime m (interiorCellVertices ε η D) a ≤
      expectedExitTime m (interiorCellVertices ε η D') a :=
    expectedExitTime_mono_domain m (interiorCellVertices_mono_of_subset (ε := ε) hη hDD') a
  have hE1 : expectedExitTime m (interiorCellVertices ε η D') a =
      exitTimeMoment m (interiorCellVertices ε η D') a 1 := by
    simp [expectedExitTime, exitTimeMoment]
  have hsub1 : thickening (ε ^ α₀) D' ⊆ thickening (ε ^ α) D :=
    (thickening_thickening_subset _ _ _).trans (thickening_mono hle D)
  have hsub2 : D' ⊆ thickening (ε ^ α) D :=
    thickening_mono (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith : α ≤ 2 * α)) D
  have hsup : (⨆ z ∈ D', ∫⁻ w in thickening (ε ^ α₀) D',
      ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ≤ largestExitTimeRV μ (thickening (ε ^ α) D) := by
    unfold largestExitTimeRV
    refine iSup₂_le fun z hz => le_trans (lintegral_mono_set hsub1) ?_
    exact le_iSup₂ (f := fun z (_ : z ∈ thickening (ε ^ α) D) =>
      ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) z (hsub2 hz)
  calc expectedExitTime m (interiorCellVertices ε η D) a
      ≤ expectedExitTime m (interiorCellVertices ε η D') a := hmono
    _ = exitTimeMoment m (interiorCellVertices ε η D') a 1 := hE1
    _ ≤ _ := hmom
    _ = ENNReal.ofReal (C₂ * ε⁻¹) * (⨆ z ∈ D', ∫⁻ w in thickening (ε ^ α₀) D',
          ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) := by
        simp only [pow_one, Nat.factorial_one, Nat.cast_one, Real.rpow_neg_one, one_mul]
    _ ≤ ENNReal.ofReal (C₂ * ε⁻¹) * largestExitTimeRV μ (thickening (ε ^ α) D) :=
        mul_le_mul_of_nonneg_left hsup zero_le

/-- The deterministic core: the two clauses of `ExitTimeUpperBoundStmt` at the scale `ε` from the first clause at the
radii `ρ` (constant `C₁`) and `ρ'` (constant `C₂`), and the volume-growth lower bound at scale `ε^{2α}`. -/
theorem clauses_of_events (m : ℤ → ℤ → ℕ) (μ : Measure ℂ) (η : ℝ → ℂ) (hη : Continuous η)
    {ε α α₀ b C₁ C₂ C ρ ρ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hα : 0 < α) (hαα₀ : α ≤ α₀) (h2α : 2 * α < α₀)
    (h2αb : 2 * α * b ≤ α₀) (hρ'1 : ρ' < 1) (hδ : ε ^ (2 * α) < ρ' - ρ)
    (hα_half : ε ^ α ≤ 1 / 2) (hC₁pos : 0 ≤ C₁) (hC₁ : C₁ ≤ C) (hC₂ : C₂ ≤ C)
    (hE₁ : ExitMomentClause m μ η ε α₀ C₁ ρ) (hE₂ : ExitMomentClause m μ η ε α₀ C₂ ρ')
    (hvol : ∀ z ∈ ball (0 : ℂ) (1 - ε ^ (2 * α)),
      ENNReal.ofReal ((ε ^ (2 * α)) ^ b) ≤ μ (ball z (ε ^ (2 * α)))) :
    ExitMomentClause m μ η ε α C ρ ∧
      (∀ D : Set ℂ, D ⊆ ball 0 ρ → ∀ a ∈ cellVertices ε η D,
        ENNReal.ofReal (normExitTime m (interiorCellVertices ε η D) a) ≤
          expectedExitTime m (interiorCellVertices ε η D) a ∧
        expectedExitTime m (interiorCellVertices ε η D) a ≤
          ENNReal.ofReal (C * ε⁻¹) * largestExitTimeRV μ (thickening (ε ^ α) D)) := by
  have hαε : ε ^ α₀ ≤ ε ^ α := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hαα₀
  refine ⟨fun D hDm hDρ hmass a ha N => ?_, fun D hDρ a ha => ⟨ofReal_normExitTime_le_expectedExitTime' m _ a, ?_⟩⟩
  · have h := hE₁ D hDm hDρ ((ENNReal.ofReal_le_ofReal hαε).trans hmass) a ha N
    have hthick : thickening (ε ^ α₀) D ⊆ thickening (ε ^ α) D := thickening_mono hαε D
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (pow_le_pow_left' ?_ N))
    · gcongr
    · exact iSup₂_mono fun z _ => lintegral_mono_set hthick
  · have h := second_clause_of_events m μ η hη hε0 hε1 hα h2α h2αb hρ'1 hδ hα_half hE₂ hvol D hDρ a ha
    exact h.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC₂ (inv_nonneg.mpr hε0.le))) zero_le)

end S3cBridge

/-- **Lemma 2.18 (`ExitTimeUpperBoundStmt`) from BG20 Proposition 5.1** (route A, audit §2.3). The mass-restricted first
moment `BG20Prop51` (frozen) and the volume growth `VolumeGrowthStmt` (Lemma 2.7) imply both clauses of Lemma 2.18,
including the unrestricted-domain clause for every `D ⊆ B_ρ`. -/
theorem exitTimeUpperBoundStmt_core {𝒮 : SpaceFillingSLEModel} (hBG : BG20Prop51 𝒮) (h27 : VolumeGrowthStmt) :
    ExitTimeUpperBoundStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨α₀, hα₀, hfr⟩ := hBG γ hγ hγ2
  set b : ℝ := (2 + γ) ^ 2 / 2 + 1 with hb_def
  have hb_pos : 0 < b := by rw [hb_def]; positivity
  have hb_gt : (2 + γ) ^ 2 / 2 < b := by rw [hb_def]; linarith
  set α : ℝ := α₀ / (2 + 2 * b) with hα_def
  have hden : 0 < 2 + 2 * b := by linarith
  have hα_pos : 0 < α := div_pos hα₀ hden
  have hαmul : α * (2 + 2 * b) = α₀ := by rw [hα_def]; field_simp
  have hαα₀ : α ≤ α₀ := by nlinarith [mul_pos hα_pos hb_pos]
  have h2α : 2 * α < α₀ := by nlinarith [mul_pos hα_pos hb_pos]
  have h2αb : 2 * α * b ≤ α₀ := by nlinarith [hα_pos]
  refine ⟨α, hα_pos, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨C₁, hC₁, hfr₁⟩ := hfr ρ hρ0 hρ1
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  obtain ⟨C₂, hC₂, hfr₂⟩ := hfr ((1 + ρ) / 2) hρ'0 hρ'1
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun Ω _ S hS => ?_⟩
  have hE₁ := hfr₁ Ω S hS
  have hE₂ := hfr₂ Ω S hS
  have hcone := hS.isConeField
  have hβ0 : 0 < (2 - γ) ^ 2 / 4 := by
    have : 0 < 2 - γ := by linarith
    positivity
  have hβ1 : (2 - γ) ^ 2 / 4 < (2 - γ) ^ 2 / 2 := by
    have : 0 < (2 - γ) ^ 2 := by
      have : 0 < 2 - γ := by linarith
      positivity
    linarith
  have hEv := h27 γ hγ hγ2 ((2 - γ) ^ 2 / 4) b hβ0 hβ1 hb_gt Ω S.P S.hC S.hcirc S.μ hcone
  have hEvc := S3cBridge.polyHighProb_comp_rpow hEv (k := 2 * α) (by linarith)
  have hcont : ∀ᵐ ω ∂S.P, Continuous (S.η ω) := hS.isAreaParametrized.mono fun ω h => h.1
  have hcomb := polyHighProb_of_inter hE₂ hEvc (fun r => subset_rfl)
  have hcomb2 := polyHighProb_of_inter hE₁ hcomb (fun r => subset_rfl)
  set δ₀ : ℝ := (1 - ρ) / 2 with hδ₀
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; linarith
  have hr₁ : 0 < min 1 (min (δ₀ ^ (1 / (2 * α))) ((1 / 2) ^ (1 / α))) :=
    lt_min one_pos (lt_min (Real.rpow_pos_of_pos hδ₀pos _) (Real.rpow_pos_of_pos (by norm_num) _))
  refine S3cBridge.polyHighProb_mono_ae_small hr₁ hcomb2 hcont fun r hr0 hrr₁ ω hω hq => ?_
  obtain ⟨h1, h2, h3⟩ := hω
  have hr1 : r < 1 := lt_of_lt_of_le hrr₁ (min_le_left _ _)
  have hr_a : r < δ₀ ^ (1 / (2 * α)) := lt_of_lt_of_le hrr₁ ((min_le_right _ _).trans (min_le_left _ _))
  have hr_b : r < (1 / 2) ^ (1 / α) := lt_of_lt_of_le hrr₁ ((min_le_right _ _).trans (min_le_right _ _))
  have hr0' : 0 < r := hr0
  have hδr : r ^ (2 * α) < δ₀ := by
    calc r ^ (2 * α) < (δ₀ ^ (1 / (2 * α))) ^ (2 * α) := Real.rpow_lt_rpow hr0.le hr_a (by linarith)
      _ = δ₀ := by rw [← Real.rpow_mul hδ₀pos.le, one_div_mul_cancel (by linarith), Real.rpow_one]
  have hαhalf : r ^ α < 1 / 2 := by
    calc r ^ α < ((1 / 2) ^ (1 / α)) ^ α := Real.rpow_lt_rpow hr0.le hr_b hα_pos
      _ = 1 / 2 := by rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hα_pos.ne', Real.rpow_one]
  have hδρ : r ^ (2 * α) < (1 + ρ) / 2 - ρ := by
    have : (1 + ρ) / 2 - ρ = δ₀ := by rw [hδ₀]; ring
    rw [this]; exact hδr
  exact S3cBridge.clauses_of_events (S.mult r ω) (S.μ ω) (S.η ω) hq hr0 hr1 hα_pos hαα₀ h2α h2αb hρ'1
    hδρ hαhalf.le hC₁.le (le_max_left _ _) (le_max_right _ _) h1 h2 (fun z hz => (h3 z hz).1)

/-- **Lemma 2.18 from BG20 Proposition 5.1, restricted to the reference package** (route A). Under `SLEReferenceInput ν`
and `HasNormalizedSLELaw 𝒮 ν`, the frozen input `BG20Prop51Ref ν` and `VolumeGrowthStmt` give `ExitTimeUpperBoundStmt 𝒮`. -/
theorem exitTimeUpperBoundStmt_of_bg20 {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hν : SLEReferenceInput ν) (hBG : BG20Prop51Ref ν) (hLaw : HasNormalizedSLELaw 𝒮 ν)
    (h27 : VolumeGrowthStmt) : ExitTimeUpperBoundStmt 𝒮 :=
  exitTimeUpperBoundStmt_core (hBG hν 𝒮 hLaw) h27

end MatedCRT
