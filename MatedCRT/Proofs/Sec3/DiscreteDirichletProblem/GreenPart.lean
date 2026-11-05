import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GeneralPotentialTranslation
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DirichletUniqueness
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.WeightedPotential
import HarmonicBalls.Proofs.Sec6.DiscPotentialHolderTranslation
import MatedCRT.Proofs.LBM.DirichletDiscHolder

/-!
# The Green-potential part of the continuum candidate in Lemma 3.5

For a locally finite measure `μ` with the volume growth condition on `B_R(0) ⊇ B_r(z)` and a source `ψ` continuous
and bounded on `B_r(z)`, the Green potential `g(x) = ∫_{B_r(z)} G_{B_r(z)}(x,y) ψ(y) μ(dy)`

* converges absolutely and is Hölder continuous on `cl B_r(z)` (HB22 Proposition 2.5, Green clause, in its
  deterministic form `Section6.greenPotential_disc_holderOnWith_of_volumeGrowth`), and vanishes off `B_r(z)`;
* satisfies `Δ(-c g) = c ψ μ` on `B_r(z)` in the distributional sense, for `c ≥ 0`
  (`ballGreenPotential_hasLaplacian_of_upper` applied to the normalized positive and negative parts of `ψ`).
-/

open MeasureTheory Metric Filter Topology Set Laplacian _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-! ## Elementary facts -/

theorem greenFunction_eq_zero_of_notMem_left {O : Set ℂ} {x y : ℂ} (hx : x ∉ O) :
    greenFunction O x y = 0 := by
  unfold greenFunction
  rw [ite_eq_right (fun h => hx h.1)]

/-- A Hölder function with a positive exponent on a bounded set is Hölder with an exponent in `(0, 1]`. -/
theorem isHolderContinuousOn_of_holderOnWith {f : ℂ → ℝ} {s : Set ℂ} (hs : Bornology.IsBounded s)
    {C t : ℝ≥0} (ht : 0 < t) (h : HolderOnWith C t f s) : IsHolderContinuousOn f s := by
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hs
  refine ⟨_, min t 1, lt_min ht one_pos, min_le_right _ _,
    h.of_le (D := Real.toNNReal D) (fun x hx y hy => ?_) (min_le_left _ _)⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hD hx hy)

/-- `f - c g` is Hölder on a bounded set when `f` and `g` are. -/
theorem IsHolderContinuousOn.sub_const_mul {f g : ℂ → ℝ} {s : Set ℂ} (hs : Bornology.IsBounded s)
    (hf : IsHolderContinuousOn f s) (hg : IsHolderContinuousOn g s) (c : ℝ) :
    IsHolderContinuousOn (fun x => f x - c * g x) s := by
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hs
  have hDe : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ (Real.toNNReal D : ℝ≥0∞) := fun x hx y hy => by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hD hx hy)
  obtain ⟨C₁, t₁, ht₁, ht₁1, h₁⟩ := hf
  obtain ⟨C₂, t₂, ht₂, -, h₂⟩ := hg
  set t := min t₁ t₂ with ht
  set K₁ : ℝ≥0 := C₁ * (Real.toNNReal D) ^ ((t₁ : ℝ) - (t : ℝ)) with hK₁
  set K₂ : ℝ≥0 := C₂ * (Real.toNNReal D) ^ ((t₂ : ℝ) - (t : ℝ)) with hK₂
  have h₁' : HolderOnWith K₁ t f s := h₁.of_le hDe (min_le_left t₁ t₂)
  have h₂' : HolderOnWith K₂ t g s := h₂.of_le hDe (min_le_right t₁ t₂)
  refine ⟨K₁ + ‖c‖₊ * K₂, t, lt_min ht₁ ht₂, (min_le_left _ _).trans ht₁1,
    MatedCRT.holderOnWith_of_dist_le fun x hx y hy => ?_⟩
  have e₁ := h₁'.dist_le hx hy
  have e₂ := h₂'.dist_le hx hy
  rw [Real.dist_eq] at e₁ e₂ ⊢
  have htri := norm_sub_le (f x - f y) (c * (g x - g y))
  simp only [Real.norm_eq_abs, abs_mul] at htri
  have hc0 : 0 ≤ |c| := abs_nonneg c
  calc |f x - c * g x - (f y - c * g y)| = |f x - f y - c * (g x - g y)| := by
        congr 1
        ring
    _ ≤ |f x - f y| + |c| * |g x - g y| := htri
    _ ≤ K₁ * dist x y ^ (t : ℝ) + |c| * (K₂ * dist x y ^ (t : ℝ)) :=
        add_le_add e₁ (mul_le_mul_of_nonneg_left e₂ hc0)
    _ = ((K₁ + ‖c‖₊ * K₂ : ℝ≥0) : ℝ) * dist x y ^ (t : ℝ) := by
        push_cast
        rw [Real.norm_eq_abs]
        ring

/-! ## Distributional Laplacians -/

theorem hasLaplacian_add {f g : ℂ → ℝ} {a b c d : Measure ℂ} {U : Set ℂ}
    (hf : HasLaplacian f a b U) (hg : HasLaplacian g c d U) :
    HasLaplacian (fun x => f x + g x) (a + c) (b + d) U := by
  refine ⟨hf.1.add hg.1, fun φ hφ => ?_⟩
  obtain ⟨ha, hb, hfe⟩ := hf.2 φ hφ
  obtain ⟨hc, hd, hge⟩ := hg.2 φ hφ
  refine ⟨ha.add_measure hc, hb.add_measure hd, ?_⟩
  have heq : (fun x => (f x + g x) * Δ φ x) = fun x => f x * Δ φ x + g x * Δ φ x := by
    funext x
    ring
  rw [heq, integral_add (integrable_mul_laplacian_of_test hf.1 hφ)
    (integrable_mul_laplacian_of_test hg.1 hφ), hfe, hge, integral_add_measure ha hc,
    integral_add_measure hb hd]
  ring

theorem hasLaplacian_neg {f : ℂ → ℝ} {a b : Measure ℂ} {U : Set ℂ} (hf : HasLaplacian f a b U) :
    HasLaplacian (fun x => -f x) b a U := by
  refine ⟨hf.1.neg, fun φ hφ => ?_⟩
  obtain ⟨ha, hb, he⟩ := hf.2 φ hφ
  refine ⟨hb, ha, ?_⟩
  have heq : (fun x => -f x * Δ φ x) = fun x => -(f x * Δ φ x) := by
    funext x
    ring
  rw [heq, integral_neg, he]
  ring

/-- Only the restrictions of the measures to `U` matter in `HasLaplacian _ _ _ U`. -/
theorem hasLaplacian_congr_restrict {w : ℂ → ℝ} {a b a' b' : Measure ℂ} {U : Set ℂ}
    (h : HasLaplacian w a b U) (ha : a.restrict U = a'.restrict U)
    (hb : b.restrict U = b'.restrict U) : HasLaplacian w a' b' U := by
  refine ⟨h.1, fun φ hφ => ?_⟩
  obtain ⟨hia, hib, he⟩ := h.2 φ hφ
  have hsupp : Function.support φ ⊆ U := (subset_tsupport φ).trans hφ.2.2
  have hzero : ∀ x ∉ U, φ x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => hx (hsupp h)
  have key : ∀ ν ν' : Measure ℂ, ν.restrict U = ν'.restrict U → Integrable φ ν →
      Integrable φ ν' ∧ ∫ x, φ x ∂ν' = ∫ x, φ x ∂ν := by
    intro ν ν' hνν' hi
    have hi' : IntegrableOn φ U ν := (integrableOn_iff_integrable_of_support_subset hsupp).2 hi
    change Integrable φ (ν.restrict U) at hi'
    rw [hνν'] at hi'
    refine ⟨(integrableOn_iff_integrable_of_support_subset hsupp).1 hi', ?_⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν) hzero, hνν']
  obtain ⟨hia', ea⟩ := key a a' ha hia
  obtain ⟨hib', eb⟩ := key b b' hb hib
  exact ⟨hia', hib', by rw [ea, eb, he]⟩

theorem ofReal_mul_max_zero {c : ℝ} (hc : 0 ≤ c) (a : ℝ) :
    ENNReal.ofReal (c * max a 0) = ENNReal.ofReal (c * a) := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, mul_zero, ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc h)]

/-! ## The Green potential of a bounded continuous source -/

section GreenPart

variable {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R βm βp r M : ℝ} {z : ℂ}

/-- **Regularity of the Green part**: absolute convergence and Hölder continuity on `cl B_r(z)`. -/
theorem greenPart_integrable_holder (hV : VolumeGrowth μ R βm βp) (hr : 0 < r)
    (hsub : ball z r ⊆ ball 0 R) {ψ : ℂ → ℝ} (hψc : ContinuousOn ψ (ball z r))
    (hψM : ∀ x ∈ ball z r, |ψ x| ≤ M) :
    (∀ x ∈ closedBall z r,
      IntegrableOn (fun y => greenFunction (ball z r) x y * ψ y) (ball z r) μ) ∧
    IsHolderContinuousOn (fun x => ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂μ)
      (closedBall z r) := by
  set f := (ball z r).indicator ψ with hf
  have hfm : AEStronglyMeasurable f μ :=
    (aestronglyMeasurable_indicator_iff measurableSet_ball).2
      (hψc.aestronglyMeasurable measurableSet_ball)
  have hfb : ∀ x, ‖f x‖ ≤ |M| := by
    intro x
    by_cases hx : x ∈ ball z r
    · rw [hf, indicator_of_mem hx, Real.norm_eq_abs]
      exact (hψM x hx).trans (le_abs_self M)
    · rw [hf, indicator_of_notMem hx, norm_zero]
      exact abs_nonneg M
  have hLp : MemLp f ⊤ (μ.restrict (closedBall z r)) :=
    memLp_top_of_bound hfm.restrict |M| (Eventually.of_forall hfb)
  obtain ⟨hI, C, t, ht, hH⟩ :=
    Section6.greenPotential_disc_holderOnWith_of_volumeGrowth hr hV hsub hLp
  have hEqOn : ∀ x, EqOn (fun y => greenFunction (ball z r) x y * f y)
      (fun y => greenFunction (ball z r) x y * ψ y) (ball z r) := fun x y hy => by
    simp only [hf, indicator_of_mem hy]
  have hfun : (fun x => ∫ y in ball z r, greenFunction (ball z r) x y * f y ∂μ) =
      fun x => ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂μ :=
    funext fun x => setIntegral_congr_fun measurableSet_ball (hEqOn x)
  refine ⟨fun x hx => (hI x hx).congr_fun (hEqOn x) measurableSet_ball, ?_⟩
  rw [← hfun]
  exact isHolderContinuousOn_of_holderOnWith isBounded_closedBall ht hH

omit [IsLocallyFiniteMeasure μ] in
/-- The Green part vanishes off the disc. -/
theorem greenPart_eq_zero_of_notMem {ψ : ℂ → ℝ} {x : ℂ} (hx : x ∉ ball z r) :
    ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂μ = 0 := by
  simp only [greenFunction_eq_zero_of_notMem_left hx, zero_mul, integral_zero]

/-- **Laplacian of the Green part**: `Δ(-c g) = c ψ μ` on `B_r(z)`, for `c ≥ 0`. -/
theorem greenPart_hasLaplacian (hV : VolumeGrowth μ R βm βp) (hr : 0 < r)
    (hsub : ball z r ⊆ ball 0 R) {ψ : ℂ → ℝ} (hψc : ContinuousOn ψ (ball z r))
    (hψM : ∀ x ∈ ball z r, |ψ x| ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    HasLaplacian (fun x => -(c * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂μ))
      (μ.withDensity fun x => ENNReal.ofReal (c * ψ x))
      (μ.withDensity fun x => ENNReal.ofReal (-(c * ψ x))) (ball z r) := by
  classical
  set M' := max M 1 with hM'def
  have hM' : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hinv : M' * M'⁻¹ = 1 := mul_inv_cancel₀ hM'.ne'
  have hV' := hV
  obtain ⟨-, hβp, r₀, hr₀, hgr⟩ := hV'
  -- the normalized positive and negative parts of `ψ`
  have hpart : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      let fσ : ℂ → ℝ := (ball z r).indicator (fun y => max (σ * ψ y) 0 / M')
      Measurable fσ ∧ (∀ y, 0 ≤ fσ y) ∧ (∀ y, fσ y ≤ 1) ∧ ContinuousOn fσ (ball z r) ∧
      HasLaplacian (fun x => ∫ y in ball z r, greenFunction (ball z r) x y * fσ y ∂μ) 0
        (μ.withDensity fun y => ENNReal.ofReal (fσ y)) (ball z r) := by
    intro σ hσ fσ
    have hσ1 : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
    have hσψ : ContinuousOn (fun y => σ * ψ y) (ball z r) := continuousOn_const.mul hψc
    have hmax : ContinuousOn (fun y => max (σ * ψ y) 0) (ball z r) :=
      (continuous_id.max continuous_const).comp_continuousOn hσψ
    have hcont : ContinuousOn (fun y => max (σ * ψ y) 0 / M') (ball z r) := hmax.div_const M'
    have hfc : ContinuousOn fσ (ball z r) := hcont.congr fun y hy => by
      simp only [fσ, indicator_of_mem hy]
    have hfm : Measurable fσ := by
      have h := hcont.measurable_piecewise (g := 0) continuous_zero.continuousOn measurableSet_ball
      rwa [Set.piecewise_eq_indicator] at h
    have hf0 : ∀ y, 0 ≤ fσ y := fun y => by
      by_cases hy : y ∈ ball z r
      · simp only [fσ, indicator_of_mem hy]
        exact div_nonneg (le_max_right _ _) hM'.le
      · simp only [fσ, indicator_of_notMem hy, le_refl]
    have hf1 : ∀ y, fσ y ≤ 1 := fun y => by
      by_cases hy : y ∈ ball z r
      · simp only [fσ, indicator_of_mem hy]
        rw [div_le_one hM']
        refine max_le ?_ hM'.le
        calc σ * ψ y ≤ |σ * ψ y| := le_abs_self _
          _ = |ψ y| := by rw [abs_mul, hσ1, one_mul]
          _ ≤ M := hψM y hy
          _ ≤ M' := le_max_left _ _
      · simp only [fσ, indicator_of_notMem hy]
        exact zero_le_one
    set ν := μ.withDensity fun y => ENNReal.ofReal (fσ y) with hν
    have hle : ν ≤ μ := withDensity_ofReal_le_of_le_one μ fσ hf1
    have : IsLocallyFiniteMeasure ν := Measure.isLocallyFiniteMeasure_of_le hle
    have hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball z r, ν (ball x s) ≤ ENNReal.ofReal (s ^ βp) :=
      fun s hs hsr x hx => (hle _).trans (hgr s hs hsr x (hsub hx)).2
    have hpot : (fun x => ∫ y in ball z r, greenFunction (ball z r) x y ∂ν) =
        fun x => ∫ y in ball z r, greenFunction (ball z r) x y * fσ y ∂μ := by
      funext x
      rw [hν, setIntegral_withDensity_eq_setIntegral_toReal_smul
        hfm.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
        _ measurableSet_ball]
      refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
      simp only [ENNReal.toReal_ofReal (hf0 y), smul_eq_mul, mul_comm]
    have hbound : ∀ x ∈ ball z r, |fσ x| ≤ 1 := fun x _ => by
      rw [abs_of_nonneg (hf0 x)]
      exact hf1 x
    obtain ⟨C, t, ht, -, hH⟩ :=
      (greenPart_integrable_holder (μ := μ) (M := 1) hV hr hsub hfc hbound).2
    have h := ballGreenPotential_hasLaplacian_of_upper ν hr hr₀ hβp hup
      (by rw [hpot]; exact hH.continuousOn ht)
    rw [hpot] at h
    exact ⟨hfm, hf0, hf1, hfc, h⟩
  obtain ⟨hpm, hp0, hp1, hpc, Hp⟩ := hpart 1 (Or.inl rfl)
  obtain ⟨hnm, hn0, hn1, hnc, Hn⟩ := hpart (-1) (Or.inr rfl)
  set fp : ℂ → ℝ := (ball z r).indicator (fun y => max (1 * ψ y) 0 / M') with hfp
  set fn : ℂ → ℝ := (ball z r).indicator (fun y => max (-1 * ψ y) 0 / M') with hfn
  have hk : 0 ≤ c * M' := mul_nonneg hc hM'.le
  have H := hasLaplacian_add (hasLaplacian_neg (hasLaplacian_const_mul_zero_left Hp hk))
    (hasLaplacian_const_mul_zero_left Hn hk)
  have hpb : ∀ x ∈ ball z r, |fp x| ≤ 1 := fun x _ => by rw [abs_of_nonneg (hp0 x)]; exact hp1 x
  have hnb : ∀ x ∈ ball z r, |fn x| ≤ 1 := fun x _ => by rw [abs_of_nonneg (hn0 x)]; exact hn1 x
  have hfun : (fun x => -(c * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂μ)) =
      fun x => -((c * M') * ∫ y in ball z r, greenFunction (ball z r) x y * fp y ∂μ) +
        (c * M') * ∫ y in ball z r, greenFunction (ball z r) x y * fn y ∂μ := by
    funext x
    by_cases hx : x ∈ ball z r
    · have hip := (greenPart_integrable_holder hV hr hsub hpc hpb).1 x (ball_subset_closedBall hx)
      have hin := (greenPart_integrable_holder hV hr hsub hnc hnb).1 x (ball_subset_closedBall hx)
      have hsplit : ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂μ =
          M' * ∫ y in ball z r, (greenFunction (ball z r) x y * fp y -
            greenFunction (ball z r) x y * fn y) ∂μ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
        simp only [hfp, hfn, indicator_of_mem hy, one_mul, neg_one_mul]
        have hmax : max (ψ y) 0 - max (-ψ y) 0 = ψ y := by
          rcases le_total 0 (ψ y) with h | h
          · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
          · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
        linear_combination (-(greenFunction (ball z r) x y)) * hmax -
          (greenFunction (ball z r) x y * (max (ψ y) 0 - max (-ψ y) 0)) * hinv
      rw [hsplit, integral_sub hip hin]
      ring
    · simp only [greenPart_eq_zero_of_notMem hx, mul_zero, neg_zero, add_zero]
  rw [hfun]
  refine hasLaplacian_congr_restrict H ?_ ?_
  · rw [add_zero, ← withDensity_smul _ hpm.ennreal_ofReal, restrict_withDensity measurableSet_ball,
      restrict_withDensity measurableSet_ball]
    refine withDensity_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hfp, indicator_of_mem hy, one_mul]
    rw [← ENNReal.ofReal_mul hk, ← ofReal_mul_max_zero hc]
    congr 1
    linear_combination (c * max (ψ y) 0) * hinv
  · rw [zero_add, ← withDensity_smul _ hnm.ennreal_ofReal, restrict_withDensity measurableSet_ball,
      restrict_withDensity measurableSet_ball]
    refine withDensity_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hfn, indicator_of_mem hy, neg_one_mul]
    rw [← ENNReal.ofReal_mul hk, show -(c * ψ y) = c * -ψ y by ring, ← ofReal_mul_max_zero hc]
    congr 1
    linear_combination (c * max (-ψ y) 0) * hinv

end GreenPart

end MatedCRT
