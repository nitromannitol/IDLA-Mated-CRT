import MatedCRT.FirstPass.Derived.GMS21UniformStartOfReference
import MatedCRT.FirstPass.Derived.UniformStartDilation
import MatedCRT.FirstPass.Derived.EnvironmentScalingHolds
import MatedCRT.FirstPass.Derived.QuantumConeScalingDerived
import MatedCRT.FirstPass.Derived.ConeScaleRadiusUniform
import MatedCRT.FirstPass.Derived.ConeScaleRadiusMeasurable
import MatedCRT.FirstPass.Derived.ConeScaledWalkData

/-!
# The uniform-start invariance principle at every small mesh from the reciprocal meshes

Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, is stated for the cell masses `1/n`. The uniform-start
statement `GMS21UniformStartInput` asks for every small positive mesh `ε`. The passage uses the exact scaling of the
environment (eq:scale-invariance-of-field-and-eta, `ConeEnvironmentScalingStep`, a theorem under the closure
properties `SLEModelClosureInput` of the model): for `n = ⌊1/ε⌋` and `c = n ε ∈ [1/2, 1]`, the rescaled
environment `S^c`, with curve `R_c⁻¹ η(c ·)` and boundary-length pair `c^{-1/2} bm(c ·)`, is a valid environment
of the same model, its mated-CRT map at mesh `ε / c = 1/n` is the map of `S` at mesh `ε`, and its embedded walk is the
`R_c⁻¹`-dilate of the walk of `S`.

The comparison at mesh `1/n` for `S^c` is made at the larger radius `R'' = (R + 2) L`, where `L` bounds `R_c⁻¹`
and `R_c ≤ M` on an event of probability at least `1 - θ/2` uniformly in `c ∈ [1/2, 1]` (monotonicity of the cone
scale radius in the mass, `ae_coneScaleRadius_mono`, and tightness of `R_{1/2}⁻¹` and of `sup_{b ≤ 1} R_b`).
Dilating back by `R_c`, and using Brownian scaling (`planarBrownianMotion_mul_apply`), the comparison holds for the
walk of `S` and Brownian motion both stopped at the variable radius `R_c R'' > R + 1`; the transfer from a variable
larger radius (`exists_forall_stopAtExit_le_of_forall_le_variable`) gives the comparison at the fixed radius `R`.
The probability of the comparison at mesh `1/n` for `S^c` must be bounded uniformly in `c`; this is the case when it
is bounded uniformly over all valid environments, for instance by the law-level bound on one reference environment
(`measure_compl_uniformStartGood_le_map`, `map_curveVersion_mult_eq_of_valid`).

## Main results

* `gms21UniformStartInput_of_uniform_reciprocal`: `GMS21UniformStartInput 𝒮` from the closure properties of `𝒮` and
  a bound at the reciprocal meshes `1/n` that is uniform over the valid environments.
* `uniformReciprocal_of_reference`: that uniform bound from the law-level bound on one reference environment.
* `gms21UniformStartInput_of_reference_reciprocal`: `GMS21UniformStartInput 𝒮` from the normalized law of `𝒮`, its
  closure properties, and the law-level bound at the reciprocal meshes `1/n` on one reference environment for each
  `γ`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open UniformStartDilation

/-- **The uniform-start invariance principle from the reciprocal meshes.** Let `𝒮` have the closure properties
`SLEModelClosureInput 𝒮`. Suppose that for each `0 < γ < 2`, all `0 < ρ < R` and `κ, θ > 0` there is `N` such that
for every `n ≥ N` and every valid environment `S` of `𝒮` (on any carrier), the failure probability of the
uniform-start comparison at the mesh `1/n` is at most `θ` (the bound is uniform over the environments; it holds when
the failure probability is controlled by the law of the environment, `uniformReciprocal_of_reference`). Then
`GMS21UniformStartInput 𝒮`. -/
theorem gms21UniformStartInput_of_uniform_reciprocal {𝒮 : SpaceFillingSLEModel} (h2 : SLEModelClosureInput 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        S.P {ω | ∀ x : ℤ, vertexPoint (1 / (n : ℝ)) (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (S.mult (1 / (n : ℝ)) ω) x
              {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (1 / (n : ℝ)) (S.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint (1 / (n : ℝ)) (S.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ}ᶜ ≤ ENNReal.ofReal θ) :
    GMS21UniformStartInput 𝒮 := by
  intro γ hγ0 hγ2 Ω _ S hS R ρ hρ hρR κ hκ θ hθ
  have := hS.isProbabilityMeasure
  have hEnv : ConeEnvironmentScalingStep 𝒮 :=
    coneEnvironmentScalingUnderSLE_of_scaling 𝒮 FirstPass.Derived.quantumConeScalingInput_derived
      h2.1 h2.2.1 h2.2.2
  -- the transfer from a variable larger radius to the radius `R`
  obtain ⟨δ, hδ, hvar⟩ :=
    StopAtExitCmp.exists_forall_stopAtExit_le_of_forall_le_variable (Ω' := ℕ → ℤ) hρR one_pos hκ hκ
  -- tails of the cone scale radii, uniformly in the mass parameter `b ∈ [1/2, 1]`
  have hθ4 : (0 : ℝ≥0∞) < ENNReal.ofReal (θ / 4) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨M, hM⟩ := FirstPass.Derived.exists_measure_coneScaleRadius_sup_le hγ0 hγ2 hS.isQuantumCone
    (B := 1) hθ4
  obtain ⟨M', hM'⟩ := FirstPass.Derived.exists_measure_gt_le_of_aemeasurable
    (FirstPass.Derived.aemeasurable_coneScaleRadius hγ0 hγ2 hS.isQuantumCone (1 / 2)).inv hθ4
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = max M' 1 := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max M 1 := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := hLdef ▸ le_max_right _ _
  have hK1 : 1 ≤ K := hKdef ▸ le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  -- the parameters of the comparison at the reciprocal meshes
  have hρ' : 0 < ρ * L := mul_pos hρ hL0
  have hρR' : ρ * L < (R + 2) * L := mul_lt_mul_of_pos_right (by linarith) hL0
  have hκ' : 0 < δ / K := div_pos hδ hK0
  obtain ⟨N, hN⟩ := hU γ hγ0 hγ2 ((R + 2) * L) (ρ * L) hρ' hρR' (δ / K) hκ' (θ / 2) (by positivity)
  refine ⟨min (1 / 2) (1 / ((N : ℝ) + 1)), lt_min (by norm_num) (by positivity), fun ε hε0 hεlt => ?_⟩
  -- the nearby reciprocal mesh
  have hε2 : ε < 1 / 2 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεN : ε < 1 / ((N : ℝ) + 1) := lt_of_lt_of_le hεlt (min_le_right _ _)
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ⌊1 / ε⌋₊ := ⟨_, rfl⟩
  have hn1 : (n : ℝ) ≤ 1 / ε := hndef ▸ Nat.floor_le (one_div_nonneg.2 hε0.le)
  have hn2 : 1 / ε < (n : ℝ) + 1 := hndef ▸ Nat.lt_floor_add_one (1 / ε)
  have hNlt : ((N : ℝ) + 1) < 1 / ε := by
    rw [lt_div_iff₀ hε0]
    rw [lt_div_iff₀ (by positivity)] at hεN
    linarith
  have hNn : N + 1 ≤ n := by
    rw [hndef]
    exact Nat.le_floor (by push_cast; exact hNlt.le)
  have hn0 : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (n : ℝ) * ε := ⟨_, rfl⟩
  have hc0 : 0 < c := hcdef ▸ mul_pos hn0 hε0
  have hc1 : c ≤ 1 := by
    rw [hcdef]
    calc (n : ℝ) * ε ≤ 1 / ε * ε := mul_le_mul_of_nonneg_right hn1 hε0.le
      _ = 1 := one_div_mul_cancel hε0.ne'
  have hc2 : 1 / 2 ≤ c := by
    have h3 : 1 < ((n : ℝ) + 1) * ε := by
      have := mul_lt_mul_of_pos_right hn2 hε0
      rwa [one_div, inv_mul_cancel₀ hε0.ne'] at this
    rw [hcdef]
    linarith
  have hεc : ε / c = 1 / (n : ℝ) := by
    rw [hcdef, mul_comm, ← div_div, div_self hε0.ne']
  -- the rescaled environment
  obtain ⟨Sc, hSc, hP, hη, hbm, -⟩ := hEnv γ hγ0 hγ2 Ω S hS c hc0
  have hfailc : S.P {ω | ∀ x : ℤ, vertexPoint (ε / c) (Sc.η ω) x ∈ closedBall (0 : ℂ) (ρ * L) →
      ∀ A : Set (ℝ≥0 → ℂ),
        srwLaw (Sc.mult (ε / c) ω) x
            {w | stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (interpolatedWalk (ε / c) (Sc.η ω) 1 w) ∈ A} ≤
          planarBrownianMotion (vertexPoint (ε / c) (Sc.η ω) x)
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) ((R + 2) * L)) ⇑b) f <
              ENNReal.ofReal (δ / K)} + ENNReal.ofReal (δ / K)}ᶜ ≤ ENNReal.ofReal (θ / 2) := by
    have h := hN n (by omega) Ω Sc hSc
    rw [← hεc, hP] at h
    exact h
  -- almost sure regularity of the radii
  have hpos : ∀ᵐ ω ∂S.P, ∀ b : ℝ, 0 < coneScaleRadius γ (S.hcirc ω) b := by
    filter_upwards [FirstPass.Derived.ae_coneRadialLevel hγ0 hγ2 hS.isQuantumCone] with ω hω b
    exact (FirstPass.Derived.coneScaleRadius_spec hω.1 hω.2.1 hω.2.2).1
  have hmono := FirstPass.Derived.ae_coneScaleRadius_mono hγ0 hγ2 hS.isQuantumCone
  -- the good event of `S` at mesh `ε` contains the good event of `S^c` at mesh `ε / c` off a small event
  have hsub : ∀ᵐ ω ∂S.P, ω ∈ {ω | ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ →
      ∀ A : Set (ℝ≥0 → ℂ),
        srwLaw (S.mult ε ω) x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
          planarBrownianMotion (vertexPoint ε (S.η ω) x)
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
            ENNReal.ofReal κ}ᶜ →
      ω ∈ {ω | ∀ x : ℤ, vertexPoint (ε / c) (Sc.η ω) x ∈ closedBall (0 : ℂ) (ρ * L) →
        ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (Sc.mult (ε / c) ω) x
              {w | stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (interpolatedWalk (ε / c) (Sc.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint (ε / c) (Sc.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) ((R + 2) * L)) ⇑b) f <
                ENNReal.ofReal (δ / K)} + ENNReal.ofReal (δ / K)}ᶜ ∪
        ({ω | ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ M < coneScaleRadius γ (S.hcirc ω) b} ∪
          {ω | M' < (coneScaleRadius γ (S.hcirc ω) (1 / 2))⁻¹}) := by
    filter_upwards [hpos, hmono, hη, hbm] with ω hωpos hωmono hωη hωbm
    intro hbad
    rw [mem_compl_iff] at hbad
    by_contra hcon
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, not_exists, not_and,
      not_lt] at hcon
    obtain ⟨hgood, hup, hlow⟩ := hcon
    apply hbad
    -- the dilation factor `r = R_c` and its bounds
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = coneScaleRadius γ (S.hcirc ω) c := ⟨_, rfl⟩
    have hr0 : 0 < r := hrdef ▸ hωpos c
    have hrK : r ≤ K := hrdef ▸ (hup c hc0 hc1).trans (hKdef ▸ le_max_left _ _)
    have hrL : r⁻¹ ≤ L := by
      have h12 : coneScaleRadius γ (S.hcirc ω) (1 / 2) ≤ r :=
        hrdef ▸ hωmono (1 / 2) c (by norm_num) hc2
      exact (inv_anti₀ (hωpos (1 / 2)) h12).trans (hlow.trans (hLdef ▸ le_max_left _ _))
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
    have hηω : ∀ s, Sc.η ω s = ((r : ℝ) : ℂ)⁻¹ * S.η ω (c * s) := by
      intro s
      rw [hωη s, hrdef]
    have hvert : ∀ k, vertexPoint (ε / c) (Sc.η ω) k = (r : ℂ)⁻¹ * vertexPoint ε (S.η ω) k :=
      ConeScaledWalkData.vertexPoint_rescale hc0 (S.η ω) (Sc.η ω) hηω
    have hmult : Sc.mult (ε / c) ω = S.mult ε ω := by
      unfold MatedCRTEnv.mult
      funext j k
      refine Sec1.bmEdgeCount_rescale hc0 (inv_pos.2 (Real.sqrt_pos.2 hc0)) _ _ _ _ (fun s => ?_)
        (fun s => ?_) j k
      · simp only [hωbm s, Prod.smul_fst, smul_eq_mul]
      · simp only [hωbm s, Prod.smul_snd, smul_eq_mul]
    intro x hx A
    -- the start of the rescaled walk
    have hzc : vertexPoint (ε / c) (Sc.η ω) x ∈ closedBall (0 : ℂ) (ρ * L) := by
      rw [hvert x, mem_closedBall_zero_iff, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hr0.le]
      have hx' : ‖vertexPoint ε (S.η ω) x‖ ≤ ρ := mem_closedBall_zero_iff.1 hx
      calc r⁻¹ * ‖vertexPoint ε (S.η ω) x‖ ≤ L * ρ :=
            mul_le_mul hrL hx' (norm_nonneg _) hL0.le
        _ = ρ * L := mul_comm _ _
    have hz : vertexPoint ε (S.η ω) x = (r : ℂ) * vertexPoint (ε / c) (Sc.η ω) x := by
      rw [hvert x, mul_inv_cancel_left₀ hrC]
    refine hvar (vertexPoint ε (S.η ω) x) hx (srwLaw (S.mult ε ω) x)
      (fun w => interpolatedWalk ε (S.η ω) 1 w)
      (fun w => continuous_interpolatedWalk ε 1 (S.η ω) w) ?_ A
    intro T
    -- the image of `T` at the larger radius for the rescaled walk
    have hgc := hgood x hzc
      ((fun g : ℝ≥0 → ℂ => stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (fun t => (r : ℂ)⁻¹ * g t)) '' T)
    have hwalk : {w : ℕ → ℤ | interpolatedWalk ε (S.η ω) 1 w ∈ T} ⊆
        {w | stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (interpolatedWalk (ε / c) (Sc.η ω) 1 w) ∈
          (fun g : ℝ≥0 → ℂ => stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (fun t => (r : ℂ)⁻¹ * g t)) '' T} := by
      intro w hw
      refine ⟨interpolatedWalk ε (S.η ω) 1 w, hw, ?_⟩
      dsimp only
      congr 1
      funext t
      exact (interpolatedWalk_eq_mul_of_vertexPoint hvert 1 w t).symm
    have hbm' : {b : ContinuousPath ℂ | ∃ f ∈ (fun g : ℝ≥0 → ℂ =>
          stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (fun t => (r : ℂ)⁻¹ * g t)) '' T,
          cmpEDist (stopAtExit (ball (0 : ℂ) ((R + 2) * L)) ⇑b) f < ENNReal.ofReal (δ / K)} ⊆
        {b | dilationPath hr0 b ∈ {b : ContinuousPath ℂ | ∃ g ∈ T, ∃ r' : ℝ, R + 1 < r' ∧
          cmpEDist (stopAtExit (ball (0 : ℂ) r') g) (stopAtExit (ball (0 : ℂ) r') ⇑b) <
            ENNReal.ofReal δ}} := by
      rintro b ⟨f, ⟨g, hgT, rfl⟩, hfb⟩
      refine ⟨g, hgT, r * ((R + 2) * L), ?_, ?_⟩
      · have h1' : 1 ≤ r * L := by
          have := mul_le_mul_of_nonneg_left hrL hr0.le
          rwa [mul_inv_cancel₀ hr0.ne'] at this
        nlinarith [mul_le_mul_of_nonneg_left h1' (by linarith : (0 : ℝ) ≤ R + 2)]
      · have hg : g = fun t => (r : ℂ) * ((r : ℂ)⁻¹ * g t) := by
          funext t
          rw [mul_inv_cancel_left₀ hrC]
        have hdb : (⇑(dilationPath hr0 b) : ℝ≥0 → ℂ) = fun t => (r : ℂ) * b (dilationTime r * t) := by
          funext t
          exact dilationPath_apply hr0 b t
        have hgs : stopAtExit (ball (0 : ℂ) (r * ((R + 2) * L))) g =
            fun t => (r : ℂ) * stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (fun t => (r : ℂ)⁻¹ * g t) t := by
          conv_lhs => rw [hg]
          exact stopAtExit_ball_mul hr0 _ _
        have hbs : stopAtExit (ball (0 : ℂ) (r * ((R + 2) * L))) ⇑(dilationPath hr0 b) =
            fun t => (r : ℂ) * stopAtExit (ball (0 : ℂ) ((R + 2) * L)) ⇑b (dilationTime r * t) := by
          rw [hdb, stopAtExit_ball_mul hr0, stopAtExit_comp_mul isOpen_ball b (dilationTime_pos hr0)]
        rw [hgs, hbs]
        refine cmpEDist_mul_comp_mul_lt (a := δ / K) hr0 (dilationTime_pos hr0) ?_ ?_
        · rwa [StopAtExitCmp.cmpEDist_comm] at hfb
        · calc r * (δ / K) ≤ K * (δ / K) := mul_le_mul_of_nonneg_right hrK hκ'.le
            _ = δ := by field_simp
    calc srwLaw (S.mult ε ω) x {w | interpolatedWalk ε (S.η ω) 1 w ∈ T}
        ≤ srwLaw (Sc.mult (ε / c) ω) x
            {w | stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (interpolatedWalk (ε / c) (Sc.η ω) 1 w) ∈
              (fun g : ℝ≥0 → ℂ => stopAtExit (ball (0 : ℂ) ((R + 2) * L))
                (fun t => (r : ℂ)⁻¹ * g t)) '' T} := by
          rw [hmult]
          exact measure_mono hwalk
      _ ≤ _ := hgc
      _ ≤ planarBrownianMotion (vertexPoint ε (S.η ω) x)
            {b | ∃ g ∈ T, ∃ r' : ℝ, R + 1 < r' ∧
              cmpEDist (stopAtExit (ball (0 : ℂ) r') g) (stopAtExit (ball (0 : ℂ) r') ⇑b) <
                ENNReal.ofReal δ} + ENNReal.ofReal δ := by
          refine add_le_add ?_ (ENNReal.ofReal_le_ofReal ?_)
          · rw [hz, planarBrownianMotion_mul_apply hr0]
            exact measure_mono hbm'
          · exact div_le_self hδ.le hK1
  calc S.P {ω | ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
        srwLaw (S.mult ε ω) x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
          planarBrownianMotion (vertexPoint ε (S.η ω) x)
            {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
            ENNReal.ofReal κ}ᶜ
      ≤ S.P ({ω | ∀ x : ℤ, vertexPoint (ε / c) (Sc.η ω) x ∈ closedBall (0 : ℂ) (ρ * L) →
        ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (Sc.mult (ε / c) ω) x
              {w | stopAtExit (ball (0 : ℂ) ((R + 2) * L)) (interpolatedWalk (ε / c) (Sc.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint (ε / c) (Sc.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) ((R + 2) * L)) ⇑b) f <
                ENNReal.ofReal (δ / K)} + ENNReal.ofReal (δ / K)}ᶜ ∪
        ({ω | ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ M < coneScaleRadius γ (S.hcirc ω) b} ∪
          {ω | M' < (coneScaleRadius γ (S.hcirc ω) (1 / 2))⁻¹})) := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (θ / 2) + (ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4)) :=
        (measure_union_le _ _).trans (add_le_add hfailc ((measure_union_le _ _).trans (add_le_add hM hM')))
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ θ / 4) (by positivity : (0 : ℝ) ≤ θ / 4),
          ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ θ / 2) (by positivity : (0 : ℝ) ≤ θ / 4 + θ / 4)]
        congr 1
        ring

/-- **The uniform reciprocal-mesh bound from one reference environment.** If `𝒮` has normalized law `ν` and, for
each `0 < γ < 2`, some model `𝒮₀` with law `ν` has a valid environment `S₀` with a measurable continuous version
`η₀` of its curve such that the law of `(η₀, S₀.mult (1/n))` gives mass at most `θ` to the complement of
`uniformStartGoodData (1/n) ρ R κ` for all large `n`, then the failure probability at the mesh `1/n` is at most
`θ` in every valid environment of `𝒮`, for the same `n`. -/
theorem uniformReciprocal_of_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartGoodData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        S.P {ω | ∀ x : ℤ, vertexPoint (1 / (n : ℝ)) (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (S.mult (1 / (n : ℝ)) ω) x
              {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk (1 / (n : ℝ)) (S.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint (1 / (n : ℝ)) (S.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ}ᶜ ≤ ENNReal.ofReal θ := by
  intro γ hγ0 hγ2 R ρ hρ hρR κ hκ θ hθ
  obtain ⟨𝒮₀, hν₀, Ω₀, _, S₀, hS₀, η₀, hη₀m, hη₀, hbd⟩ := hRef γ hγ0 hγ2
  obtain ⟨N, hN⟩ := hbd R ρ hρ hρR κ hκ θ hθ
  refine ⟨N, fun n hn Ω _ S hS => ?_⟩
  obtain ⟨η', hη'm, hη'⟩ := hS.exists_curveVersion
  refine (measure_compl_uniformStartGood_le_map hS hη'm hη' (1 / (n : ℝ)) ρ R κ).trans ?_
  rw [map_curveVersion_mult_eq_of_valid h1 hν₀ hγ0 hγ2 hS hS₀ hη'm hη' hη₀m hη₀ (1 / (n : ℝ))]
  exact hN n hn

/-- **The uniform-start invariance principle from the reciprocal meshes on one reference environment.** Let `𝒮`
have normalized space-filling SLE law `ν` and the closure properties `SLEModelClosureInput 𝒮`. Suppose that for each
`0 < γ < 2` some model `𝒮₀` with the same law `ν` has a valid environment `S₀` (on any carrier) with a measurable
continuous version `η₀` of its curve, such that for all `0 < ρ < R` and `κ, θ > 0`, for all large `n` the law of
`(η₀, S₀.mult (1/n))` gives mass at most `θ` to the complement of `uniformStartGoodData (1/n) ρ R κ`
(Gwynne–Miller–Sheffield, arXiv:1705.11161, Theorem 3.4, at the cell masses `1/n`, on the reference environment).
Then `GMS21UniformStartInput 𝒮`. -/
theorem gms21UniformStartInput_of_reference_reciprocal {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartGoodData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    GMS21UniformStartInput 𝒮 :=
  gms21UniformStartInput_of_uniform_reciprocal h2 (uniformReciprocal_of_reference h1 hRef)

end MatedCRT
