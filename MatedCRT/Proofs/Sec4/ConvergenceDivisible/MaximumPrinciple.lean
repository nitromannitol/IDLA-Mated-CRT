import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitCDF
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-! Maximum-principle ingredients for the continuum obstacle comparison. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls Laplacian
open scoped ENNReal

/-- Wherever a candidate lies strictly above the scaled least supersolution, it lies
strictly above the obstacle away from the pole. This does not require the obstacle
inequality to hold strictly on the interior of a closure. -/
theorem strict_comparison_subset_noncoincidence
    {μ : Measure ℂ} {ρ t c : ℝ} {w : ℂ → ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    {x ∈ ball (0 : ℂ) ρ | c * leastSupersolution μ ρ 0 t x < w x} ⊆
      {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * c * greenFunction (ball 0 ρ) 0 x < w x} := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have h := mul_le_mul_of_nonneg_left (le_leastSupersolution (μ := μ) ht (ball_subset_closedBall hx.1) hx0) hc
    have hid : c * (-t * greenFunction (ball 0 ρ) 0 x) =
        -t * c * greenFunction (ball 0 ρ) 0 x := by ring
    rw [hid] at h
    exact h.trans_lt hx.2

/-- A nonempty bounded open set cannot support a positive weakly subharmonic
function that is continuous on its closure and nonpositive on its boundary. -/
theorem eq_empty_of_positive_laplacianGE_zero {W : Set ℂ} {f : ℂ → ℝ}
    (hW : IsOpen W) (hWb : Bornology.IsBounded W) (hfc : ContinuousOn f (closure W))
    (hpos : ∀ x ∈ W, 0 < f x) (hfr : ∀ x ∈ frontier W, f x ≤ 0)
    (hLap : LaplacianGE f 0 W) : W = ∅ := by
  have hneg : LaplacianLE (-f) 0 W := by
    refine ⟨hLap.1.neg, fun φ hφ hφ0 _ => ?_⟩
    have h := (hLap.2 φ hφ hφ0).2
    simp only [integral_zero_measure] at h
    simpa only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] using neg_nonpos.mpr h
  have hsuper := superharmonicOfLaplacianLEStep_holds W (-f) hW
    ((hfc.mono subset_closure).neg) hneg
  apply eq_empty_of_pos_of_subMean hWb hfc hpos hfr
  intro x hx
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hW x hx
  have hr2 : 0 < r / 2 := half_pos hr
  have hsub : closedBall x (r / 2) ⊆ W :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrsub
  refine ⟨r / 2, hr2, hsub, ?_⟩
  have hm := (hsuper.2 x hx (r / 2) hr2 hsub).2
  rw [circleAverage_neg_fun, Pi.neg_apply] at hm
  linarith

/-- If the candidate has Laplacian `c μ` and the continuum solution has
Laplacian `μ` restricted to a set, their difference is weakly subharmonic. -/
theorem laplacianGE_sub_scaled_of_restrict
    {μ : Measure ℂ} {Λ U W : Set ℂ} {w v : ℂ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hWU : W ⊆ U)
    (hw : HasLaplacian w (ENNReal.ofReal c • μ) 0 W)
    (hv : HasLaplacian v (μ.restrict Λ) 0 U) :
    LaplacianGE (fun x => w x - c * v x) 0 W := by
  have hv' : LocallyIntegrableOn v W := hv.1.mono_set hWU
  refine ⟨hw.1.sub (hv'.smul c), fun φ hφ hφ0 => ?_⟩
  have hφU : IsTestFunction U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hWU⟩
  obtain ⟨hφμ, _, hwφ⟩ := hw.2 φ hφ
  obtain ⟨_, _, hvφ⟩ := hv.2 φ hφU
  have hwint := integrable_mul_laplacian hw.1 hφ
  have hvint := (integrable_mul_laplacian hv' hφ).const_mul c
  have hfun : (fun x => (w x - c * v x) * Δ φ x) =
      fun x => w x * Δ φ x - c * (v x * Δ φ x) := by
    funext x
    ring
  have hmeasure := integral_mono_measure
    (Measure.restrict_le_self : (ENNReal.ofReal c • μ).restrict Λ ≤ ENNReal.ofReal c • μ)
    (Filter.Eventually.of_forall hφ0) hφμ
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hc] at hmeasure
  refine ⟨integrable_zero_measure, ?_⟩
  rw [hfun, integral_sub hwint hvint, integral_const_mul, hwφ, hvφ]
  simp only [integral_zero_measure, sub_zero, smul_eq_mul] at *
  linarith

/-- A continuous function which is weakly subharmonic on its positive set and
nonpositive on the boundary of a ball is nonpositive on the closed ball. -/
theorem le_zero_of_laplacianGE_on_positive_set {ρ : ℝ} {f : ℂ → ℝ}
    (hfc : ContinuousOn f (closedBall 0 ρ))
    (hboundary : ∀ x ∈ sphere (0 : ℂ) ρ, f x ≤ 0)
    (hLap : LaplacianGE f 0 {x ∈ ball (0 : ℂ) ρ | 0 < f x}) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, f x ≤ 0 := by
  let W : Set ℂ := {x ∈ ball (0 : ℂ) ρ | 0 < f x}
  have hWo : IsOpen W := by
    have h := (hfc.mono ball_subset_closedBall).isOpen_inter_preimage (t := Ioi (0 : ℝ)) isOpen_ball isOpen_Ioi
    exact h
  have hWsub : W ⊆ ball (0 : ℂ) ρ := fun _ hx => hx.1
  have hcl : closure W ⊆ closedBall (0 : ℂ) ρ :=
    (closure_mono hWsub).trans closure_ball_subset_closedBall
  have hfr : ∀ x ∈ frontier W, f x ≤ 0 := by
    intro x hx
    have hxcl : x ∈ closedBall (0 : ℂ) ρ := hcl (frontier_subset_closure hx)
    by_cases hxb : x ∈ ball (0 : ℂ) ρ
    · by_contra hn
      have hxW : x ∈ W := ⟨hxb, lt_of_not_ge hn⟩
      rw [hWo.frontier_eq] at hx
      exact hx.2 hxW
    · apply hboundary x
      apply mem_sphere.mpr
      have hle := mem_closedBall.mp hxcl
      have hge : ρ ≤ dist x (0 : ℂ) := le_of_not_gt (fun h => hxb (mem_ball.mpr h))
      exact le_antisymm hle hge
  have hempty : W = ∅ := eq_empty_of_positive_laplacianGE_zero hWo
    (isBounded_ball.subset hWsub) (hfc.mono hcl) (fun _ hx => hx.2) hfr hLap
  intro x hx
  by_cases hxb : x ∈ ball (0 : ℂ) ρ
  · by_contra hn
    have hxW : x ∈ W := ⟨hxb, lt_of_not_ge hn⟩
    rw [hempty] at hxW
    exact hxW
  · apply hboundary x
    apply mem_sphere.mpr
    have hle := mem_closedBall.mp hx
    have hge : ρ ≤ dist x (0 : ℂ) := le_of_not_gt (fun h => hxb (mem_ball.mpr h))
    exact le_antisymm hle hge

/-- The harmonic-ball characterization and the weak maximum principle give the
reverse obstacle comparison on the closed ball. -/
theorem obstacleLimitMaximumPrinciple (𝒮 : SpaceFillingSLEModel) :
    ObstacleLimitMaximumPrincipleStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ
  have hc : 0 < S.c₀ / 6 := matedCRTScalingConstantPositive 𝒮 γ hγ hγ2 Ω S hS
  filter_upwards [hΛ] with ω hfam
  intro t ht hT w hw hbound _ hLap _ x hx
  have hnonempty : {s : ℝ | 0 < s ∧ Λ ω s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    have hempty : {s : ℝ | 0 < s ∧ Λ ω s ⊆ ball 0 (ρ / 3)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    have hT' := hT
    simp only [clusterExitTime, hempty, Real.sSup_empty] at hT'
    linarith
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hnonempty hT
  have hsub : Λ ω t ⊆ ball 0 (ρ / 3) :=
    (hfam.2.1.monotoneOn ht hs.1 hts.le).trans hs.2
  have hchar := hfam.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)
  let v : ℂ → ℝ := leastSupersolution (S.μ ω) ρ 0 t
  let f : ℂ → ℝ := fun y => w y - (S.c₀ / 6) * v y
  let W : Set ℂ := {y ∈ ball (0 : ℂ) ρ | 0 < f y}
  have hWsub : W ⊆ {y ∈ ball (0 : ℂ) ρ |
      y = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 y < w y} := by
    intro y hy
    apply strict_comparison_subset_noncoincidence ht.le hc.le
    exact ⟨hy.1, sub_pos.mp hy.2⟩
  have hwLap : HasLaplacian w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) 0 W := by
    refine ⟨hLap.1.mono_set hWsub, fun φ hφ => hLap.2 φ ?_⟩
    exact ⟨hφ.1, hφ.2.1, hφ.2.2.trans hWsub⟩
  have hfLap : LaplacianGE f 0 W :=
    laplacianGE_sub_scaled_of_restrict hc.le (fun _ hy => hy.1) hwLap hchar.2.2.1
  have hfc : ContinuousOn f (closedBall 0 ρ) := hw.sub (continuousOn_const.mul hchar.2.1)
  have hboundary : ∀ y ∈ sphere (0 : ℂ) ρ, f y ≤ 0 := by
    intro y hy
    have hw0 := obstacleLimit_eq_zero_on_sphere hρ hbound y hy
    have hv0 := hchar.2.2.2 y hy
    simp [f, v, hw0, hv0]
  have hf := le_zero_of_laplacianGE_on_positive_set hfc hboundary hfLap x hx
  dsimp [f, v] at hf
  linarith

/-- The regularity and maximum-principle comparisons identify every candidate
limit with the scaled continuum least supersolution. -/
theorem obstacleLimitUniqueness (𝒮 : SpaceFillingSLEModel) :
    ObstacleLimitUniquenessStep 𝒮 :=
  obstacleLimitUniqueness_of_steps 𝒮
    (obstacleLimitRegularity_of_steps 𝒮 (matedCRTScalingConstantPositive 𝒮))
    (obstacleLimitMaximumPrinciple 𝒮)

end MatedCRT
