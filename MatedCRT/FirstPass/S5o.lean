import MatedCRT.FirstPass.S5l
import MatedCRT.FirstPass.S5k
import MatedCRT.FirstPass.S5d.FloorProof
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# FirstPass S5o: discharge of the floor constant input `FloorConstantStep` (Prop 5.1, Part I §5)

Helper facts for the instantiation of the generic constant of `FirstPass/S5l.lean` at the Green function of the disc
`G_{B_ρ}(0,·)` (Armitage-Gardiner §4.1, `HarmonicBalls.greenFunction`) and at the continuum surplus.

* `greenPole ρ` is `G_{B_ρ}(0,·) = greenFunction (ball 0 ρ) 0`; on `B̄_ρ \ {0}` it equals `(2π)⁻¹ log(ρ/|z|)`
  (`greenPole_eq_log`, from `greenFunction_ball`), vanishes on `∂B_ρ` (`greenPole_eq_zero_of_norm`), is continuous on
  `B̄_ρ \ {0}` (`continuousOn_greenPole`) and tends to `+∞` at the pole (`tendsto_greenPole`).
* `floorBound α ρ Ŵ` is the measurable bound `M(ω) = sup_{q ∈ ℚ+iℚ ∩ B_ρ} |α Ŵ(ω,q)|` of `FloorConstantStep`;
  `floorBound_bound` shows `|α Ŵ(ω,x)| ≤ M(ω)` for every `x ∈ B̄_ρ` (density of `ℚ+iℚ` and continuity of `Ŵ(ω)` on `B̄_ρ`).

The Green-function facts are proved from `HarmonicBalls.greenFunction_ball` (Harmonic-Balls-LQG). The only hypotheses of
`floorConstantStep_proved` are the measurable obstacle version `StoppedFloorObstacleVersion` (§4) and the strict
obstacle gap `HarmonicBallStrictObstacleGapStep` ([C20]; proved as `firstPass_strictObstacleGap`, `S4S5b.lean:25`, under
its frozen inputs). No new frozen statement is introduced here.
-/

namespace MatedCRT.S5o

open MeasureTheory Metric Set Filter Topology
open _root_.HarmonicBalls
open MatedCRT.S5l
open scoped Classical

/-- The Green function of the disc `B_ρ` with pole `0`, as a function of the second variable:
`G_{B_ρ}(0,·)` of §5. -/
noncomputable def greenPole (ρ : ℝ) : ℂ → ℝ := greenFunction (ball (0 : ℂ) ρ) 0

/-- On `B̄_ρ \ {0}` the Green function of the disc with pole `0` is `(2π)⁻¹ log(ρ/|z|)`. -/
theorem greenPole_eq_log {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) ρ) (hz0 : z ≠ 0) :
    greenPole ρ z = (2 * Real.pi)⁻¹ * Real.log (ρ / ‖z‖) := by
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  by_cases hzρ : z ∈ ball (0 : ℂ) ρ
  · unfold greenPole
    rw [greenFunction_ball (mem_ball_self hρ) hzρ (Ne.symm hz0)]
    unfold greenBall
    have h1 : ‖(ρ : ℂ) ^ 2 - (starRingEnd ℂ) 0 * z‖ = ρ ^ 2 := by
      simp [Complex.norm_real, abs_of_pos hρ]
    have h2 : ‖(0 : ℂ) - z‖ = ‖z‖ := by simp
    rw [h1, h2, show ρ ^ 2 / (ρ * ‖z‖) = ρ / ‖z‖ by field_simp]
  · have hn : ‖z‖ = ρ :=
      le_antisymm (mem_closedBall_zero_iff.1 hz) (not_lt.1 (fun h => hzρ (mem_ball_zero_iff.2 h)))
    unfold greenPole
    rw [greenFunction_ball_of_le_norm (le_of_eq hn.symm) 0, hn, div_self hρ.ne', Real.log_one, mul_zero]

/-- The Green function of the disc vanishes on `∂B_ρ`. -/
theorem greenPole_eq_zero_of_norm {ρ : ℝ} {z : ℂ} (h : ‖z‖ = ρ) : greenPole ρ z = 0 :=
  greenFunction_ball_of_le_norm (le_of_eq h.symm) 0

/-- `G_{B_ρ}(0,·)` is continuous on `B̄_ρ \ {0}`. -/
theorem continuousOn_greenPole {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (greenPole ρ) (closedBall (0 : ℂ) ρ \ {0}) := by
  have hH : ContinuousOn (fun z : ℂ => (2 * Real.pi)⁻¹ * Real.log (ρ / ‖z‖)) (closedBall (0 : ℂ) ρ \ {0}) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log
    · exact continuousOn_const.div continuous_norm.continuousOn (fun z hz => norm_ne_zero_iff.2 hz.2)
    · intro z hz
      exact (div_pos hρ (norm_pos_iff.2 hz.2)).ne'
  exact hH.congr (fun z hz => greenPole_eq_log hρ hz.1 hz.2)

/-- `G_{B_ρ}(0,·) → +∞` at the pole. -/
theorem tendsto_greenPole {ρ : ℝ} (hρ : 0 < ρ) : Tendsto (greenPole ρ) (𝓝[≠] (0 : ℂ)) atTop := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuous_norm.tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact norm_pos_iff.2 hz
  have hlog : Tendsto (fun z : ℂ => Real.log ‖z‖) (𝓝[≠] (0 : ℂ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hnorm
  have hlin : Tendsto (fun z : ℂ => Real.log ρ + -Real.log ‖z‖) (𝓝[≠] (0 : ℂ)) atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp hlog)
  have hH : Tendsto (fun z : ℂ => (2 * Real.pi)⁻¹ * Real.log (ρ / ‖z‖)) (𝓝[≠] (0 : ℂ)) atTop := by
    have hpos : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
    refine (hlin.const_mul_atTop hpos).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Real.log_div hρ.ne' (norm_pos_iff.2 hz).ne', sub_eq_add_neg]
  have hball : ball (0 : ℂ) ρ ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))
  refine hH.congr' ?_
  filter_upwards [hball, self_mem_nhdsWithin] with z hz1 hz2
  exact (greenPole_eq_log hρ (ball_subset_closedBall hz1) hz2).symm

/-- The term `z ↦ |α Ŵ(ω,z)|` of the bound `M` on `ℚ+iℚ ∩ B_ρ`, and `0` off `B_ρ`. -/
noncomputable def floorBound (α ρ : ℝ) {Ω : Type*} (What : Ω → ℂ → ℝ) (ω : Ω) : ℝ :=
  ⨆ p : ℚ × ℚ, (if ratCentre p ∈ ball (0 : ℂ) ρ then |α * What ω (ratCentre p)| else 0)

/-- The bound `M` is measurable for the σ-algebra on `Ω` (countable supremum of measurable terms). -/
theorem floorBound_measurable {Ω : Type*} [MeasurableSpace Ω] {α ρ : ℝ} {What : Ω → ℂ → ℝ}
    (hWm : ∀ x, Measurable fun ω => What ω x) : Measurable (floorBound α ρ What) := by
  unfold floorBound
  refine Measurable.iSup fun p => ?_
  by_cases h : ratCentre p ∈ ball (0 : ℂ) ρ
  · have hfun : (fun ω => if ratCentre p ∈ ball (0 : ℂ) ρ then |α * What ω (ratCentre p)| else 0) =
        fun ω => |α * What ω (ratCentre p)| := by
      funext ω
      simp [h]
    rw [hfun]
    exact continuous_abs.measurable.comp ((hWm (ratCentre p)).const_mul α)
  · have hfun : (fun ω => if ratCentre p ∈ ball (0 : ℂ) ρ then |α * What ω (ratCentre p)| else 0) =
        fun _ => (0 : ℝ) := by
      funext ω
      simp [h]
    rw [hfun]
    exact measurable_const

/-- The bound dominates `|α Ŵ(ω,x)|` on the closed disc: density of `ℚ+iℚ ∩ B_ρ` in `B̄_ρ` and continuity of
`Ŵ(ω)` on `B̄_ρ`. -/
theorem floorBound_bound {Ω : Type*} {α ρ : ℝ} {What : Ω → ℂ → ℝ} (hρ : 0 < ρ)
    (hWc : ∀ ω, ContinuousOn (What ω) (closedBall (0 : ℂ) ρ)) (ω : Ω) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, |α * What ω x| ≤ floorBound α ρ What ω := by
  intro x hx
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn (hWc ω)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self hρ.le))
  have hbdd : BddAbove (Set.range fun p : ℚ × ℚ =>
      (if ratCentre p ∈ ball (0 : ℂ) ρ then |α * What ω (ratCentre p)| else 0)) := by
    refine ⟨|α| * C, ?_⟩
    rintro _ ⟨p, rfl⟩
    dsimp only
    split_ifs with h
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using hC _ (ball_subset_closedBall h)) (abs_nonneg α)
    · exact mul_nonneg (abs_nonneg α) hC0
  have hdense : closedBall (0 : ℂ) ρ ⊆ closure (ball (0 : ℂ) ρ ∩ ratComplex) := by
    have h1 : ball (0 : ℂ) ρ ⊆ closure (ball (0 : ℂ) ρ ∩ ratComplex) :=
      ratComplex_dense.open_subset_closure_inter isOpen_ball
    have h2 : closure (ball (0 : ℂ) ρ) ⊆ closure (ball (0 : ℂ) ρ ∩ ratComplex) :=
      closure_minimal h1 isClosed_closure
    rwa [closure_ball (0 : ℂ) hρ.ne'] at h2
  have hS : ∀ z ∈ ball (0 : ℂ) ρ ∩ ratComplex, |α * What ω z| ≤ floorBound α ρ What ω := by
    rintro z ⟨hzB, p, rfl⟩
    have hterm : (if ratCentre p ∈ ball (0 : ℂ) ρ then |α * What ω (ratCentre p)| else 0) =
        |α * What ω (ratCentre p)| := by
      simp [hzB]
    unfold floorBound
    rw [← hterm]
    exact le_ciSup hbdd p
  have hcont : ContinuousOn (fun z => |α * What ω z|) (closure (ball (0 : ℂ) ρ ∩ ratComplex)) := by
    have hc : ContinuousOn (fun z => |α * What ω z|) (closedBall (0 : ℂ) ρ) :=
      continuous_abs.comp_continuousOn (continuousOn_const.mul (hWc ω))
    exact hc.mono (closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall)
  exact le_on_closure (f := fun z => |α * What ω z|) (g := fun _ => floorBound α ρ What ω) hS hcont
    continuousOn_const (hdense hx)

/-- **The floor constant input `FloorConstantStep` (Prop 5.1, Part I §5), discharged.** The measurable obstacle version
`Ŵ` of §4 (`StoppedFloorObstacleVersion`) and the strict obstacle gap (`HarmonicBallStrictObstacleGapStep`, [C20]) give
the constant `s = floorConstant (c₀/6) t ρ δ G Ŵ` of (9) and the bound `M = floorBound (c₀/6) ρ Ŵ`, with `G = G_{B_ρ}(0,·)`:
`s` is measurable for `S.fieldSigma` and `0 < s ≤ 1` everywhere (Step 5.1); on the good event `Λ_t ⊆ 𝒞_t = cluster`
the ball `B(x, δ/4)` lies in `{φ_ω > 0}` for `x ∈ B⁻_{δ/4}(Λ_t) \ {0}`, so `s ≤ φ_ω(x) ≤ α(Ŵ + tG)(x)` (Step 5.2, (11));
and `|α Ŵ| ≤ M` on `B̄_ρ` (density). -/
theorem floorConstantStep_proved (𝒮 : SpaceFillingSLEModel)
    (hobs : MatedCRT.StoppedFloorObstacleVersion 𝒮)
    (hgap : MatedCRT.HarmonicBallStrictObstacleGapStep 𝒮) :
    MatedCRT.FloorProof.FloorConstantStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨What, hWm, hWc, hWb, hagree⟩ := hobs γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  have hgapS := hgap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht
  have hc0 : 0 < S.c₀ := div_pos two_pos (hS.m₀_pos hγ hγ2)
  have hα : 0 < S.c₀ / 6 := div_pos hc0 (by norm_num)
  have hWb' : ∀ ω x, ‖x‖ = ρ → What ω x = 0 := fun ω x hx => hWb ω x (mem_sphere_zero_iff_norm.2 hx)
  have hGc := continuousOn_greenPole hρ
  have hGb : ∀ x : ℂ, ‖x‖ = ρ → greenPole ρ x = 0 := fun x hx => greenPole_eq_zero_of_norm hx
  have hGp := tendsto_greenPole hρ
  refine ⟨floorConstant (S.c₀ / 6) t ρ δ (greenPole ρ) What,
    floorBound (S.c₀ / 6) ρ What, ?_, ?_, ?_, ?_⟩
  · exact @floorConstant_measurable Ω S.fieldSigma (S.c₀ / 6) t ρ δ (greenPole ρ) What hWm
  · exact @floorBound_measurable Ω S.fieldSigma (S.c₀ / 6) ρ What hWm
  · intro ω
    exact ⟨floorConstant_pos hα ht hρ hδ hWc hWb' hGc hGb hGp ω,
      floorConstant_le_one (S.c₀ / 6) t ρ δ (greenPole ρ) What ω⟩
  · filter_upwards [hagree, hgapS] with ω hω1 hω2 hT
    have hW := hω1 hT
    have hsub := hω2 hT
    refine ⟨fun x hx hx0 => ?_, fun x hx => ?_⟩
    · have hball : ball x (δ / 4) ⊆ {y | 0 < floorPhi (S.c₀ / 6) t ρ (greenPole ρ) What ω y} := by
        intro y hy
        have hyΛ : y ∈ Λ ω t := by
          by_contra hyΛ
          have h1 : Metric.infEDist x (Λ ω t)ᶜ ≤ edist x y := Metric.infEDist_le_edist_of_mem hyΛ
          have h2 : edist x y < ENNReal.ofReal (δ / 4) := by
            rw [edist_dist]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [dist_comm]; exact mem_ball.1 hy)
          exact lt_irrefl _ (lt_of_le_of_lt (hx.2.trans h1) h2)
        obtain ⟨hyB, hyc⟩ := hsub hyΛ
        show 0 < floorPhi (S.c₀ / 6) t ρ (greenPole ρ) What ω y
        by_cases hy0 : y = 0
        · simp [floorPhi, hy0]
        · have hn : ‖y‖ < ρ := mem_ball_zero_iff.1 hyB
          have hyc' : -t * greenPole ρ y < _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t y :=
            hyc.resolve_left hy0
          have hWy : What ω y = _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t y :=
            hW y (ball_subset_closedBall hyB)
          have e : -t * greenPole ρ y = -(t * greenPole ρ y) := by ring
          have h' : 0 < _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t y + t * greenPole ρ y := by
            rw [e] at hyc'
            linarith
          have key : 0 < S.c₀ / 6 * (What ω y + t * greenPole ρ y) := by
            rw [hWy]
            exact mul_pos hα h'
          have hfp : floorPhi (S.c₀ / 6) t ρ (greenPole ρ) What ω y =
              min 1 (max 0 (S.c₀ / 6 * (What ω y + t * greenPole ρ y))) := by
            simp [floorPhi, hy0, hn]
          rw [hfp]
          exact lt_min one_pos (lt_max_of_lt_right key)
      have hc := floorConstant_controls hα ht hρ hδ hWc hWb' hGc hGb hGp ω x hx0 hball
      have hxB : x ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall (hsub hx.1).1
      have h2 : floorPhi (S.c₀ / 6) t ρ (greenPole ρ) What ω x ≤
          S.c₀ / 6 * (_root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x + t * greenPole ρ x) := by
        rw [← hW x hxB]
        exact hc.2
      exact hc.1.trans h2
    · rw [← hW x hx]
      exact floorBound_bound hρ hWc ω x hx

end MatedCRT.S5o
