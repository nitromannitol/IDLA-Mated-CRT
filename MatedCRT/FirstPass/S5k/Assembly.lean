import MatedCRT.FirstPass.S5k.Graph.Main
import MatedCRT.FirstPass.S5k.Identify
import MatedCRT.FirstPass.Frozen.S5k

/-!
# First pass: assembly of the measurable obstacle (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Step 4.2 of `notes/fp-gaps/CHATGPT-z5-floor.md` (Part I), the final assembly: the measurable version `Ŵ` of the continuum
least supersolution is the decoder of (6) applied to the measure `μ|_{B̄_ρ}` (zero-replaced when it is not finite).
This file gives the two ingredients: the congruence of (6) under changes of the values outside the closed disk, and the
measurable zero-replacement of the restriction of a measure to the closed disk.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

open scoped Classical in
/-- The restriction of `μ` to the closed disk, replaced by the zero measure when it is not finite (Step 4.2). -/
noncomputable def restrictOrZero (ρ : ℝ) (μ : Measure ℂ) : Measure ℂ :=
  if IsFiniteMeasure (μ.restrict (closedBall (0 : ℂ) ρ)) then μ.restrict (closedBall (0 : ℂ) ρ) else 0

theorem restrictOrZero_mem (ρ : ℝ) (μ : Measure ℂ) :
    IsFiniteMeasure (restrictOrZero ρ μ) ∧
      (restrictOrZero ρ μ).restrict (closedBall (0 : ℂ) ρ) = restrictOrZero ρ μ := by
  unfold restrictOrZero
  split_ifs with h
  · exact ⟨h, by rw [Measure.restrict_restrict measurableSet_closedBall, Set.inter_self]⟩
  · exact ⟨inferInstance, Measure.restrict_zero _⟩

open scoped Classical in
theorem measurable_restrictOrZero (ρ : ℝ) : Measurable (restrictOrZero ρ) := by
  unfold restrictOrZero
  refine Measurable.ite ?_ ?_ measurable_const
  · have e : {μ : Measure ℂ | IsFiniteMeasure (μ.restrict (closedBall (0 : ℂ) ρ))} =
        {μ : Measure ℂ | μ (closedBall (0 : ℂ) ρ) ∈ ({⊤}ᶜ : Set ENNReal)} := by
      ext μ
      exact isFiniteMeasure_restrict
    rw [e]
    exact (Measure.measurable_coe measurableSet_closedBall) (measurableSet_singleton ⊤).compl
  · refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.restrict_apply hs]
    exact Measure.measurable_coe (hs.inter measurableSet_closedBall)

/-- The zero-replaced restriction, as an element of `M_f(B̄_ρ)`. -/
noncomputable def diskMeasOf (ρ : ℝ) (μ : Measure ℂ) : FinMeasDisk ρ :=
  ⟨restrictOrZero ρ μ, restrictOrZero_mem ρ μ⟩

theorem measurable_diskMeasOf (ρ : ℝ) : Measurable (diskMeasOf ρ) :=
  (measurable_restrictOrZero ρ).subtype_mk

open scoped Classical in
theorem restrictOrZero_eq_restrict {ρ : ℝ} {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) :
    restrictOrZero ρ μ = μ.restrict (closedBall (0 : ℂ) ρ) := by
  have hfin : IsFiniteMeasure (μ.restrict (closedBall (0 : ℂ) ρ)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  unfold restrictOrZero
  simp [hfin]

/-- Integrals `∫ w Δφ` against a test function on `B_ρ` depend only on the values of `w` on `B_ρ`. -/
theorem integral_mul_laplacian_congr {ρ : ℝ} {w w' φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) ρ) φ)
    (hw : EqOn w' w (ball (0 : ℂ) ρ)) :
    ∫ x, w' x * Δ φ x = ∫ x, w x * Δ φ x := by
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : ℂ) ρ
  · rw [hw hx]
  · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero, mul_zero]

/-- **Congruence of (6).** Changing the values of `w` outside the closed disk does not affect the solutions of (6). -/
theorem IsObstacleSolutionOn.congr_closedBall {ρ t : ℝ} {ν : Measure ℂ} {w w' : ℂ → ℝ}
    (hG : FrozenGreenDiscPole) (hρ : 0 < ρ) (ht : 0 < t)
    (h : IsObstacleSolutionOn ρ t ν w) (hw : EqOn w' w (closedBall (0 : ℂ) ρ)) :
    IsObstacleSolutionOn ρ t ν w' := by
  have hball : EqOn w' w (ball (0 : ℂ) ρ) := hw.mono ball_subset_closedBall
  have hU : floorObstacleCluster ρ t w ⊆ ball (0 : ℂ) ρ := fun x hx => (mem_obstacleCluster.1 hx).1
  have hUopen : IsOpen (floorObstacleCluster ρ t w) := isOpen_obstacleCluster hG hρ ht h.continuousOn
  have hcl : floorObstacleCluster ρ t w' = floorObstacleCluster ρ t w := by
    ext x
    simp only [mem_obstacleCluster]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨hx, ?_⟩
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (by rw [← hball hx]; exact hy)
    · rintro ⟨hx, hy⟩
      refine ⟨hx, ?_⟩
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (by rw [hball hx]; exact hy)
  refine ⟨h.continuousOn.congr hw, fun x hx => (hw (sphere_subset_closedBall hx)).trans (h.zero_on_sphere x hx),
    fun x hx hx0 => by rw [hw hx]; exact h.obstacle x hx hx0, ?_, ?_⟩
  · refine ⟨((h.continuousOn.congr hw).mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ hφ0 hint => ?_⟩
    rw [integral_mul_laplacian_congr hφ hball]
    exact h.laplacian_le.2 φ hφ hφ0 hint
  · rw [hcl]
    refine ⟨((h.continuousOn.congr hw).mono (hU.trans ball_subset_closedBall)).locallyIntegrableOn hUopen.measurableSet, fun φ hφ => ?_⟩
    obtain ⟨hI1, hI0, heq⟩ := h.laplacian_eq.2 φ hφ
    exact ⟨hI1, hI0, by rw [integral_mul_laplacian_congr (isTestFunction_of_subset hφ hU) hball, heq]⟩

end MatedCRT
