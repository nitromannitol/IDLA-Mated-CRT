import MatedCRT.FirstPass.S5k.Graph.HasLap
import MatedCRT.FirstPass.S5k.Graph.LapCount

/-!
# First pass: the cover of the cluster by admissible disks and the countable presentation of `Δw = ν`
(task fp-S5k-5-1-floor-obstacle-version, worker z10)

Step 4.1 of `notes/fp-gaps/CHATGPT-z5-floor.md` (Part I), the last condition of (6). Every point of the cluster
`U_w` lies in an admissible rational disk on which `w + tG > c` at the rational points (`exists_disk_cover`); conversely
such a disk lies in `U_w` (`ball_subset_obstacleCluster`). With the localization `vanish_of_local`, the identity
`Δw = ν` on `U_w` is equivalent to its countable form on the disks (`hasLaplacian_extDisk_iff`), and the set of `(ν, f)`
satisfying the countable form is measurable (`measurableSet_hasLap_family`).
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

/-- **Cover of the cluster.** Every point of `U_w` lies in an admissible disk with a rational test (pole: `G → +∞`). -/
theorem exists_disk_cover {ρ t : ℝ} (hG : FrozenGreenDiscPole) (hρ : 0 < ρ) (ht : 0 < t) {D₀ : Set ℂ}
    (hD₀d : Dense D₀) (f : DiskFun ρ) {x : ℂ} (hx : x ∈ floorObstacleCluster ρ t (extDisk ρ f)) :
    ∃ q₀ ∈ D₀, ∃ r c : ℚ, AdmDisk ρ q₀ r ∧ 0 < c ∧ HypDisk ρ t D₀ f q₀ r c ∧ x ∈ ball q₀ (r : ℝ) := by
  obtain ⟨hxb, hxc⟩ := mem_obstacleCluster.1 hx
  by_cases hx0 : x = 0
  · subst hx0
    have hev := (hG ρ hρ).2.eventually_gt_atTop ((‖f‖ + 1) / t)
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
    have hmin : 0 < min ε ρ := lt_min hε hρ
    obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show (0 : ℝ) < min ε ρ / 2 by linarith)
    obtain ⟨q₀, hq₀D, hq₀b⟩ := hD₀d.exists_mem_open (isOpen_ball (x := (0 : ℂ)) (ε := (r : ℝ) / 2))
      ⟨0, mem_ball_self (by linarith)⟩
    have hq₀n : dist q₀ 0 < (r : ℝ) / 2 := hq₀b
    refine ⟨q₀, hq₀D, r, 1, ⟨by linarith, ?_⟩, by norm_num, ?_, ?_⟩
    · intro y hy
      rw [mem_ball] at hy ⊢
      have := dist_triangle y q₀ 0
      linarith [min_le_right ε ρ]
    · intro q _ hqb hq0
      rw [mem_ball] at hqb
      have hqε : dist q 0 < ε := by
        have := dist_triangle q q₀ 0
        linarith [min_le_left ε ρ]
      have hG' : (‖f‖ + 1) / t < greenFunction (ball 0 ρ) 0 q :=
        hεP hqε hq0
      have h2 : (‖f‖ + 1) < greenFunction (ball 0 ρ) 0 q * t := (div_lt_iff₀ ht).mp hG'
      have h3 := abs_extDisk_le f q
      have h4 := (abs_le.1 h3).1
      push_cast
      nlinarith
    · rw [mem_ball, dist_comm]
      linarith
  · have hlt : -t * greenFunction (ball 0 ρ) 0 x < extDisk ρ f x := hxc.resolve_left hx0
    have hm : (0 : ℝ) < extDisk ρ f x + t * greenFunction (ball 0 ρ) 0 x := by linarith
    obtain ⟨c, hc0, hcm⟩ := exists_rat_btwn hm
    have hOopen : IsOpen (ball (0 : ℂ) ρ \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball (0 : ℂ) ρ \ {0}) :=
      (hG ρ hρ).1.mono (fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩)
    have hcont : ContinuousOn (fun y => extDisk ρ f y + t * greenFunction (ball 0 ρ) 0 y)
        (ball (0 : ℂ) ρ \ {0}) :=
      ((continuousOn_extDisk f).mono (fun y hy => ball_subset_closedBall hy.1)).add
        (continuousOn_const.mul hGc)
    have hWopen := hcont.isOpen_inter_preimage hOopen (isOpen_Ioi (a := (c : ℝ)))
    have hxW : x ∈ (ball (0 : ℂ) ρ \ {0}) ∩ (fun y => extDisk ρ f y + t * greenFunction (ball 0 ρ) 0 y) ⁻¹' Ioi (c : ℝ) :=
      ⟨⟨hxb, hx0⟩, hcm⟩
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWopen x hxW
    obtain ⟨q₀, hq₀D, hq₀b⟩ := hD₀d.exists_mem_open (isOpen_ball (x := x) (ε := ε / 3))
      ⟨x, mem_ball_self (by linarith)⟩
    have hq₀n : dist q₀ x < ε / 3 := hq₀b
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 3 < 2 * ε / 3 by linarith)
    have hWsub : ∀ y, y ∈ ball q₀ (r : ℝ) → y ∈ ball x ε := by
      intro y hy
      rw [mem_ball] at hy ⊢
      have := dist_triangle y q₀ x
      linarith
    refine ⟨q₀, hq₀D, r, c, ⟨by linarith, ?_⟩, by exact_mod_cast hc0, ?_, ?_⟩
    · intro y hy
      have hyW := hεW (hWsub y hy)
      exact hyW.1.1
    · intro q _ hqb hq0
      have hyW := hεW (hWsub q hqb)
      exact hyW.2
    · rw [mem_ball, dist_comm]
      linarith

/-- **Countable presentation of `Δw = ν` on the cluster.** The distributional identity on the cluster holds iff it holds
on the test functions of the countable dense family of each admissible disk where the rational test holds. -/
theorem hasLaplacian_extDisk_iff {ρ t : ℝ} (hG : FrozenGreenDiscPole) (hρ : 0 < ρ) (ht : 0 < t)
    {D₀ : Set ℂ} (hD₀d : Dense D₀) (ν : FinMeasDisk ρ) (f : DiskFun ρ) :
    HasLaplacian (extDisk ρ f) (ν : Measure ℂ) 0 (floorObstacleCluster ρ t (extDisk ρ f)) ↔
      ∀ q₀ ∈ D₀, ∀ r c : ℚ, AdmDisk ρ q₀ r → 0 < c → HypDisk ρ t D₀ f q₀ r c →
        ∀ φ ∈ Phidisk ρ (ball q₀ (r : ℝ)), Lf ν f (psiF (ρ := ρ) φ) = 0 := by
  have : IsFiniteMeasure (ν : Measure ℂ) := ν.2.1
  constructor
  · intro hH q₀ _ r c hadm hc hyp φ hφ
    have hφt : IsTestFunction (ball q₀ (r : ℝ)) φ := (Phidisk_spec ρ _).1 hφ
    have hφU : IsTestFunction (floorObstacleCluster ρ t (extDisk ρ f)) φ :=
      isTestFunction_of_subset hφt (ball_subset_obstacleCluster hG hρ hD₀d f hadm hc hyp)
    obtain ⟨-, -, heq⟩ := hH.2 φ hφU
    rw [Lf_psiF ν f hφt]
    unfold Lt
    rw [integral_zero_measure, sub_zero] at heq
    linarith
  · intro hall
    let I := {p : D₀ × ℚ × ℚ // AdmDisk ρ (p.1 : ℂ) p.2.1 ∧ 0 < p.2.2 ∧ HypDisk ρ t D₀ f (p.1 : ℂ) p.2.1 p.2.2}
    have hDU : ∀ i : I, ball ((i.1.1 : ℂ)) ((i.1.2.1 : ℚ) : ℝ) ⊆ floorObstacleCluster ρ t (extDisk ρ f) :=
      fun i => ball_subset_obstacleCluster hG hρ hD₀d f i.2.1 (by exact_mod_cast i.2.2.1) i.2.2.2
    have hU : floorObstacleCluster ρ t (extDisk ρ f) ⊆ ⋃ i : I, ball ((i.1.1 : ℂ)) ((i.1.2.1 : ℚ) : ℝ) := by
      intro x hx
      obtain ⟨q₀, hq₀, r, c, hadm, hc, hyp, hxb⟩ := exists_disk_cover hG hρ ht hD₀d f hx
      exact Set.mem_iUnion.2 ⟨⟨⟨⟨q₀, hq₀⟩, r, c⟩, hadm, by exact_mod_cast hc, hyp⟩, hxb⟩
    have hUball : floorObstacleCluster ρ t (extDisk ρ f) ⊆ ball (0 : ℂ) ρ := fun x hx => (mem_obstacleCluster.1 hx).1
    have hvan := vanish_of_local (U := floorObstacleCluster ρ t (extDisk ρ f))
      (fun i : I => ball ((i.1.1 : ℂ)) ((i.1.2.1 : ℚ) : ℝ)) (fun i => isOpen_ball) hDU hU (Lt ν f)
      (fun φ ψ hφ hψ => Lt_add ν f hUball hφ hψ) (Lt_zero ν f)
      (fun i φ hφ => Lt_eq_zero_of_Phidisk ν f
        (fun φ' hφ' => hall i.1.1.1 i.1.1.2 i.1.2.1 i.1.2.2 i.2.1 i.2.2.1 i.2.2.2 φ' hφ') φ hφ)
    refine ⟨(locallyIntegrableOn_extDisk f).mono_set hUball, fun φ hφ => ⟨?_, integrable_zero_measure, ?_⟩⟩
    · exact hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
    · have h0 := hvan φ hφ
      unfold Lt at h0
      rw [integral_zero_measure, sub_zero]
      linarith

/-- The countable presentation is measurable in `(ν, f)`. -/
theorem measurableSet_hasLap_family {ρ t : ℝ} {D₀ : Set ℂ} (hD₀c : D₀.Countable) :
    MeasurableSet {p : FinMeasDisk ρ × DiskFun ρ | ∀ q₀ ∈ D₀, ∀ r c : ℚ, AdmDisk ρ q₀ r → 0 < c →
      HypDisk ρ t D₀ p.2 q₀ r c → ∀ φ ∈ Phidisk ρ (ball q₀ (r : ℝ)), Lf p.1 p.2 (psiF (ρ := ρ) φ) = 0} := by
  -- the rational test is measurable in `f`
  have hHyp : ∀ (q₀ : ℂ) (r c : ℚ), MeasurableSet {p : FinMeasDisk ρ × DiskFun ρ | HypDisk ρ t D₀ p.2 q₀ r c} := by
    intro q₀ r c
    have e : {p : FinMeasDisk ρ × DiskFun ρ | HypDisk ρ t D₀ p.2 q₀ r c} =
        ⋂ q ∈ D₀, {p : FinMeasDisk ρ × DiskFun ρ | q ∈ ball q₀ (r : ℝ) → q ≠ 0 →
          (c : ℝ) < extDisk ρ p.2 q + t * greenFunction (ball 0 ρ) 0 q} := by
      ext p
      simp only [HypDisk, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [e]
    refine MeasurableSet.biInter hD₀c fun q _ => ?_
    refine MeasurableSet.imp (MeasurableSet.const _) (MeasurableSet.imp (MeasurableSet.const _) ?_)
    exact measurableSet_lt measurable_const
      ((((measurable_extDisk_eval q).comp measurable_snd)).add measurable_const)
  -- the countable identity for a fixed test function is measurable
  have hLf : ∀ φ : ℂ → ℝ, MeasurableSet {p : FinMeasDisk ρ × DiskFun ρ | Lf p.1 p.2 (psiF (ρ := ρ) φ) = 0} := by
    intro φ
    have hA : Measurable fun p : FinMeasDisk ρ × DiskFun ρ =>
        ∫ x, extDisk ρ p.2 x * extDisk ρ (psiF (ρ := ρ) φ).2 x :=
      (continuous_integral_extDisk_mul_left (psiF (ρ := ρ) φ).2).measurable.comp measurable_snd
    have hB : Measurable fun p : FinMeasDisk ρ × DiskFun ρ =>
        ∫ x, extDisk ρ (psiF (ρ := ρ) φ).1 x ∂(p.1 : Measure ℂ) :=
      measurable_integral_finMeasDisk (a := fun x => extDisk ρ (psiF (ρ := ρ) φ).1 x)
        (measurable_extDisk _) (C := ‖(psiF (ρ := ρ) φ).1‖) (fun x => abs_extDisk_le _ x) |>.comp measurable_fst
    exact measurableSet_eq_fun (hA.sub hB) measurable_const
  have e : {p : FinMeasDisk ρ × DiskFun ρ | ∀ q₀ ∈ D₀, ∀ r c : ℚ, AdmDisk ρ q₀ r → 0 < c →
      HypDisk ρ t D₀ p.2 q₀ r c → ∀ φ ∈ Phidisk ρ (ball q₀ (r : ℝ)), Lf p.1 p.2 (psiF (ρ := ρ) φ) = 0} =
      ⋂ q₀ ∈ D₀, ⋂ r : ℚ, ⋂ c : ℚ, ⋂ φ ∈ Phidisk ρ (ball q₀ (r : ℝ)),
        {p : FinMeasDisk ρ × DiskFun ρ | AdmDisk ρ q₀ r → 0 < c → HypDisk ρ t D₀ p.2 q₀ r c →
          Lf p.1 p.2 (psiF (ρ := ρ) φ) = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h q₀ hq₀ r c φ hφ hA hc hy => h q₀ hq₀ r c hA hc hy φ hφ,
      fun h q₀ hq₀ r c hA hc hy φ hφ => h q₀ hq₀ r c φ hφ hA hc hy⟩
  rw [e]
  refine MeasurableSet.biInter hD₀c fun q₀ _ => ?_
  refine MeasurableSet.iInter fun r => ?_
  refine MeasurableSet.iInter fun c => ?_
  refine MeasurableSet.biInter (Phidisk_spec ρ _).2.1 fun φ _ => ?_
  exact MeasurableSet.imp (MeasurableSet.const _) (MeasurableSet.imp (MeasurableSet.const _)
    (MeasurableSet.imp (hHyp q₀ r c) (hLf φ)))

end MatedCRT
