import MatedCRT.FirstPass.S5k.Graph.Lap
import MatedCRT.FirstPass.Frozen.S2g

/-!
# First pass: countable presentation of the boundary and obstacle conditions

The conditions of (6) that are not differential: `w = 0` on
`∂B_ρ` and `w ≥ -tG` on `B̄_ρ ∖ {0}`. Each is a closed condition in `w`, so it is tested on a countable dense subset:
the sphere for the boundary values, and the punctured open disk for the obstacle (the sphere case of the obstacle follows
from the boundary values, because `G_{B_ρ}(0,·) = 0` off the open disk). The disc Green function is continuous off its pole
by `FrozenGreenDiscPole` (Frozen/S2g.lean).
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology HarmonicBalls

theorem measurable_extDisk_eval {ρ : ℝ} (a : ℂ) : Measurable fun f : DiskFun ρ => extDisk ρ f a := by
  by_cases h : a ∈ closedBall (0 : ℂ) ρ
  · have e : (fun f : DiskFun ρ => extDisk ρ f a) = fun f => f ⟨a, h⟩ := by
      funext f
      exact extDisk_apply_of_mem f h
    rw [e]
    exact measurable_diskFun_eval ⟨a, h⟩
  · have e : (fun f : DiskFun ρ => extDisk ρ f a) = fun _ => (0 : ℝ) := by
      funext f
      exact extDisk_apply_of_notMem f h
    rw [e]
    exact measurable_const

/-- Off the open disk the disc Green function `G_{B_ρ}(0,·)` vanishes (junk value of `greenFunction`). -/
theorem greenFunction_ball_eq_zero_of_notMem {ρ : ℝ} {x : ℂ} (hx : x ∉ ball (0 : ℂ) ρ) :
    greenFunction (ball 0 ρ) 0 x = 0 := by
  unfold greenFunction
  simp [hx]

/-- A closed condition on the boundary: `w = 0` on the sphere iff it holds on a dense countable subset of the sphere. -/
theorem zero_sphere_iff_dense {ρ : ℝ} (f : DiskFun ρ) {D : Set ℂ} (hDs : D ⊆ sphere (0 : ℂ) ρ)
    (hdense : ∀ x ∈ sphere (0 : ℂ) ρ, x ∈ closure D) :
    (∀ x ∈ sphere (0 : ℂ) ρ, extDisk ρ f x = 0) ↔ ∀ d ∈ D, extDisk ρ f d = 0 := by
  constructor
  · intro h d hd
    exact h d (hDs hd)
  · intro h
    have hE := EqOn.of_subset_closure (f := extDisk ρ f) (g := fun _ => (0 : ℝ)) (s := D)
      (t := sphere (0 : ℂ) ρ) (fun d hd => h d hd) ((continuousOn_extDisk f).mono sphere_subset_closedBall)
      continuousOn_const hDs hdense
    intro x hx
    exact hE hx

/-- A function continuous on an open set `O` which is nonnegative on a dense subset of `O` is nonnegative on `O`. -/
theorem nonneg_of_dense_on_open {O D : Set ℂ} {h : ℂ → ℝ} (hO : IsOpen O) (hh : ContinuousOn h O)
    (hdense : ∀ x ∈ O, x ∈ closure D) (hD : ∀ d ∈ D, 0 ≤ h d) : ∀ x ∈ O, 0 ≤ h x := by
  intro x hx
  by_contra hneg
  have hneg' : h x < 0 := not_le.mp hneg
  have hev : ∀ᶠ y in 𝓝 x, h y < 0 :=
    (hh.continuousAt (hO.mem_nhds hx)).eventually_lt continuousAt_const hneg'
  obtain ⟨d, hd1, hd2⟩ := (mem_closure_iff_nhds.1 (hdense x hx)) _ hev
  exact absurd (hD d hd2) (not_le.mpr hd1)

/-- The obstacle inequality `-tG ≤ w` on the punctured open disk holds iff it holds on a dense countable subset of it. -/
theorem obstacle_ball_iff_dense {ρ t : ℝ} (hG : FrozenGreenDiscPole) (hρ : 0 < ρ) (f : DiskFun ρ)
    {D : Set ℂ} (hDO : D ⊆ ball (0 : ℂ) ρ \ {0}) (hdense : ∀ x ∈ ball (0 : ℂ) ρ \ {0}, x ∈ closure D) :
    (∀ x ∈ ball (0 : ℂ) ρ \ {0}, -t * greenFunction (ball 0 ρ) 0 x ≤ extDisk ρ f x) ↔
      ∀ d ∈ D, -t * greenFunction (ball 0 ρ) 0 d ≤ extDisk ρ f d := by
  constructor
  · intro h d hd
    exact h d (hDO hd)
  · intro h
    have hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball (0 : ℂ) ρ \ {0}) :=
      (hG ρ hρ).1.mono (sdiff_subset_sdiff_left ball_subset_closedBall)
    have hcont : ContinuousOn (fun y => extDisk ρ f y - -t * greenFunction (ball 0 ρ) 0 y)
        (ball (0 : ℂ) ρ \ {0}) :=
      ((continuousOn_extDisk f).mono (sdiff_subset.trans ball_subset_closedBall)).sub
        (continuousOn_const.mul hGc)
    have key := nonneg_of_dense_on_open (isOpen_ball.sdiff isClosed_singleton) hcont hdense
      (fun d hd => sub_nonneg.2 (h d hd))
    intro x hx
    exact sub_nonneg.1 (key x hx)

/-- The obstacle inequality on the closed disk minus the pole, from the open disk and the boundary values. -/
theorem obstacle_closedBall_of {ρ t : ℝ} (f : DiskFun ρ)
    (hball : ∀ x ∈ ball (0 : ℂ) ρ \ {0}, -t * greenFunction (ball 0 ρ) 0 x ≤ extDisk ρ f x)
    (hsph : ∀ x ∈ sphere (0 : ℂ) ρ, extDisk ρ f x = 0) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ 0 → -t * greenFunction (ball 0 ρ) 0 x ≤ extDisk ρ f x := by
  intro x hx hx0
  by_cases hxb : x ∈ ball (0 : ℂ) ρ
  · exact hball x ⟨hxb, hx0⟩
  · have hxs : x ∈ sphere (0 : ℂ) ρ := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hx, hxb⟩
    rw [greenFunction_ball_eq_zero_of_notMem hxb, hsph x hxs]
    simp

/-- Countable presentation of the boundary condition: a finite family on the sphere. -/
theorem measurableSet_zero_family {ρ : ℝ} {Φs : Set ℂ} (hΦs : Φs.Countable) :
    MeasurableSet {f : DiskFun ρ | ∀ d ∈ Φs, extDisk ρ f d = 0} := by
  have e : {f : DiskFun ρ | ∀ d ∈ Φs, extDisk ρ f d = 0} = ⋂ d ∈ Φs, {f : DiskFun ρ | extDisk ρ f d = 0} := by
    ext f
    simp
  rw [e]
  exact MeasurableSet.biInter hΦs fun d _ => (measurable_extDisk_eval d) (measurableSet_singleton 0)

/-- Countable presentation of the obstacle inequality. -/
theorem measurableSet_obstacle_family {ρ t : ℝ} {Φo : Set ℂ} (hΦo : Φo.Countable) :
    MeasurableSet {f : DiskFun ρ | ∀ d ∈ Φo, -t * greenFunction (ball 0 ρ) 0 d ≤ extDisk ρ f d} := by
  have e : {f : DiskFun ρ | ∀ d ∈ Φo, -t * greenFunction (ball 0 ρ) 0 d ≤ extDisk ρ f d} =
      ⋂ d ∈ Φo, {f : DiskFun ρ | -t * greenFunction (ball 0 ρ) 0 d ≤ extDisk ρ f d} := by
    ext f
    simp
  rw [e]
  exact MeasurableSet.biInter hΦo fun d _ => measurableSet_le measurable_const (measurable_extDisk_eval d)

end MatedCRT
