import MatedCRT.FirstPass.S5k.Graph.HasLapCover
import MatedCRT.FirstPass.S5k.Graph.Obstacle
import MatedCRT.FirstPass.S5k.Graph.LapCount
import MatedCRT.FirstPass.S5k.Decoder
import MatedCRT.FirstPass.Frozen.S5k

/-!
# First pass: the Borel graph of (6) and its measurable decoder (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Step 4.1 and Step 4.2 of `notes/fp-gaps/CHATGPT-z5-floor.md` (Part I). The set of pairs `(ν, f) ∈ M_f(K) × C(K)` for which
`f` solves (6) for `ν` (`IsObstacleSolutionOn`, pole `0`) is a Borel set (`measurableSet_isObstacle_graph`), by a countable
presentation of each condition; it projects injectively (uniqueness, `IsObstacleSolutionOn.eqOn_closedBall`). The
Lusin-Souslin decoder (`Decoder.lean`) then gives a measurable map `F : M_f(K) → C(K)`, which is the solution of (6) on
the projection and `0` off it (`exists_decoder_disk`). The frozen standard Borel structure of `M_f(K)` is an input.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

/-- A fixed countable dense subset of `ℂ`. -/
noncomputable def denseC : Set ℂ := Classical.choose (TopologicalSpace.exists_countable_dense ℂ)

theorem denseC_spec : denseC.Countable ∧ Dense denseC :=
  Classical.choose_spec (TopologicalSpace.exists_countable_dense ℂ)

/-- A fixed countable dense subset of the sphere `∂B_ρ`. -/
noncomputable def Phis (ρ : ℝ) : Set ℂ :=
  Classical.choose (exists_countable_dense_family (sphere (0 : ℂ) ρ) (id : ℂ → ℂ))

theorem Phis_spec (ρ : ℝ) : Phis ρ ⊆ sphere (0 : ℂ) ρ ∧ (Phis ρ).Countable ∧
    ∀ x ∈ sphere (0 : ℂ) ρ, x ∈ closure (Phis ρ) := by
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec
    (exists_countable_dense_family (sphere (0 : ℂ) ρ) (id : ℂ → ℂ))
  exact ⟨h1, h2, fun x hx => by simpa [Phis] using h3 x hx⟩

/-- A fixed countable dense subset of the punctured open disk `B_ρ ∖ {0}`. -/
noncomputable def Phio (ρ : ℝ) : Set ℂ :=
  Classical.choose (exists_countable_dense_family (ball (0 : ℂ) ρ \ {0}) (id : ℂ → ℂ))

theorem Phio_spec (ρ : ℝ) : Phio ρ ⊆ ball (0 : ℂ) ρ \ {0} ∧ (Phio ρ).Countable ∧
    ∀ x ∈ ball (0 : ℂ) ρ \ {0}, x ∈ closure (Phio ρ) := by
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec
    (exists_countable_dense_family (ball (0 : ℂ) ρ \ {0}) (id : ℂ → ℂ))
  exact ⟨h1, h2, fun x hx => by simpa [Phio] using h3 x hx⟩

/-- A fixed countable family of nonnegative test functions for `Δw ≤ ν`. -/
noncomputable def Phil (ρ : ℝ) : Set (NonnegTest ρ) := Classical.choose (exists_countable_psiTest ρ)

theorem Phil_spec (ρ : ℝ) : (Phil ρ).Countable ∧ ∀ a, psiTest a ∈ closure (psiTest '' Phil ρ) :=
  Classical.choose_spec (exists_countable_psiTest ρ)

/-- **Countable presentation of (6).** `f` solves (6) for `ν` iff the countable families of conditions hold. -/
theorem isObstacleSolutionOn_extDisk_iff {ρ t : ℝ} (hG : FrozenGreenDiscPole) (hρ : 0 < ρ) (ht : 0 < t)
    (ν : FinMeasDisk ρ) (f : DiskFun ρ) :
    IsObstacleSolutionOn ρ t (ν : Measure ℂ) (extDisk ρ f) ↔
      (∀ d ∈ Phis ρ, extDisk ρ f d = 0) ∧
      (∀ d ∈ Phio ρ, -t * greenFunction (ball 0 ρ) 0 d ≤ extDisk ρ f d) ∧
      (∀ a ∈ Phil ρ, Lf ν f (psiTest a) ≤ 0) ∧
      (∀ q₀ ∈ denseC, ∀ r c : ℚ, AdmDisk ρ q₀ r → 0 < c → HypDisk ρ t denseC f q₀ r c →
        ∀ φ ∈ Phidisk ρ (ball q₀ (r : ℝ)), Lf ν f (psiF (ρ := ρ) φ) = 0) := by
  obtain ⟨hs1, hs2, hs3⟩ := Phis_spec ρ
  obtain ⟨ho1, ho2, ho3⟩ := Phio_spec ρ
  obtain ⟨hl1, hl2⟩ := Phil_spec ρ
  obtain ⟨hD1, hD2⟩ := denseC_spec
  constructor
  · intro h
    refine ⟨(zero_sphere_iff_dense f hs1 hs3).1 h.zero_on_sphere, ?_, ?_, ?_⟩
    · exact (obstacle_ball_iff_dense hG hρ f ho1 ho3).1
        (fun x hx => h.obstacle x (ball_subset_closedBall hx.1) hx.2)
    · exact (laplacianLE_extDisk_iff ν f hl2).1 h.laplacian_le
    · exact (hasLaplacian_extDisk_iff hG hρ ht hD2 ν f).1 h.laplacian_eq
  · rintro ⟨h1, h2, h3, h4⟩
    have hzero : ∀ x ∈ sphere (0 : ℂ) ρ, extDisk ρ f x = 0 := (zero_sphere_iff_dense f hs1 hs3).2 h1
    refine ⟨continuousOn_extDisk f, hzero, ?_, ?_, ?_⟩
    · exact obstacle_closedBall_of f ((obstacle_ball_iff_dense hG hρ f ho1 ho3).2 h2) hzero
    · exact (laplacianLE_extDisk_iff ν f hl2).2 h3
    · exact (hasLaplacian_extDisk_iff hG hρ ht hD2 ν f).2 h4

/-- The Borel graph of (6): a measurable subset of `M_f(K) × C(K)`. -/
theorem measurableSet_isObstacle_graph {ρ t : ℝ} (hG : FrozenGreenDiscPole) (hρ : 0 < ρ) (ht : 0 < t) :
    MeasurableSet {p : FinMeasDisk ρ × DiskFun ρ | IsObstacleSolutionOn ρ t (p.1 : Measure ℂ) (extDisk ρ p.2)} := by
  obtain ⟨hs1, hs2, -⟩ := Phis_spec ρ
  obtain ⟨ho1, ho2, -⟩ := Phio_spec ρ
  obtain ⟨hl1, -⟩ := Phil_spec ρ
  obtain ⟨hD1, -⟩ := denseC_spec
  have e : {p : FinMeasDisk ρ × DiskFun ρ | IsObstacleSolutionOn ρ t (p.1 : Measure ℂ) (extDisk ρ p.2)} =
      {p : FinMeasDisk ρ × DiskFun ρ | ∀ d ∈ Phis ρ, extDisk ρ p.2 d = 0} ∩
      ({p : FinMeasDisk ρ × DiskFun ρ | ∀ d ∈ Phio ρ, -t * greenFunction (ball 0 ρ) 0 d ≤ extDisk ρ p.2 d} ∩
      ({p : FinMeasDisk ρ × DiskFun ρ | ∀ a ∈ Phil ρ, Lf p.1 p.2 (psiTest a) ≤ 0} ∩
      {p : FinMeasDisk ρ × DiskFun ρ | ∀ q₀ ∈ denseC, ∀ r c : ℚ, AdmDisk ρ q₀ r → 0 < c →
        HypDisk ρ t denseC p.2 q₀ r c → ∀ φ ∈ Phidisk ρ (ball q₀ (r : ℝ)), Lf p.1 p.2 (psiF (ρ := ρ) φ) = 0})) := by
    ext p
    exact isObstacleSolutionOn_extDisk_iff hG hρ ht p.1 p.2
  rw [e]
  refine ((measurableSet_zero_family (ρ := ρ) hs2).preimage measurable_snd).inter
    (((measurableSet_obstacle_family (ρ := ρ) (t := t) ho2).preimage measurable_snd).inter
      ((measurableSet_laplacianLE_family (ρ := ρ) hl1).inter (measurableSet_hasLap_family (ρ := ρ) (t := t) hD1)))

/-- Two solutions of (6) for `ν` have equal extension by zero, hence the same element of `C(K)`. -/
theorem diskFun_eq_of_isObstacle {ρ t : ℝ} {ν : FinMeasDisk ρ} {y₁ y₂ : DiskFun ρ}
    (h₁ : IsObstacleSolutionOn ρ t (ν : Measure ℂ) (extDisk ρ y₁))
    (h₂ : IsObstacleSolutionOn ρ t (ν : Measure ℂ) (extDisk ρ y₂)) : y₁ = y₂ := by
  refine ContinuousMap.ext fun x => ?_
  have h := h₁.eqOn_closedBall h₂ x.2
  rwa [extDisk_apply_of_mem _ x.2, extDisk_apply_of_mem _ x.2] at h

/-- **Measurable decoder of (6).** There is a measurable `F : M_f(K) → C(K)` which solves (6) for `ν` whenever some
continuous function does, and vanishes otherwise. -/
theorem exists_decoder_disk {ρ t : ℝ} (hSB : FrozenFiniteMeasureDiskStandardBorel) (hG : FrozenGreenDiscPole)
    (hρ : 0 < ρ) (ht : 0 < t) :
    ∃ F : FinMeasDisk ρ → DiskFun ρ, Measurable F ∧
      (∀ ν : FinMeasDisk ρ, (∃ f : DiskFun ρ, IsObstacleSolutionOn ρ t (ν : Measure ℂ) (extDisk ρ f)) →
        IsObstacleSolutionOn ρ t (ν : Measure ℂ) (extDisk ρ (F ν))) ∧
      (∀ ν : FinMeasDisk ρ, (¬ ∃ f : DiskFun ρ, IsObstacleSolutionOn ρ t (ν : Measure ℂ) (extDisk ρ f)) →
        F ν = 0) := by
  have : StandardBorelSpace (FinMeasDisk ρ) := hSB ρ hρ
  obtain ⟨F, hFm, hF1, hF2⟩ := exists_measurable_section_of_injective (0 : DiskFun ρ)
    {p : FinMeasDisk ρ × DiskFun ρ | IsObstacleSolutionOn ρ t (p.1 : Measure ℂ) (extDisk ρ p.2)}
    (measurableSet_isObstacle_graph hG hρ ht)
    (fun ν y₁ y₂ h₁ h₂ => diskFun_eq_of_isObstacle h₁ h₂)
  exact ⟨F, hFm, fun ν hν => hF1 ν (by
      obtain ⟨f, hf⟩ := hν
      exact ⟨f, hf⟩), fun ν hν => hF2 ν (fun ⟨y, hy⟩ => hν ⟨y, hy⟩)⟩

end MatedCRT
