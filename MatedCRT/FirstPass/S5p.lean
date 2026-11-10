import MatedCRT.FirstPass.S5k
import MatedCRT.FirstPass.S5k.Identify
import MatedCRT.FirstPass.S5k.Decoder
import MatedCRT.FirstPass.S5k.Graph.Basic
import MatedCRT.FirstPass.S5k.Graph.Obstacle
import MatedCRT.FirstPass.Frozen.S5k
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.FirstPass.Frozen.S2g

/-!
# First pass: the measurable floor obstacle, main theorem (task fp-S5p-5-1-obstacle-version-main, worker z1)

`stoppedFloorObstacleVersion_of_graph` proves `StoppedFloorObstacleVersion 𝒮` (S5k.lean, Part I §4 of
`notes/fp-gaps/CHATGPT-z5-floor.md`, step R5) from the following inputs:
* `hμae` (`FrozenLQGMeasureFieldMeasurable`): a `S.fieldSigma`-measurable version `g` of the LQG measure `S.μ`;
* `hsup` (`FrozenLeastSupersolutionMemCone`): the continuum least supersolution lies in `supersolutions`, a.s.;
* `hstd` (`FrozenFiniteMeasureDiskStandardBorel`): the finite measures on each closed disk form a standard Borel space;
* `hG` (`FrozenGreenDiscPole`): the disc Green function is continuous off its pole (used by `Identify.lean`);
* `hgraph`: the graph `floorObstacleGraph ρ t` of the obstacle conditions (6) is Borel. This is z10's R3
  (S5k/Graph); it is carried with the exact type below (the unconditional version is `stoppedFloorObstacleVersion_proved`, S5k.lean).

Route (Step 4.2 and equation (7) of the floor note):
1. `diskPart ρ μ`: the restriction of `μ` to `B̄_ρ`, replaced by `0` when its mass on `B̄_ρ` is infinite. It is
   measurable into `FinMeasDisk ρ` (`measurable_diskPartFM`).
2. `exists_obstacleDecoder`: a measurable section of the obstacle graph, with value `0` outside its projection
   (`exists_measurable_section_of_injective`, Lusin–Souslin), with zero boundary values for every measure.
3. Identification (7): `isObstacleSolutionOn_leastSupersolution` gives the obstacle solution for the continuum least
   supersolution. Uniqueness, `IsObstacleSolutionOn.eqOn_closedBall`, identifies the decoder's output on `B̄_ρ`.
   The obstacle conditions depend only on values on `B̄_ρ` (`isObstacleSolutionOn_of_eqOn_closedBall`), which is used to
   put the restriction of the least supersolution into the graph (`exists_diskFun_of_isObstacleSolutionOn`).

Terminology: obstacle problem of Armstrong–Kuusi–Mourrat; LQG measure of Duplantier–Sheffield; Green function of
Armitage–Gardiner (`greenFunction` of the disk). -/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology HarmonicBalls

/-- The graph of the obstacle solution map on `M_f(B̄_ρ) × C(B̄_ρ)`: the pairs `(ν, f)` such that the extension by zero
`extDisk ρ f` solves the conditions (6) of Step 4.1 for `ν`, with pole `0` and obstacle `-t G_{B_ρ}(0,·)`. -/
def floorObstacleGraph (ρ t : ℝ) : Set (FinMeasDisk ρ × DiskFun ρ) :=
  {p | IsObstacleSolutionOn ρ t p.1.1 (extDisk ρ p.2)}

/-- The obstacle conditions are local on the closed disk: a function agreeing with a solution on `B̄_ρ` is a solution.
Only the values on `B̄_ρ` enter: the Laplacian conditions on `B_ρ` and the cluster `U_w ⊆ B_ρ`. -/
theorem isObstacleSolutionOn_of_eqOn_closedBall (hG : FrozenGreenDiscPole) {ρ t : ℝ} {ν : Measure ℂ} {w w' : ℂ → ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (h : IsObstacleSolutionOn ρ t ν w) (heq : EqOn w w' (closedBall (0 : ℂ) ρ)) :
    IsObstacleSolutionOn ρ t ν w' := by
  have hball : EqOn w w' (ball (0 : ℂ) ρ) := heq.mono ball_subset_closedBall
  have hcl : floorObstacleCluster ρ t w = floorObstacleCluster ρ t w' := by
    ext x
    rw [mem_obstacleCluster, mem_obstacleCluster]
    constructor
    · rintro ⟨hxb, hx⟩
      refine ⟨hxb, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by rw [← hball hxb]; exact hx)
    · rintro ⟨hxb, hx⟩
      refine ⟨hxb, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by rw [hball hxb]; exact hx)
  refine ⟨h.continuousOn.congr heq.symm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← heq (sphere_subset_closedBall hx)]
    exact h.zero_on_sphere x hx
  · intro x hx hx0
    rw [← heq hx]
    exact h.obstacle x hx hx0
  · exact h.laplacian_le.congr_eqOn measurableSet_ball hball
  · rw [← hcl]
    exact h.laplacian_eq.congr_eqOn
      (isOpen_obstacleCluster hG hρ ht h.continuousOn).measurableSet
      (fun x hx => hball (mem_obstacleCluster.1 hx).1)

/-- A solution on `B̄_ρ` (as a function on `ℂ`) is the extension by zero of a continuous function on `B̄_ρ`. -/
theorem exists_diskFun_of_isObstacleSolutionOn (hG : FrozenGreenDiscPole) {ρ t : ℝ} {ν : Measure ℂ} {w : ℂ → ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (h : IsObstacleSolutionOn ρ t ν w) :
    ∃ y : DiskFun ρ, IsObstacleSolutionOn ρ t ν (extDisk ρ y) := by
  refine ⟨⟨(closedBall (0 : ℂ) ρ).domRestrict w, h.continuousOn.domRestrict⟩, ?_⟩
  refine isObstacleSolutionOn_of_eqOn_closedBall hG hρ ht h ?_
  intro x hx
  rw [extDisk_apply_of_mem _ hx]
  rfl

open scoped Classical in
/-- The restriction of `μ` to `B̄_ρ`, replaced by the zero measure when its mass on `B̄_ρ` is infinite (Step 4 of the
floor note; the LQG measure is locally finite, so the replacement is a null event). -/
noncomputable def diskPart (ρ : ℝ) (μ : Measure ℂ) : Measure ℂ :=
  if μ (closedBall (0 : ℂ) ρ) < ⊤ then μ.restrict (closedBall (0 : ℂ) ρ) else 0

theorem diskPart_mem (ρ : ℝ) (μ : Measure ℂ) :
    IsFiniteMeasure (diskPart ρ μ) ∧ (diskPart ρ μ).restrict (closedBall (0 : ℂ) ρ) = diskPart ρ μ := by
  unfold diskPart
  split_ifs with h
  · exact ⟨isFiniteMeasure_restrict.mpr h.ne,
      by rw [Measure.restrict_restrict measurableSet_closedBall, Set.inter_self]⟩
  · exact ⟨inferInstance, Measure.restrict_zero _⟩

theorem diskPart_of_lt (ρ : ℝ) (μ : Measure ℂ) (h : μ (closedBall (0 : ℂ) ρ) < ⊤) :
    diskPart ρ μ = μ.restrict (closedBall (0 : ℂ) ρ) := by
  unfold diskPart
  split_ifs
  rfl

/-- `diskPart` as an element of `FinMeasDisk ρ`. -/
noncomputable def diskPartFM (ρ : ℝ) (μ : Measure ℂ) : FinMeasDisk ρ :=
  ⟨diskPart ρ μ, diskPart_mem ρ μ⟩

theorem measurable_diskPart (ρ : ℝ) : Measurable (diskPart ρ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h1 : Measurable fun μ : Measure ℂ => μ (s ∩ closedBall (0 : ℂ) ρ) :=
    Measure.measurable_coe (hs.inter measurableSet_closedBall)
  have h2 : MeasurableSet {μ : Measure ℂ | μ (closedBall (0 : ℂ) ρ) < ⊤} :=
    measurableSet_lt (Measure.measurable_coe measurableSet_closedBall) measurable_const
  have heq : (fun μ : Measure ℂ => diskPart ρ μ s) =
      fun μ => if μ (closedBall (0 : ℂ) ρ) < ⊤ then μ (s ∩ closedBall (0 : ℂ) ρ) else 0 := by
    funext μ
    unfold diskPart
    split_ifs with h
    · rw [Measure.restrict_apply hs]
    · simp
  rw [heq]
  exact Measurable.ite h2 h1 measurable_const

theorem measurable_diskPartFM (ρ : ℝ) : Measurable (diskPartFM ρ) :=
  (measurable_diskPart ρ).subtype_mk

/-- **Measurable decoder of the obstacle graph** (Step 4.2 of the floor note). If the graph `floorObstacleGraph ρ t` is
Borel, there is a measurable `dec : M_f(B̄_ρ) → C(B̄_ρ)` such that: `dec ν` has zero boundary values for every `ν`;
and `dec ν` solves the obstacle problem for `ν` whenever some continuous function on `B̄_ρ` does. The section and its
extension by `0` outside the projection come from `exists_measurable_section_of_injective` (Lusin–Souslin); uniqueness of
solutions (`IsObstacleSolutionOn.eqOn_closedBall`) makes the graph the graph of a partial function. -/
theorem exists_obstacleDecoder (ρ t : ℝ) [StandardBorelSpace (FinMeasDisk ρ)] [StandardBorelSpace (DiskFun ρ)]
    (hgraph : MeasurableSet (floorObstacleGraph ρ t)) :
    ∃ dec : FinMeasDisk ρ → DiskFun ρ, Measurable dec ∧
      (∀ ν : FinMeasDisk ρ, ∀ x ∈ sphere (0 : ℂ) ρ, extDisk ρ (dec ν) x = 0) ∧
      (∀ (ν : FinMeasDisk ρ) (y : DiskFun ρ), IsObstacleSolutionOn ρ t ν.1 (extDisk ρ y) →
        IsObstacleSolutionOn ρ t ν.1 (extDisk ρ (dec ν))) := by
  have hinj : ∀ (ν : FinMeasDisk ρ) (y₁ y₂ : DiskFun ρ), (ν, y₁) ∈ floorObstacleGraph ρ t →
      (ν, y₂) ∈ floorObstacleGraph ρ t → y₁ = y₂ := by
    intro ν y₁ y₂ h₁ h₂
    have h₁' : IsObstacleSolutionOn ρ t ν.1 (extDisk ρ y₁) := h₁
    have h₂' : IsObstacleSolutionOn ρ t ν.1 (extDisk ρ y₂) := h₂
    refine ContinuousMap.ext fun x => ?_
    have hE := IsObstacleSolutionOn.eqOn_closedBall h₁' h₂' x.2
    rw [extDisk_apply_of_mem _ x.2, extDisk_apply_of_mem _ x.2] at hE
    exact hE
  obtain ⟨F, hFm, hFsec, hFzero⟩ :=
    exists_measurable_section_of_injective (0 : DiskFun ρ) (floorObstacleGraph ρ t) hgraph
      (fun x y₁ y₂ h₁ h₂ => hinj x y₁ y₂ h₁ h₂)
  refine ⟨F, hFm, ?_, ?_⟩
  · intro ν x hx
    by_cases hν : ∃ y, (ν, y) ∈ floorObstacleGraph ρ t
    · have hsol : IsObstacleSolutionOn ρ t ν.1 (extDisk ρ (F ν)) := hFsec ν hν
      exact hsol.zero_on_sphere x hx
    · rw [hFzero ν hν]
      exact extDisk_apply_of_mem _ (sphere_subset_closedBall hx)
  · intro ν y hy
    have hmem : (ν, F ν) ∈ floorObstacleGraph ρ t := hFsec ν ⟨y, hy⟩
    exact hmem

/-- **Measurable version of the continuum floor obstacle, proved** (task fp-S5p-5-1-obstacle-version-main; Part I, Step 4
and equation (7) of `notes/fp-gaps/CHATGPT-z5-floor.md`). The conclusion is `StoppedFloorObstacleVersion 𝒮`.

Hypotheses: `hμae` (field-measurable version of the LQG measure), `hsup` (least-supersolution membership a.s.),
`hstd` (standard Borel structure of finite measures on closed disks), `hG` (continuity of the disc Green function off
its pole), and `hgraph`: for `ρ > 0`, `t > 0`, the graph `floorObstacleGraph ρ t` of the obstacle conditions (6) is
Borel. `hgraph` is z10's R3 and is carried as a hypothesis here. The unconditional version is `stoppedFloorObstacleVersion_proved` (S5k.lean, z10). -/
theorem stoppedFloorObstacleVersion_of_graph (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hstd : FrozenFiniteMeasureDiskStandardBorel) (hG : FrozenGreenDiscPole)
    (hgraph : ∀ ρ : ℝ, 0 < ρ → ∀ t : ℝ, 0 < t → MeasurableSet (floorObstacleGraph ρ t)) :
    StoppedFloorObstacleVersion 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS Λ hΛ t ht
  obtain ⟨g, hgm, hg⟩ := hμae γ hγ0 hγ2 Ω S hS
  have hsupS := hsup γ hγ0 hγ2 Ω S hS
  have hLQG : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  have : StandardBorelSpace (FinMeasDisk ρ) := hstd ρ hρ0
  obtain ⟨dec, hdecm, hdecS, hdecSol⟩ := exists_obstacleDecoder ρ t (hgraph ρ hρ0 t ht)
  refine ⟨fun ω x => extDisk ρ (dec (diskPartFM ρ (g ω))) x, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (measurable_extDisk_eval x).comp (hdecm.comp ((measurable_diskPartFM ρ).comp hgm))
  · intro ω
    exact continuousOn_extDisk _
  · intro ω x hx
    exact hdecS _ x hx
  · filter_upwards [hg, hsupS, hΛ, hLQG] with ω hgω hsupω hΛω hLQGω
    intro hexit x hx
    have := hLQGω.isLocallyFiniteMeasure
    have hKfin : S.μ ω (closedBall (0 : ℂ) ρ) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
    have hKg : g ω (closedBall (0 : ℂ) ρ) < ⊤ := by rw [← hgω]; exact hKfin
    have hval : (diskPartFM ρ (g ω)).1 = (S.μ ω).restrict (closedBall (0 : ℂ) ρ) := by
      show diskPart ρ (g ω) = _
      rw [diskPart_of_lt ρ (g ω) hKg, ← hgω]
    have hW : IsObstacleSolutionOn ρ t ((S.μ ω).restrict (closedBall (0 : ℂ) ρ))
        (leastSupersolution (S.μ ω) ρ 0 t) :=
      isObstacleSolutionOn_leastSupersolution hG hΛω hρ0 ht (hsupω ρ hρ0 hρ1 t ht) hexit
    have hWd : IsObstacleSolutionOn ρ t (diskPartFM ρ (g ω)).1 (leastSupersolution (S.μ ω) ρ 0 t) := by
      rw [hval]
      exact hW
    obtain ⟨y, hy⟩ := exists_diskFun_of_isObstacleSolutionOn hG hρ0 ht hWd
    have hsol := hdecSol (diskPartFM ρ (g ω)) y hy
    exact hsol.eqOn_closedBall hWd hx

end MatedCRT
