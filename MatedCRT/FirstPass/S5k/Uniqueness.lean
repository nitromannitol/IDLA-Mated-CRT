import MatedCRT.FirstPass.S5k.MaxPrinciple
import HarmonicBalls.Proofs.Sec6.DiscPotentialComparison
import HarmonicBalls.Steps.Sec3.Basic

/-!
# First pass: uniqueness of the obstacle solution (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Steps 4.1 and 4.2 of Part I of `notes/fp-gaps/CHATGPT-z5-floor.md`. For a measure `ν` and a level `t`, the conditions (6)
of Step 4.1 (`IsObstacleSolutionOn`, pole `0`, obstacle `-t G_{B_ρ}(0,·)`) admit at most one solution on the closed disk.
Proof (Step 4.2): on `D = B_ρ ∩ {w₁ > w₂}` the function `w₁ - w₂` satisfies `Δ(w₁-w₂) = ν - Δw₂ ≥ 0`, because
`D ⊆ U_{w₁}`; it is continuous and vanishes on `∂B_ρ`, so the maximum principle `maximum_principle_of_frontier`
(`MaxPrinciple.lean`) gives `w₁ ≤ w₂`. Exchanging the roles gives equality.
-/

namespace MatedCRT

open MeasureTheory Metric Set Laplacian
open HarmonicBalls

/-- The cluster `U_w = {x ∈ B_ρ : x = 0 ∨ -t G_{B_ρ}(0,x) < w x}` of a candidate `w` (Step 4.1 of the floor note); the
same shape as `HarmonicBalls.cluster` (pole `0`). -/
def obstacleCluster (ρ t : ℝ) (w : ℂ → ℝ) : Set ℂ :=
  {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * greenFunction (ball 0 ρ) 0 x < w x}

/-- The set `{w₁ > w₂} ∩ B_ρ` on which the comparison of Step 4.2 is made. -/
def posSetOn (ρ : ℝ) (w₁ w₂ : ℂ → ℝ) : Set ℂ :=
  ball (0 : ℂ) ρ ∩ (fun x => w₁ x - w₂ x) ⁻¹' Ioi 0

/-- The conditions (6) of Step 4.1 for a measure `ν` (on the closed disk) and `w`, with pole `0` and obstacle
`-t G_{B_ρ}(0,·)`: `w` is continuous on `B̄_ρ`, vanishes on `∂B_ρ`, lies above the obstacle on `B̄_ρ ∖ {0}`,
satisfies `Δw ≤ ν` on `B_ρ`, and `Δw = ν` on the cluster `U_w` (`HasLaplacian`, with `μneg = 0`). -/
structure IsObstacleSolutionOn (ρ t : ℝ) (ν : Measure ℂ) (w : ℂ → ℝ) : Prop where
  continuousOn : ContinuousOn w (closedBall (0 : ℂ) ρ)
  zero_on_sphere : ∀ x ∈ sphere (0 : ℂ) ρ, w x = 0
  obstacle : ∀ x ∈ closedBall (0 : ℂ) ρ, x ≠ 0 → -t * greenFunction (ball 0 ρ) 0 x ≤ w x
  laplacian_le : LaplacianLE w ν (ball (0 : ℂ) ρ)
  laplacian_eq : HasLaplacian w ν 0 (obstacleCluster ρ t w)

theorem mem_obstacleCluster {ρ t : ℝ} {w : ℂ → ℝ} {x : ℂ} :
    x ∈ obstacleCluster ρ t w ↔ x ∈ ball (0 : ℂ) ρ ∧ (x = 0 ∨ -t * greenFunction (ball 0 ρ) 0 x < w x) :=
  Iff.rfl

theorem mem_posSetOn {ρ : ℝ} {w₁ w₂ : ℂ → ℝ} {x : ℂ} :
    x ∈ posSetOn ρ w₁ w₂ ↔ x ∈ ball (0 : ℂ) ρ ∧ 0 < w₁ x - w₂ x :=
  Iff.rfl

theorem isTestFunction_of_subset {U V : Set ℂ} {φ : ℂ → ℝ} (h : IsTestFunction U φ) (hUV : U ⊆ V) :
    IsTestFunction V φ :=
  ⟨h.1, h.2.1, h.2.2.trans hUV⟩

/-- **Comparison of solutions of (6)** (Step 4.2 of the floor note). Two solutions `w₁`, `w₂` of (6) for the same
`ν` satisfy `w₁ ≤ w₂` on `B̄_ρ`. -/
theorem IsObstacleSolutionOn.le_of_solution {ρ t : ℝ} {ν : Measure ℂ} {w₁ w₂ : ℂ → ℝ}
    (h₁ : IsObstacleSolutionOn ρ t ν w₁) (h₂ : IsObstacleSolutionOn ρ t ν w₂) :
    ∀ x ∈ closedBall (0 : ℂ) ρ, w₁ x ≤ w₂ x := by
  have hucont : ContinuousOn (fun x => w₁ x - w₂ x) (closedBall (0 : ℂ) ρ) :=
    h₁.continuousOn.sub h₂.continuousOn
  have hDopen : IsOpen (posSetOn ρ w₁ w₂) :=
    (hucont.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hDball : posSetOn ρ w₁ w₂ ⊆ ball (0 : ℂ) ρ := fun x hx => (mem_posSetOn.1 hx).1
  have hDcl : closure (posSetOn ρ w₁ w₂) ⊆ closedBall (0 : ℂ) ρ :=
    (closure_mono hDball).trans closure_ball_subset_closedBall
  -- `D ⊆ U_{w₁}`: off the pole, `w₁ > w₂ ≥ -tG`
  have hDcluster : posSetOn ρ w₁ w₂ ⊆ obstacleCluster ρ t w₁ := by
    intro x hx
    obtain ⟨hxb, hpos⟩ := mem_posSetOn.1 hx
    refine mem_obstacleCluster.2 ⟨hxb, ?_⟩
    by_cases h0 : x = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hob := h₂.obstacle x (ball_subset_closedBall hxb) h0
      linarith
  -- the Laplacian of `w₁ - w₂` on `D` is nonnegative: `∫ (w₁ - w₂) Δφ = ∫ φ dν - ∫ w₂ Δφ ≥ 0`
  have hkey : ∀ φ : ℂ → ℝ, IsTestFunction (posSetOn ρ w₁ w₂) φ → 0 ≤ φ →
      0 ≤ ∫ x, (w₁ x - w₂ x) * Δ φ x := by
    intro φ hφD hφ0
    have hφ1 : IsTestFunction (obstacleCluster ρ t w₁) φ := isTestFunction_of_subset hφD hDcluster
    have hφb : IsTestFunction (ball (0 : ℂ) ρ) φ := isTestFunction_of_subset hφD hDball
    obtain ⟨hνφ, -, heq1⟩ := h₁.laplacian_eq.2 φ hφ1
    rw [integral_zero_measure, sub_zero] at heq1
    have hle2 := h₂.laplacian_le.2 φ hφb hφ0 hνφ
    have hi1 : Integrable (fun x => w₁ x * Δ φ x) :=
      integrable_mul_laplacian_of_test (h₁.laplacian_eq.1.mono_set hDcluster) hφD
    have hi2 : Integrable (fun x => w₂ x * Δ φ x) :=
      integrable_mul_laplacian_of_test (h₂.laplacian_le.1.mono_set hDball) hφD
    have e : ∫ x, (w₁ x - w₂ x) * Δ φ x = (∫ x, w₁ x * Δ φ x) - ∫ x, w₂ x * Δ φ x := by
      rw [← integral_sub hi1 hi2]
      congr 1
      funext x
      ring
    linarith
  have hGE : LaplacianGE (fun x => w₁ x - w₂ x) 0 (posSetOn ρ w₁ w₂) := by
    refine ⟨?_, fun φ hφD hφ0 => ⟨integrable_zero_measure, ?_⟩⟩
    · exact (h₁.laplacian_eq.1.mono_set hDcluster).sub (h₂.laplacian_le.1.mono_set hDball)
    · rw [integral_zero_measure]
      exact hkey φ hφD hφ0
  have hq0 : HasLaplacian (fun _ : ℂ => (0 : ℝ)) 0 0 (posSetOn ρ w₁ w₂) :=
    ⟨((continuous_const : Continuous fun _ : ℂ => (0 : ℝ)).locallyIntegrable).locallyIntegrableOn _, fun φ _ =>
      ⟨integrable_zero_measure, integrable_zero_measure, by simp⟩⟩
  have hvc : ContinuousOn (fun x => w₁ x - w₂ x) (posSetOn ρ w₁ w₂) :=
    hucont.mono (hDball.trans ball_subset_closedBall)
  have hsub0 := Section6.isSubharmonicOn_add_of_laplacianGE hDopen le_rfl hvc continuousOn_const hGE hq0
  have hsum : ((fun x => w₁ x - w₂ x) + fun _ : ℂ => (0 : ℝ)) = fun x => w₁ x - w₂ x := by
    funext x
    simp
  rw [hsum] at hsub0
  have hfr : ∀ p ∈ frontier (posSetOn ρ w₁ w₂), w₁ p - w₂ p ≤ 0 := by
    intro p hp
    have hpD : p ∉ posSetOn ρ w₁ w₂ := fun hpD => hp.2 (by rw [hDopen.interior_eq]; exact hpD)
    have hpb : p ∈ closedBall (0 : ℂ) ρ := hDcl hp.1
    by_cases hpball : p ∈ ball (0 : ℂ) ρ
    · by_contra hc
      have hc := not_le.mp hc
      exact hpD (mem_posSetOn.2 ⟨hpball, hc⟩)
    · have hps : p ∈ sphere (0 : ℂ) ρ := by
        rw [← closedBall_sdiff_ball]
        exact ⟨hpb, hpball⟩
      simp [h₁.zero_on_sphere p hps, h₂.zero_on_sphere p hps]
  have hmax := maximum_principle_of_frontier hDopen (isBounded_ball.subset inter_subset_left) hsub0
    (hucont.mono hDcl) hfr
  have hnonpos : ∀ x ∈ ball (0 : ℂ) ρ, w₁ x - w₂ x ≤ 0 := by
    intro x hx
    by_contra hc
    have hc := not_le.mp hc
    linarith [hmax x (mem_posSetOn.2 ⟨hx, hc⟩)]
  intro x hx
  by_cases hxb : x ∈ ball (0 : ℂ) ρ
  · linarith [hnonpos x hxb]
  · have hxs : x ∈ sphere (0 : ℂ) ρ := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hx, hxb⟩
    simp [h₁.zero_on_sphere x hxs, h₂.zero_on_sphere x hxs]

/-- **Uniqueness of the solution of (6)** (Step 4.2 of the floor note): two solutions agree on `B̄_ρ`. -/
theorem IsObstacleSolutionOn.eqOn_closedBall {ρ t : ℝ} {ν : Measure ℂ} {w₁ w₂ : ℂ → ℝ}
    (h₁ : IsObstacleSolutionOn ρ t ν w₁) (h₂ : IsObstacleSolutionOn ρ t ν w₂) :
    EqOn w₁ w₂ (closedBall (0 : ℂ) ρ) :=
  fun x hx => le_antisymm (h₁.le_of_solution h₂ x hx) (h₂.le_of_solution h₁ x hx)

end MatedCRT
