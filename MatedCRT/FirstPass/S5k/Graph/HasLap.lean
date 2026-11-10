import MatedCRT.FirstPass.S5k.Graph.Local
import MatedCRT.FirstPass.S5k.Graph.Obstacle

/-!
# First pass: countable presentation of `Δw = ν` on the cluster (task fp-S5k-5-1-floor-obstacle-version, worker z10)

Step 4.1 of `notes/fp-gaps/CHATGPT-z5-floor.md` (Part I), the last condition of (6): `Δw = ν` on the cluster
`U_w = {x ∈ B_ρ : x = 0 ∨ -tG(0,x) < w(x)}` (`obstacleCluster`). It is tested on countably many disks `B(q₀, r)` with
rational data, each admitted when `w + tG > c` at the rational points of the disk (a countable test of the open condition).
The cover of `U_w` by such disks, and the localization `vanish_of_local`, give the equivalence with `HasLaplacian`.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology Laplacian HarmonicBalls

open scoped Classical in
/-- The total version of `psiOn`: the pair `(φ|_K, Δφ|_K)` for continuous `φ` with continuous `Δφ`, and `0` otherwise. -/
noncomputable def psiF {ρ : ℝ} (φ : ℂ → ℝ) : DiskFun ρ × DiskFun ρ :=
  if h : Continuous φ ∧ Continuous (Δ φ) then (restrictDisk φ h.1, restrictDisk (Δ φ) h.2) else 0

theorem Lf_psiF {ρ : ℝ} {U : Set ℂ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) {φ : ℂ → ℝ}
    (hφ : IsTestFunction U φ) : Lf ν f (psiF (ρ := ρ) φ) = Lt ν f φ := by
  have hc := continuous_of_isTestFunction_laplacian hφ
  have e : psiF (ρ := ρ) φ = psiOn (ρ := ρ) ⟨φ, hφ⟩ := by

    simp [psiF, psiOn, hc]
  rw [e, Lf_psiOn]
  rfl

/-- A countable dense family of test functions on `U`, for the total `psiF`. -/
theorem exists_countable_psiF (ρ : ℝ) (U : Set ℂ) :
    ∃ Φ : Set (ℂ → ℝ), Φ ⊆ {φ | IsTestFunction U φ} ∧ Φ.Countable ∧
      ∀ φ, IsTestFunction U φ → psiF (ρ := ρ) φ ∈ closure (psiF (ρ := ρ) '' Φ) := by
  obtain ⟨Φ, hΦA, hc, hd⟩ := exists_countable_dense_family {φ | IsTestFunction U φ} (psiF (ρ := ρ))
  exact ⟨Φ, hΦA, hc, fun φ hφ => hd φ hφ⟩

/-- A chosen countable dense family of test functions on `U`. -/
noncomputable def Phidisk (ρ : ℝ) (U : Set ℂ) : Set (ℂ → ℝ) := Classical.choose (exists_countable_psiF ρ U)

theorem Phidisk_spec (ρ : ℝ) (U : Set ℂ) :
    Phidisk ρ U ⊆ {φ | IsTestFunction U φ} ∧ (Phidisk ρ U).Countable ∧
      ∀ φ, IsTestFunction U φ → psiF (ρ := ρ) φ ∈ closure (psiF (ρ := ρ) '' Phidisk ρ U) :=
  Classical.choose_spec (exists_countable_psiF ρ U)

/-- If `Lf ν f (psiF φ) = 0` on the dense family of `U`, then `Lt ν f φ = 0` for all test functions on `U`. -/
theorem Lt_eq_zero_of_Phidisk {ρ : ℝ} (ν : FinMeasDisk ρ) (f : DiskFun ρ) {U : Set ℂ}
    (h : ∀ φ ∈ Phidisk ρ U, Lf ν f (psiF (ρ := ρ) φ) = 0) :
    ∀ φ, IsTestFunction U φ → Lt ν f φ = 0 := by
  intro φ hφ
  obtain ⟨-, -, hd⟩ := Phidisk_spec ρ U
  have hcl : psiF (ρ := ρ) φ ∈ {y | Lf ν f y = 0} :=
    closure_minimal (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
      (isClosed_eq (continuous_Lf ν f) continuous_const) (hd φ hφ)
  have h0 : Lf ν f (psiF (ρ := ρ) φ) = 0 := hcl
  rw [Lf_psiF ν f hφ] at h0
  exact h0

/-- Admissible rational disks: `B(q₀, r) ⊆ B_ρ` with `r > 0`. -/
def AdmDisk (ρ : ℝ) (q₀ : ℂ) (r : ℚ) : Prop :=
  0 < (r : ℝ) ∧ ball q₀ (r : ℝ) ⊆ ball (0 : ℂ) ρ

/-- The rational test `c < w + tG` at the points of the countable set `D₀` in `B(q₀, r) ∖ {0}`. -/
def HypDisk (ρ t : ℝ) (D₀ : Set ℂ) (f : DiskFun ρ) (q₀ : ℂ) (r c : ℚ) : Prop :=
  ∀ q ∈ D₀, q ∈ ball q₀ (r : ℝ) → q ≠ 0 →
    (c : ℝ) < extDisk ρ f q + t * greenFunction (ball 0 ρ) 0 q

/-- On an admissible disk where the rational test holds, `w + tG > c` on the whole punctured disk, so the disk lies in the
cluster `U_w`. -/
theorem ball_subset_obstacleCluster {ρ t : ℝ} (hG : FrozenGreenDiscPole) (hρ : 0 < ρ)
    {D₀ : Set ℂ} (hD₀d : Dense D₀) (f : DiskFun ρ) {q₀ : ℂ} {r c : ℚ} (hadm : AdmDisk ρ q₀ r)
    (hc : 0 < c) (hyp : HypDisk ρ t D₀ f q₀ r c) :
    ball q₀ (r : ℝ) ⊆ obstacleCluster ρ t (extDisk ρ f) := by
  obtain ⟨-, hsub⟩ := hadm
  set O : Set ℂ := ball q₀ (r : ℝ) \ {0} with hO
  have hOopen : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  have hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) O :=
    (hG ρ hρ).1.mono (fun y hy => ⟨ball_subset_closedBall (hsub hy.1), hy.2⟩)
  have hcont : ContinuousOn (fun y => extDisk ρ f y + t * greenFunction (ball 0 ρ) 0 y - (c : ℝ)) O :=
    (((continuousOn_extDisk f).mono (fun y hy => ball_subset_closedBall (hsub hy.1))).add
      (continuousOn_const.mul hGc)).sub continuousOn_const
  have hdense : ∀ x ∈ O, x ∈ closure (O ∩ D₀) := fun x hx =>
    hD₀d.open_subset_closure_inter hOopen hx
  have hnn := nonneg_of_dense_on_open hOopen hcont hdense (fun d hd => by
    have := hyp d hd.2 hd.1.1 hd.1.2
    linarith)
  intro x hx
  by_cases hx0 : x = 0
  · exact mem_obstacleCluster.2 ⟨hsub hx, Or.inl hx0⟩
  · have hxO : x ∈ O := ⟨hx, hx0⟩
    have h1 := hnn x hxO
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    refine mem_obstacleCluster.2 ⟨hsub hx, Or.inr ?_⟩
    linarith

end MatedCRT
