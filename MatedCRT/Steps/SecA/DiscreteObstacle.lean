import MatedCRT.Draft.SectionA

/-!
# Appendix A: carving of Lemmas A.2-A.4 into steps

For the setting of Appendix A (`IsObstacleSetting m V o 𝔯 φ 𝔱`), with `w = discreteLeastSupersolution m V (cl V) 𝔯 φ`
and `Λ = {a ∈ cl V : w(a) > φ(a)}`:

* Lemma A.2 = `ObstacleBoundsStep` (`φ ≤ w ≤ 0`) + `ObstacleComparisonStep` (`𝔮 ≤ w`, minimum principle) +
  `ObstacleSupersolutionStep` (`Δw ≤ 𝔯`: the infimum of supersolutions is a supersolution);
* Lemma A.3 = `ObstacleSupersolutionStep` + `ObstacleClusterLaplacianStep` (`Δw = 𝔯` on `Λ`) +
  `ObstacleLaplacianNonnegStep` + `ObstacleClusterPreconnectedStep` + `ObstacleOriginStep`;
* Lemma A.4 = `ObstacleClusterCardStep` + `ObstacleMassIdentityStep` (Gauss-Green identity for `w - φ`).
The steps are proved in MatedCRT/Proofs/SecA/Statements.lean.
-/

namespace MatedCRT

open Set

/-- The discrete least supersolution `w` of Appendix A (eq:discrete-least-supersolution-general, line 3375). -/
noncomputable abbrev obstacleW {α : Type*} (m : α → α → ℕ) (V : Set α) (𝔯 φ : α → ℝ) : α → ℝ :=
  discreteLeastSupersolution m V (vClosure m V) 𝔯 φ

/-- The discrete cluster `Λ` of Appendix A (eq:discrete-cluster-general, line 3389). -/
abbrev obstacleCluster {α : Type*} (m : α → α → ℕ) (V : Set α) (𝔯 φ : α → ℝ) : Set α :=
  discreteCluster (vClosure m V) (obstacleW m V 𝔯 φ) φ

/-- Step: `φ ≤ w ≤ 0` on `cl(V)`. -/
def ObstacleBoundsStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    ∀ a ∈ vClosure m V, φ a ≤ obstacleW m V 𝔯 φ a ∧ obstacleW m V 𝔯 φ a ≤ 0

/-- Step: `𝔮 ≤ w` on `cl(V)` for the solution `𝔮` of `Δ𝔮 = 𝔯` on `V`, `𝔮 = 0` on `∂V`. -/
def ObstacleComparisonStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    ∀ 𝔮 : α → ℝ, (∀ a ∈ V, mLaplacian m 𝔮 a = 𝔯 a) → (∀ a ∈ vBoundary m V, 𝔮 a = 0) →
      ∀ a ∈ vClosure m V, 𝔮 a ≤ obstacleW m V 𝔯 φ a

/-- Step: `Δw ≤ 𝔯` on `V`. -/
def ObstacleSupersolutionStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    ∀ a ∈ V, mLaplacian m (obstacleW m V 𝔯 φ) a ≤ 𝔯 a

/-- Step: `Δw = 𝔯` on `Λ`. -/
def ObstacleClusterLaplacianStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    ∀ a ∈ obstacleCluster m V 𝔯 φ, mLaplacian m (obstacleW m V 𝔯 φ) a = 𝔯 a

/-- Step: `Δw ≥ 0` on `V`. -/
def ObstacleLaplacianNonnegStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    ∀ a ∈ V, 0 ≤ mLaplacian m (obstacleW m V 𝔯 φ) a

/-- Step: `Λ` is connected (possibly empty). -/
def ObstacleClusterPreconnectedStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    IsVPreconnected m (obstacleCluster m V 𝔯 φ)

/-- Step: if `𝔱 > 𝔯(o)` then `o ∈ Λ`. -/
def ObstacleOriginStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    𝔯 o < 𝔱 → o ∈ obstacleCluster m V 𝔯 φ

/-- Step: for `𝔯 = deg⁻¹`, `|Λ| ≤ 𝔱 deg(o)`. -/
def ObstacleClusterCardStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    (∀ a ∈ V, 𝔯 a = ((mdeg m a : ℕ) : ℝ)⁻¹) →
    ((obstacleCluster m V 𝔯 φ).ncard : ℝ) ≤ 𝔱 * (mdeg m o : ℝ)

/-- Step: for `𝔯 = deg⁻¹` and `Λ ⊆ int(V)`, `∑_{a ∈ V} Δw(a) deg(a) = 𝔱 deg(o)`. -/
def ObstacleMassIdentityStep : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    (∀ a ∈ V, 𝔯 a = ((mdeg m a : ℕ) : ℝ)⁻¹) → obstacleCluster m V 𝔯 φ ⊆ vInterior m V →
    ∑ᶠ a ∈ V, mLaplacian m (obstacleW m V 𝔯 φ) a * (mdeg m a : ℝ) = 𝔱 * (mdeg m o : ℝ)

theorem discreteBasicPropertiesGeneral_of_steps (h₁ : ObstacleBoundsStep) (h₂ : ObstacleComparisonStep)
    (h₃ : ObstacleSupersolutionStep) : DiscreteBasicPropertiesGeneralStmt := by
  intro α m V o 𝔯 φ 𝔱 hS 𝔮 hq hqb
  exact ⟨fun a ha => ⟨max_le (h₂ α m V o 𝔯 φ 𝔱 hS 𝔮 hq hqb a ha) (h₁ α m V o 𝔯 φ 𝔱 hS a ha).1,
    (h₁ α m V o 𝔯 φ 𝔱 hS a ha).2⟩, h₃ α m V o 𝔯 φ 𝔱 hS⟩

theorem discreteLaplacianBoundGeneral_of_steps (h₃ : ObstacleSupersolutionStep) (h₄ : ObstacleClusterLaplacianStep)
    (h₅ : ObstacleLaplacianNonnegStep) (h₆ : ObstacleClusterPreconnectedStep) (h₇ : ObstacleOriginStep) :
    DiscreteLaplacianBoundGeneralStmt := by
  intro α m V o 𝔯 φ 𝔱 hS
  exact ⟨h₄ α m V o 𝔯 φ 𝔱 hS, fun a ha => ⟨h₅ α m V o 𝔯 φ 𝔱 hS a ha, h₃ α m V o 𝔯 φ 𝔱 hS a ha⟩,
    h₆ α m V o 𝔯 φ 𝔱 hS, h₇ α m V o 𝔯 φ 𝔱 hS⟩

theorem discreteConservationOfMassGeneral_of_steps (h₈ : ObstacleClusterCardStep) (h₉ : ObstacleMassIdentityStep) :
    DiscreteConservationOfMassGeneralStmt := by
  intro α m V o 𝔯 φ 𝔱 hS hr
  exact ⟨h₈ α m V o 𝔯 φ 𝔱 hS hr, h₉ α m V o 𝔯 φ 𝔱 hS hr⟩

end MatedCRT
