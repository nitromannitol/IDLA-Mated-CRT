import MatedCRT.FirstPass.S3i.Frozen

/-!
# Minimal internal definitions for the lens route of `QuenchedLensStep` (S3i)

Ordinary definitions from the approved plan (section "Minimal internal definitions"), not new frozen inputs. Shared by the lens files of this directory.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

def shiftedPath (n : ℕ) (x : ℕ → ℤ) : ℕ → ℤ :=
  fun k => x (n + k)

def UsesEdges (m : ℤ → ℤ → ℕ) (a : ℤ) (x : ℕ → ℤ) : Prop :=
  x 0 = a ∧ ∀ n : ℕ, m (x n) (x (n + 1)) ≠ 0

/-- Sufficient finite-state data for almost-sure exit and first-step
harmonicity. -/
def FiniteExitData (m : ℤ → ℤ → ℕ) (A : Set ℤ) : Prop :=
  A.Finite ∧
  (∀ a ∈ A, 0 < mdeg m a) ∧
  ∀ a ∈ A, ∃ b ∈ vBoundary m A, ∃ p : List ℤ,
    IsVPathIn m (vClosure m A) p a b

/-- Probability of exiting `A` through `B`, as a real-valued function
of the starting vertex. -/
noncomputable def exitHitProb
    (m : ℤ → ℤ → ℕ) (A B : Set ℤ) (a : ℤ) : ℝ :=
  (srwLaw m a
    {x | vExitTime A x < ⊤ ∧ vExitPosition A x ∈ B}).toReal

/-- Enlarged-disk lens. -/
def fp36LensDomain
    (z : ℂ) (r δ : ℝ) (P : ℂ) (s : ℝ) : Set ℂ :=
  ball z (r + 4 * δ) ∩ ball P (s / 4)

/-- Cells meeting the far circular side of the lens. -/
def fp36LensFarCells
    (ε : ℝ) (η : ℝ → ℂ) (P : ℂ) (s : ℝ) : Set ℤ :=
  cellVertices ε η (sphere P (s / 4))

noncomputable def fp36LensProb
    (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (z : ℂ) (r δ : ℝ) (P : ℂ) (s : ℝ) (a : ℤ) : ℝ :=
  exitHitProb m
    (interiorCellVertices ε η (fp36LensDomain z r δ P s))
    (fp36LensFarCells ε η P s) a

/-- The pointwise BE property on one fixed environment. -/
def FP36OneSidedBEAt
    (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (ρ ν A : ℝ) : Prop :=
  ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    SimplyConnectedSpace D →
    (∀ x ∈ interiorCellVertices ε η D,
      matedLaplacian m f x = 0) →
    ∀ x ∈ cellVertices ε η D, ∀ t : ℝ, 0 < t →
      f x ≤ boundarySupNear ε η D f x t
        + A * discreteSupNorm ε η D f
          * (t / infDist (vertexPoint ε η x) (frontier D)) ^ (-ν)

/-- Everything needed at one environment and mesh. The universal
finite-domain clause is derived from `ae_isRegularMatedMap`, not assumed
externally. -/
def FP36GoodEnv {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ₀ ρ₁ b ν A r : ℝ)
    (z y : ℂ) (ε : ℝ) (ω : Ω) : Prop :=
  let η := S.η ω
  let m := S.mult ε ω
  IsAreaParametrized (S.μ ω) η ∧
  (∀ j k : ℤ, m j k ≠ 0 →
    (cell ε η j ∩ cell ε η k).Nonempty) ∧
  (∀ k : ℤ, (cell ε η k ∩ ball 0 ρ₁).Nonempty →
    diam (cell ε η k) ≤ ε ^ b) ∧
  (∀ U : Set ℂ, closure U ⊆ ball 0 ρ₀ →
    FiniteExitData m (cellVertices ε η U) ∧
    FiniteExitData m (interiorCellVertices ε η U)) ∧
  vertexOf ε η y ∈
    interiorCellVertices ε η (ball z r) ∧
  FP36OneSidedBEAt m ε η ρ₁ ν A

end FirstPass36
end MatedCRT
