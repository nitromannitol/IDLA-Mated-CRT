import MatedCRT.Defs.RandomWalk

/-!
# The divisible sandpile and the discrete obstacle problem (Section 4, lines 1535-1595; Section 7, lines 2930-2950;
Appendix A, lines 3338-3412)

## The divisible sandpile

The single-source divisible sandpile with mass `M` at the origin `0` of a multigraph `m` on `ℤ` (lines 1537-1540):
unstable sites (mass `> 1`) topple, sending their excess mass to their neighbours, equally along incident edges. The
odometer `v` (total mass emitted) is characterized by the *least action principle* (eq:least-action-principle,
line 1557; Levine-Peres 2009, Lemma 3.2):
`v/deg = min {w : V → [0, ∞) : Δw + deg(0)⁻¹ M δ₀ ≤ deg⁻¹}` (pointwise minimum),
which is how it is defined here (`sandpileNormOdometer`, the pointwise infimum). The final configuration is
`s = M δ₀ + deg · Δ(v/deg)` (eq:final-sandpile-definition, line 1546) and the cluster is `D(M) = {s > 0}`
(eq:cluster-definition, line 1552). The paper's `D_ε(t ε⁻¹)` is `sandpileCluster (cellMult ε η) (t / ε)`.

## The discrete obstacle problem

`discreteLeastSupersolution m V W 𝔯 φ` is the pointwise infimum of the functions `u` with `Δu ≤ 𝔯` on `V` and
`u ≥ φ` on `W`:
* Appendix A (eq:discrete-least-supersolution-general, line 3375): `W = cl(V)`;
* Section 4 (eq:discrete-least-supersolution, line 1570): `w̃^ε_t` with `V = V^ε(B_ρ) \ V^ε(∂B_ρ)`,
  `W = V^ε(cl(B_ρ))`, `𝔯 = deg⁻¹` and `φ = -(t ε⁻¹) g^ε_{B_ρ}(0, ·)` (`matedLeastSupersolution`).
The discrete cluster is `{a ∈ W : w(a) > φ(a)}` (eq:discrete-cluster, line 1690; eq:discrete-cluster-general,
line 3389), and the stopped odometer is `u^ε_t = w̃^ε_t + (t ε⁻¹) g^ε_{B_ρ}(0, ·)` (line 2941; it is `0` off
`V^ε(cl(B_ρ))`).
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- The Dirac function `δ₀` of the origin `0 ∈ ℤ`. -/
noncomputable def diracZero (a : ℤ) : ℝ :=
  if a = 0 then 1 else 0

/-- The normalized odometer `v/deg` of the divisible sandpile with mass `M` at the origin, by the least action principle
(eq:least-action-principle, line 1557): the pointwise infimum of the nonnegative `w` with
`Δw + deg(0)⁻¹ M δ₀ ≤ deg⁻¹` everywhere. -/
noncomputable def sandpileNormOdometer (m : ℤ → ℤ → ℕ) (M : ℝ) (a : ℤ) : ℝ :=
  sInf ((fun w : ℤ → ℝ => w a) ''
    {w | (∀ b, 0 ≤ w b) ∧ ∀ b, mLaplacian m w b + ((mdeg m 0 : ℕ) : ℝ)⁻¹ * M * diracZero b ≤
      ((mdeg m b : ℕ) : ℝ)⁻¹})

/-- The *odometer* `v = deg · (v/deg)` of the divisible sandpile with mass `M` at the origin (line 1543). -/
noncomputable def sandpileOdometer (m : ℤ → ℤ → ℕ) (M : ℝ) (a : ℤ) : ℝ :=
  (mdeg m a : ℝ) * sandpileNormOdometer m M a

/-- The final configuration `s = M δ₀ + deg · Δ(v/deg)` (eq:final-sandpile-definition, line 1546). -/
noncomputable def sandpileFinal (m : ℤ → ℤ → ℕ) (M : ℝ) (a : ℤ) : ℝ :=
  M * diracZero a + (mdeg m a : ℝ) * mLaplacian m (sandpileNormOdometer m M) a

/-- The *divisible sandpile cluster* `D(M) = {a : s(a) > 0}` (eq:cluster-definition, line 1552). -/
def sandpileCluster (m : ℤ → ℤ → ℕ) (M : ℝ) : Set ℤ :=
  {a | 0 < sandpileFinal m M a}

/-- The *discrete obstacle problem* (eq:discrete-least-supersolution-general, line 3375; eq:discrete-least-supersolution,
line 1570): the pointwise infimum of the functions `u` with `Δu ≤ 𝔯` on `V` and `u ≥ φ` on `W`. -/
noncomputable def discreteLeastSupersolution {α : Type*} (m : α → α → ℕ) (V W : Set α) (𝔯 φ : α → ℝ) (a : α) : ℝ :=
  sInf ((fun u : α → ℝ => u a) '' {u | (∀ b ∈ V, mLaplacian m u b ≤ 𝔯 b) ∧ ∀ b ∈ W, φ b ≤ u b})

/-- The *discrete cluster* `{a ∈ W : w(a) > φ(a)}` (eq:discrete-cluster-general, line 3389). -/
def discreteCluster {α : Type*} (W : Set α) (w φ : α → ℝ) : Set α :=
  {a ∈ W | φ a < w a}

/-- The vertex set `V^ε(B_ρ) \ V^ε(∂B_ρ)` of Section 4. -/
def ballInterior (ε : ℝ) (η : ℝ → ℂ) (ρ : ℝ) : Set ℤ :=
  interiorCellVertices ε η (ball 0 ρ)

/-- The obstacle `-(t ε⁻¹) g^ε_{B_ρ}(0, ·)` of eq:discrete-least-supersolution (line 1571). -/
noncomputable def matedObstacle (ε : ℝ) (η : ℝ → ℂ) (ρ t : ℝ) (a : ℤ) : ℝ :=
  -(t / ε) * greenKernel (cellMult ε η) (ballInterior ε η ρ) 0 a

/-- `w̃^ε_t` (eq:discrete-least-supersolution, line 1570): the pointwise minimum of the `w` on `V^ε(cl(B_ρ))` with
`Δ^ε w ≤ (deg^ε)⁻¹` on `V^ε(B_ρ) \ V^ε(∂B_ρ)` and `w ≥ -(t ε⁻¹) g^ε_{B_ρ}(0, ·)`. -/
noncomputable def matedLeastSupersolution (ε : ℝ) (η : ℝ → ℂ) (ρ t : ℝ) (a : ℤ) : ℝ :=
  discreteLeastSupersolution (cellMult ε η) (ballInterior ε η ρ) (cellVertices ε η (closedBall 0 ρ))
    (fun b => ((matedDeg ε η b : ℕ) : ℝ)⁻¹) (matedObstacle ε η ρ t) a

/-- The discrete cluster `Λ^ε_t = {a ∈ V^ε(B_ρ) : w̃^ε_t(a) > -(t ε⁻¹) g^ε_{B_ρ}(0, a)}` (eq:discrete-cluster,
line 1690). -/
def matedDiscreteCluster (ε : ℝ) (η : ℝ → ℂ) (ρ t : ℝ) : Set ℤ :=
  discreteCluster (cellVertices ε η (ball 0 ρ)) (matedLeastSupersolution ε η ρ t) (matedObstacle ε η ρ t)

open Classical in
/-- The stopped odometer `u^ε_t = w̃^ε_t + (t ε⁻¹) g^ε_{B_ρ}(0, ·)` on `V^ε(cl(B_ρ))`, `0` elsewhere
(eq:stopped-odometer-de and line 2941). -/
noncomputable def stoppedOdometer (ε : ℝ) (η : ℝ → ℂ) (ρ t : ℝ) (a : ℤ) : ℝ :=
  if a ∈ cellVertices ε η (closedBall 0 ρ) then
    matedLeastSupersolution ε η ρ t a - matedObstacle ε η ρ t a
  else 0

/-- The setting of Appendix A (lines 3339-3370): an undirected (symmetric multiplicity, no loops), locally finite,
infinite graph; a finite connected vertex set `V` containing the origin `o`; a threshold `𝔯 > 0` on `V`; and an
obstacle `φ ≤ 0` on `cl(V)` with `Δφ = 𝔱 δ_o` on `V`, `φ = 0` on `∂V`, `𝔱 > 0` (eq:laplacian-of-phi, line 3364). The
paper's graph is simple (`m ∈ {0, 1}`); multiplicities are allowed here, as needed for the mated-CRT map. -/
structure IsObstacleSetting {α : Type*} (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ) : Prop where
  symm : ∀ a b, m a b = m b a
  loopless : ∀ a, m a a = 0
  locallyFinite : ∀ a, {b | m a b ≠ 0}.Finite
  infinite : Infinite α
  finite : V.Finite
  connected : IsVConnected m V
  origin_mem : o ∈ V
  threshold_pos : ∀ a ∈ V, 0 < 𝔯 a
  obstacle_nonpos : ∀ a ∈ vClosure m V, φ a ≤ 0
  obstacle_laplacian : ∀ a ∈ V, mLaplacian m φ a = 𝔱 * (open Classical in if a = o then 1 else 0)
  obstacle_boundary : ∀ a ∈ vBoundary m V, φ a = 0
  mass_pos : 0 < 𝔱

end MatedCRT
