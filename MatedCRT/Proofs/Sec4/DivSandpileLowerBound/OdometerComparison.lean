import MatedCRT.Proofs.Sandpile.Geometry
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Steps.Sec4.DivSandpileLowerBound
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov

/-!
# Comparison of the obstacle and sandpile odometers

The least-action principle compares the global odometer with an obstacle problem on any
vertex set, without requiring that the domain be connected.
-/

namespace MatedCRT.Sandpile

open Set

/-- If the obstacle has the point-source Laplacian, the global normalized odometer
lies above the obstacle gap on the set where the obstacle constraint is imposed. -/
theorem obstacle_gap_le_normOdometer {m : ℤ → ℤ → ℕ} {M : ℝ} {V W : Set ℤ}
    {φ : ℤ → ℝ} (hlf : IsLocallyFiniteMult m) (hne : (admissible m M).Nonempty)
    (hφ : ∀ a ∈ V, mLaplacian m φ a = (mdeg m 0 : ℝ)⁻¹ * M * diracZero a)
    {a : ℤ} (ha : a ∈ W) :
    discreteLeastSupersolution m V W (fun b => (mdeg m b : ℝ)⁻¹) φ a - φ a ≤
      sandpileNormOdometer m M a := by
  let u := sandpileNormOdometer m M
  have hu := normOdometer_mem_admissible hlf hne
  have hcomp : (fun b => u b + φ b) ∈
      {v | (∀ b ∈ V, mLaplacian m v b ≤ (mdeg m b : ℝ)⁻¹) ∧ ∀ b ∈ W, φ b ≤ v b} := by
    refine ⟨?_, ?_⟩
    · intro b hb
      rw [mLaplacian_add_of_locallyFinite hlf, hφ b hb]
      exact hu.2 b
    · intro b hb
      have h := normOdometer_nonneg hne b
      dsimp [u]
      linarith
  have hbelow : BddBelow ((fun v : ℤ → ℝ => v a) ''
      {v | (∀ b ∈ V, mLaplacian m v b ≤ (mdeg m b : ℝ)⁻¹) ∧ ∀ b ∈ W, φ b ≤ v b}) := by
    refine ⟨φ a, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hv.2 a ha
  have h := csInf_le hbelow ⟨_, hcomp, rfl⟩
  change discreteLeastSupersolution m V W (fun b => (mdeg m b : ℝ)⁻¹) φ a ≤ u a + φ a at h
  dsimp [u] at h
  linarith

/-- The Section 4 obstacle gap is bounded by the global odometer, including when the
origin is outside the discrete ball. -/
theorem matedObstacle_gap_le_normOdometer {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hfin : (ballInterior ε η ρ).Finite)
    (hne : (admissible m (t / ε)).Nonempty) {a : ℤ}
    (ha : a ∈ cellVertices ε η (Metric.closedBall 0 ρ)) :
    matedLeastSupersolution m ε η ρ t a - matedObstacle m ε η ρ t a ≤
      sandpileNormOdometer m (t / ε) a := by
  apply obstacle_gap_le_normOdometer hlf hne _ ha
  intro b hb
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hG := greenKernelLaplacianStep m (ballInterior ε η ρ) hsymm hlf hcons hfin 0 h0
    rw [matedObstacle_laplacian hG hb]
    simp only [matedDeg, diracZero]
    ring
  · have hzero : matedObstacle m ε η ρ t = fun _ => 0 := by
      funext x
      exact matedObstacle_eq_zero_of_origin_not_mem h0 x
    have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
    simp [hzero, mLaplacian, diracZero, hb0]

/-- A symmetric multigraph on the integers containing every consecutive edge is connected. -/
theorem connected_of_consecutive_edges {m : ℤ → ℤ → ℕ}
    (hsymm : ∀ a b, m a b = m b a) (hcons : ∀ a, m a (a + 1) ≠ 0) :
    IsVConnected m Set.univ := by
  let v : ℤ → (Set.univ : Set ℤ) := fun k => ⟨k, trivial⟩
  have hstep (k : ℤ) : ((adjGraph m).induce Set.univ).Reachable (v k) (v (k + 1)) := by
    apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.induce_adj, adjGraph_adj_iff hsymm]
    exact ⟨by change k ≠ k + 1; omega, hcons k⟩
  have hreach : ∀ k : ℤ, ((adjGraph m).induce Set.univ).Reachable (v 0) (v k) := by
    intro k
    induction k using Int.induction_on with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih => simpa using ih.trans (hstep (k : ℤ))
    | pred k ih =>
      have h := (hstep (-(k : ℤ) - 1)).symm
      have heq : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by omega
      rw [heq] at h
      exact ih.trans h
  let : Nonempty (Set.univ : Set ℤ) := ⟨v 0⟩
  refine ⟨fun a b => ?_⟩
  exact (hreach a).symm.trans (hreach b)

end MatedCRT.Sandpile

namespace MatedCRT

open MeasureTheory Filter Set Metric

/-- The Section 4 odometer comparison follows from adjacent cells meeting in the
mating-of-trees embedding. -/
theorem divSandpileOdometerComparison_of_cellsMeet {𝒮 : SpaceFillingSLEModel}
    (hcell : AdjacentCellsMeetAeStep 𝒮) : DivSandpileOdometerComparisonStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hS.ae_isLocallyFiniteMult hγ hγ2 hcell, hS.isAreaParametrized,
    hS.ae_tendsto_cocompact] with ω hlf hη hp
  intro t ε ht hε
  have hloc := hlf ε hε
  have hsymm := S.mult_symm ε ω
  have hloop := S.mult_self ε ω
  have hcons : ∀ a, S.mult ε ω a (a + 1) ≠ 0 := S.mult_succ_ne_zero hε.le ω
  have hdeg : ∀ a, 0 < mdeg (S.mult ε ω) a := fun a => mdeg_pos_of_ne_zero hloc (hcons a)
  have hconn := Sandpile.connected_of_consecutive_edges hsymm hcons
  obtain ⟨v, hv, _⟩ := Sandpile.exists_finite_stabilizer hloc hsymm hloop hdeg hconn (t / ε)
  have hne : (Sandpile.admissible (S.mult ε ω) (t / ε)).Nonempty := ⟨v, hv⟩
  have hfin : (ballInterior ε (S.η ω) ρ).Finite := by
    apply (cellVertices_finite_of_isCompact hη.1 hp hε (isCompact_closedBall 0 ρ)).subset
    intro a ha
    obtain ⟨z, hz, hzball⟩ := ballInterior_subset_cellVertices_ball ha
    exact ⟨z, hz, ball_subset_closedBall hzball⟩
  refine ⟨hloc, hloop, hdeg, hne, ?_⟩
  intro a ha
  apply Sandpile.matedObstacle_gap_le_normOdometer hloc hsymm hcons hfin hne
  obtain ⟨z, hz, hzball⟩ := ha
  exact ⟨z, hz, ball_subset_closedBall hzball⟩

end MatedCRT
