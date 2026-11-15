import MatedCRT.FirstPass.Derived.AreaCellFiniteFamilyEndpoint
import MatedCRT.FirstPass.Derived.FiniteDomainBrownianEndpointSelectorMarginals

/-! Endpoint couplings for families of area-cell walks. -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory HarmonicBalls LatticeProb BouRabeeGwynne Filter Set
open LatticeProb.ReparamDistanceIsometry LatticeProb.UnboundedRayIntervalIntegrand
open scoped NNReal ENNReal Topology

/-- Uniform stopped-curve convergence gives nearby-start couplings of the
walk exit position and Brownian endpoint with controlled selector disagreement
and endpoint separation. -/
theorem areaCell_finiteFamily_nearby_endpoint_selector_coupling
    {J : Type*} [Fintype J] {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    (W : J → Set ℂ) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (Complex.orthonormalBasisOneI.repr '' W j))
    (K : J → Set (BouRabeeGwynne.Euc 2)) (hKc : ∀ j, IsCompact (K j))
    (hKW : ∀ j, K j ⊆ Complex.orthonormalBasisOneI.repr '' W j)
    (ρ : Measure (BouRabeeGwynne.BrownianPath 2)) (hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ)
    (V : ∀ _j, ℕ → Type*) (x : ∀ j n, V j n → ℤ)
    (ε m a : J → ℕ → ℝ) (hε : ∀ j n, 0 < ε j n) (hm : ∀ j n, 0 ≤ m j n)
    (mult : J → ℕ → ℤ → ℤ → ℕ)
    (hK : ∀ j n (v : V j n), Complex.orthonormalBasisOneI.repr
      (a j n • vertexPoint (ε j n) η (x j n v)) ∈ K j)
    (hc : ∀ j, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovEDist
        ((srwLaw (mult j n) (x j n v)).map (fun w => CurveSpaceComparison.isometryEquiv 2
          (normalizedPrefixCurve
            (complexToEuclideanPath (a j n • interpPathCM (vertexPoint (ε j n) η) (hm j n) w))
            (pathExitTime (W j) (a j n • interpPathCM (vertexPoint (ε j n) η) (hm j n) w)).toNNReal)))
        (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' W j)
          (Complex.orthonormalBasisOneI.repr (a j n • vertexPoint (ε j n) η (x j n v))) ρ)
        < ENNReal.ofReal δ)
    {ι A : Type*} [Fintype ι] (S : ι → Set (BouRabeeGwynne.Euc 2))
    (select : ι → Option A) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hnull : ∀ j i (z : K j),
      ((stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' W j) z ρ).map
        BouRabeeGwynne.CurveSpace.endPoint) (frontier (S i)) = 0)
    (hcover : ∀ j (z : K j),
      ((stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' W j) z ρ).map
        BouRabeeGwynne.CurveSpace.endPoint) (⋃ i, S i) = 1)
    (r : ℝ) (hdiam : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, dist x y < r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : K j),
      dist (Complex.orthonormalBasisOneI.repr (a j n • vertexPoint (ε j n) η (x j n v))) z ≤ t →
        ∃ π : Measure (BouRabeeGwynne.Euc 2 × BouRabeeGwynne.Euc 2),
          IsProbabilityMeasure π ∧
          π.fst = (areaCellEuclideanExitProbability (η := η) (ε := ε j n) (hm j n)
            (mult j n) (a j n) (hW j) (x j n v) : Measure (BouRabeeGwynne.Euc 2)) ∧
          π.snd = (stoppedBrownianLaw (Complex.orthonormalBasisOneI.repr '' W j) z ρ).map
            BouRabeeGwynne.CurveSpace.endPoint ∧
          π {q | cellSelector S select q.1 ≠ cellSelector S select q.2 ∨
            r ≤ dist q.1 q.2} ≤ ENNReal.ofReal δ := by
  exact BrownianExitLawIdentification.finite_uniform_nearby_stoppedBrownian_endpoint_selector_coupling
    (fun j => Complex.orthonormalBasisOneI.repr '' W j) K
    (fun j => Complex.orthonormalBasisOneI.repr.toHomeomorph.isOpenMap _ (hW j))
    hWb hKc hKW ρ hρ V
    (fun j n v => ⟨_, hK j n v⟩)
    (fun j n v => areaCellEuclideanExitProbability (η := η) (ε := ε j n) (hm j n)
      (mult j n) (a j n) (hW j) (x j n v))
    (areaCell_finiteFamily_endpoint_hLP h W hW K ρ hρ V x ε m a hε hm mult hK hc)
    S select hS hd hnull hcover r hdiam hδ

end MatedCRT
end
