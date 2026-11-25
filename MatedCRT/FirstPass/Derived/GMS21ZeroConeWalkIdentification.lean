import MatedCRT.FirstPass.Derived.GMS21ZeroConeUniformError
import MatedCRT.FirstPass.Derived.GMS21Theorem310Form
import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig
import MatedCRT.FirstPass.Derived.PaperConstantStepInterpolation

/-!
# The walk of Theorem 3.10 on a shifted area-cell configuration

The uniform-start invariance principle of Gwynne–Miller–Sheffield (arXiv:1807.07515, Theorem 3.10) is stated for
the jump chain of the simple random walk on an abstract cell configuration `H`, read through points `p K ∈ K` and
rescaled by `ε` (`GMS310.walkCurveLaw`). For the configuration of the time-shifted cells `η([x - 1, x] + θ)` of an
area-parametrized curve with conductances given by a multigraph `m` on `ℤ` (`shiftedAreaCellConfig`), with
`p K` the embedded vertex of `K`, this law is the law modulo time parametrization of the interpolated embedded walk
on `m` with vertices `ε η(x + θ)`.

* `unitScaleError A ε η m`: the uniform error over starts in `A` of the walk on `m` with the cells and vertices of
  the unit-mesh curve `ε η` (`uniformLPError`).
* `tendsto_unitScaleError_of_theorem310`: if `H` is the shifted area-cell configuration of `η` and `m`, `m` is
  locally finite with the successor edges, the Brownian covariance is a positive multiple of the identity, and the
  conclusion of Theorem 3.10 holds at `H`, then `unitScaleError A ε (η (· + θ)) m → 0` as `ε → 0` for every
  compact set `A`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open LatticeProb LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.UnboundedRayLocalDistance
  LatticeProb.UnboundedRayCurveSpace LatticeProb.ReparamDistanceIsometry
open ReflectedGMS.StatementIngredients

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _

attribute [local instance] isProbabilityMeasure_map_complexToEuclideanPath

/-- A locally finite multigraph with the successor edges has positive degrees. -/
theorem mdeg_pos_of_succ {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) (a : ℤ) : 0 < mdeg m a := by
  unfold mdeg
  have hs : (Function.support fun c => m a c).Finite := hlf a
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (hsucc a))
    (single_le_finsum (a + 1) hs fun _ => Nat.zero_le _)

/-- **The uniform error at spatial scale `ε` of a unit-mesh datum**: the uniform error over starts in `A` of the
walk on `m` with the cells and vertices at mesh `1` of the curve `ε η`. -/
def unitScaleError (A : Set ℂ) (ε : ℝ≥0) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) : ℝ≥0∞ :=
  uniformLPError A (cell 1 (fun t => ((ε : ℝ) : ℂ) * η t))
    (vertexPoint 1 (fun t => ((ε : ℝ) : ℂ) * η t)) m

/-- **The walk of Theorem 3.10 on a shifted area-cell configuration.** Let `H` be the configuration of the
time-shifted cells `η([x - 1, x] + θ)` of an area-parametrized curve `η` with the conductances of a locally finite
multigraph `m` with the successor edges, and let the Brownian covariance of Theorem 3.10 be a positive multiple of
the identity. If the second conclusion of Theorem 3.10 holds at `H`, then for every compact set `A` the uniform
error over starts in `A` of the walk on `m` with the cells and vertices of `ε η(· + θ)` tends to `0` as `ε → 0`. -/
theorem tendsto_unitScaleError_of_theorem310 {μa : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μa η) (θ : ℝ) (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0) (H : ReflectedGMS.GMS.GMSSpace)
    (hH : H.1 = shiftedAreaCellConfig h one_pos θ m)
    (target : AnisotropicBrownianTarget) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1)
    (h310 : ∀ p : H.1.cells → ReflectedGMS.Plane,
      (∀ K : H.1.cells, p K ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) →
      ∀ A : Set ReflectedGMS.Plane, IsCompact A → ∀ δ : ℝ, 0 < δ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∀ z ∈ A, ∀ K : H.1.cells,
            ε⁻¹ • z ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) →
            ∀ Q : Measure (ℕ → H.1.cells), H.1.IsSRWLaw K Q →
              levyProkhorovEDist (GMS310.walkCurveLaw H.1 p ε Q)
                (GMS310.brownianCurveLaw target z) < ENNReal.ofReal δ)
    {A : Set ℂ} (hA : IsCompact A) :
    Tendsto (fun ε : ℝ≥0 => unitScaleError A ε (fun t => η (t + 1 * θ)) m) (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨C, hC⟩ := H
  dsimp only at hH h310
  subst hH
  have hpos : ∀ a, 0 < mdeg m a := mdeg_pos_of_succ hlf hsucc
  obtain ⟨p, hp⟩ : ∃ p : (shiftedAreaCellConfig h one_pos θ m).cells → ReflectedGMS.Plane,
      p = fun K => Complex.orthonormalBasisOneI.repr
        (vertexPoint 1 (fun t => η (t + 1 * θ)) ((shiftedEuclideanCellEquiv h one_pos θ).symm K)) :=
    ⟨_, rfl⟩
  have hpK : ∀ K : (shiftedAreaCellConfig h one_pos θ m).cells,
      p K ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
    intro K
    obtain ⟨k, rfl⟩ := (shiftedEuclideanCellEquiv h one_pos θ).surjective K
    rw [hp]
    show Complex.orthonormalBasisOneI.repr (vertexPoint 1 (fun t => η (t + 1 * θ))
      ((shiftedEuclideanCellEquiv h one_pos θ).symm (shiftedEuclideanCellEquiv h one_pos θ k))) ∈ _
    rw [Equiv.symm_apply_apply]
    exact shiftedAreaCellConfig_vertex_mem h one_pos θ k
  have hA' : IsCompact (Complex.orthonormalBasisOneI.repr '' A) :=
    hA.image Complex.orthonormalBasisOneI.repr.continuous
  rw [ENNReal.tendsto_nhds_zero]
  intro δ' hδ'
  obtain ⟨δ, -, hδpos, hδlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ'
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδpos
  obtain ⟨ε₀, hε₀, hball⟩ := h310 p hpK _ hA' δ hδ
  have hmem : Ioo (0 : ℝ≥0) ε₀.toNNReal ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (Real.toNNReal_pos.2 hε₀)
  filter_upwards [hmem] with ε hε
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 hε.1
  have hεlt : (ε : ℝ) < ε₀ := Real.lt_toNNReal_iff_coe_lt.1 hε.2
  refine le_trans ?_ hδlt.le
  unfold unitScaleError uniformLPError
  refine iSup₂_le fun z hz => iSup₂_le fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := hx
  -- the relabelled walk and its law
  have hF : Measurable (fun ξ : ℕ → ℤ => fun n => shiftedEuclideanCellEquiv h one_pos θ (ξ n)) :=
    Measurable.of_eval fun n =>
      (measurable_of_countable (shiftedEuclideanCellEquiv h one_pos θ)).comp (measurable_pi_apply n)
  have hG : Measurable (GMS310.scaledStepPath (shiftedAreaCellConfig h one_pos θ m) p (ε : ℝ)) := by
    let _ : Countable (shiftedAreaCellConfig h one_pos θ m).cells :=
      Countable.of_equiv ℤ (shiftedEuclideanCellEquiv h one_pos θ)
    unfold GMS310.scaledStepPath
    apply LatticeProb.CellConfigWalk.measurable_constantStepPath
    exact Measurable.of_eval fun n =>
      (measurable_of_countable (fun K => (ε : ℝ) • p K)).comp (measurable_pi_apply n)
  have hwalk : GMS310.walkCurveLaw (shiftedAreaCellConfig h one_pos θ m) p (ε : ℝ)
      ((srwLaw m x).map (fun ξ n => shiftedEuclideanCellEquiv h one_pos θ (ξ n))) =
      GMS310.unboundedCurveLaw ((srwLaw m x).map fun ξ => complexToEuclideanPath
        (interpPathCM (vertexPoint 1 (fun t => ((ε : ℝ) : ℂ) * η (t + 1 * θ))) zero_le_one ξ)) := by
    unfold GMS310.walkCurveLaw
    rw [Measure.map_map hG hF]
    congr 2
    funext ξ
    rw [complexToEuclideanPath_interpPathCM_eq_constantStep]
    show LatticeProb.ConstantStepInterpolation.continuousPlanePath 1
      (fun n => (ε : ℝ) • p (shiftedEuclideanCellEquiv h one_pos θ (ξ n))) = _
    refine congrArg (LatticeProb.ConstantStepInterpolation.continuousPlanePath 1) (funext fun n => ?_)
    rw [hp]
    show (ε : ℝ) • Complex.orthonormalBasisOneI.repr (η (1 * ((shiftedEuclideanCellEquiv h one_pos θ).symm
        (shiftedEuclideanCellEquiv h one_pos θ (ξ n)) : ℝ) + 1 * θ)) =
      Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * η (1 * (ξ n : ℝ) + 1 * θ))
    rw [Equiv.symm_apply_apply, ← Complex.real_smul, LinearIsometryEquiv.map_smul]
  have hmemK : (ε : ℝ)⁻¹ • Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * η (t + 1 * θ)) ∈
      (((shiftedEuclideanCellEquiv h one_pos θ x : (shiftedAreaCellConfig h one_pos θ m).cells) :
        ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
    change _ ∈ (euclideanCell 1 (fun t => η (t + 1 * θ))
      (h.1.comp (continuous_id.add continuous_const)) one_pos x : Set ReflectedGMS.Plane)
    rw [coe_euclideanCell]
    refine ⟨η (t + 1 * θ), ⟨t, ht, rfl⟩, ?_⟩
    rw [← Complex.real_smul, LinearIsometryEquiv.map_smul, smul_smul, inv_mul_cancel₀ hεpos.ne',
      one_smul]
  have h1 := hball (ε : ℝ) hεpos hεlt _ (mem_image_of_mem _ hz)
    (shiftedEuclideanCellEquiv h one_pos θ x) hmemK _
    (shiftedAreaCellConfig_isSRWLaw h one_pos θ m hlf hpos x)
  rw [hwalk, brownianCurveLaw_eq_planar target hc hcov] at h1
  exact h1.le

end MatedCRT.GMS310Transfer
