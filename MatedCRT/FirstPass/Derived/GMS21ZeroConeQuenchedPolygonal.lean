import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusQuenched
import LatticeProb.Topology.TranslatedCurveLawUniformContinuity

/-!
# The quenched unit-scale convergence for the zero-cone cells from a polygonal cell configuration

The invariance principle at unit mesh in the proof of Lemma 3.5 of Gwynne–Miller–Sheffield (arXiv:1705.11161) is the uniform-start invariance principle of Gwynne–Miller–Sheffield (arXiv:1807.07515,
Theorem 3.10) for the unit-mesh cells `K_j = η₀([j - 1, j] + θ)` of the `0`-quantum cone, read through the embedded
vertices `η₀(j + θ)`. The written argument applies Theorem 3.10 to a measurable
*polygonal* cell configuration `{C_j}` on the same weighted graph: the cells `C_j` retain the
conductances `m_{ij}` of the zero-cone data and contain the vertices `v_j`, and the law of the configuration
satisfies the hypotheses of Theorem 1.16 of arXiv:1807.07515 and is invariant under a quarter turn.
Theorem 3.10 at this law, the isotropy of the limiting covariance, the small-cell estimate (arXiv:1807.07515,
Lemmas 2.8-2.9) and a comparison of every starting cell `K_j ∋ z` with a nearby point of `C_j` give
the quenched convergence of the unit-scale errors of the zero-cone weighted data on every annulus.

## Main declarations

* `CarriesUnitMeshWalk w H`: the cells of the GMS configuration `H` carry the walk of the unit-mesh weighted datum
  `w`, with the comparison of the starting cells.
* `GMSSmallCellEstimate`: almost surely the diameters of the cells meeting `B_R(0)` are `o(R)`, for every law on
  the GMS space satisfying the hypotheses of Theorem 1.16 (arXiv:1807.07515, Lemmas 2.8-2.9).
* `tendsto_weightedUnitScaleError_of_carriesUnitMeshWalk`: the deterministic step of the written argument.
* `ZeroConePolygonalConfiguration`: the existence of the polygonal configuration of the written argument.
* `zeroConeQuenchedUnitScaleConvergence_of_polygonal`: Theorem 3.10, the small-cell estimate and the polygonal
  configuration give `ZeroConeQuenchedUnitScaleConvergence`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

section Deterministic

open LatticeProb LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.UnboundedRayLocalDistance
  LatticeProb.UnboundedRayCurveSpace LatticeProb.ReparamDistanceIsometry
open ReflectedGMS.StatementIngredients

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _

local instance : BorelSpace (UnboundedRayCurveSpace 2) := ⟨rfl⟩

attribute [local instance] isProbabilityMeasure_map_complexToEuclideanPath

/-- **A GMS cell configuration carrying the walk of a unit-mesh weighted datum.** For a unit-mesh weighted datum
`w = (η, m)` (a curve `η` and edge counts `m` on `ℤ`) and a cell configuration `H` of the GMS space, there is a
labelling `e : ℤ ≃ cells of H` of the cells of `H` such that
* the conductance of `H` between the cells `e a` and `e b` is the edge count `m a b`;
* the embedded vertex `η(j)` lies in the cell `e j`;
* every point `z` of the unit-mesh cell `η([j - 1, j])` lies in a cell `K` of `H` and within distance
  `diam K` of the cell `e j`.

(Written argument: the polygonal cell `C_j` retains the
conductances `m_{ij}` and contains `v_j`; the Voronoi tile containing a point `z ∈ K_j` lies in the cell
of its owner, and its boundary lies in `C_j`.) -/
def CarriesUnitMeshWalk (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (H : ReflectedGMS.GMS.GMSSpace) : Prop :=
  ∃ e : ℤ ≃ H.1.cells,
    (∀ a b : ℤ, H.1.c (e a) (e b) = (w.2 a b : ℝ)) ∧
    (∀ j : ℤ, Complex.orthonormalBasisOneI.repr (vertexPoint 1 w.1 j) ∈
      ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) ∧
    ∀ j : ℤ, ∀ z ∈ cell 1 w.1 j, ∃ K : H.1.cells,
      Complex.orthonormalBasisOneI.repr z ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ∧
      ∃ y ∈ ((e j : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane),
        dist (Complex.orthonormalBasisOneI.repr z) y ≤
          Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)

/-- **The small-cell estimate of Gwynne–Miller–Sheffield** (arXiv:1807.07515, Lemmas 2.8-2.9; the estimate used in
the written argument: "Almost surely the maximum diameter of the scaled
polygonal cells meeting a fixed disk tends to zero as the spatial scale `s ↓ 0`. For instance, GMS Lemma 2.9 gives
this estimate on large origin dyadic squares. Lemma 2.8 gives the same estimate on all four possible parents").
PENDING TRUTH CHECK. For the coded environments of the reflected invariance principle this is
`ReflectedGMS.ae_maxDiamHittingBall_finite_and_sublinear` (Lattice-Probability,
`LatticeProb/Bonanno/ReflectedGMS/Spatial/LargeCellDiameterDecay.lean`, from mass transport and the finite-energy
moment); its transfer to laws on the GMS space is not available.

For every probability law on the GMS space satisfying the hypotheses of Theorem 1.16 of arXiv:1807.07515, almost
surely, for every `r > 0`, for all large `R`, every cell meeting `closedBall 0 R` has diameter at most `r R`. -/
def GMSSmallCellEstimate : Prop :=
  ∀ (μ : Measure ReflectedGMS.GMS.GMSSpace) [IsProbabilityMeasure μ],
    ReflectedGMS.GMS.MassTransport μ → ReflectedGMS.GMS.ErgodicModuloScaling μ →
      ReflectedGMS.GMS.FiniteExpectation μ → ReflectedGMS.GMS.ConnectedAlongLines μ →
        ∀ᵐ H ∂μ, ∀ r : ℝ, 0 < r → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          ∀ K : H.1.cells,
            (((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ∩ closedBall 0 R).Nonempty →
              Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ≤ r * R

/-- The law modulo time parametrization of Brownian motion with the covariance of `target` is a probability
measure. -/
theorem isProbabilityMeasure_brownianCurveLaw (target : AnisotropicBrownianTarget)
    (z : ReflectedGMS.Plane) : IsProbabilityMeasure (GMS310.brownianCurveLaw target z) :=
  (translatedCurveProbability (target.pathLaw : Measure (LatticeProb.UnboundedRayIntervalIntegrand.Path 2))
    (ae_unbounded_range_anisotropicBrownian target) z).2

/-- **The unit-scale errors of a weighted datum carried by a GMS configuration**. Let the cells of the configuration `H` carry the walk of the
unit-mesh weighted datum `w`, whose edge counts are locally finite with the successor edges, let the Brownian
covariance of Theorem 3.10 be a positive multiple of the identity, let the second conclusion of Theorem 3.10 hold at
`H`, and let the cells of `H` meeting `B_R(0)` have diameters `o(R)`. Then for every compact set `A` the uniform
error over starts in `A` of the walk on `w` at spatial scale `ε` tends to `0` as `ε ↓ 0`.

For `z ∈ A` in the scaled cell `ε K_j`, the comparison of the starting cells gives a point `z'` of `ε C_j` within
`ε diam K` of `z`, where `K ∋ z / ε` meets `B_{M/ε}(0)`; by the small-cell estimate `|z - z'|` is uniformly small.
The walks from `j` on `w` and on `H` (read through the vertices) have the same law, Theorem 3.10 compares it with
Brownian motion from `z'`, and the uniform continuity of the Brownian law in its starting point compares Brownian
motion from `z'` and from `z`. -/
theorem tendsto_weightedUnitScaleError_of_carriesUnitMeshWalk {w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)}
    (hlf : IsLocallyFiniteMult w.2) (hsucc : ∀ k : ℤ, w.2 k (k + 1) ≠ 0)
    {H : ReflectedGMS.GMS.GMSSpace} (hcar : CarriesUnitMeshWalk w H)
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
    (hsmall : ∀ r : ℝ, 0 < r → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ K : H.1.cells,
        (((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ∩ closedBall 0 R).Nonempty →
          Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ≤ r * R)
    {A : Set ℂ} (hA : IsCompact A) :
    Tendsto (fun ε : ℝ≥0 => weightedUnitScaleError A ε w) (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨e, he_c, he_v, he_cmp⟩ := hcar
  have hpos : ∀ a, 0 < mdeg w.2 a := mdeg_pos_of_succ hlf hsucc
  obtain ⟨p, hp⟩ : ∃ p : H.1.cells → ReflectedGMS.Plane,
      p = fun K => Complex.orthonormalBasisOneI.repr (vertexPoint 1 w.1 (e.symm K)) := ⟨_, rfl⟩
  have hpK : ∀ K : H.1.cells, p K ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
    intro K
    obtain ⟨k, rfl⟩ := e.surjective K
    rw [hp]
    show Complex.orthonormalBasisOneI.repr (vertexPoint 1 w.1 (e.symm (e k))) ∈ _
    rw [Equiv.symm_apply_apply]
    exact he_v k
  obtain ⟨M, hM, hAM⟩ := hA.isBounded.exists_pos_norm_le
  have hA' : IsCompact (cthickening 1 (Complex.orthonormalBasisOneI.repr '' A)) :=
    (hA.image Complex.orthonormalBasisOneI.repr.continuous).cthickening
  rw [ENNReal.tendsto_nhds_zero]
  intro δ' hδ'
  obtain ⟨δ, -, hδpos, hδlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ'
  have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδpos
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨κ, hκ, hcont⟩ := translated_curveLaw_levyProkhorovDist_lt
    (target.pathLaw : Measure (LatticeProb.UnboundedRayIntervalIntegrand.Path 2))
    (ae_unbounded_range_anisotropicBrownian target) hA' (δ / 2) hδ2
  obtain ⟨ε₀, hε₀, hball⟩ := h310 p hpK _ hA' (δ / 2) hδ2
  obtain ⟨κ', hκ'pos, hκ'κ, hκ'1⟩ : ∃ κ' : ℝ, 0 < κ' ∧ κ' < κ ∧ κ' ≤ 1 :=
    ⟨min κ 1 / 2, half_pos (lt_min hκ one_pos),
      by linarith [min_le_left κ 1, lt_min hκ one_pos], by linarith [min_le_right κ 1]⟩
  obtain ⟨R₀, hR₀, hsm⟩ := hsmall (κ' / M) (div_pos hκ'pos hM)
  have hmem : Ioo (0 : ℝ≥0) (min ε₀ (M / R₀)).toNNReal ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (Real.toNNReal_pos.2 (lt_min hε₀ (div_pos hM hR₀)))
  filter_upwards [hmem] with ε hε
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 hε.1
  have hεlt : (ε : ℝ) < min ε₀ (M / R₀) := Real.lt_toNNReal_iff_coe_lt.1 hε.2
  have hεlt₀ : (ε : ℝ) < ε₀ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hR₀le : R₀ ≤ M / ε := by
    rw [le_div_iff₀ hεpos]
    have h1 : (ε : ℝ) < M / R₀ := lt_of_lt_of_le hεlt (min_le_right _ _)
    rw [lt_div_iff₀ hR₀] at h1
    linarith
  have hscale : (ε : ℝ) * (κ' / M * (M / ε)) = κ' := by
    have h1 : (ε : ℝ) * (κ' / M * (M / ε)) = κ' * (M / M) * ((ε : ℝ) / ε) := by ring
    rw [h1, div_self hM.ne', div_self hεpos.ne', mul_one, mul_one]
  refine le_trans ?_ hδlt.le
  unfold weightedUnitScaleError unitScaleError uniformLPError
  refine iSup₂_le fun z hz => iSup₂_le fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := hx
  have hzA : ((ε : ℝ) : ℂ) * w.1 t ∈ A := hz
  -- a cell of `H` containing the point, and a nearby point of the cell of `x`
  obtain ⟨K, hK, y, hy, hdist⟩ := he_cmp x (w.1 t) ⟨t, ht, rfl⟩
  have hrepr : Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 t) =
      (ε : ℝ) • Complex.orthonormalBasisOneI.repr (w.1 t) := by
    rw [← Complex.real_smul, LinearIsometryEquiv.map_smul]
  have hnorm : ‖w.1 t‖ ≤ M / ε := by
    rw [le_div_iff₀ hεpos]
    have h1 := hAM _ hzA
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hεpos.le] at h1
    linarith
  have hdiam : Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) ≤ κ' / M * (M / ε) :=
    hsm (M / ε) hR₀le K ⟨_, hK, mem_closedBall_zero_iff.2 (by
      rw [LinearIsometryEquiv.norm_map]; exact hnorm)⟩
  have hzz' : dist (Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 t)) ((ε : ℝ) • y) ≤ κ' := by
    rw [hrepr, dist_smul₀, Real.norm_of_nonneg hεpos.le]
    calc (ε : ℝ) * dist (Complex.orthonormalBasisOneI.repr (w.1 t)) y
        ≤ (ε : ℝ) * (κ' / M * (M / ε)) :=
          mul_le_mul_of_nonneg_left (hdist.trans hdiam) hεpos.le
      _ = κ' := hscale
  have hzA' : Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 t) ∈
      cthickening 1 (Complex.orthonormalBasisOneI.repr '' A) :=
    self_subset_cthickening _ (mem_image_of_mem _ hzA)
  have hz'A' : (ε : ℝ) • y ∈ cthickening 1 (Complex.orthonormalBasisOneI.repr '' A) :=
    mem_cthickening_of_dist_le _ _ 1 _ (mem_image_of_mem _ hzA) (by rw [dist_comm]; linarith)
  -- the walk of Theorem 3.10 from the cell of `x`
  have hF : Measurable (fun ξ : ℕ → ℤ => fun n => e (ξ n)) :=
    Measurable.of_eval fun n => (measurable_of_countable e).comp (measurable_pi_apply n)
  have hG : Measurable (GMS310.scaledStepPath H.1 p (ε : ℝ)) := by
    let _ : Countable H.1.cells := Countable.of_equiv ℤ e
    unfold GMS310.scaledStepPath
    apply LatticeProb.CellConfigWalk.measurable_constantStepPath
    exact Measurable.of_eval fun n =>
      (measurable_of_countable (fun K => (ε : ℝ) • p K)).comp (measurable_pi_apply n)
  have hwalk : GMS310.walkCurveLaw H.1 p (ε : ℝ) ((srwLaw w.2 x).map (fun ξ n => e (ξ n))) =
      GMS310.unboundedCurveLaw ((srwLaw w.2 x).map fun ξ => complexToEuclideanPath
        (interpPathCM (vertexPoint 1 (fun t => ((ε : ℝ) : ℂ) * w.1 t)) zero_le_one ξ)) := by
    unfold GMS310.walkCurveLaw
    rw [Measure.map_map hG hF]
    congr 2
    funext ξ
    rw [complexToEuclideanPath_interpPathCM_eq_constantStep]
    show LatticeProb.ConstantStepInterpolation.continuousPlanePath 1
      (fun n => (ε : ℝ) • p (e (ξ n))) = _
    refine congrArg (LatticeProb.ConstantStepInterpolation.continuousPlanePath 1) (funext fun n => ?_)
    rw [hp]
    show (ε : ℝ) • Complex.orthonormalBasisOneI.repr (w.1 (1 * ((e.symm (e (ξ n)) : ℤ) : ℝ))) =
      Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 (1 * (ξ n : ℝ)))
    rw [Equiv.symm_apply_apply, ← Complex.real_smul, LinearIsometryEquiv.map_smul]
  have hmemK : (ε : ℝ)⁻¹ • ((ε : ℝ) • y) ∈ ((e x : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) := by
    rw [inv_smul_smul₀ hεpos.ne']
    exact hy
  have h1 := hball (ε : ℝ) hεpos hεlt₀ _ hz'A' (e x) hmemK _
    (isSRWLaw_map_srwLaw w.2 hlf hpos H.1 e he_c x)
  rw [hwalk] at h1
  -- the Brownian laws from the two nearby starts
  have hB1 := isProbabilityMeasure_brownianCurveLaw target ((ε : ℝ) • y)
  have hB2 := isProbabilityMeasure_brownianCurveLaw target
    (Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 t))
  have h2 : levyProkhorovDist (GMS310.brownianCurveLaw target ((ε : ℝ) • y))
      (GMS310.brownianCurveLaw target (Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 t))) <
      δ / 2 :=
    hcont _ hz'A' _ hzA' (by rw [dist_comm]; linarith)
  have h2' : levyProkhorovEDist (GMS310.brownianCurveLaw target ((ε : ℝ) • y))
      (GMS310.brownianCurveLaw target (Complex.orthonormalBasisOneI.repr (((ε : ℝ) : ℂ) * w.1 t))) <
      ENNReal.ofReal (δ / 2) :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).2 h2
  have hsum : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add hδ2.le hδ2.le, add_halves]
  have hfinal := ((levyProkhorovEDist_triangle _ (GMS310.brownianCurveLaw target ((ε : ℝ) • y)) _).trans
    (add_le_add h1.le h2'.le)).trans_eq hsum
  rw [brownianCurveLaw_eq_planar target hc hcov] at hfinal
  exact hfinal

end Deterministic

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b ReflectedGMS.GMS

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The polygonal cell configuration carrying the zero-cone walk** (the construction of the written argument, for the unit-mesh cells of the `0`-quantum cone in the proof of
Lemma 3.5 of Gwynne–Miller–Sheffield, arXiv:1705.11161). A named step: it is not proved here.

For every measurable version `G` of the boundary-length pair of the zero-cone curve there is a map `Φ` from the
sample and the phase `θ` to the GMS space, almost measurable for `P ⊗ Unif[0, 1]`, such that
* the law of `Φ` satisfies the hypotheses of Theorem 1.16 of arXiv:1807.07515: mass transport (translation
  invariance modulo scaling), ergodicity modulo scaling, the finite expectation and connectedness along lines;
* the law of `Φ` is invariant under the quarter turn of the plane;
* almost surely the cells of `Φ` carry the walk of the unit-mesh weighted data of `t ↦ η₀(t + θ)` and the edge
  counts of `t ↦ G(t + θ)` (the polygonal cells `C_j` retain the conductances and contain the
  vertices, and the Voronoi tiles compare every starting cell). -/
def ZeroConePolygonalConfiguration
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    ∃ Φ : Ω × ℝ → GMSSpace, AEMeasurable Φ (P.prod zeroConePhase) ∧
      ReflectedGMS.GMS.MassTransport ((P.prod zeroConePhase).map Φ) ∧
      ReflectedGMS.GMS.ErgodicModuloScaling ((P.prod zeroConePhase).map Φ) ∧
      ReflectedGMS.GMS.FiniteExpectation ((P.prod zeroConePhase).map Φ) ∧
      ReflectedGMS.GMS.ConnectedAlongLines ((P.prod zeroConePhase).map Φ) ∧
      ((P.prod zeroConePhase).map Φ).map (isometryGMS quarterTurn) = (P.prod zeroConePhase).map Φ ∧
      ∀ᵐ p ∂P.prod zeroConePhase, CarriesUnitMeshWalk (phaseShiftedData η₀ G 1 p) (Φ p)

/-- **The quenched unit-scale convergence for the zero-cone cells from the polygonal configuration**. Theorem 3.10 of arXiv:1807.07515 applies to the law of the
polygonal configuration; the quarter-turn invariance makes the limiting covariance a positive multiple of the
identity; on the event where the configuration carries the zero-cone walk, the small-cell estimate holds and the
edge counts are locally finite with the successor edges, the comparison of the starting cells gives the
convergence of the unit-scale errors on every annulus. -/
theorem zeroConeQuenchedUnitScaleConvergence_of_polygonal
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (h310 : GMSTheorem310) (hsmall : GMSSmallCellEstimate)
    (hpoly : ZeroConePolygonalConfiguration D hγ) :
    ZeroConeQuenchedUnitScaleConvergence D hγ := by
  intro G hG b ρ _ _
  have hPprob : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Φ, hΦm, hMT, hErg, hFE, hconn, hrot, hcar⟩ := hpoly G hG
  have hμ : IsProbabilityMeasure ((P.prod zeroConePhase).map Φ) :=
    (Measure.isProbabilityMeasure_map_iff hΦm).2 inferInstance
  obtain ⟨target, hconv, hunif⟩ := h310 _ hMT hErg hFE hconn
  obtain ⟨c₀, hc₀, hcov₀⟩ := covariance_eq_smul_one_of_map_quarterTurn hrot hconn hconv
  have hA : IsCompact (closedBall (0 : ℂ) ρ \ ball 0 b) :=
    (isCompact_closedBall (0 : ℂ) ρ).diff isOpen_ball
  filter_upwards [ae_of_ae_map hΦm hunif, ae_of_ae_map hΦm (hsmall _ hMT hErg hFE hconn), hcar,
    ae_mem_regularData_phaseShifted D hγ hf hG one_pos] with p hu hs hc hreg
  exact tendsto_weightedUnitScaleError_of_carriesUnitMeshWalk (w := phaseShiftedData η₀ G 1 p)
    hreg.2.1 hreg.2.2 hc target hc₀ hcov₀ hu hs hA

end ZeroCone

end MatedCRT.GMS310Transfer
