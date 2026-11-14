import MatedCRT.FirstPass.Derived.FieldCoordinateCircleAverages
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Topology.PolishContinuousMap

/-!
# An explicit Borel set of field coordinates with continuous dyadic circle averages

For a coordinate vector `x : LQGMetric.CoordJ → ℝ` of a whole-plane distribution, the circle-average process
`coordCircleAverage x r z` is the distributional circle version of the decoded distribution
`LQGMetric.pairJInv ⊤ x`. This file isolates an explicit Borel set `coordCircleGood` of coordinate vectors on
which, at every dyadic radius `2^{-n}`, the circle-average process is a continuous function of the center, and
shows that the coordinates of the field of every valid mated-CRT environment lie in it almost surely.

The set is described through the raw circle averages at the grid centers `FieldCircle.gridPt m a b`: a
coordinate vector `x` lies in `coordCircleGood` if it is in the range of the coordinate map and, for every `n`,
the grid values `LQGMetric.circleAvg (LQGMetric.pairJInv ⊤ x) (2^{-n}) (gridPt m a b)` are the grid values of a
continuous function on the plane. Grid evaluation `gridEval : C(ℂ, ℝ) → (ℕ × ℤ × ℤ → ℝ)` is a continuous
injection out of the Polish space `C(ℂ, ℝ)` (the grid is dense), so its range is Borel; this makes
`coordCircleGood` Borel. On `coordCircleGood` the spatial grid limsup defining the circle version reproduces the
continuous extension at every center, and the outer dyadic radius approximation is eventually exact at radius
`2^{-n}`. Almost sure membership follows from the almost sure continuity of the circle-average process of a
quantum cone and the almost sure agreement of distributional and cone circle averages at each grid circle.

## Main statements

* `MatedCRT.gridEval`, `MatedCRT.measurableSet_range_gridEval`;
* `MatedCRT.coordCircleGood`, `MatedCRT.measurableSet_coordCircleGood`;
* `MatedCRT.continuous_coordCircleAverage_of_mem` (radius `(2 : ℝ) ^ (-(n : ℤ))`);
* `MatedCRT.MatedCRTEnv.IsValid.ae_pairJ_mem_coordCircleGood`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace MatedCRT

/-- Evaluation of a continuous function on the plane at the grid centers
`FieldCircle.gridPt m a b`, indexed by `(m, a, b) : ℕ × ℤ × ℤ`. -/
def gridEval (f : C(ℂ, ℝ)) : ℕ × ℤ × ℤ → ℝ :=
  fun i => f (FieldCircle.gridPt i.1 i.2.1 i.2.2)

/-- Grid evaluation is continuous for the compact-open topology. -/
theorem continuous_gridEval : Continuous gridEval :=
  continuous_pi fun i => continuous_eval_const (FieldCircle.gridPt i.1 i.2.1 i.2.2)

/-- A continuous function on the plane is determined by its values at the grid centers, which are dense. -/
theorem gridEval_injective : Function.Injective gridEval := by
  intro f g h
  ext z
  have hfg : ∀ m : ℕ, f (FieldCircle.gridApprox m z) = g (FieldCircle.gridApprox m z) := fun m =>
    congrFun h (m, ⌊z.re * 2 ^ m⌋, ⌊z.im * 2 ^ m⌋)
  exact tendsto_nhds_unique ((f.continuous.tendsto z).comp (FieldCircle.tendsto_gridApprox z))
    (((g.continuous.tendsto z).comp (FieldCircle.tendsto_gridApprox z)).congr fun m => (hfg m).symm)

/-- The set of grid value vectors that extend to a continuous function on the plane is Borel: it is the
range of a continuous injection out of the Polish space `C(ℂ, ℝ)`. -/
theorem measurableSet_range_gridEval : MeasurableSet (range gridEval) := by
  have : PolishSpace C(ℂ, ℝ) := LatticeProb.polishSpace_continuousMap ℂ ℝ
  exact measurableSet_range_of_continuous_injective continuous_gridEval gridEval_injective

/-- The raw circle averages, at radius `2^{-n}` and at the grid centers, of the distribution decoded from a
coordinate vector. -/
def coordGridCircleAverages (n : ℕ) (x : LQGMetric.CoordJ → ℝ) : ℕ × ℤ × ℤ → ℝ :=
  fun i => LQGMetric.circleAvg (LQGMetric.pairJInv ⊤ x) ((2 : ℝ) ^ (-(n : ℤ)))
    (FieldCircle.gridPt i.1 i.2.1 i.2.2)

/-- The raw grid circle averages of a coordinate vector depend measurably on the coordinates. -/
theorem measurable_coordGridCircleAverages (n : ℕ) : Measurable (coordGridCircleAverages n) :=
  measurable_pi_iff.2 fun i =>
    (LQGMetric.measurable_circleAvg_left ((2 : ℝ) ^ (-(n : ℤ)))
      (FieldCircle.gridPt i.1 i.2.1 i.2.2)).comp (LQGMetric.measurable_pairJInv ⊤)

/-- The explicit good set of field coordinates: coordinate vectors of whole-plane distributions whose raw
circle averages at every dyadic radius `2^{-n}`, evaluated at the grid centers, are the grid values of a
continuous function on the plane. -/
def coordCircleGood : Set (LQGMetric.CoordJ → ℝ) :=
  range (LQGMetric.pairJ ⊤) ∩ ⋂ n : ℕ, coordGridCircleAverages n ⁻¹' range gridEval

/-- The good set of field coordinates is Borel. -/
theorem measurableSet_coordCircleGood : MeasurableSet coordCircleGood :=
  (LQGMetric.measurableSet_range_pairJ ⊤).inter (MeasurableSet.iInter fun n =>
    measurableSet_range_gridEval.preimage (measurable_coordGridCircleAverages n))

/-- At a dyadic radius `k / 2^j`, the spatial interpolation of the distributional circle averages is the
grid limsup of the circle averages at that radius. -/
theorem distributionCircleAtDyadic_eq_gridVersion {j : ℕ} {k : ℤ} {r : ℝ} (h : (k : ℝ) / 2 ^ j = r)
    (d : LQGMetric.DistC) (z : ℂ) :
    Sec1.distributionCircleAtDyadic j k d z =
      FieldCircle.gridVersion (fun w d => LQGMetric.circleAvg d r w) d z := by
  subst h
  rfl

/-- If the raw grid circle averages at radius `2^{-n}` of a coordinate vector are the grid values of a
continuous function `f`, then the circle-average process at radius `2^{-n}` is `f` at every center. -/
theorem coordCircleAverage_eq_of_gridEval_eq {x : LQGMetric.CoordJ → ℝ} {n : ℕ} {f : C(ℂ, ℝ)}
    (hf : gridEval f = coordGridCircleAverages n x) (z : ℂ) :
    coordCircleAverage x ((2 : ℝ) ^ (-(n : ℤ))) z = f z := by
  unfold coordCircleAverage Sec1.distributionCircleVersion
  refine Tendsto.limsup_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop n] with j hj
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h2nt : (2 : ℝ) ^ (n + t) ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ (-(n : ℤ)) * 2 ^ (n + t) = (((2 : ℤ) ^ t : ℤ) : ℝ) := by
    rw [Int.cast_pow, Int.cast_ofNat, pow_add, ← mul_assoc, zpow_neg, zpow_natCast,
      inv_mul_cancel₀ h2n, one_mul]
  have hrad : (((2 : ℤ) ^ t : ℤ) : ℝ) / 2 ^ (n + t) = (2 : ℝ) ^ (-(n : ℤ)) := by
    rw [← hmul, mul_div_assoc, div_self h2nt, mul_one]
  have hpos : (0 : ℤ) < 2 ^ t := by positivity
  rw [hmul, Int.ceil_intCast]
  simp only [hpos, ↓reduceIte]
  rw [distributionCircleAtDyadic_eq_gridVersion hrad]
  exact (FieldCircle.gridVersion_eq (X := fun w d => LQGMetric.circleAvg d ((2 : ℝ) ^ (-(n : ℤ))) w)
    (ω := LQGMetric.pairJInv ⊤ x) f.continuous (fun m a b => (congrFun hf (m, a, b)).symm) z).symm

/-- On the good set of field coordinates, the circle-average process at every dyadic radius
`(2 : ℝ) ^ (-(n : ℤ))` is a continuous function of the center. -/
theorem continuous_coordCircleAverage_of_mem {x : LQGMetric.CoordJ → ℝ} (hx : x ∈ coordCircleGood)
    (n : ℕ) : Continuous (fun z => coordCircleAverage x ((2 : ℝ) ^ (-(n : ℤ))) z) := by
  have hx' : x ∈ range (LQGMetric.pairJ ⊤) ∩ ⋂ n : ℕ, coordGridCircleAverages n ⁻¹' range gridEval := hx
  have hn : coordGridCircleAverages n x ∈ range gridEval := mem_iInter.1 hx'.2 n
  obtain ⟨f, hf⟩ := hn
  have hfun : (fun z => coordCircleAverage x ((2 : ℝ) ^ (-(n : ℤ))) z) = f :=
    funext (coordCircleAverage_eq_of_gridEval_eq hf)
  rw [hfun]
  exact f.continuous

/-- For any measurable version `H` of the field of a valid mated-CRT environment, the coordinates
`LQGMetric.pairJ ⊤ (H ω)` lie almost surely in the good set of field coordinates. -/
theorem MatedCRTEnv.IsValid.ae_pairJ_mem_coordCircleGood
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (_hH : Measurable H)
    (hHC : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, LQGMetric.pairJ ⊤ (H ω) ∈ coordCircleGood := by
  have hgrid : ∀ᵐ ω ∂S.P, ∀ n m : ℕ, ∀ a b : ℤ,
      LQGMetric.circleAvg (H ω) ((2 : ℝ) ^ (-(n : ℤ))) (FieldCircle.gridPt m a b) =
        S.hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) (FieldCircle.gridPt m a b) := by
    simp only [ae_all_iff]
    intro n m a b
    have hne : ‖FieldCircle.gridPt m a b‖ ≠ (2 : ℝ) ^ (-(n : ℤ)) := by
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact FieldCircle.norm_gridPt_ne m n a b
    exact Sec1.ae_distribution_circleAvg_eq hS hHC (by positivity) hne
  filter_upwards [hgrid, hS.isQuantumCone.ae_continuousOn_circle] with ω hg hc
  have hcont : ∀ n : ℕ, Continuous fun w => S.hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w := by
    intro n
    rw [← continuousOn_univ]
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      fun w _ => ⟨mem_Ioi.2 (by positivity), mem_univ _⟩
  refine Set.mem_inter (mem_range_self _) (mem_iInter.2 fun n => mem_preimage.2 (mem_range.2
    ⟨⟨fun w => S.hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w, hcont n⟩, funext fun i => ?_⟩))
  have hinv := LQGMetric.pairJInv_pairJ ⊤ (H ω)
  change S.hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) (FieldCircle.gridPt i.1 i.2.1 i.2.2) =
    LQGMetric.circleAvg (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω))) ((2 : ℝ) ^ (-(n : ℤ)))
      (FieldCircle.gridPt i.1 i.2.1 i.2.2)
  rw [hinv]
  exact (hg n i.1 i.2.1 i.2.2).symm

end MatedCRT
