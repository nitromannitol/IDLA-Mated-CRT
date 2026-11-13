import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import MatedCRT.Proofs.Infra.LocallyFinite
import LatticeProb.Prob.PathSpaceDUnif
import LatticeProb.Prob.InterpolatedLaw
import LatticeProb.Prob.AtomicPairingReplacement

/-!
# The reversibility pairing of the interpolated walk laws at the degree measure (BG20 Lemma 7.6, step C2)

Let `S` be a valid environment, `η'` a version of its curve, and for a cell size `ε > 0` let
`Q^ε(x)` be the quenched laws of the interpolated embedded walks (`walkPathLaw`) and `P̃^ε = interpWalkLaw S η' ε`
the interpolated law field. For bounded Lipschitz `f, g` and a continuous compactly supported cutoff `0 ≤ ψ` with
`ψ = 1` on `tsupport f ∪ tsupport g`, the cutoff degree measure is the atomic measure
`ν^ε = Σ_x ε deg^ε(x) ψ(η(x)) δ_{η(x)}` (`degreeCutoffMeasure`, an `atomicMeasure`), and the reversibility pairing is
`Φ_{f,g,t}(ν, P) = ∫ f(z) E_{P_z}[g(X_t)] ψ(z) dν(z) - ∫ g(z) E_{P_z}[f(X_t)] ψ(z) dν(z)`
(`reversibilityPairing`).

The walks of `walkPathLaw` make `m_ε` steps per unit time (`interpPathCM`), so the times at which the interpolated walk
sits at a vertex are the lattice times `t` with `m_ε t ∈ ℕ`, e.g. `latticeTime m_ε s = ⌊m_ε s⌋ / m_ε ≤ s`.

* `sum_degreeCutoffWeight_walkPathLaw_symm`: at a lattice time, the atomic pairing with the walk laws `Q^ε(x)` in place
  of `P̃^ε_{η(x)}` vanishes exactly, by `n`-step detailed balance `deg(x) p_n(x,y) = deg(y) p_n(y,x)`.
* `abs_reversibilityPairing_degreeCutoffMeasure_le`: replacing `Q^ε(x)` by `P̃^ε_{η(x)}` costs at most
  `C · a · ν^ε(supp ψ)` when the Lévy–Prokhorov distances (local uniform metric `dUnif`) are `< a` on `supp ψ`.
* `pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le`: `LP(Q^ε(x), P̃^ε_{η(x)}) ≤ ω^ε_R(δ)` (the vertex-indexed
  modulus `walkLawModulus`) once `ε + diam^ε_R ≤ δ`, `diam^ε_R = maxCellDiam`.
* `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`: along `ε_n → 0⁺` and lattice times `t_n ≤ T`,
  `Φ_{f,g,t_n}(ν^{ε_n}, P̃^{ε_n}) → 0` in probability, given the equicontinuity of the walk laws in law, cell diameters
  tending to `0` in probability and the mass of `ν^ε` bounded in probability;
  `tendstoInMeasure_reversibilityPairing_latticeTime` is the case `t_n = latticeTime m_{ε_n} s`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-! ### Lattice times, path evaluations and the local uniform metric -/

/-- Linear interpolation at an integer time returns the value there. -/
theorem linInterp_natCast (a : ℕ → ℂ) (N : ℕ) : linInterp a (N : ℝ) = a N := by
  simp [linInterp]

/-- The lattice time `⌊m s⌋ / m` of a walk making `m` steps per unit time: the last time `≤ s` at which the
interpolated walk sits at a vertex (`0` if `m = 0`). -/
noncomputable def latticeTime (m : ℝ) (s : ℝ≥0) : ℝ≥0 :=
  (⌊m * s⌋₊ : ℝ≥0) / m.toNNReal

theorem mul_latticeTime {m : ℝ} (hm : 0 ≤ m) (s : ℝ≥0) : m * (latticeTime m s : ℝ) = ⌊m * s⌋₊ := by
  rcases hm.eq_or_lt with h | h
  · subst h
    simp [latticeTime]
  · have hne : m ≠ 0 := h.ne'
    rw [latticeTime, NNReal.coe_div, NNReal.coe_natCast, Real.coe_toNNReal _ hm]
    field_simp

theorem latticeTime_le {m : ℝ} (hm : 0 ≤ m) (s : ℝ≥0) : latticeTime m s ≤ s := by
  rcases hm.eq_or_lt with h | h
  · subst h
    simp [latticeTime]
  · rw [← NNReal.coe_le_coe, latticeTime, NNReal.coe_div, NNReal.coe_natCast, Real.coe_toNNReal _ hm,
      div_le_iff₀ h]
    calc (⌊m * s⌋₊ : ℝ) ≤ m * s := Nat.floor_le (mul_nonneg hm s.2)
      _ = s * m := mul_comm _ _

/-- `e^{T+1}`: for `t ≤ T`, `min 1 |X_t - Y_t| ≤ e^{T+1} dUnif(X, Y)` (`min_one_dist_eval_le_dUnif`). -/
noncomputable def pathEvalLipschitzConst (T : ℝ≥0) : ℝ≥0 :=
  ⟨Real.exp ((T : ℝ) + 1), (Real.exp_pos _).le⟩

/-- Evaluation at a time `t ≤ T` is controlled by the local uniform metric:
`min 1 |X_t - Y_t| ≤ e^{T+1} dUnif(X, Y)`. -/
theorem min_one_dist_eval_le_dUnif {T t : ℝ≥0} (ht : t ≤ T) (X Y : C(ℝ≥0, ℂ)) :
    min 1 (dist (X t) (Y t)) ≤ Real.exp ((T : ℝ) + 1) * dUnif X Y := by
  by_contra hcon
  rw [not_le] at hcon
  have hE : 0 < Real.exp ((T : ℝ) + 1) := Real.exp_pos _
  have hd0 : 0 ≤ dist (X t) (Y t) := dist_nonneg
  have hm0 : 0 ≤ min 1 (dist (X t) (Y t)) := le_min zero_le_one hd0
  have hle1 : Real.exp (-((T : ℝ) + 1)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith [NNReal.coe_nonneg T])
  have hpos' : 0 < Real.exp (-((T : ℝ) + 1)) := Real.exp_pos _
  have hu : dUnif X Y < min 1 (dist (X t) (Y t)) * Real.exp (-((T : ℝ) + 1)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ hE, mul_comm]
    exact hcon
  have hmin : min 1 (dist (X t) (Y t)) * Real.exp (-((T : ℝ) + 1))
      ≤ min (Real.exp (-((T : ℝ) + 1))) (dist (X t) (Y t)) := by
    refine le_min ?_ ?_
    · calc min 1 (dist (X t) (Y t)) * Real.exp (-((T : ℝ) + 1))
          ≤ 1 * Real.exp (-((T : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hpos'.le
        _ = Real.exp (-((T : ℝ) + 1)) := one_mul _
    · calc min 1 (dist (X t) (Y t)) * Real.exp (-((T : ℝ) + 1))
          ≤ min 1 (dist (X t) (Y t)) * 1 := mul_le_mul_of_nonneg_left hle1 hm0
        _ ≤ dist (X t) (Y t) := by rw [mul_one]; exact min_le_right _ _
  have h1 := pathSupDist_lt_of_dUnif_lt T (hu.trans_le hmin)
  have h2 := dist_le_pathSupDist X Y ht
  linarith

/-- The local uniform metric `dUnif` on continuous paths (Lattice-Probability `dUnifMetricSpace`); its topology is
the compact-open topology. -/
noncomputable abbrev dUnifPseudoMetric : PseudoMetricSpace (ContinuousPath ℂ) :=
  (dUnifMetricSpace (E := ℂ)).toPseudoMetricSpace

/-- The Borel sets of the compact-open topology contain the open sets of `dUnif` (the topologies agree). -/
theorem opensMeasurableSpace_dUnif :
    @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ dUnifPseudoMetric)) _ :=
  (inferInstance : OpensMeasurableSpace (ContinuousPath ℂ))

/-- The Lévy–Prokhorov distance of two laws on continuous paths, for the local uniform metric `dUnif`. -/
noncomputable def pathLevyProkhorovEDist (μ ν : ProbabilityMeasure (ContinuousPath ℂ)) : ℝ≥0∞ :=
  letI : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  levyProkhorovEDist (μ : Measure (ContinuousPath ℂ)) (ν : Measure (ContinuousPath ℂ))

/-! ### The cutoff degree measure and the reversibility pairing -/

/-- The vertices `k` with `v k ∈ K`, when there are finitely many of them (otherwise `∅`). -/
noncomputable def vertexWindow (v : ℤ → ℂ) (K : Set ℂ) : Finset ℤ :=
  open Classical in if h : (v ⁻¹' K).Finite then h.toFinset else ∅

theorem mem_vertexWindow {v : ℤ → ℂ} {K : Set ℂ} (h : (v ⁻¹' K).Finite) {k : ℤ} :
    k ∈ vertexWindow v K ↔ v k ∈ K := by
  simp [vertexWindow, h]

/-- The weight `ε deg(x) ψ(v x)` of the vertex `x` in the cutoff degree measure. -/
noncomputable def degreeCutoffWeight (m : ℤ → ℤ → ℕ) (ε : ℝ) (v : ℤ → ℂ) (ψ : ℂ → ℝ) (x : ℤ) : ℝ :=
  ε * (mdeg m x : ℝ) * ψ (v x)

theorem atomicMeasure_univ_lt_top {ι : Type*} (s : Finset ι) (c : ι → ℝ) (p : ι → ℂ) :
    atomicMeasure s c p univ < ∞ := by
  rw [atomicMeasure, Measure.finsetSum_apply]
  refine lt_top_iff_ne_top.2 (ENNReal.sum_ne_top.2 fun x _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- **The cutoff degree measure** `ν = Σ_x ε deg(x) ψ(v x) δ_{v x}`, the sum over the vertices with `v x ∈ tsupport ψ`:
the degree measure of the map with edge multiplicity `m` at the vertex positions `v`, weighted by the cutoff `ψ`. -/
noncomputable def degreeCutoffMeasure (m : ℤ → ℤ → ℕ) (ε : ℝ) (v : ℤ → ℂ) (ψ : ℂ → ℝ) : FiniteMeasure ℂ :=
  ⟨atomicMeasure (vertexWindow v (tsupport ψ)) (degreeCutoffWeight m ε v ψ) v,
    ⟨atomicMeasure_univ_lt_top _ _ _⟩⟩

theorem measureReal_le_mass (ν : FiniteMeasure ℂ) (s : Set ℂ) : (ν : Measure ℂ).real s ≤ (ν.mass : ℝ) := by
  rw [measureReal_def]
  have h : (ν : Measure ℂ) s ≤ (ν.mass : ℝ≥0∞) := by
    rw [FiniteMeasure.ennreal_mass]
    exact measure_mono (subset_univ s)
  exact ENNReal.toReal_le_of_le_ofReal ν.mass.coe_nonneg (by rwa [ENNReal.ofReal_coe_nnreal])

/-- **The reversibility pairing** `Φ_{f,g,t}(ν, P) = ∫ f(z) E_{P_z}[g(X_t)] ψ(z) dν(z) - ∫ g(z) E_{P_z}[f(X_t)] ψ(z) dν(z)`
of a finite measure `ν` and a law field `P`, the function of `continuous_reversibilityPairing` (Lattice-Probability). -/
noncomputable def reversibilityPairing (f g ψ : ℂ → ℝ) (ν : FiniteMeasure ℂ)
    (P : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (t : ℝ≥0) : ℝ :=
  (∫ z, f z * (∫ X, g (X t) ∂(P z : Measure (ContinuousPath ℂ))) * ψ z ∂(ν : Measure ℂ))
    - ∫ z, g z * (∫ X, f (X t) ∂(P z : Measure (ContinuousPath ℂ))) * ψ z ∂(ν : Measure ℂ)

theorem mem_tsupport_of_eqOn_one {ψ u : ℂ → ℝ} (h : EqOn ψ 1 (tsupport u)) {z : ℂ} (hz : u z ≠ 0) :
    z ∈ tsupport ψ := by
  refine subset_tsupport ψ ?_
  show ψ z ≠ 0
  rw [h (subset_tsupport u hz)]
  exact one_ne_zero

private theorem vertexPoint_mem_cell_aux {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- For a continuous proper curve, finitely many vertices have their position in a compact set. -/
theorem vertexPoint_preimage_finite {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {K : Set ℂ} (hK : IsCompact K) :
    (vertexPoint ε η ⁻¹' K).Finite :=
  (cellVertices_finite_of_isCompact hη hp hε hK).subset fun x hx =>
    ⟨vertexPoint ε η x, vertexPoint_mem_cell_aux hε.le η x, hx⟩

/-! ### The walk laws, their modulus and the cell diameters -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- At a lattice time `t` (`m t = N`), the walk law `Q(k)` evaluates `u(X_t)` as `E^k[u(v(X_N))]`. -/
theorem integral_walkPathLaw_comp_eval (S : MatedCRTEnv Ω) (v : Ω → ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (ε : ℝ)
    (k : ℤ) (ω : Ω) {u : ℂ → ℝ} (hu : Continuous u) {t : ℝ≥0} {N : ℕ} (htN : m * (t : ℝ) = N) :
    ∫ X, u (X t) ∂(walkPathLaw S v hm ε k ω : Measure (ContinuousPath ℂ)) =
      ∫ w, u (v ω (w N)) ∂(srwLaw (S.mult ε ω) k) := by
  show ∫ X, u (X t) ∂(Measure.map (interpPathCM (v ω) hm) (srwLaw (S.mult ε ω) k)) = _
  rw [integral_map (f := fun X : ContinuousPath ℂ => u (X t)) (measurable_interpPathCM (v ω) hm).aemeasurable
    (hu.comp (continuous_eval_const t)).aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [interpPathCM_apply, interpPathFn, htN, linInterp_natCast]

/-- **The vertex-indexed modulus** `ω^ε_R(δ) = sup {LP(Q^ε(j), Q^ε(k)) : η(j), η(k) ∈ B_{R+1}, |η(j) - η(k)| ≤ δ}` of the
quenched walk laws, for the Lévy–Prokhorov distance of the local uniform metric. -/
noncomputable def walkLawModulus (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε R δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (j : ℤ) (k : ℤ) (_ : vertexPoint ε (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) ∧
      vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) (R + 1) ∧
      dist (vertexPoint ε (⇑(η' ω)) j) (vertexPoint ε (⇑(η' ω)) k) ≤ δ),
    pathLevyProkhorovEDist (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω)
      (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)

/-- `diam^ε_R`: the largest diameter of the cells `η([ε(k-1), εk])` meeting `B_{R+1}`. -/
noncomputable def maxCellDiam (ε : ℝ) (η : ℝ → ℂ) (R : ℝ) : ℝ≥0∞ :=
  ⨆ (k : ℤ) (_ : (cell ε η k ∩ ball (0 : ℂ) (R + 1)).Nonempty), ENNReal.ofReal (Metric.diam (cell ε η k))

/-- **The walk law against the interpolated law** (MATH-ANSWERS step 3, with `a = 0`): on the event where the
interpolation is defined, if `η(x) ∈ B̄_R`, the cells meeting `B_{R+1}` have diameter at most `d`, `ε + d ≤ δ`,
`ε + d < 1` and `ω^ε_R(δ) ≤ a`, then `LP(Q^ε(x), P̃^ε_{η(x)}) ≤ a`. -/
theorem pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    {R δ d a : ℝ} (hd0 : 0 ≤ d) (hd : ε + d ≤ δ) (hd1 : ε + d < 1) (ha : 0 ≤ a)
    (hD : maxCellDiam ε (⇑(η' ω)) R ≤ ENNReal.ofReal d)
    (hmod : walkLawModulus S η' ε R δ ω ≤ ENNReal.ofReal a)
    {x : ℤ} (hx : ‖vertexPoint ε (⇑(η' ω)) x‖ ≤ R) :
    pathLevyProkhorovEDist (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
      (interpWalkLaw S η' ε ω (vertexPoint ε (⇑(η' ω)) x)) ≤ ENNReal.ofReal a := by
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  have hOMS : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ ‹_›)) _ :=
    opensMeasurableSpace_dUnif
  have hk : ∀ k : ℤ, Metric.infDist (vertexPoint ε (⇑(η' ω)) x) (cell ε (⇑(η' ω)) k) < ε →
      levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω : Measure (ContinuousPath ℂ))
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω : Measure (ContinuousPath ℂ))
        ≤ a := by
    intro k hk
    have hvk := vertexPoint_mem_cell_aux hε (⇑(η' ω)) k
    obtain ⟨y, hy, hyx⟩ := (Metric.infDist_lt_iff ⟨_, hvk⟩).1 hk
    have hbdd : Bornology.IsBounded (cell ε (⇑(η' ω)) k) :=
      (isCompact_Icc.image (η' ω).continuous).isBounded
    have hyk := Metric.dist_le_diam_of_mem hbdd hy hvk
    have hx0 := dist_zero_right (vertexPoint ε (⇑(η' ω)) x)
    have hyball : y ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      have h1 := dist_triangle y (vertexPoint ε (⇑(η' ω)) x) 0
      have h2 := dist_comm y (vertexPoint ε (⇑(η' ω)) x)
      linarith
    have hdiam : Metric.diam (cell ε (⇑(η' ω)) k) ≤ d := by
      have h := (le_iSup₂ (f := fun k (_ : (cell ε (⇑(η' ω)) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
        ENNReal.ofReal (Metric.diam (cell ε (⇑(η' ω)) k))) k ⟨y, hy, hyball⟩).trans hD
      exact (ENNReal.ofReal_le_ofReal_iff hd0).1 h
    have hxk : dist (vertexPoint ε (⇑(η' ω)) x) (vertexPoint ε (⇑(η' ω)) k) < ε + d := by
      have := dist_triangle (vertexPoint ε (⇑(η' ω)) x) y (vertexPoint ε (⇑(η' ω)) k)
      linarith
    have hxball : vertexPoint ε (⇑(η' ω)) x ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      linarith
    have hkball : vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      have h1 := dist_triangle (vertexPoint ε (⇑(η' ω)) k) (vertexPoint ε (⇑(η' ω)) x) 0
      have h2 := dist_comm (vertexPoint ε (⇑(η' ω)) k) (vertexPoint ε (⇑(η' ω)) x)
      linarith
    have hm : pathLevyProkhorovEDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
          ≤ walkLawModulus S η' ε R δ ω :=
      le_iSup₂_of_le x k (le_iSup_of_le ⟨hxball, hkball, by linarith⟩ le_rfl)
    exact ENNReal.toReal_le_of_le_ofReal ha (hm.trans hmod)
  have hL := levyProkhorovDist_interpLaw_le hloc hpos
    (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
    (vertexPoint ε (⇑(η' ω)) x) ha hk
  rw [interpWalkLaw_eq_of_good S η' hloc hpos]
  show levyProkhorovEDist _ _ ≤ _
  rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hL

/-! ### The exact discrete identity and the replacement estimate -/

/-- **The exact discrete identity** (MATH-ANSWERS step C2): for the cutoff degree weights `c x = ε deg(x) ψ(η(x))`, the
walk laws `Q^ε(x)` at a lattice time `t` (`m_ε t = N`) and `ψ = 1` on `tsupport f ∪ tsupport g`,
`Σ_x c x f(η x) ψ(η x) E_{Q(x)}[g(X_t)] = Σ_x c x g(η x) ψ(η x) E_{Q(x)}[f(X_t)]`, by `n`-step detailed balance
`deg(x) p_N(x,y) = deg(y) p_N(y,x)` (`sum_mdeg_mul_integral_comp_eval_symm`). -/
theorem sum_degreeCutoffWeight_walkPathLaw_symm (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} {ω : Ω}
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) {f g ψ : ℂ → ℝ}
    (hW : (vertexPoint ε (⇑(η' ω)) ⁻¹' tsupport ψ).Finite) (hf : Continuous f) (hg : Continuous g)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g)) {t : ℝ≥0} {N : ℕ} (htN : S.mε ε * (t : ℝ) = N) :
    ∑ x ∈ vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ),
        degreeCutoffWeight (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ x * f (vertexPoint ε (⇑(η' ω)) x)
          * ψ (vertexPoint ε (⇑(η' ω)) x)
          * ∫ X, g (X t) ∂(walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω
            : Measure (ContinuousPath ℂ)) =
      ∑ x ∈ vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ),
        degreeCutoffWeight (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ x * g (vertexPoint ε (⇑(η' ω)) x)
          * ψ (vertexPoint ε (⇑(η' ω)) x)
          * ∫ X, f (X t) ∂(walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω
            : Measure (ContinuousPath ℂ)) := by
  set v : ℤ → ℂ := vertexPoint ε (⇑(η' ω)) with hv
  have hE : ∀ u : ℂ → ℝ, Continuous u → ∀ x : ℤ,
      ∫ X, u (X t) ∂(walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω
        : Measure (ContinuousPath ℂ)) = ∫ y, u (v (y N)) ∂(srwLaw (S.mult ε ω) x) :=
    fun u hu x => integral_walkPathLaw_comp_eval S _ (S.mε_nonneg ε) ε x ω hu htN
  have hterm : ∀ u w : ℂ → ℝ, Continuous w → EqOn ψ 1 (tsupport u) → ∀ x : ℤ,
      degreeCutoffWeight (S.mult ε ω) ε v ψ x * u (v x) * ψ (v x)
          * ∫ X, w (X t) ∂(walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω
            : Measure (ContinuousPath ℂ))
        = ε * ((mdeg (S.mult ε ω) x : ℝ) * u (v x) * ∫ y, w (v (y N)) ∂(srwLaw (S.mult ε ω) x)) := by
    intro u w hw hψu x
    rw [hE w hw x]
    by_cases hu0 : u (v x) = 0
    · rw [hu0]
      ring
    · have h1 : ψ (v x) = 1 := hψu (subset_tsupport u hu0)
      rw [degreeCutoffWeight, h1]
      ring
  have hvan : ∀ u : ℂ → ℝ, EqOn ψ 1 (tsupport u) → ∀ x ∉ vertexWindow v (tsupport ψ), u (v x) = 0 := by
    intro u hψu x hx
    by_contra h
    exact hx ((mem_vertexWindow hW).2 (mem_tsupport_of_eqOn_one hψu h))
  have hψf : EqOn ψ 1 (tsupport f) := hψ1.mono subset_union_left
  have hψg : EqOn ψ 1 (tsupport g) := hψ1.mono subset_union_right
  rw [Finset.sum_congr rfl fun x _ => hterm f g hg hψf x, Finset.sum_congr rfl fun x _ => hterm g f hf hψg x,
    ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  exact sum_mdeg_mul_integral_comp_eval_symm (S.mult_symm ε ω) hlf N (f := fun k => f (v k))
    (g := fun k => g (v k)) _ (hvan f hψf) (hvan g hψg)

/-- **Replacement of the walk laws by the interpolated law field** (MATH-ANSWERS step C2): at a lattice time `t ≤ T`,
if `LP(Q^ε(x), P̃^ε_{η(x)}) < a` for every vertex `x` with `ψ(η(x)) ≠ 0`, then
`|Φ_{f,g,t}(ν^ε, P̃^ε)| ≤ (C_f C_ψ B_g(a) + C_g C_ψ B_f(a)) ν^ε(supp ψ)` with `B = levyProkhorovEvalBound`, since the
atomic pairing with the walk laws vanishes exactly (`sum_degreeCutoffWeight_walkPathLaw_symm`). -/
theorem abs_reversibilityPairing_degreeCutoffMeasure_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Ω} (hlf : IsLocallyFiniteMult (S.mult ε ω)) {f g ψ : ℂ → ℝ}
    (hW : (vertexPoint ε (⇑(η' ω)) ⁻¹' tsupport ψ).Finite)
    {Cf Cg Cψ : ℝ} (hfb : ∀ z, |f z| ≤ Cf) (hgb : ∀ z, |g z| ≤ Cg) (hψb : ∀ z, |ψ z| ≤ Cψ)
    {Kf Kg : ℝ≥0} (hfl : LipschitzWith Kf f) (hgl : LipschitzWith Kg g)
    (hψ0 : ∀ z, 0 ≤ ψ z) (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {t T : ℝ≥0} (htT : t ≤ T) {N : ℕ} (htN : S.mε ε * (t : ℝ) = N) {a : ℝ} (ha : 0 < a)
    (hLP : ∀ x ∈ vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ),
      ψ (vertexPoint ε (⇑(η' ω)) x) ≠ 0 →
        pathLevyProkhorovEDist (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
          (interpWalkLaw S η' ε ω (vertexPoint ε (⇑(η' ω)) x)) < ENNReal.ofReal a) :
    |reversibilityPairing f g ψ (degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ)
        (interpWalkLaw S η' ε ω) t|
      ≤ (Cf * Cψ * levyProkhorovEvalBound Kg Cg (pathEvalLipschitzConst T) a
          + Cg * Cψ * levyProkhorovEvalBound Kf Cf (pathEvalLipschitzConst T) a)
        * (degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ : Measure ℂ).real
          (Function.support ψ) := by
  have hid := sum_degreeCutoffWeight_walkPathLaw_symm S η' hlf hW hfl.continuous hgl.continuous hψ1 htN
  have hc0 : ∀ x, 0 ≤ degreeCutoffWeight (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ x :=
    fun x => mul_nonneg (mul_nonneg hε (Nat.cast_nonneg _)) (hψ0 _)
  have hν : ((degreeCutoffMeasure (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ : FiniteMeasure ℂ) : Measure ℂ)
      = atomicMeasure (vertexWindow (vertexPoint ε (⇑(η' ω))) (tsupport ψ))
          (degreeCutoffWeight (S.mult ε ω) ε (vertexPoint ε (⇑(η' ω))) ψ) (vertexPoint ε (⇑(η' ω))) := rfl
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  have hOMS : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ ‹_›)) _ :=
    opensMeasurableSpace_dUnif
  have he : ∀ X Y : ContinuousPath ℂ,
      min 1 (dist (X t) (Y t)) ≤ ((pathEvalLipschitzConst T : ℝ≥0) : ℝ) * dist X Y :=
    fun X Y => min_one_dist_eval_le_dUnif htT X Y
  have h1 := abs_sum_mul_integral_sub_integral_atomicMeasure_le _ hc0 (vertexPoint ε (⇑(η' ω)))
    (fun x => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
    (⇑(interpWalkLaw S η' ε ω)) hfb hψb hgb hgl (e := fun X : ContinuousPath ℂ => X t) he ha hLP
  have h2 := abs_sum_mul_integral_sub_integral_atomicMeasure_le _ hc0 (vertexPoint ε (⇑(η' ω)))
    (fun x => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
    (⇑(interpWalkLaw S η' ε ω)) hgb hψb hfb hfl (e := fun X : ContinuousPath ℂ => X t) he ha hLP
  rw [reversibilityPairing, hν]
  rw [abs_le] at h1 h2 ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  constructor
  · linarith
  · linarith

/-! ### Convergence in probability -/

/-- **The reversibility pairing at the cutoff degree measure tends to `0` in probability** (BG20 Lemma 7.6 without
Lemma 7.7, step C2; MATH-ANSWERS N6). Let `S` be a valid environment, `η'` a version of its curve, `ε_n → 0⁺`, and
`t_n ≤ T` lattice times of the walks (`m_{ε_n} t_n ∈ ℕ`). Assume that the maps are almost surely locally finite, that
the walk laws are equicontinuous in law (`hEqLaw`: for all `R` and `a > 0` there is `δ > 0` with
`P[ω^{ε_n}_R(δ) > a] ≤ a` eventually, the step-3 input of MATH-ANSWERS), that the cell diameters near `B_{R+1}` tend to
`0` in probability (`hdiam`), and that the mass of the cutoff degree measure `ν^{ε_n}` is bounded in probability
(`hmass`). Then `Φ_{f,g,t_n}(ν^{ε_n}, P̃^{ε_n}) → 0` in probability. -/
theorem tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hlf : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {t : ℕ → ℝ≥0} {T : ℝ≥0} (htT : ∀ n, t n ≤ T) (htN : ∀ n, ∃ N : ℕ, S.mε (ε n) * (t n : ℝ) = N)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    (hmass : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ᶠ n in atTop,
      S.P {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)}
        ≤ ENNReal.ofReal a) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (t n)) atTop (fun _ => 0) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  obtain ⟨Cψ, hCψ⟩ : ∃ C, ∀ z, |ψ z| ≤ C := by
    obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψc
    exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC z⟩
  obtain ⟨R₀, hR₀⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hCg0 : 0 ≤ Cg := (abs_nonneg _).trans (hCg 0)
  have hCψ0 : 0 ≤ Cψ := (abs_nonneg _).trans (hCψ 0)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = Cf * Cψ * (max (Kg : ℝ) (2 * Cg) * (pathEvalLipschitzConst T : ℝ) + 2 * Cg)
      + Cg * Cψ * (max (Kf : ℝ) (2 * Cf) * (pathEvalLipschitzConst T : ℝ) + 2 * Cf) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by
    have hΛ0 : 0 ≤ (pathEvalLipschitzConst T : ℝ) := NNReal.coe_nonneg _
    have h1 : 0 ≤ max (Kg : ℝ) (2 * Cg) := (NNReal.coe_nonneg _).trans (le_max_left _ _)
    have h2 : 0 ≤ max (Kf : ℝ) (2 * Cf) := (NNReal.coe_nonneg _).trans (le_max_left _ _)
    have h3 := mul_nonneg h1 hΛ0
    have h4 := mul_nonneg h2 hΛ0
    rw [hκ]
    exact add_nonneg (mul_nonneg (mul_nonneg hCf0 hCψ0) (by linarith))
      (mul_nonneg (mul_nonneg hCg0 hCψ0) (by linarith))
  have hgood : ∀ᵐ ω ∂S.P, ∀ n, Tendsto (⇑(η' ω)) (cocompact ℝ) (cocompact ℂ) ∧
      IsLocallyFiniteMult (S.mult (ε n) ω) ∧
      (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U,
        interpWeight (fun k => cell (ε n) (⇑(η' ω)) k) (ε n) k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell (ε n) (⇑(η' ω)) k) (ε n) k z ≠ 0 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hS.ae_tendsto_cocompact, hae, hlf, hS.ae_interpWeight_good hae (hε0 n)]
      with ω hp hω hl hi
    exact ⟨by rw [hω]; exact hp, hl _ (hε0 n), hi.1, hi.2⟩
  rw [tendstoInMeasure_iff_dist]
  intro θ hθ
  rw [ENNReal.tendsto_nhds_zero]
  intro r' hr'
  obtain ⟨r, hr0, hrr'⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ r' := by
    rcases eq_or_ne r' ⊤ with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · exact ⟨r'.toReal, ENNReal.toReal_pos hr'.ne' h, (ENNReal.ofReal_toReal h).le⟩
  obtain ⟨C, hC⟩ := hmass (r / 4) (by linarith)
  obtain ⟨C', hC'0, hCC'⟩ : ∃ C' : ℝ, 0 < C' ∧ C ≤ C' :=
    ⟨max C 0 + 1, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos,
      (le_max_left C 0).trans (by linarith)⟩
  have hden : 0 < 4 * (κ + 1) * C' := mul_pos (by linarith) hC'0
  obtain ⟨a', ha'0, ha'r, ha'θ⟩ : ∃ a' : ℝ, 0 < a' ∧ a' ≤ r / 4 ∧ a' * (4 * (κ + 1) * C') ≤ θ :=
    ⟨min (r / 4) (θ / (4 * (κ + 1) * C')), lt_min (by linarith) (div_pos hθ hden), min_le_left _ _,
      (le_div_iff₀ hden).1 (min_le_right _ _)⟩
  have hlast : κ * (2 * a') * C' < θ := by
    have h1 : κ * (2 * a') * C' ≤ (κ + 1) * (2 * a') * C' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hC'0.le
    have h2 : (κ + 1) * (2 * a') * C' = (a' * (4 * (κ + 1) * C')) / 2 := by ring
    have h3 : 0 ≤ a' * C' := mul_nonneg ha'0.le hC'0.le
    linarith
  have hBκ : Cf * Cψ * levyProkhorovEvalBound Kg Cg (pathEvalLipschitzConst T) (2 * a')
      + Cg * Cψ * levyProkhorovEvalBound Kf Cf (pathEvalLipschitzConst T) (2 * a') = κ * (2 * a') := by
    rw [hκ]
    simp only [levyProkhorovEvalBound]
    ring
  obtain ⟨δ, hδ0, hδ⟩ := hEqLaw R₀ a' ha'0
  obtain ⟨δ', hδ'0, hδ'δ, hδ'1⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ 1 :=
    ⟨min δ 1, lt_min hδ0 one_pos, min_le_left _ _, min_le_right _ _⟩
  have hD' : ∀ᶠ n in atTop, S.P {ω | ENNReal.ofReal (δ' / 2) < maxCellDiam (ε n) (⇑(η' ω)) R₀}
      ≤ ENNReal.ofReal (r / 4) :=
    (ENNReal.tendsto_nhds_zero.1 (hdiam R₀ (δ' / 2) (by linarith))) _ (ENNReal.ofReal_pos.2 (by linarith))
  have hεs : ∀ᶠ n in atTop, ε n < δ' / 2 := hε.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hC, hδ, hD', hεs] with n hn1 hn2 hn3 hn4
  refine (measure_mono_ae (t := {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n)
      (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)} ∪
      {ω | ENNReal.ofReal a' < walkLawModulus S η' (ε n) R₀ δ ω} ∪
      {ω | ENNReal.ofReal (δ' / 2) < maxCellDiam (ε n) (⇑(η' ω)) R₀}) ?_).trans ?_
  · filter_upwards [hgood] with ω hω hmem
    by_contra hnot
    have h1 : ¬ C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ) :=
      fun h => hnot (Or.inl (Or.inl h))
    have h2 : ¬ ENNReal.ofReal a' < walkLawModulus S η' (ε n) R₀ δ ω := fun h => hnot (Or.inl (Or.inr h))
    have h3 : ¬ ENNReal.ofReal (δ' / 2) < maxCellDiam (ε n) (⇑(η' ω)) R₀ := fun h => hnot (Or.inr h)
    obtain ⟨hp, hlfn, hloc, hpos⟩ := hω n
    obtain ⟨N, hN⟩ := htN n
    have hW := vertexPoint_preimage_finite (hε0 n) (η' ω).continuous hp hψc.isCompact
    have hLP : ∀ x ∈ vertexWindow (vertexPoint (ε n) (⇑(η' ω))) (tsupport ψ),
        ψ (vertexPoint (ε n) (⇑(η' ω)) x) ≠ 0 →
          pathLevyProkhorovEDist
            (walkPathLaw S (fun ω => vertexPoint (ε n) (⇑(η' ω))) (S.mε_nonneg (ε n)) (ε n) x ω)
            (interpWalkLaw S η' (ε n) ω (vertexPoint (ε n) (⇑(η' ω)) x)) < ENNReal.ofReal (2 * a') := by
      intro x _ hx
      have hxR : ‖vertexPoint (ε n) (⇑(η' ω)) x‖ ≤ R₀ := by
        have h := hR₀ (subset_tsupport ψ hx)
        rwa [mem_closedBall_zero_iff] at h
      refine (pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le S η' (hε0 n).le hloc hpos
        (d := δ' / 2) (by linarith) (by linarith) (by linarith) ha'0.le (not_lt.1 h3) (not_lt.1 h2)
        hxR).trans_lt ?_
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have hbound := abs_reversibilityPairing_degreeCutoffMeasure_le S η' (hε0 n).le hlfn hW hCf hCg hCψ
      hfl hgl hψ0 hψ1 (htT n) hN (by linarith : (0 : ℝ) < 2 * a') hLP
    rw [hBκ] at hbound
    have hmC : (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ : Measure ℂ).real
        (Function.support ψ) ≤ C' :=
      (measureReal_le_mass _ _).trans ((not_lt.1 h1).trans hCC')
    have hfinal := hbound.trans_lt
      ((mul_le_mul_of_nonneg_left hmC (mul_nonneg hκ0 (by linarith))).trans_lt hlast)
    exact absurd hmem (not_le.2 (by rw [Real.dist_eq, sub_zero]; exact hfinal))
  · refine ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)).trans ?_
    refine (add_le_add (add_le_add hn1 (hn2.trans (ENNReal.ofReal_le_ofReal ha'r))) hn3).trans ?_
    have hr4 : (0 : ℝ) ≤ r / 4 := by linarith
    have hr8 : (0 : ℝ) ≤ r / 4 + r / 4 := by linarith
    rw [← ENNReal.ofReal_add hr4 hr4, ← ENNReal.ofReal_add hr8 hr4]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hrr'

/-- **The reversibility pairing at the lattice times `⌊m_ε s⌋ / m_ε`** tends to `0` in probability (the case
`t_n = latticeTime m_{ε_n} s ≤ s` of `tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure`). -/
theorem tendstoInMeasure_reversibilityPairing_latticeTime {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    (hlf : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω))
    {f g ψ : ℂ → ℝ} (hfb : ∃ C, ∀ z, |f z| ≤ C) {Kf : ℝ≥0} (hfl : LipschitzWith Kf f)
    (hgb : ∃ C, ∀ z, |g z| ≤ C) {Kg : ℝ≥0} (hgl : LipschitzWith Kg g)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψ1 : EqOn ψ 1 (tsupport f ∪ tsupport g))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) (s : ℝ≥0)
    (hEqLaw : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (ε n) R δ ω} ≤ ENNReal.ofReal a)
    (hdiam : ∀ R a : ℝ, 0 < a →
      Tendsto (fun n => S.P {ω | ENNReal.ofReal a < maxCellDiam (ε n) (⇑(η' ω)) R}) atTop (𝓝 0))
    (hmass : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ᶠ n in atTop,
      S.P {ω | C < ((degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ).mass : ℝ)}
        ≤ ENNReal.ofReal a) :
    TendstoInMeasure S.P (fun n ω => reversibilityPairing f g ψ
        (degreeCutoffMeasure (S.mult (ε n) ω) (ε n) (vertexPoint (ε n) (⇑(η' ω))) ψ)
        (interpWalkLaw S η' (ε n) ω) (latticeTime (S.mε (ε n)) s)) atTop (fun _ => 0) :=
  tendstoInMeasure_reversibilityPairing_degreeCutoffMeasure hS hae hlf hfb hfl hgb hgl hψ hψc hψ0 hψ1 hε0 hε
    (fun n => latticeTime_le (S.mε_nonneg (ε n)) s) (fun n => ⟨_, mul_latticeTime (S.mε_nonneg (ε n)) s⟩)
    hEqLaw hdiam hmass

end MatedCRT.FirstPass.Derived
