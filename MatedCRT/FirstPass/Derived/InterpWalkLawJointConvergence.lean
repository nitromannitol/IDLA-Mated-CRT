import MatedCRT.FirstPass.Derived.InterpLawProkhorovBound
import MatedCRT.FirstPass.Derived.CellUniquePointDense
import MatedCRT.FirstPass.Derived.JointBoundedTestOfConvergenceInMeasure
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockSubsequence

/-!
# Joint convergence of the interpolated walk laws with the field

Let `S` be a valid environment and `η'` a continuous version of its space-filling curve. For a cell size `ε > 0`
and a point `z`, the **selected-cell law** `P^ε_z(ω)` (Berestycki–Gwynne (2020), Theorem 1.2) is the quenched law
of the rescaled walk on the mated-CRT map started from the vertex of a cell `H^ε_k = η'([ε(k - 1), εk])` containing
`z` (a fixed choice among the cells containing `z`). The interpolated walk law `P̃^ε(ω) = interpWalkLaw S η' ε ω`
averages the laws of the cells at distance less than `ε` from `z`.

* `selCellLaw`: the selected-cell law field `z ↦ P^ε_z(ω)`.
* `ae_forall_exists_dist_lt_selCellLaw_eq`: almost surely, for every `ε > 0`, the law of every cell with positive
  interpolation weight at `z` is the selected-cell law `P^ε_{z'}` of a point `z'` with `|z - z'| < 2ε`: since points
  lying in a single cell are dense in each cell, take `z'` lying only in that cell, close to its nearest point to `z`.
* `tendsto_of_forall_isCompact_pathLevyProkhorovEDist_lt`: if `d_LP(F_i(z), G(z)) → 0` uniformly on compact sets,
  for the Lévy–Prokhorov distance of the local uniform metric on paths, then `F_i → G` in
  `C(ℂ, Prob(ContinuousPath ℂ))` (compact-open topology over the topology of weak convergence of laws).
* `tendsto_interpWalkLaw_of_eventually_selCellLaw`: the deterministic transfer: uniform closeness of the
  selected-cell laws to a continuous law field `G` on growing balls gives `P̃^ε(ω) → G`.
* `tendsto_integral_interpWalkLaw_of_selCellLaw`: if the selected-cell laws converge to `Φ(R h)` uniformly on
  compact sets in probability, then for every bounded continuous `f`,
  `E[f(R h, P̃^ε)] → E[f(R h, Φ(R h))]` as `ε → 0⁺`: from any sequence `ε_n → 0⁺` a Borel–Cantelli subsequence
  gives almost sure convergence `P̃^ε → Φ(R h)` in `C(ℂ, Prob(ContinuousPath ℂ))`, and bounded convergence applies.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

/-! ### The selected-cell law field -/

section SelectedCell

variable {Ω : Type} [MeasurableSpace Ω]

/-- The index of a cell `H^ε_k = η([ε(k - 1), εk])` containing `z` (a fixed choice; `0` if there is none). -/
noncomputable def selCell (η : ℝ → ℂ) (ε : ℝ) (z : ℂ) : ℤ :=
  open Classical in if h : ∃ k : ℤ, z ∈ cell ε η k then h.choose else 0

/-- A point lying in the cell `H^ε_k` and in no other cell selects the cell `k`. -/
theorem selCell_eq_of_forall_ne_notMem {η : ℝ → ℂ} {ε : ℝ} {z : ℂ} {k : ℤ} (hz : z ∈ cell ε η k)
    (hk : ∀ j ≠ k, z ∉ cell ε η j) : selCell η ε z = k := by
  have h : ∃ k : ℤ, z ∈ cell ε η k := ⟨k, hz⟩
  rw [selCell, dite_eq_left h]
  by_contra hne
  exact hk _ hne h.choose_spec

/-- **The selected-cell law field** `z ↦ P^ε_z(ω)` (Berestycki–Gwynne (2020), Theorem 1.2): the quenched path
law `Q^ε(k)(ω)` of the rescaled walk on the mated-CRT map started from the vertex of the selected cell
`k = selCell (η' ω) ε z` containing `z`. -/
noncomputable def selCellLaw (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) (z : ℂ) :
    ProbabilityMeasure (ContinuousPath ℂ) :=
  walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε (selCell (⇑(η' ω)) ε z) ω

theorem selCellLaw_eq_of_forall_ne_notMem (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} {ω : Ω} {z : ℂ}
    {k : ℤ} (hz : z ∈ cell ε (⇑(η' ω)) k) (hk : ∀ j ≠ k, z ∉ cell ε (⇑(η' ω)) j) :
    selCellLaw S η' ε ω z = walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω := by
  rw [selCellLaw, selCell_eq_of_forall_ne_notMem hz hk]

/-- If points lying in a single cell are dense in each cell, the law of every cell `k` with positive
interpolation weight at `z` is the selected-cell law `P^ε_{z'}` of a point `z'` with `|z - z'| < 2ε`. -/
theorem exists_dist_lt_selCellLaw_eq (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) {ω : Ω}
    (hdense : ∀ (k : ℤ) (y : ℂ), y ∈ cell ε (⇑(η' ω)) k → ∀ r > 0,
      ∃ z', dist y z' < r ∧ z' ∈ cell ε (⇑(η' ω)) k ∧ ∀ j ≠ k, z' ∉ cell ε (⇑(η' ω)) j)
    {z : ℂ} {k : ℤ} (hk : interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0) :
    ∃ z', dist z z' < 2 * ε ∧
      selCellLaw S η' ε ω z' = walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω := by
  rw [interpWeight_ne_zero_iff] at hk
  have hne : (cell ε (⇑(η' ω)) k).Nonempty :=
    (Set.nonempty_Icc.2 (mul_le_mul_of_nonneg_left (by linarith) hε.le :
      ε * ((k : ℝ) - 1) ≤ ε * (k : ℝ))).image _
  obtain ⟨y, hy, hzy⟩ := (Metric.infDist_lt_iff hne).1 hk
  obtain ⟨z', hyz', hz'k, hz'j⟩ := hdense k y hy ε hε
  refine ⟨z', ?_, selCellLaw_eq_of_forall_ne_notMem S η' hz'k hz'j⟩
  calc dist z z' ≤ dist z y + dist y z' := dist_triangle _ _ _
    _ < ε + ε := add_lt_add hzy hyz'
    _ = 2 * ε := by ring

/-- **The selected-cell laws represent the interpolated components.** Almost surely, for every `ε > 0`, every
set `K` and every `z ∈ K`, the law of every cell with positive interpolation weight at `z` is the selected-cell
law `P^ε_{z'}` of a point `z'` with `|z - z'| < 2ε`. -/
theorem ae_forall_exists_dist_lt_selCellLaw_eq {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (η' : Ω → C(ℝ, ℂ)) (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, ∀ ε > 0, ∀ K : Set ℂ, ∀ z ∈ K, ∀ k : ℤ,
      interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0 →
        ∃ z', dist z z' < 2 * ε ∧
          selCellLaw S η' ε ω z' = walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω := by
  filter_upwards [ae_exists_dist_lt_mem_cell_notMem_cell_of_ne_of_ae_eq hS η' hη'] with ω hω
  intro ε hε _ z _ k hk
  exact exists_dist_lt_selCellLaw_eq S η' hε (hω ε hε) hk

/-- Almost surely the interpolation weights of the version `η'` are locally finite and positive, for all cell
sizes `ε > 0` simultaneously. -/
theorem ae_forall_interpWeight_good {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, ∀ ε > 0,
      (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0 := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hae] with ω hap hcoc hω
  intro ε hε
  rw [hω]
  exact interpWeight_good_of_proper_surjective hε hcoc hap.2.2.1

end SelectedCell

/-! ### Convergence of law fields from uniform Lévy–Prokhorov closeness on compact sets -/

section LevyProkhorovTopology

attribute [local instance] LatticeProb.dUnifMetricSpace

/-- `pathLevyProkhorovEDist` is the extended distance of the Lévy–Prokhorov metric space of laws on paths. -/
theorem pathLevyProkhorovEDist_eq_ofReal_dist (μ ν : ProbabilityMeasure (ContinuousPath ℂ)) :
    pathLevyProkhorovEDist μ ν =
      ENNReal.ofReal (dist (LevyProkhorov.ofMeasure μ) (LevyProkhorov.ofMeasure ν)) := by
  rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist,
    ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
  rfl

/-- **Uniform continuity of a law field on a compact set** for the Lévy–Prokhorov distance: weak convergence of
laws on paths is metrized by the Lévy–Prokhorov distance of the local uniform metric (a separable metric). -/
theorem exists_pos_forall_dist_lt_pathLevyProkhorovEDist_lt (G : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))
    {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ z ∈ K, ∀ z', dist z z' < ρ → pathLevyProkhorovEDist (G z') (G z) < ENNReal.ofReal δ := by
  have hG : Continuous fun z => LevyProkhorov.ofMeasure (G z) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp G.continuous
  have hK1 : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  obtain ⟨ρ, hρ, hU⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK1.uniformContinuousOn_of_continuous hG.continuousOn) δ hδ
  refine ⟨min ρ 1, lt_min hρ one_pos, fun z hz z' hzz' => ?_⟩
  have hzK : z ∈ Metric.cthickening 1 K := Metric.self_subset_cthickening K hz
  have hz'K : z' ∈ Metric.cthickening 1 K :=
    Metric.mem_cthickening_of_dist_le z' z 1 K hz (by rw [dist_comm]; exact hzz'.le.trans (min_le_right _ _))
  rw [pathLevyProkhorovEDist_eq_ofReal_dist, ENNReal.ofReal_lt_ofReal_iff hδ]
  exact hU z' hz'K z hzK (by rw [dist_comm]; exact hzz'.trans_le (min_le_left _ _))

/-- **Convergence of law fields from uniform Lévy–Prokhorov closeness on compact sets.** If
`d_LP(F_i(z), G(z)) → 0` uniformly on every compact set, for the Lévy–Prokhorov distance of the local uniform
metric on paths, then `F_i → G` in `C(ℂ, Prob(ContinuousPath ℂ))`. -/
theorem tendsto_of_forall_isCompact_pathLevyProkhorovEDist_lt {ι : Type*} {l : Filter ι}
    {F : ι → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} {G : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    (h : ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ i in l, ∀ z ∈ K, pathLevyProkhorovEDist (F i z) (G z) < ENNReal.ofReal δ) :
    Tendsto F l (𝓝 G) := by
  let ψ : C(LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ)), ProbabilityMeasure (ContinuousPath ℂ)) :=
    ⟨LevyProkhorov.toMeasure, LevyProkhorov.continuous_toMeasure_probabilityMeasure⟩
  let lift : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →
      C(ℂ, LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))) := fun H =>
    ⟨fun z => LevyProkhorov.ofMeasure (H z),
      LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp H.continuous⟩
  have hlift : ∀ H, ψ.comp (lift H) = H := fun H => ContinuousMap.ext fun _ => rfl
  have hconv : Tendsto (fun i => lift (F i)) l (𝓝 (lift G)) := by
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [h K hK δ hδ] with i hi z hz
    have hiz := hi z hz
    rw [pathLevyProkhorovEDist_eq_ofReal_dist, ENNReal.ofReal_lt_ofReal_iff hδ] at hiz
    rw [dist_comm]
    exact hiz
  have h2 : Tendsto (fun i => ψ.comp (lift (F i))) l (𝓝 (ψ.comp (lift G))) :=
    ((ContinuousMap.continuous_postcomp ψ).tendsto (lift G)).comp hconv
  simp only [hlift] at h2
  exact h2

end LevyProkhorovTopology

/-! ### From the selected-cell laws to the interpolated walk laws -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Deterministic transfer to the interpolated walk laws.** Fix an environment `ω` whose interpolation weights
are locally finite and positive and whose selected-cell laws represent the interpolated components (for all
`ε > 0`). Let `ε_n → 0⁺` and let `G` be a continuous law field such that eventually
`d_LP(P^{ε_n}_z(ω), G(z)) < 1 / (n + 1)` on the ball `|z| ≤ n + 1`. Then `P̃^{ε_n}(ω) → G` in
`C(ℂ, Prob(ContinuousPath ℂ))`. -/
theorem tendsto_interpWalkLaw_of_eventually_selCellLaw (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ω : Ω}
    (hgood : ∀ ε > 0,
      (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    (hsel : ∀ ε > 0, ∀ K : Set ℂ, ∀ z ∈ K, ∀ k : ℤ,
      interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0 →
        ∃ z', dist z z' < 2 * ε ∧
          selCellLaw S η' ε ω z' = walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (G : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝[>] 0))
    (hclose : ∀ᶠ n : ℕ in atTop, ∀ z ∈ closedBall (0 : ℂ) ((n : ℝ) + 1),
      pathLevyProkhorovEDist (selCellLaw S η' (e n) ω z) (G z) < ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => interpWalkLaw S η' (e n) ω) atTop (𝓝 G) := by
  refine tendsto_of_forall_isCompact_pathLevyProkhorovEDist_lt fun K hK δ hδ => ?_
  have hδ3 : 0 < δ / 3 := by linarith
  obtain ⟨ρ, hρ, hG⟩ := exists_pos_forall_dist_lt_pathLevyProkhorovEDist_lt G hK hδ3
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hρ' : 0 < min (ρ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hpos : ∀ᶠ n in atTop, 0 < e n := he.eventually self_mem_nhdsWithin
  have hsmall : ∀ᶠ n in atTop, e n < min (ρ / 2) (1 / 2) :=
    (tendsto_nhds_of_tendsto_nhdsWithin he).eventually (Iio_mem_nhds hρ')
  have hr' : ∀ᶠ n : ℕ in atTop, r ≤ (n : ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop r
  have hinv : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ / 3 :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hδ3)
  filter_upwards [hpos, hsmall, hr', hinv, hclose] with n hn hsm hrn hin hcl z hz
  have hsm1 := min_le_left (ρ / 2) (1 / 2)
  have hsm2 := min_le_right (ρ / 2) (1 / 2)
  obtain ⟨hloc, hposw⟩ := hgood (e n) hn
  have ha : ∀ z' ∈ Metric.thickening (2 * e n) K,
      pathLevyProkhorovEDist (selCellLaw S η' (e n) ω z') (G z') ≤ ENNReal.ofReal (δ / 3) := by
    intro z' hz'
    obtain ⟨z₀, hz₀, hd⟩ := Metric.mem_thickening_iff.1 hz'
    have h0 : dist z₀ 0 ≤ r := mem_closedBall.1 (hr hz₀)
    have hz'b : z' ∈ closedBall (0 : ℂ) ((n : ℝ) + 1) := by
      rw [mem_closedBall]
      linarith [dist_triangle z' z₀ 0]
    exact (hcl z' hz'b).le.trans (ENNReal.ofReal_le_ofReal hin.le)
  have hb : ∀ z₀ ∈ K, ∀ z', dist z₀ z' < 2 * e n →
      pathLevyProkhorovEDist (G z') (G z₀) ≤ ENNReal.ofReal (δ / 3) := fun z₀ hz₀ z' hzz' =>
    (hG z₀ hz₀ z' (by linarith)).le
  have h3 : ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) = ENNReal.ofReal (δ / 3 + δ / 3) :=
    (ENNReal.ofReal_add hδ3.le hδ3.le).symm
  refine (pathLevyProkhorovEDist_interpWalkLaw_le_add S η' hloc hposw (selCellLaw S η' (e n) ω) G
    (hsel (e n) hn K) ha hb hz).trans_lt ?_
  rw [h3, ENNReal.ofReal_lt_ofReal_iff hδ]
  linarith

/-- **Joint convergence of the interpolated walk laws with the field** (Berestycki–Gwynne (2020), Theorem 1.2,
with the joint convergence of Section 7.3). Let `S₀` be a valid environment, `H₀` a measurable version of its
field, `η₀` a measurable continuous version of its curve, `R` a measurable map from distributions to Polish data
`X`, and `Φ γ (R h)` a law field. Suppose the selected-cell laws converge to `Φ γ (R H₀)` uniformly on compact sets
in probability:
`P(∃ z ∈ K, d_LP(P^ε_z, Φ γ (R H₀) z) ≥ δ) → 0` as `ε → 0⁺` for every compact `K` and `δ > 0`.
Then the pairs `(R H₀, P̃^ε)` converge in law to `(R H₀, Φ γ (R H₀))`: for every bounded continuous `f`,
`E[f(R H₀, P̃^ε)] → E[f(R H₀, Φ γ (R H₀))]` as `ε → 0⁺`. -/
theorem tendsto_integral_interpWalkLaw_of_selCellLaw {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [PolishSpace X] [BorelSpace X] {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S₀ : MatedCRTEnv Ω}
    (hS₀ : S₀.IsValid 𝒮 γ) {R : LQGMetric.DistC → X} (hR : Measurable R)
    {Φ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} {H₀ : Ω → LQGMetric.DistC}
    (hH₀ : Measurable H₀) {η₀ : Ω → C(ℝ, ℂ)} (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω)
    (hBG : ∀ K : Set ℂ, IsCompact K → ∀ δ > 0, Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
      δ ≤ pathLevyProkhorovEDist (selCellLaw S₀ η₀ ε ω z) (Φ γ (R (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0))
    (f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ) :
    Tendsto (fun ε => ∫ ω, f (R (H₀ ω), interpWalkLaw S₀ η₀ ε ω) ∂S₀.P) (𝓝[>] 0)
      (𝓝 (∫ ω, f (R (H₀ ω), Φ γ (R (H₀ ω))) ∂S₀.P)) := by
  refine tendsto_integral_interpWalkLaw_of_exists_subseq_ae hS₀ hη₀m hη₀
    (hR.comp hH₀).aestronglyMeasurable (fun e he => ?_) f
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_eventually_notMem S₀.P
    (fun j k => {ω | ∃ z ∈ closedBall (0 : ℂ) ((j : ℝ) + 1), ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤
      pathLevyProkhorovEDist (selCellLaw S₀ η₀ (e k) ω z) (Φ γ (R (H₀ ω)) z)})
    (fun j => (hBG _ (isCompact_closedBall _ _) _ (ENNReal.ofReal_pos.2 (by positivity))).comp he)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae, ae_forall_interpWeight_good hS₀ hη₀,
    ae_forall_exists_dist_lt_selCellLaw_eq hS₀ η₀ hη₀] with ω hω hgood hsel
  refine tendsto_interpWalkLaw_of_eventually_selCellLaw S₀ η₀ hgood hsel (Φ γ (R (H₀ ω)))
    (he.comp hφ.tendsto_atTop) ?_
  filter_upwards [hω] with j hj z hz
  exact not_le.1 fun h => hj ⟨z, hz, h⟩

end MatedCRT.FirstPass.Derived
