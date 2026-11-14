import MatedCRT.FirstPass.Derived.ReferenceTripleLaw
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import MatedCRT.FirstPass.Derived.BLPathFunctionalDUnif
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentVertex
import MatedCRT.Proofs.IDLA.Measurable

/-!
# Transfer of the convergence of the interpolated walk laws from a reference environment

Let `P̃^ε = interpWalkLaw S η' ε` be the interpolated quenched law of the embedded random walk on the mated-CRT map
(Berestycki-Gwynne (1.7)), a random element of `C(ℂ, Prob(ContinuousPath ℂ))`. The field enters through Polish
data `R h` of the distribution `h` (for instance its pairings `(h φ_n)_n ∈ ℕ → ℝ` with a sequence of test functions,
`pairingSeq`), and the law field of the rescaled Liouville Brownian motion is `Φ (R h)` for a measurable `Φ`
(Berestycki-Gwynne Section 7.3). The convergence of `P̃^ε` to `Φ (R h)` in probability (Berestycki-Gwynne Theorem 1.2)
is stated in law: the pairs `(R h, P̃^ε)` converge in law to `(R h, Φ (R h))` as `ε → 0⁺`, that is
`∫ f (R h, P̃^ε) dP → ∫ f (R h, Φ (R h)) dP` for every bounded continuous `f` on `Data × C(ℂ, Prob)`.

* `curveMultInterpLaw`: the interpolated law as a function of a curve and an edge multiplicity array, so that
  `interpWalkLaw S η' ε ω = curveMultInterpLaw ε (S.mε_nonneg ε) (η' ω, S.mult ε ω)`.
* `locallyFiniteDenseCellCurves`: a measurable set of curves on which the interpolation weights are locally finite
  and positive; every proper onto curve belongs to it.
* `mε_eq_of_map_eq`: the time scaling `m_ε` (the median of the annealed exit time of the embedded walk) depends only
  on the law of (curve, edge multiplicities).
* `tendsto_integral_interpWalkLaw_of_reference`: the convergence in law of `(R h, P̃^ε)` to `(R h, Φ (R h))`
  transfers from one valid environment to every valid environment with the same normalized space-filling SLE law
  (the triple (field, curve, edge multiplicities) has the same law in both,
  `map_distribution_curveVersion_mult_eq_of_valid`).
* `eq_map_of_tendsto_integral_interpWalkLaw`: every subsequential weak limit of `(D, P̃^{ε_n})` is the law of
  `(D, Λ D)`.
* `exists_identification_of_tendsto_integral` and `identification_of_reference_convergence`: the identification
  hypothesis of `randomWalkToLBMStmt_of_identification`, with the data `D = R (field)` and `Λ = Φ`, from the
  identification of the law field by `Φ` (Berestycki-Gwynne Section 7.3: the Liouville Brownian law field is a.s.
  determined by the field) and the convergence on the reference environments.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open _root_.HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-! ### The interpolated law as a function of (curve, edge multiplicities) -/

/-- The quenched law of the interpolated embedded walk started from `k`, for the curve `x.1` and the edge
multiplicities `x.2`, with time scaling `m`. -/
noncomputable def curveMultPathLaw (ε : ℝ) {m : ℝ} (hm : 0 ≤ m) (x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (k : ℤ) :
    ProbabilityMeasure (ContinuousPath ℂ) :=
  ⟨Measure.map (interpPathCM (vertexPoint ε (⇑x.1)) hm) (srwLaw x.2 k),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_interpPathCM (vertexPoint ε (⇑x.1)) hm).aemeasurable).2 inferInstance⟩

/-- The interpolated law `P̃^ε` of the curve `x.1` and the edge multiplicities `x.2`, with time scaling `m`. -/
noncomputable def curveMultInterpLaw (ε : ℝ) {m : ℝ} (hm : 0 ≤ m) (x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :
    C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) :=
  interpLawCMT (ι := ℤ) (fun k => cell ε (⇑x.1) k) ε (curveMultPathLaw ε hm x)

theorem interpWalkLaw_eq_curveMultInterpLaw {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (η' : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) :
    interpWalkLaw S η' ε ω = curveMultInterpLaw ε (S.mε_nonneg ε) (η' ω, S.mult ε ω) :=
  rfl

theorem curveMultInterpLaw_congr (ε : ℝ) {m m' : ℝ} (hm : 0 ≤ m) (hm' : 0 ≤ m') (h : m = m')
    (x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) : curveMultInterpLaw ε hm x = curveMultInterpLaw ε hm' x := by
  subst h
  rfl

/-- Each component law is a measurable function of (curve, edge multiplicities). -/
theorem measurable_curveMultPathLaw (ε : ℝ) {m : ℝ} (hm : 0 ≤ m) (k : ℤ) :
    Measurable fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => curveMultPathLaw ε hm x k := by
  let κ : Kernel (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (ℕ → ℤ) :=
    ⟨fun x => srwLaw x.2 k, (measurable_srwLaw k).comp measurable_snd⟩
  have : IsMarkovKernel κ := ⟨fun x => isProbabilityMeasure_srwLaw x.2 k⟩
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hv : Measurable fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => vertexPoint ε (⇑x.1) :=
    measurable_vertexPoint_curve measurable_fst ε
  have hT : MeasurableSet {q : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℕ → ℤ) |
      interpPathCM (vertexPoint ε (⇑q.1.1)) hm q.2 ∈ s} :=
    (measurable_interpPathCM_uncurry hm).comp ((hv.comp measurable_fst).prodMk measurable_snd) hs
  have key := κ.measurable_kernel_prodMk_left hT
  convert key using 1
  funext x
  exact Measure.map_apply (measurable_interpPathCM (vertexPoint ε (⇑x.1)) hm) hs

/-- The curves whose `ε`-cells are locally finite (only finitely many cells within each distance of `0`) and
`ε/2`-dense (every point of the dense sequence of `ℂ` is within `ε/2` of a cell). -/
def locallyFiniteDenseCellCurves (ε : ℝ) : Set C(ℝ, ℂ) :=
  (⋂ n : ℕ, ⋃ a : ℤ, ⋃ b : ℤ, ⋂ k ∈ (Icc a b)ᶜ,
      {η : C(ℝ, ℂ) | (n : ℝ) ≤ infDist 0 (cell ε (⇑η) k)}) ∩
    ⋂ j : ℕ, ⋃ k : ℤ, {η : C(ℝ, ℂ) | infDist (TopologicalSpace.denseSeq ℂ j) (cell ε (⇑η) k) < ε / 2}

theorem measurableSet_locallyFiniteDenseCellCurves {ε : ℝ} (hε : 0 < ε) :
    MeasurableSet (locallyFiniteDenseCellCurves ε) := by
  have hd : ∀ (z : ℂ) (k : ℤ), Measurable fun η : C(ℝ, ℂ) => infDist z (cell ε (⇑η) k) :=
    fun z k => measurable_infDist_cell measurable_id' hε k z
  exact (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        measurableSet_le measurable_const (hd 0 k)).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iUnion fun k =>
      measurableSet_lt (hd _ k) measurable_const)

/-- On `locallyFiniteDenseCellCurves ε` the interpolation weights are locally finite and positive. -/
theorem interpWeight_good_of_mem {ε : ℝ} (hε : 0 < ε) {η : C(ℝ, ℂ)}
    (hη : η ∈ locallyFiniteDenseCellCurves ε) :
    (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑η) k) ε k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑η) k) ε k z ≠ 0 := by
  obtain ⟨h1, h2⟩ := hη
  refine ⟨fun z => interpWeight_locallyFinite (fun k => TraceInputs68.cell_nonempty hε (⇑η) k) ε
    (fun w R => ?_) z, fun z => ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt (‖w‖ + R)
    obtain ⟨a, ha⟩ := mem_iUnion.1 (mem_iInter.1 h1 n)
    obtain ⟨b, hb⟩ := mem_iUnion.1 ha
    refine (Set.finite_Icc a b).subset fun k hk => ?_
    obtain ⟨x, hx, hxw⟩ := hk
    by_contra hkab
    have hle : (n : ℝ) ≤ infDist 0 (cell ε (⇑η) k) := mem_iInter₂.1 hb k hkab
    have h0x : infDist 0 (cell ε (⇑η) k) ≤ dist 0 x := infDist_le_dist_of_mem hx
    have hdx : dist (0 : ℂ) x ≤ ‖w‖ + dist x w := by
      calc dist (0 : ℂ) x ≤ dist 0 w + dist w x := dist_triangle _ _ _
        _ = ‖w‖ + dist x w := by rw [dist_zero_left, dist_comm]
    linarith
  · obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_dist_lt z (half_pos hε)
    obtain ⟨k, hk⟩ := mem_iUnion.1 (mem_iInter.1 h2 j)
    refine ⟨k, (interpWeight_ne_zero_iff _ ε k z).2 ?_⟩
    have hk' : infDist (TopologicalSpace.denseSeq ℂ j) (cell ε (⇑η) k) < ε / 2 := hk
    have htri := infDist_le_infDist_add_dist (x := z) (y := TopologicalSpace.denseSeq ℂ j)
      (s := cell ε (⇑η) k)
    linarith

/-- A proper onto curve belongs to `locallyFiniteDenseCellCurves ε`. -/
theorem mem_locallyFiniteDenseCellCurves {ε : ℝ} (hε : 0 < ε) {η : C(ℝ, ℂ)}
    (hcoc : Tendsto (⇑η) (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective ⇑η) :
    η ∈ locallyFiniteDenseCellCurves ε := by
  obtain ⟨hne, hcov, hfin⟩ := cell_cover_finite_of_proper_surjective hε hcoc hsurj
  refine ⟨mem_iInter.2 fun n => ?_, mem_iInter.2 fun j => ?_⟩
  · have hf : {k : ℤ | infDist 0 (cell ε (⇑η) k) < n}.Finite :=
      (hfin 0 n).subset fun k hk => by
        obtain ⟨x, hx, hxd⟩ := (infDist_lt_iff (hne k)).1 hk
        exact ⟨x, hx, by rwa [dist_comm]⟩
    obtain ⟨b, hb⟩ := hf.bddAbove
    obtain ⟨a, ha⟩ := hf.bddBelow
    refine mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨b, mem_iInter₂.2 fun k hk => ?_⟩⟩
    show (n : ℝ) ≤ infDist 0 (cell ε (⇑η) k)
    by_contra hlt
    exact hk ⟨ha (not_le.1 hlt), hb (not_le.1 hlt)⟩
  · obtain ⟨k, hk⟩ := hcov (TopologicalSpace.denseSeq ℂ j)
    refine mem_iUnion.2 ⟨k, ?_⟩
    show infDist (TopologicalSpace.denseSeq ℂ j) (cell ε (⇑η) k) < ε / 2
    rw [infDist_zero_of_mem hk]
    exact half_pos hε

/-- Under the law of (curve, edge multiplicities) of a valid environment, the curve almost surely belongs to
`locallyFiniteDenseCellCurves ε`. -/
theorem ae_map_mem_locallyFiniteDenseCellCurves {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η')
    (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(S.P.map fun ω => (η' ω, S.mult ε ω)), x.1 ∈ locallyFiniteDenseCellCurves ε := by
  have hg : Measurable fun ω => (η' ω, S.mult ε ω) := hη'm.prodMk (hS.measurable_mult_array ε)
  refine (ae_map_iff (p := fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => x.1 ∈ locallyFiniteDenseCellCurves ε)
    hg.aemeasurable ((measurableSet_locallyFiniteDenseCellCurves hε).preimage measurable_fst)).2 ?_
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hη'] with ω hap hcoc hω
  rw [← hω] at hap hcoc
  exact mem_locallyFiniteDenseCellCurves hε hcoc hap.2.2.1

/-- The interpolated law is almost everywhere measurable for every law of (curve, edge multiplicities) under which
the curve almost surely belongs to `locallyFiniteDenseCellCurves ε`. -/
theorem aemeasurable_curveMultInterpLaw {μ : Measure (C(ℝ, ℂ) × (ℤ → ℤ → ℕ))} {ε : ℝ} (hε : 0 < ε) {m : ℝ}
    (hm : 0 ≤ m) (hgood : ∀ᵐ x ∂μ, x.1 ∈ locallyFiniteDenseCellCurves ε) :
    AEMeasurable (curveMultInterpLaw ε hm) μ :=
  aemeasurable_interpLawCMT (Ω := C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (P := μ)
    (H := fun (x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (k : ℤ) => cell ε (⇑x.1) k)
    (Q := fun (k : ℤ) (x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) => curveMultPathLaw ε hm x k)
    (fun k z => measurable_infDist_cell measurable_fst hε k z)
    (hgood.mono fun _ hx => interpWeight_good_of_mem hε hx)
    (fun k => measurable_curveMultPathLaw ε hm k)

/-! ### The time scaling `m_ε` depends only on the law of (curve, edge multiplicities) -/

/-- The exit time from a set of vertices depending measurably on a parameter is jointly measurable. -/
theorem measurable_vExitTime_param {α : Type*} [MeasurableSpace α] {A : α → Set ℤ}
    (hA : ∀ k : ℤ, MeasurableSet {a | k ∈ A a}) :
    Measurable fun q : α × (ℕ → ℤ) => vExitTime (A q.1) q.2 := by
  have hP : Measurable fun p : α × ℤ => p.2 ∈ A p.1 :=
    measurable_from_prod_countable_left fun k => measurableSet_setOfPred.1 (hA k)
  have hcoord : ∀ n : ℕ, MeasurableSet {q : α × (ℕ → ℤ) | q.2 n ∈ A q.1} := fun n =>
    measurableSet_setOfPred.2 (hP.comp (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd)))
  refine measurable_to_countable' fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    have h : (fun q : α × (ℕ → ℤ) => vExitTime (A q.1) q.2) ⁻¹' {⊤} =
        ⋂ n : ℕ, {q : α × (ℕ → ℤ) | q.2 n ∈ A q.1} := by
      ext q
      simp only [mem_preimage, mem_singleton_iff, mem_iInter]
      exact vExitTime_eq_top_iff
    rw [h]
    exact MeasurableSet.iInter hcoord
  | coe k =>
    have hlt : MeasurableSet {q : α × (ℕ → ℤ) | (k : ℕ∞) < vExitTime (A q.1) q.2} := by
      have h : {q : α × (ℕ → ℤ) | (k : ℕ∞) < vExitTime (A q.1) q.2} =
          ⋂ j : ℕ, ⋂ (_ : j ≤ k), {q : α × (ℕ → ℤ) | q.2 j ∈ A q.1} := by
        ext q
        simp only [mem_iInter]
        exact natCast_lt_vExitTime_iff
      rw [h]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hcoord j
    have h : (fun q : α × (ℕ → ℤ) => vExitTime (A q.1) q.2) ⁻¹' {(k : ℕ∞)} =
        {q : α × (ℕ → ℤ) | (k : ℕ∞) < vExitTime (A q.1) q.2}ᶜ ∩
          ⋂ j : ℕ, ⋂ (_ : j < k), {q : α × (ℕ → ℤ) | q.2 j ∈ A q.1} := by
      ext q
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_compl_iff, mem_iInter]
      exact vExitTime_eq_natCast_iff
    rw [h]
    exact hlt.compl.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hcoord j)

/-- The simple random walk law started from `V (x.1, 0)` is a measurable function of (curve, edge multiplicities). -/
theorem measurable_srwLaw_vertexOfCurve {V : C(ℝ, ℂ) × ℂ → ℤ} (hV : Measurable V) :
    Measurable fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => srwLaw x.2 (V (x.1, 0)) := by
  have hk : Measurable fun p : (ℤ → ℤ → ℕ) × ℤ => srwLaw p.1 p.2 := by
    refine measurable_from_prod_countable_left (f := fun p : (ℤ → ℤ → ℕ) × ℤ => srwLaw p.1 p.2) fun k => ?_
    exact measurable_srwLaw k
  have hf : Measurable fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => (x.2, V (x.1, 0)) :=
    measurable_snd.prodMk (hV.comp (measurable_fst.prodMk measurable_const))
  have h := hk.comp hf
  simp only [Function.comp_def] at h
  exact h

/-- The simple random walk kernel from (curve, edge multiplicities) to paths, started at `V (x.1, 0)`. -/
noncomputable def srwVertexKernel {V : C(ℝ, ℂ) × ℂ → ℤ} (hV : Measurable V) :
    Kernel (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) (ℕ → ℤ) :=
  ⟨fun x => srwLaw x.2 (V (x.1, 0)), measurable_srwLaw_vertexOfCurve hV⟩

theorem srwVertexKernel_apply {V : C(ℝ, ℂ) × ℂ → ℤ} (hV : Measurable V) (x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :
    srwVertexKernel hV x = srwLaw x.2 (V (x.1, 0)) :=
  rfl

instance isMarkovKernel_srwVertexKernel {V : C(ℝ, ℂ) × ℂ → ℤ} (hV : Measurable V) :
    IsMarkovKernel (srwVertexKernel hV) :=
  ⟨fun x => by rw [srwVertexKernel_apply]; infer_instance⟩

/-- The vertices whose cell centres lie in `B_{1/2}` depend measurably on the curve. -/
theorem measurableSet_vertexPoint_mem_ball (ε : ℝ) (k : ℤ) :
    MeasurableSet {x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) | vertexPoint ε (⇑x.1) k ∈ ball (0 : ℂ) (1 / 2)} :=
  (measurable_pi_apply k).comp (measurable_vertexPoint_curve measurable_fst ε) measurableSet_ball

/-- The exit time of the embedded walk from `B_{1/2}` is a measurable function of (curve, multiplicities, path). -/
theorem measurable_embeddedExitTime_curve (ε : ℝ) :
    Measurable fun q : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℕ → ℤ) =>
      vExitTime {k : ℤ | vertexPoint ε (⇑q.1.1) k ∈ ball (0 : ℂ) (1 / 2)} q.2 :=
  measurable_vExitTime_param
    (A := fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => {k : ℤ | vertexPoint ε (⇑x.1) k ∈ ball (0 : ℂ) (1 / 2)})
    (measurableSet_vertexPoint_mem_ball ε)

/-- The event that the embedded walk leaves `B_{1/2}` within time `s` is measurable in (curve, multiplicities,
path). -/
theorem measurableSet_embeddedExitTime_le (ε s : ℝ) :
    MeasurableSet {q : (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) × (ℕ → ℤ) |
      (embeddedExitTime ε (⇑q.1.1) (ball 0 (1 / 2)) q.2 : ℝ≥0∞) ≤ ENNReal.ofReal s} :=
  measurable_embeddedExitTime_curve ε (Set.to_countable {n : ℕ∞ | (n : ℝ≥0∞) ≤ ENNReal.ofReal s}).measurableSet

/-- The quenched probability that the embedded walk started from `V (x.1, 0)` leaves `B_{1/2}` within time `s` is a
measurable function of (curve, edge multiplicities). -/
theorem measurable_embeddedExitTime_le {ε : ℝ} {V : C(ℝ, ℂ) × ℂ → ℤ} (hV : Measurable V) (s : ℝ) :
    Measurable fun x : C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => srwLaw x.2 (V (x.1, 0))
      {y | (embeddedExitTime ε (⇑x.1) (ball 0 (1 / 2)) y : ℝ≥0∞) ≤ ENNReal.ofReal s} := by
  have h := (srwVertexKernel hV).measurable_kernel_prodMk_left (measurableSet_embeddedExitTime_le ε s)
  simp only [srwVertexKernel_apply] at h
  exact h

/-- The distribution function of the annealed exit time of the embedded walk (the function whose median is `m_ε`)
is an integral against the law of (curve, edge multiplicities). -/
theorem lintegral_embeddedExitTime_le_eq_map {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η')
    (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} {V : C(ℝ, ℂ) × ℂ → ℤ} (hV : Measurable V)
    (hVe : ∀ (η : C(ℝ, ℂ)) (x : ℂ), Tendsto η (cocompact ℝ) (cocompact ℂ) →
      Function.Surjective η → V (η, x) = vertexOf ε η x) (s : ℝ) :
    (∫⁻ ω, srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
      {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ ENNReal.ofReal s} ∂S.P) =
    ∫⁻ x, srwLaw x.2 (V (x.1, 0))
      {y | (embeddedExitTime ε (⇑x.1) (ball 0 (1 / 2)) y : ℝ≥0∞) ≤ ENNReal.ofReal s}
      ∂(S.P.map fun ω => (η' ω, S.mult ε ω)) := by
  rw [lintegral_map (measurable_embeddedExitTime_le hV s) (hη'm.prodMk (hS.measurable_mult_array ε))]
  refine lintegral_congr_ae ?_
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hη'] with ω hap hcoc hω
  show _ = srwLaw (S.mult ε ω) (V (η' ω, 0))
    {y | (embeddedExitTime ε (⇑(η' ω)) (ball 0 (1 / 2)) y : ℝ≥0∞) ≤ ENNReal.ofReal s}
  rw [hVe (η' ω) 0 (by rw [hω]; exact hcoc) (by rw [hω]; exact hap.2.2.1), hω]

/-- **`m_ε` depends only on the law of (curve, edge multiplicities).** -/
theorem mε_eq_of_map_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {𝒮 𝒮' : SpaceFillingSLEModel}
    {γ γ' : ℝ} {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ')
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ζ' : Ω' → C(ℝ, ℂ)} (hζ'm : Measurable ζ') (hζ' : ∀ᵐ ω ∂S'.P, ⇑(ζ' ω) = S'.η ω) {ε : ℝ} (hε : 0 < ε)
    (hmap : S.P.map (fun ω => (η' ω, S.mult ε ω)) = S'.P.map (fun ω => (ζ' ω, S'.mult ε ω))) :
    S.mε ε = S'.mε ε := by
  obtain ⟨V, hV, hVe⟩ := exists_measurable_vertexOf_curve hε
  unfold MatedCRTEnv.mε
  congr 1
  funext s
  rw [lintegral_embeddedExitTime_le_eq_map hS hη'm hη' hV hVe s,
    lintegral_embeddedExitTime_le_eq_map hS' hζ'm hζ' hV hVe s, hmap]

/-! ### Transfer of the convergence -/

/-- Integrals of a function of a random element agree when the laws agree. -/
theorem integral_comp_eq_of_map_eq {α Ω Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'} {g : Ω → α} {g' : Ω' → α}
    (hg : AEMeasurable g μ) (hg' : AEMeasurable g' μ') (hmap : μ.map g = μ'.map g') {u : α → ℝ}
    (hu : AEStronglyMeasurable u (μ.map g)) : ∫ ω, u (g ω) ∂μ = ∫ ω, u (g' ω) ∂μ' := by
  rw [← integral_map hg hu, hmap, integral_map hg' (hmap ▸ hu)]

/-- The pairings `(h φ_n)_n` of a distribution with a sequence of test functions: Polish data of the field. -/
noncomputable def pairingSeq (φ : ℕ → LQGMetric.TestC) (h : LQGMetric.DistC) : ℕ → ℝ :=
  fun n => h (φ n)

theorem measurable_pairingSeq (φ : ℕ → LQGMetric.TestC) : Measurable (pairingSeq φ) := by
  have hev : Measurable fun (h : LQGMetric.DistC) (ψ : LQGMetric.TestC) => h ψ := fun s hs => ⟨s, hs, rfl⟩
  exact measurable_pi_iff.mpr fun n => (measurable_pi_apply (φ n)).comp hev

/-- **Transfer of the convergence of the interpolated walk laws (step T3).** Let `S₀, S` be valid environments of
models with the same normalized space-filling SLE law `ν` and the same `0 < γ < 2`, with measurable versions
`H₀, η₀` and `H, η'` of their fields and curves, and let every `0 < γ < 2` have a one-sided mating-rigid set that
is full for every `γ`-correlated two-sided Brownian law. Let `R` be a measurable map from distributions to Polish
data and `Φ` a measurable map from the data to law fields. If the pairs `(R H₀, P̃^ε)` of `S₀` converge in law to
`(R H₀, Φ (R H₀))` as `ε → 0⁺`, then the pairs `(R H, P̃^ε)` of `S` converge in law to `(R H, Φ (R H))`. -/
theorem tendsto_integral_interpWalkLaw_of_reference {Data : Type*} [TopologicalSpace Data]
    [MeasurableSpace Data] [PolishSpace Data] [BorelSpace Data] {𝒮 𝒮₀ : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (hν₀ : HasNormalizedSLELaw 𝒮₀ ν)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type} [MeasurableSpace Ω₀] {S₀ : MatedCRTEnv Ω₀} (hS₀ : S₀.IsValid 𝒮₀ γ)
    {H₀ : Ω₀ → LQGMetric.DistC} (hH₀ : Measurable H₀)
    (hrep₀ : ∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ)
    {η₀ : Ω₀ → C(ℝ, ℂ)} (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {η' : Ω → C(ℝ, ℂ)} (hη'm : Measurable η') (hη' : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {R : LQGMetric.DistC → Data} (hR : Measurable R)
    {Φ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΦ : Measurable Φ)
    (h₀ : ∀ f : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
      Tendsto (fun ε => ∫ ω, f (R (H₀ ω), interpWalkLaw S₀ η₀ ε ω) ∂S₀.P) (𝓝[>] 0)
        (𝓝 (∫ ω, f (R (H₀ ω), Φ (R (H₀ ω))) ∂S₀.P))) :
    ∀ f : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
      Tendsto (fun ε => ∫ ω, f (R (H ω), interpWalkLaw S η' ε ω) ∂S.P) (𝓝[>] 0)
        (𝓝 (∫ ω, f (R (H ω), Φ (R (H ω))) ∂S.P)) := by
  intro f
  have htrip : ∀ ε, S.P.map (fun ω => (H ω, η' ω, S.mult ε ω)) =
      S₀.P.map (fun ω => (H₀ ω, η₀ ω, S₀.mult ε ω)) := fun ε =>
    map_distribution_curveVersion_mult_eq_of_valid hν hν₀ hγ0 hγ2 hS hS₀ hU hH hH₀ hrep hrep₀ hη'm hη'
      hη₀m hη₀ ε
  have hg : ∀ ε, Measurable fun ω => (H ω, η' ω, S.mult ε ω) := fun ε =>
    hH.prodMk (hη'm.prodMk (hS.measurable_mult_array ε))
  have hg₀ : ∀ ε, Measurable fun ω => (H₀ ω, η₀ ω, S₀.mult ε ω) := fun ε =>
    hH₀.prodMk (hη₀m.prodMk (hS₀.measurable_mult_array ε))
  have hlim : ∫ ω, f (R (H ω), Φ (R (H ω))) ∂S.P = ∫ ω, f (R (H₀ ω), Φ (R (H₀ ω))) ∂S₀.P := by
    have hu : Measurable fun x : LQGMetric.DistC × C(ℝ, ℂ) × (ℤ → ℤ → ℕ) => f (R x.1, Φ (R x.1)) :=
      f.continuous.measurable.comp ((hR.comp measurable_fst).prodMk (hΦ.comp (hR.comp measurable_fst)))
    exact integral_comp_eq_of_map_eq (hg 0).aemeasurable (hg₀ 0).aemeasurable (htrip 0)
      hu.aestronglyMeasurable
  rw [hlim]
  refine Tendsto.congr' ?_ (h₀ f)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hpair : S.P.map (fun ω => (η' ω, S.mult ε ω)) = S₀.P.map (fun ω => (η₀ ω, S₀.mult ε ω)) := by
    have h1 : (S.P.map fun ω => (H ω, η' ω, S.mult ε ω)).map Prod.snd =
        (S₀.P.map fun ω => (H₀ ω, η₀ ω, S₀.mult ε ω)).map Prod.snd := by
      rw [htrip ε]
    rwa [Measure.map_map measurable_snd (hg ε), Measure.map_map measurable_snd (hg₀ ε)] at h1
  have hm : S₀.mε ε = S.mε ε := mε_eq_of_map_eq hS₀ hS hη₀m hη₀ hη'm hη' hε0 hpair.symm
  have hΨ : AEMeasurable (curveMultInterpLaw ε (S₀.mε_nonneg ε))
      ((S.P.map fun ω => (H ω, η' ω, S.mult ε ω)).map Prod.snd) := by
    rw [Measure.map_map measurable_snd (hg ε)]
    exact aemeasurable_curveMultInterpLaw hε0 _ (ae_map_mem_locallyFiniteDenseCellCurves hS hη'm hη' hε0)
  have hu : AEStronglyMeasurable
      (fun x : LQGMetric.DistC × C(ℝ, ℂ) × (ℤ → ℤ → ℕ) =>
        f (R x.1, curveMultInterpLaw ε (S₀.mε_nonneg ε) x.2))
      (S.P.map fun ω => (H ω, η' ω, S.mult ε ω)) :=
    (f.continuous.measurable.comp_aemeasurable ((hR.comp measurable_fst).aemeasurable.prodMk
      (hΨ.comp_measurable measurable_snd))).aestronglyMeasurable
  have key := integral_comp_eq_of_map_eq (hg ε).aemeasurable (hg₀ ε).aemeasurable (htrip ε) hu
  refine key.symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show f (R (H ω), curveMultInterpLaw ε (S₀.mε_nonneg ε) (η' ω, S.mult ε ω)) =
    f (R (H ω), curveMultInterpLaw ε (S.mε_nonneg ε) (η' ω, S.mult ε ω))
  rw [curveMultInterpLaw_congr ε (S₀.mε_nonneg ε) (S.mε_nonneg ε) hm]

/-! ### Identification of subsequential limits -/

/-- **Subsequential limits (step P2).** Let `D` be measurable Polish data and `Λ` a measurable map from the data to
law fields. If the pairs `(D, P̃^ε)` converge in law to `(D, Λ D)` as `ε → 0⁺`, then every subsequential weak limit
of `(D, P̃^{ε_n})` along `ε_n → 0` is the law of `(D, Λ D)`. -/
theorem eq_map_of_tendsto_integral_interpWalkLaw {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [PolishSpace X] [BorelSpace X] {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    [IsFiniteMeasure S.P] {η' : Ω → C(ℝ, ℂ)} {D : Ω → X} (hD : Measurable D)
    {Λ : X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : Measurable Λ)
    (hP1 : ∀ f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
      Tendsto (fun ε => ∫ ω, f (D ω, interpWalkLaw S η' ε ω) ∂S.P) (𝓝[>] 0)
        (𝓝 (∫ ω, f (D ω, Λ (D ω)) ∂S.P)))
    (e : ℕ → ℝ) (φ : ℕ → ℕ) (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0)) (hφ : StrictMono φ)
    (ν : Measure (X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))) (hν : IsProbabilityMeasure ν)
    (hconv : ∀ f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop (𝓝 (∫ p, f p ∂ν))) :
    ν = S.P.map fun ω => (D ω, Λ (D ω)) := by
  have hseq : Tendsto (fun k => e (φ k)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he.comp hφ.tendsto_atTop, Eventually.of_forall fun k => he0 (φ k)⟩
  have hg : Measurable fun ω => (D ω, Λ (D ω)) := hD.prodMk (hΛ.comp hD)
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hg.aemeasurable f.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique (hconv f) ((hP1 f).comp hseq)

/-- **The identification hypothesis on one valid environment.** Let `S` be a valid environment, `D` measurable
Polish data of `S` and `Λ` a measurable map from the data to law fields such that `Λ (D ω)` almost surely integrates
every bounded Lipschitz path functional as the law of the rescaled Liouville Brownian motion from each `z`. If the
pairs `(D, P̃^ε)` converge in law to `(D, Λ D)` as `ε → 0⁺`, then the conclusion of the identification hypothesis of
`randomWalkToLBMStmt_of_identification` holds for `S`, with these data. -/
theorem exists_identification_of_tendsto_integral {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [PolishSpace X] [BorelSpace X] {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)}
    {D : Ω → X} (hD : Measurable D) {Λ : X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : Measurable Λ)
    (hLBM : ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
        ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) z : Measure (ContinuousPath ℂ)))
    (hP1 : ∀ f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
      Tendsto (fun ε => ∫ ω, f (D ω, interpWalkLaw S η' ε ω) ∂S.P) (𝓝[>] 0)
        (𝓝 (∫ ω, f (D ω, Λ (D ω)) ∂S.P))) :
    ∃ (Data : Type) (_ : TopologicalSpace Data) (_ : MeasurableSpace Data) (_ : PolishSpace Data)
      (_ : BorelSpace Data) (D : Ω → Data) (Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))),
      Measurable D ∧ Measurable Λ ∧
      (∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
        ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
          ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) z : Measure (ContinuousPath ℂ))) ∧
      ∀ (e : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) → StrictMono φ →
        ∀ ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))), IsProbabilityMeasure ν →
        (∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
          Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
            (𝓝 (∫ p, f p ∂ν))) →
        ν = S.P.map fun ω => (D ω, Λ (D ω)) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, D, Λ, hD, hΛ, hLBM,
    fun e φ he0 he hφ ν hν hconv =>
      eq_map_of_tendsto_integral_interpWalkLaw hD hΛ hP1 e φ he0 he hφ ν hν hconv⟩

/-- **The identification hypothesis of Theorem 2.11 from the reference environments.** Let `𝒮` be a model with
normalized space-filling SLE law `ν` and valid reference environments, and let every `0 < γ < 2` have a one-sided
mating-rigid set that is full for every `γ`-correlated two-sided Brownian law. Let `R` be a measurable map from
distributions to Polish data `X` (for instance `pairingSeq φ`, `X = ℕ → ℝ`) and `Φ γ` measurable maps from the data to
law fields such that

* (`hLBM`, Berestycki-Gwynne Section 7.3) in every valid environment, `Φ γ (R H)` for a measurable version `H` of the
  field almost surely integrates every bounded Lipschitz path functional as the law of the rescaled Liouville
  Brownian motion from each `z`;
* (`hP1`, Berestycki-Gwynne Theorem 1.2) in every valid environment on `ℝ`, with measurable versions `H₀, η₀` of its
  field and curve, the pairs `(R H₀, P̃^ε)` converge in law to `(R H₀, Φ γ (R H₀))` as `ε → 0⁺`.

Then the identification hypothesis `hid` of `randomWalkToLBMStmt_of_identification` holds. -/
theorem identification_of_reference_convergence {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [PolishSpace X] [BorelSpace X] {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (R : LQGMetric.DistC → X) (hR : Measurable R)
    (Φ : ℝ → X → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) (hΦ : ∀ γ, Measurable (Φ γ))
    (hLBM : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
        ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
          ∫ q, blPathFunctionalBCF hF q ∂(Φ γ (R (H ω)) z : Measure (ContinuousPath ℂ)))
    (hP1 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ f : X × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) →ᵇ ℝ,
        Tendsto (fun ε => ∫ ω, f (R (H₀ ω), interpWalkLaw S₀ η₀ ε ω) ∂S₀.P) (𝓝[>] 0)
          (𝓝 (∫ ω, f (R (H₀ ω), Φ γ (R (H₀ ω))) ∂S₀.P))) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∃ (Data : Type) (_ : TopologicalSpace Data) (_ : MeasurableSpace Data) (_ : PolishSpace Data)
        (_ : BorelSpace Data) (D : Ω → Data) (Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))),
        Measurable D ∧ Measurable Λ ∧
        (∀ (z : ℂ) (F : (ℝ≥0 → ℂ) → ℝ) (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
          ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
            ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) z : Measure (ContinuousPath ℂ))) ∧
        ∀ (e : ℕ → ℝ) (φ : ℕ → ℕ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) → StrictMono φ →
          ∀ ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))), IsProbabilityMeasure ν →
          (∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
            Tendsto (fun k => ∫ ω, f (D ω, interpWalkLaw S η' (e (φ k)) ω) ∂S.P) atTop
              (𝓝 (∫ p, f p ∂ν))) →
          ν = S.P.map fun ω => (D ω, Λ (D ω)) := by
  intro γ hγ0 hγ2 Ω _ S hS η' hη'm hη'
  obtain ⟨S₀, hS₀⟩ := href γ hγ0 hγ2
  obtain ⟨H₀, hH₀m, hrep₀⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS₀
  have hH₀ : Measurable H₀ := hH₀m.mono (S₀.fieldSigma_le hS₀) le_rfl
  obtain ⟨η₀, hη₀m, hη₀⟩ := hS₀.exists_curveVersion
  obtain ⟨H, hHm, hrep⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS
  have hH : Measurable H := hHm.mono (S.fieldSigma_le hS) le_rfl
  exact exists_identification_of_tendsto_integral hS (D := fun ω => R (H ω)) (hR.comp hH) (hΦ γ)
    (hLBM γ hγ0 hγ2 Ω S hS H hH hrep)
    (tendsto_integral_interpWalkLaw_of_reference hν hν hU hγ0 hγ2 hS₀ hH₀ hrep₀ hη₀m hη₀ hS hH hrep hη'm hη'
      hR (hΦ γ) (hP1 γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep₀ η₀ hη₀m hη₀))

end MatedCRT.FirstPass.Derived
