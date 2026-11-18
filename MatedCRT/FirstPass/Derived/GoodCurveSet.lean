import MatedCRT.FirstPass.Derived.CellDiamUniform
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly

/-!
# The proper onto curves form a Borel set of `C(ℝ, ℂ)`

`properOntoCurves` is the set of continuous curves `η : ℝ → ℂ` which are proper
(`η t → ∞` as `|t| → ∞`) and onto. It is described by countably many conditions on the values of
`η` at rational times (`properOntoCurves_eq`), so it is a Borel set of `C(ℝ, ℂ)`
(`measurableSet_properOntoCurves`). Consequently, for a measurable version `η'` of the curve,
`properCurveSet η' = η' ⁻¹' properOntoCurves` is measurable, and almost surely `η' ω` is proper
and onto for every valid environment (`ae_mem_properOntoCurves`). This is the property of the curve
that makes the interpolation weights of the cells locally finite and positive, and it is carried by
the law of the curve.
-/

open MeasureTheory Filter Topology Set Metric LatticeProb

namespace MatedCRT

/-- The continuous curves `ℝ → ℂ` that are proper and onto. -/
def properOntoCurves : Set C(ℝ, ℂ) :=
  {η | Tendsto (⇑η) (cocompact ℝ) (cocompact ℂ) ∧ Function.Surjective η}

/-- The countable description of `properOntoCurves`: values at rational times leave every ball
eventually, and come arbitrarily close to every point of a dense sequence of `ℂ`. -/
def properOntoCurvesRat : Set C(ℝ, ℂ) :=
  {η | (∀ R : ℕ, ∃ T : ℕ, ∀ t : ℚ, (T : ℝ) ≤ |(t : ℝ)| → (R : ℝ) ≤ ‖η t‖) ∧
    ∀ m n : ℕ, ∃ t : ℚ, dist (η t) (TopologicalSpace.denseSeq ℂ m) < 1 / ((n : ℝ) + 1)}

/-- A closed set of reals containing the rational points of an open set contains the open set. -/
theorem subset_of_rat_mem {U C : Set ℝ} (hU : IsOpen U) (hC : IsClosed C)
    (h : ∀ q : ℚ, (q : ℝ) ∈ U → (q : ℝ) ∈ C) : U ⊆ C := by
  intro t ht
  have hcl := Rat.denseRange_cast.open_subset_closure_inter hU ht
  refine closure_minimal ?_ hC hcl
  rintro x ⟨hxU, q, rfl⟩
  exact h q hxU

theorem properOntoCurves_subset_rat : properOntoCurves ⊆ properOntoCurvesRat := by
  rintro η ⟨hcoc, hsurj⟩
  refine ⟨fun R => ?_, fun m n => ?_⟩
  · have hev : ∀ᶠ t in cocompact ℝ, (R : ℝ) ≤ ‖η t‖ :=
      (tendsto_norm_cocompact_atTop.comp hcoc).eventually_ge_atTop (R : ℝ)
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hev
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨⌈r⌉₊ + 1, fun t ht => hKs fun htK => ?_⟩
    have h1 := hr htK
    rw [mem_closedBall, Real.dist_eq, sub_zero] at h1
    have h2 : r < (((⌈r⌉₊ + 1 : ℕ)) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil r]
    linarith
  · obtain ⟨s, hs⟩ := hsurj (TopologicalSpace.denseSeq ℂ m)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδs⟩ := Metric.continuous_iff.1 η.continuous s _ hpos
    obtain ⟨q, hq⟩ := Metric.denseRange_iff.1 Rat.denseRange_cast s δ hδ
    refine ⟨q, ?_⟩
    rw [← hs]
    exact hδs _ (by rw [dist_comm]; exact hq)

theorem properOntoCurvesRat_subset : properOntoCurvesRat ⊆ properOntoCurves := by
  rintro η ⟨hprop, hdense⟩
  have hcoc : Tendsto (⇑η) (cocompact ℝ) (cocompact ℂ) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) (tendsto_atTop.2 fun b => ?_)
    obtain ⟨R, hR⟩ := exists_nat_ge b
    obtain ⟨T, hT⟩ := hprop R
    refine mem_cocompact.2 ⟨closedBall 0 T, isCompact_closedBall 0 T, ?_⟩
    have hsub : {t : ℝ | (T : ℝ) < |t|} ⊆ {t : ℝ | (R : ℝ) ≤ ‖η t‖} :=
      subset_of_rat_mem (isOpen_lt continuous_const continuous_abs)
        (isClosed_le continuous_const (continuous_norm.comp η.continuous))
        fun q hq => hT q (le_of_lt hq)
    intro t ht
    have ht' : (T : ℝ) < |t| := by
      simp only [mem_compl_iff, mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
      exact ht
    have := hsub ht'
    simp only [mem_ofPred_eq, dist_zero_right] at this ⊢
    linarith
  refine ⟨hcoc, ?_⟩
  have hcl : IsClosed (range η) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨η.continuous, hcoc⟩).isClosed_range
  have hd : DenseRange η := by
    refine Metric.denseRange_iff.2 fun z r hr => ?_
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z (r / 2)
      (by positivity)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hr)
    obtain ⟨t, ht⟩ := hdense m n
    refine ⟨t, ?_⟩
    calc dist z (η t) ≤ dist z (TopologicalSpace.denseSeq ℂ m) +
          dist (TopologicalSpace.denseSeq ℂ m) (η t) := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by
          refine add_lt_add hm ?_
          rw [dist_comm]
          exact ht.trans hn
      _ = r := by ring
  rw [← Set.range_eq_univ, ← hcl.closure_eq]
  exact hd.closure_range

/-- The proper onto curves are exactly the curves satisfying the countable rational description. -/
theorem properOntoCurves_eq : properOntoCurves = properOntoCurvesRat :=
  Subset.antisymm properOntoCurves_subset_rat properOntoCurvesRat_subset

/-- The proper onto curves form a Borel set of `C(ℝ, ℂ)`. -/
theorem measurableSet_properOntoCurves : MeasurableSet properOntoCurves := by
  rw [properOntoCurves_eq, properOntoCurvesRat]
  have hev : ∀ t : ℝ, Measurable fun η : C(ℝ, ℂ) => η t :=
    fun t => (continuous_eval_const t).measurable
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine MeasurableSet.inter
    (MeasurableSet.iInter fun R => MeasurableSet.iUnion fun T => MeasurableSet.iInter fun t =>
      MeasurableSet.iInter fun _ => measurableSet_le measurable_const (hev _).norm)
    (MeasurableSet.iInter fun m => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun t =>
      measurableSet_lt ((hev _).dist measurable_const) measurable_const)

variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The event that the curve `η' ω` is proper and onto is the preimage of `properOntoCurves`. -/
theorem properCurveSet_eq_preimage (η' : Ω → C(ℝ, ℂ)) :
    FirstPass.Derived.properCurveSet η' = η' ⁻¹' properOntoCurves := rfl

/-- For a measurable version of the curve, the proper onto event is measurable. -/
theorem measurableSet_properCurveSet {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') :
    MeasurableSet (FirstPass.Derived.properCurveSet η') :=
  measurableSet_properOntoCurves.preimage hη'

/-- For a valid environment, almost surely a version of the curve is proper and onto. -/
theorem ae_mem_properOntoCurves {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) :
    ∀ᵐ ω ∂S.P, η' ω ∈ properOntoCurves :=
  FirstPass.Derived.ae_mem_properCurveSet hS hae

/-- The interpolation weights of the cells of a proper onto curve are locally finite and
positive. -/
theorem interpWeight_good_of_mem_properOntoCurves {ε : ℝ} (hε : 0 < ε) {η : C(ℝ, ℂ)}
    (hη : η ∈ properOntoCurves) :
    (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑η) k) ε k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑η) k) ε k z ≠ 0 :=
  interpWeight_good_of_proper_surjective hε hη.1 hη.2

end MatedCRT
