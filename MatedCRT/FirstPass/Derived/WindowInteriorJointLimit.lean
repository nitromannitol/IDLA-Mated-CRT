import MatedCRT.FirstPass.Derived.LBMPathLawFieldStartExit
import MatedCRT.FirstPass.Derived.HN9OfJointChartLaws
import MatedCRT.FirstPass.Derived.ValidCurveFixedTime

/-!
# The curve point lies in the interior of its windows on the joint limit

For the window `(a, u, b)` of the curve, Berestycki–Gwynne (2020) (proof of Lemma 7.18) use that `η(u)` lies in the
interior of `η([a, b])`. For a valid environment this holds almost surely at each fixed time `u`, simultaneously for
all `a < u < b` (`MatedCRTEnv.IsValid.ae_fixedTime_mem_interior_image`). This file transfers it to a weak limit `ν''` of
the joint laws of the field coordinates, a coordinate `E`, the curve and a sequence of path-law families: the curve
marginal of `ν''` is the law of the curve, and the event is a Borel set of curves.

* `isClosed_setOf_mem_image_Icc`: `{η | p ∈ η([a, b])}` is closed in `C(ℝ, ℂ)` (projection along the compact factor
  `[a, b]` of the closed set `{(η, t) | η t = p}`).
* `mem_interior_iff_of_dense`: for a closed set `K` and a dense set `D`, `x ∈ int K` iff for some `n` every point of
  `D` in the ball `B(x, 1/(n+1))` lies in `K`.
* `measurableSet_setOf_mem_interior_image`: `{η | η u ∈ int η([a, b])}` is a Borel set of curves.
* `ae_jointLimit_curvePoint_mem_interior_image`: on the joint limit, almost surely `η(u) ∈ int η([l, r])` for all
  `l < u < r`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- The curves whose image of `[a, b]` contains a given point form a closed set. -/
theorem isClosed_setOf_mem_image_Icc (p : ℂ) (a b : ℝ) :
    IsClosed {η : C(ℝ, ℂ) | p ∈ η '' Icc a b} := by
  have : CompactSpace (Icc a b) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hc : IsClosed {x : C(ℝ, ℂ) × Icc a b | x.1 (x.2 : ℝ) = p} :=
    isClosed_eq (continuous_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      continuous_const
  have himg : {η : C(ℝ, ℂ) | p ∈ η '' Icc a b} =
      Prod.fst '' {x : C(ℝ, ℂ) × Icc a b | x.1 (x.2 : ℝ) = p} := by
    ext η
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(η, ⟨t, ht⟩), rfl, rfl⟩
    · rintro ⟨⟨η', t⟩, h, rfl⟩
      exact ⟨t, t.2, h⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- A point `x` lies in the interior of a closed set `K` iff, for some `n`, every point of a dense set `D` within
distance `1/(n+1)` of `x` lies in `K`. -/
theorem mem_interior_iff_of_dense {D : Set ℂ} (hD : Dense D) {K : Set ℂ} (hK : IsClosed K) (x : ℂ) :
    x ∈ interior K ↔ ∃ n : ℕ, ∀ p ∈ D, dist p x < 1 / ((n : ℝ) + 1) → p ∈ K := by
  constructor
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, fun p _ hp => hball (Metric.mem_ball.2 (hp.trans hn))⟩
  · rintro ⟨n, hn⟩
    refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1 / ((n : ℝ) + 1), Nat.one_div_pos_of_nat, ?_⟩)
    intro y hy
    have hsub : Metric.ball x (1 / ((n : ℝ) + 1)) ∩ D ⊆ K := fun p hp => hn p hp.2 (Metric.mem_ball.1 hp.1)
    exact hK.closure_subset_iff.2 hsub (hD.open_subset_closure_inter Metric.isOpen_ball hy)

/-- **The window event is Borel.** The curves `η` with `η(u)` in the interior of `η([a, b])` form a Borel set of
`C(ℝ, ℂ)`. -/
theorem measurableSet_setOf_mem_interior_image (u a b : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | η u ∈ interior (η '' Icc a b)} := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable D := hDc.to_subtype
  have heq : {η : C(ℝ, ℂ) | η u ∈ interior (η '' Icc a b)} =
      ⋃ n : ℕ, ⋂ p : D, ({η : C(ℝ, ℂ) | dist (p : ℂ) (η u) < 1 / ((n : ℝ) + 1)}ᶜ ∪
        {η : C(ℝ, ℂ) | (p : ℂ) ∈ η '' Icc a b}) := by
    ext η
    have hK : IsClosed (η '' Icc a b) := (isCompact_Icc.image η.continuous).isClosed
    rw [mem_ofPred_eq, mem_interior_iff_of_dense hD hK, mem_iUnion]
    refine exists_congr fun n => ?_
    simp only [mem_iInter, mem_union, mem_compl_iff, mem_ofPred_eq, Subtype.forall]
    refine ⟨fun h p hp => ?_, fun h p hp hpx => (h p hp).resolve_left (not_not_intro hpx)⟩
    by_cases hpx : dist p (η u) < 1 / ((n : ℝ) + 1)
    · exact Or.inr (h p hp hpx)
    · exact Or.inl hpx
  rw [heq]
  refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun p => ?_
  exact (measurableSet_lt (continuous_const.dist (continuous_eval_const u)).measurable
    measurable_const).compl.union (isClosed_setOf_mem_image_Icc p a b).measurableSet

/-- From the shrinking symmetric windows to all windows: if `η(u)` lies in the interior of `η([u - 1/(n+1),
u + 1/(n+1)])` for every `n`, then it lies in the interior of `η([l, r])` for all `l < u < r`. -/
theorem mem_interior_image_Icc_of_forall_nat (η : C(ℝ, ℂ)) (u : ℝ)
    (h : ∀ n : ℕ, η u ∈ interior (η '' Icc (u - 1 / ((n : ℝ) + 1)) (u + 1 / ((n : ℝ) + 1)))) {l r : ℝ}
    (hl : l < u) (hr : u < r) : η u ∈ interior (η '' Icc l r) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 hl) (sub_pos.2 hr))
  refine interior_mono (image_mono (Icc_subset_Icc ?_ ?_)) (h n)
  · linarith [min_le_left (u - l) (r - u)]
  · linarith [min_le_right (u - l) (r - u)]

/-- **The window event on the joint limit** (Berestycki–Gwynne (2020), proof of Lemma 7.18, for the limit of the
joint laws). Let `ν''` be a weak limit of the joint laws of the field coordinates, a measurable coordinate `E`, a
version `η'` of the curve and a sequence of path-law families `Z n`. Then for `ν''`-almost every sample, the curve
point `η(u)` lies in the interior of `η([l, r])` for all `l < u < r`. -/
theorem ae_jointLimit_curvePoint_mem_interior_image {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν''))) (u : ℝ) :
    ∀ᵐ q ∂ν'', ∀ l r, l < u → u < r → q.1.2 u ∈ interior (q.1.2 '' Icc l r) := by
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  let Data := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)
  have hD : Measurable fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  have hmarg : ν''.map Prod.fst = S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hD hconv
  let B : Set Data := ⋂ n : ℕ, Prod.snd ⁻¹' {η : C(ℝ, ℂ) |
    η u ∈ interior (η '' Icc (u - 1 / ((n : ℝ) + 1)) (u + 1 / ((n : ℝ) + 1)))}
  have hB : MeasurableSet B :=
    MeasurableSet.iInter fun n => measurable_snd (measurableSet_setOf_mem_interior_image u _ _)
  have hsrc : ∀ᵐ x ∂(S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data)), x ∈ B := by
    refine (ae_map_iff hD.aemeasurable hB).2 ?_
    filter_upwards [hS.ae_fixedTime_mem_interior_image u, hae] with ω hω he
    refine mem_iInter.2 fun n => ?_
    show η' ω u ∈ interior (η' ω '' Icc (u - 1 / ((n : ℝ) + 1)) (u + 1 / ((n : ℝ) + 1)))
    rw [he]
    exact hω _ _ (sub_lt_self u Nat.one_div_pos_of_nat) (lt_add_of_pos_right u Nat.one_div_pos_of_nat)
  rw [← hmarg] at hsrc
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hsrc] with q hq l r hl hr
  exact mem_interior_image_Icc_of_forall_nat q.1.2 u (fun n => mem_iInter.1 hq n) hl hr

end MatedCRT
