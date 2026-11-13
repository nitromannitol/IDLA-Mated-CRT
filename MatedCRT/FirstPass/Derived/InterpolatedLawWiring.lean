import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import MatedCRT.FirstPass.Derived.SrwLawMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EdgeMeasurable
import MatedCRT.FirstPass.S4S6c.TraceInputs68
import MatedCRT.FirstPass.S5c.GreenCount

/-!
# Measurable wiring of the interpolated walk laws (Theorem 2.11, BG20 Theorem 1.2)

For a valid environment `S`, a measurable version `η' : Ω → C(ℝ, ℂ)` of the curve, a scaling `m ≥ 0`, a
cell size `ε` and a vertex `k`, `walkPathLaw` is the quenched law, on continuous paths `ℝ≥0 → ℂ`, of the
linearly interpolated embedded simple random walk of the mated-CRT map started from `k`. It is a
measurable function of the environment (`measurable_walkPathLaw`). The cells `cell ε (η' ω) k` have
measurable distance functions (`measurable_infDist_cell`) and, whenever `η' ω` is proper and onto, cover the
plane and meet every ball in finitely many vertices (`interpWeight_good_of_proper_surjective`), the
hypotheses of the interpolated law of Lattice-Probability.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- The interpolation of an embedded walk is jointly measurable in the labelling and the walk. -/
theorem measurable_interpPathCM_uncurry {m : ℝ} (hm : 0 ≤ m) :
    Measurable fun p : (ℤ → ℂ) × (ℕ → ℤ) => interpPathCM p.1 hm p.2 := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have h1 : ∀ n : ℕ, Measurable fun p : (ℤ → ℂ) × (ℕ → ℤ) => p.1 (p.2 n) := fun n =>
    (measurable_from_prod_countable_left (f := fun q : (ℤ → ℂ) × ℤ => q.1 q.2)
      fun y => measurable_pi_apply y).comp
      (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd))
  simp only [interpPathCM_apply, interpPathFn, linInterp]
  exact (measurable_const.mul (h1 _)).add (measurable_const.mul (h1 _))

variable {Ω : Type} [MeasurableSpace Ω]

/-- The edge multiplicities of a valid environment, as a measurable array. -/
theorem MatedCRTEnv.IsValid.measurable_mult_array {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (ε : ℝ) : Measurable fun ω => S.mult ε ω :=
  measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun l => hS.measurable_mult ε j l

/-- The quenched walk law as a kernel in the environment. -/
noncomputable def walkKernel {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (k : ℤ) : Kernel Ω (ℕ → ℤ) :=
  ⟨fun ω => srwLaw (S.mult ε ω) k, (measurable_srwLaw k).comp (hS.measurable_mult_array ε)⟩

instance {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (ε : ℝ) (k : ℤ) :
    IsMarkovKernel (walkKernel hS ε k) :=
  ⟨fun ω => isProbabilityMeasure_srwLaw (S.mult ε ω) k⟩

/-- The quenched law of the interpolated embedded walk started from `k`, `Q^ε(k)(ω)`, on the continuous
paths `ℝ≥0 → ℂ`; `v ω` is the position of the vertices and `m` the time scaling. -/
noncomputable def walkPathLaw (S : MatedCRTEnv Ω) (v : Ω → ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (ε : ℝ) (k : ℤ)
    (ω : Ω) : ProbabilityMeasure (ContinuousPath ℂ) :=
  ⟨Measure.map (interpPathCM (v ω) hm) (srwLaw (S.mult ε ω) k),
    (Measure.isProbabilityMeasure_map_iff (measurable_interpPathCM (v ω) hm).aemeasurable).2 inferInstance⟩

/-- `Q^ε(k)` is a measurable family of probability measures on paths. -/
theorem measurable_walkPathLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {v : Ω → ℤ → ℂ} (hv : Measurable v) {m : ℝ} (hm : 0 ≤ m) (ε : ℝ) (k : ℤ) :
    Measurable (walkPathLaw S v hm ε k) := by
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hT : MeasurableSet {q : Ω × (ℕ → ℤ) | interpPathCM (v q.1) hm q.2 ∈ s} :=
    (measurable_interpPathCM_uncurry hm).comp ((hv.comp measurable_fst).prodMk measurable_snd) hs
  have key := (walkKernel hS ε k).measurable_kernel_prodMk_left hT
  convert key using 1
  funext ω
  exact Measure.map_apply (measurable_interpPathCM (v ω) hm) hs

/-- A measurable version of the curve: `η'` is measurable as a map to `C(ℝ, ℂ)` and almost surely equal to `S.η`
(through the area parametrization of the mating-of-trees coupling). -/
theorem MatedCRTEnv.IsValid.exists_curveVersion {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) : ∃ η' : Ω → C(ℝ, ℂ), Measurable η' ∧ ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae⟩ := hS.matingOfTrees
  exact ⟨η', hC.measurable_curves.2.1, hae.mono fun ω h => h.1⟩

/-- The distance from a point to the image of a compact interval under a measurable family of continuous
curves is measurable in the parameter (the image is the closure of the image of the rationals). -/
theorem measurable_infDist_image_Icc {η : Ω → C(ℝ, ℂ)} (hη : Measurable η) {a b : ℝ} (hab : a < b)
    (z : ℂ) : Measurable fun ω => Metric.infDist z (η ω '' Icc a b) := by
  have hev : ∀ t : ℝ, Measurable fun ω => η ω t := fun t =>
    (continuous_eval_const t).measurable.comp hη
  have heq : ∀ ω, Metric.infEDist z (η ω '' Icc a b) =
      ⨅ q : ℚ, ⨅ (_ : (q : ℝ) ∈ Ioo a b), edist z (η ω (q : ℝ)) := by
    intro ω
    set D : Set ℚ := {q : ℚ | (q : ℝ) ∈ Ioo a b} with hD
    set R : Set ℝ := ((↑) : ℚ → ℝ) '' D with hR
    have hRe : R = Ioo a b ∩ range ((↑) : ℚ → ℝ) := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨hq, q, rfl⟩
      · rintro ⟨hx, q, rfl⟩
        exact ⟨q, hx, rfl⟩
    have hdense : Icc a b ⊆ closure R := by
      have h1 : Ioo a b ⊆ closure R := by
        rw [hRe]; exact Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo
      calc Icc a b = closure (Ioo a b) := (closure_Ioo hab.ne).symm
        _ ⊆ closure R := closure_minimal h1 isClosed_closure
    have hsub : η ω '' R ⊆ η ω '' Icc a b := image_mono (by
      rw [hRe]; exact fun x hx => Ioo_subset_Icc_self hx.1)
    have hsub2 : η ω '' Icc a b ⊆ closure (η ω '' R) :=
      (image_mono hdense).trans (image_closure_subset_closure_image (η ω).continuous)
    have h1 : Metric.infEDist z (η ω '' Icc a b) = Metric.infEDist z (η ω '' R) := by
      refine le_antisymm (Metric.infEDist_anti hsub) ?_
      rw [← Metric.infEDist_closure (s := η ω '' R)]
      exact Metric.infEDist_anti hsub2
    rw [h1, hR, Set.image_image]
    simp only [Metric.infEDist, iInf_image]
    rfl
  unfold Metric.infDist
  refine ENNReal.measurable_toReal.comp ?_
  simp_rw [heq]
  exact Measurable.iInf fun q => Measurable.iInf_Prop _ ((measurable_const (a := z)).edist (hev q))

/-- The distance from a point to the cell `cell ε (η ω) k` is measurable in `ω`. -/
theorem measurable_infDist_cell {η : Ω → C(ℝ, ℂ)} (hη : Measurable η) {ε : ℝ} (hε : 0 < ε) (k : ℤ)
    (z : ℂ) : Measurable fun ω => Metric.infDist z (cell ε (⇑(η ω)) k) :=
  measurable_infDist_image_Icc hη (mul_lt_mul_of_pos_left (by linarith) hε) z

/-- For a proper onto curve and `ε > 0`, the cells are nonempty, cover the plane, and every ball meets only
finitely many of them. -/
theorem cell_cover_finite_of_proper_surjective {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) :
    (∀ k, (cell ε η k).Nonempty) ∧ (∀ z, ∃ k, z ∈ cell ε η k) ∧
      ∀ (z : ℂ) (R : ℝ), {k | ∃ x ∈ cell ε η k, dist x z < R}.Finite :=
  ⟨fun k => TraceInputs68.cell_nonempty hε η k, S5c.exists_mem_cell_of_surj hε hsurj,
    fun z R => (TraceInputs68.cellVertices_finite_of_tendsto hε hη
      (Metric.isBounded_ball (x := z) (r := R))).subset fun _ ⟨x, hx, hd⟩ => ⟨x, hx, hd⟩⟩

end MatedCRT
