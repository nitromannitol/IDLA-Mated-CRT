import MatedCRT.FirstPass.Derived.WalkIntegralMeasurable
import MatedCRT.FirstPass.Derived.ExitTimeCdfConvergence
import MatedCRT.FirstPass.Derived.EmbeddedExitTimeInterp
import MatedCRT.FirstPass.Derived.ExitTimeScaling

/-!
# The annealed law of the rescaled embedded walk from the vertex of the origin

For a valid environment `S` and `ε > 0`, let `a^ε_0` be the vertex of the cell containing `0` and let
`Q^ε(a^ε_0)(ω)` be the quenched law of the interpolated embedded walk `t ↦ η(X_{m_ε t})` (a measure on
`ContinuousPath ℂ`).  Its annealed law `annealedPathLaw S η' ε a` (the mixture over the environment) has exit-time
distribution function from `B_{1/2}` equal to `s ↦ F^interp_ε(m_ε s)`, where `F^interp_ε` is the annealed
distribution function of the exit time of the interpolated walk of unit time step (`mεInterpCdf`).  Hence the
lower median of the exit time of the annealed rescaled walk is `m^interp_ε / m_ε`, which tends to `1`
(Berestycki–Gwynne (2020), end of the proof of Theorem 1.2).

* `medianOf_comp_mul`: the lower median of `s ↦ G (c s)` is the lower median of `G` divided by `c > 0`.
* `exitTime_interpPathCM_vertexPoint`: exit time of the rescaled interpolated walk.
* `annealedPathLaw`, `exitCdf_annealedPathLaw`, `medianOf_exitCdf_annealedPathLaw`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal Pointwise

namespace MatedCRT.FirstPass.Derived

open MatedCRT.ExitTimeCdf

/-- The lower median of `s ↦ G (c s)` is the lower median of `G` divided by `c > 0`. -/
theorem medianOf_comp_mul (G : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    medianOf (fun s => G (c * s)) = medianOf G / c := by
  unfold medianOf
  have hset : {s : ℝ | 0 ≤ s ∧ (1 / 2 : ℝ≥0∞) ≤ G (c * s)} =
      c⁻¹ • {u : ℝ | 0 ≤ u ∧ (1 / 2 : ℝ≥0∞) ≤ G u} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨c * s, ⟨mul_nonneg hc.le h0, h1⟩, by field_simp⟩
    · rintro ⟨u, ⟨h0, h1⟩, rfl⟩
      refine ⟨mul_nonneg (inv_nonneg.2 hc.le) h0, ?_⟩
      rwa [show c * (c⁻¹ * u) = u by field_simp]
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le), smul_eq_mul, div_eq_inv_mul]

/-- **Exit time of the rescaled interpolated walk.**  For `m > 0`, the exit time from `U` of the path
`t ↦ η(x_{m t})` (linear interpolation) is the exit time of the interpolated walk of unit time step, divided by
`m`. -/
theorem exitTime_interpPathCM_vertexPoint (U : Set ℂ) (ε : ℝ) (η : ℝ → ℂ) {m : ℝ} (hm : 0 < m)
    (x : ℕ → ℤ) :
    ContinuousPath.exitTime U (interpPathCM (vertexPoint ε η) hm.le x) =
      interpExitTime ε η U x / (m.toNNReal : ℝ≥0∞) := by
  have hc : m.toNNReal ≠ 0 := by simpa using hm
  have h : interpPathCM (vertexPoint ε η) hm.le x =
      timeScalePath m.toNNReal (interpPathCM (vertexPoint ε η) zero_le_one x) := by
    ext t
    simp only [interpPathCM_vertexPoint, timeScalePath_apply, interpolatedWalk]
    simp [Real.coe_toNNReal _ hm.le]
  rw [h, exitTime_timeScalePath U hc]
  rfl

/-- The exit time of the rescaled interpolated walk is at most `s` iff the exit time of the interpolated walk of
unit time step is at most `m s`. -/
theorem exitTime_interpPathCM_le_iff (U : Set ℂ) (ε : ℝ) (η : ℝ → ℂ) {m : ℝ} (hm : 0 < m)
    (x : ℕ → ℤ) (s : ℝ) :
    ContinuousPath.exitTime U (interpPathCM (vertexPoint ε η) hm.le x) ≤ ENNReal.ofReal s ↔
      interpExitTime ε η U x ≤ ENNReal.ofReal (m * s) := by
  have hc : (m.toNNReal : ℝ≥0∞) ≠ 0 := by simpa using hm
  rw [exitTime_interpPathCM_vertexPoint U ε η hm,
    ENNReal.div_le_iff_le_mul (Or.inl hc) (Or.inl ENNReal.coe_ne_top), ENNReal.ofReal_mul hm.le,
    mul_comm]
  rfl

variable {Ω : Type} [MeasurableSpace Ω]

/-- The annealed law of the rescaled interpolated embedded walk started from the vertex `a ω`:
`ω ↦ Q^ε(a ω)(ω)` integrated against the law of the environment. -/
noncomputable def annealedPathLaw (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε : ℝ) (a : Ω → ℤ) :
    Measure (ContinuousPath ℂ) :=
  S.P.bind fun ω =>
    (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε (a ω) ω :
      Measure (ContinuousPath ℂ))

/-- **The exit-time distribution function of the annealed rescaled walk.**  If `a` is a measurable version of the
vertex `a^ε_0` and `m_ε > 0`, then the annealed rescaled walk leaves `B_{1/2}` by time `s` with probability
`F^interp_ε(m_ε s)`. -/
theorem exitCdf_annealedPathLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} {a : Ω → ℤ} (ha : Measurable a)
    (hav : ∀ᵐ ω ∂S.P, a ω = vertexOf ε (S.η ω) 0) (hm : 0 < S.mε ε) (s : ℝ) :
    exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (annealedPathLaw S η' ε a) s =
      S.mεInterpCdf ε (S.mε ε * s) := by
  set v : Ω → ℤ → ℂ := fun ω => vertexPoint ε (⇑(η' ω)) with hvdef
  have hv : Measurable v := measurable_vertexPoint_curve hη' ε
  have hg : Measurable (fun p : Ω × ℤ => walkPathLaw S v (S.mε_nonneg ε) ε p.2 p.1) :=
    measurable_from_prod_countable_left fun k => measurable_walkPathLaw hS hv (S.mε_nonneg ε) ε k
  have hker : Measurable fun ω =>
      (walkPathLaw S v (S.mε_nonneg ε) ε (a ω) ω : Measure (ContinuousPath ℂ)) :=
    measurable_subtype_coe.comp (hg.comp (measurable_id.prodMk ha))
  have hmeas : MeasurableSet {f : ContinuousPath ℂ |
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) (1 / 2)) f ≤ ENNReal.ofReal s} :=
    measurableSet_le (measurable_pathExitTime Metric.isOpen_ball) measurable_const
  unfold exitCdf annealedPathLaw MatedCRTEnv.mεInterpCdf
  rw [Measure.bind_apply hmeas hker.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hae, hav] with ω hω haω
  rw [haω]
  change Measure.map (interpPathCM (v ω) (S.mε_nonneg ε)) (srwLaw (S.mult ε ω) _) _ = _
  rw [Measure.map_apply (measurable_interpPathCM (v ω) (S.mε_nonneg ε)) hmeas]
  have hvω : v ω = vertexPoint ε (S.η ω) := by
    simp only [hvdef]
    rw [hω]
  congr 1
  ext x
  simp only [mem_preimage, Set.mem_ofPred_eq]
  rw [hvω]
  exact exitTime_interpPathCM_le_iff _ ε (S.η ω) hm x s

/-- **The median of the exit time of the annealed rescaled walk** from `B_{1/2}` is `m^interp_ε / m_ε`. -/
theorem medianOf_exitCdf_annealedPathLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} {a : Ω → ℤ} (ha : Measurable a)
    (hav : ∀ᵐ ω ∂S.P, a ω = vertexOf ε (S.η ω) 0) (hm : 0 < S.mε ε) :
    medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (annealedPathLaw S η' ε a)) =
      S.mεInterp ε / S.mε ε := by
  have h : exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (annealedPathLaw S η' ε a) =
      fun s => S.mεInterpCdf ε (S.mε ε * s) :=
    funext fun s => exitCdf_annealedPathLaw hS hη' hae ha hav hm s
  rw [h, medianOf_comp_mul _ hm]
  rfl

end MatedCRT.FirstPass.Derived
