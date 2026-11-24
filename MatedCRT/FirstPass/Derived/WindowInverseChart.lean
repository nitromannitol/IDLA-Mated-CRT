import MatedCRT.FirstPass.Derived.WindowDiscMapBorel
import MatedCRT.FirstPass.Derived.HN9OfChartField

/-!
# A Borel choice of the inverse chart of a window

For a continuous map `φ` of `ℂ` which is injective on the closed unit disc `𝔻̄`, the inverse map `φ⁻¹` is continuous
on the compact set `K = φ(𝔻̄)`. This file extends it to a continuous map of `ℂ` by Dieudonné's formula
(Hausdorff's proof of the Tietze extension theorem for metric spaces): for a continuous weight `c` on `𝔻̄` with
values in `[1, 3]`, the function `c ∘ φ⁻¹` on `K` extends to
`x ↦ inf_{|v| ≤ 1} c(v) |x - φ(v)| / dist(x, K)` off `K`. Applied to the weights `re + 2` and `im + 2` this gives
`discInverseExt φ : C(ℂ, ℂ)`, a left inverse of `φ` on `𝔻̄`. Unlike a Tietze extension chosen by `Classical.choice`,
it is given by a formula, and it is a Borel function of `φ` (the infima over `𝔻̄` are continuous in `φ`, the inverse
at a point is a Borel choice along a Borel graph).

Composed with the Borel normalized conformal map `windowDiscMap a u b η` of the window `(a, u, b)` of a curve `η`, it
gives `windowChart a u b η`, a Borel function of the curve which is an inverse chart of the window at `η(u)` whenever
the window has one (Berestycki–Gwynne (2020), proof of Lemma 7.18, use the inverse of the conformal map of the window
as a random variable). The input `BG20NormalizedChartInput` is `BG20ChartFieldInput` with these inverse charts in
place of the existential ones, and with the almost sure existence of an inverse chart in place of "almost surely `ψ`
is an inverse chart"; it implies `BG20ChartFieldInput` (`bg20ChartFieldInput_of_normalizedChart`).

## Main statements

* `discWeightedDist`, `discDist`, `dieudonneExt`, `continuous_dieudonneExt`, `measurable_dieudonneExt_apply`.
* `discInverseExt`, `discInverseExt_apply_image`, `measurable_discInverseExt`,
  `IsDiscMap.isInverseChart_of_leftInvOn`, `IsNormalizedDiscMap.isInverseChart_discInverseExt`.
* `windowChart`, `measurable_windowChart`, `isInverseChart_windowChart`,
  `measurableSet_setOf_exists_isInverseChart`.
* `BG20NormalizedChartInput`, `bg20ChartFieldInput_of_normalizedChart`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-! ### Weighted distances to the image of the closed disc -/

/-- The weighted distance `inf_{|v| ≤ 1} c(v) |x - φ(v)|` from `x` to the image of the closed unit disc under `φ`. -/
noncomputable def discWeightedDist (c : ℂ → ℝ) (φ : ℂ → ℂ) (x : ℂ) : ℝ :=
  sInf ((fun v => c v * ‖x - φ v‖) '' closedBall 0 1)

/-- The distance `inf_{|v| ≤ 1} |x - φ(v)|` from `x` to the image of the closed unit disc under `φ`. -/
noncomputable def discDist (φ : ℂ → ℂ) (x : ℂ) : ℝ :=
  discWeightedDist (fun _ => 1) φ x

theorem continuous_discWeightedDist_right {c : ℂ → ℝ} (hc : Continuous c) {φ : ℂ → ℂ} (hφ : Continuous φ) :
    Continuous (discWeightedDist c φ) :=
  (isCompact_closedBall (0 : ℂ) 1).continuous_sInf (f := fun (x v : ℂ) => c v * ‖x - φ v‖)
    ((hc.comp continuous_snd).mul (continuous_fst.sub (hφ.comp continuous_snd)).norm)

theorem continuous_discWeightedDist_left {c : ℂ → ℝ} (hc : Continuous c) (x : ℂ) :
    Continuous fun φ : C(ℂ, ℂ) => discWeightedDist c φ x :=
  (isCompact_closedBall (0 : ℂ) 1).continuous_sInf (f := fun (φ : C(ℂ, ℂ)) (v : ℂ) => c v * ‖x - φ v‖)
    ((hc.comp continuous_snd).mul (continuous_const.sub continuous_eval).norm)

theorem continuous_discDist {φ : ℂ → ℂ} (hφ : Continuous φ) : Continuous (discDist φ) :=
  continuous_discWeightedDist_right (c := fun _ => 1) continuous_const hφ

theorem continuous_discDist_left (x : ℂ) : Continuous fun φ : C(ℂ, ℂ) => discDist φ x :=
  continuous_discWeightedDist_left (c := fun _ => 1) continuous_const x

theorem discWeightedDist_le {c : ℂ → ℝ} {φ : ℂ → ℂ} (hc : Continuous c) (hφ : Continuous φ) (x : ℂ) {v : ℂ}
    (hv : v ∈ closedBall (0 : ℂ) 1) : discWeightedDist c φ x ≤ c v * ‖x - φ v‖ :=
  csInf_le ((isCompact_closedBall (0 : ℂ) 1).image (hc.mul (continuous_const.sub hφ).norm)).bddBelow
    (mem_image_of_mem _ hv)

theorem le_discWeightedDist {c : ℂ → ℝ} {φ : ℂ → ℂ} {x : ℂ} {m : ℝ}
    (h : ∀ v ∈ closedBall (0 : ℂ) 1, m ≤ c v * ‖x - φ v‖) : m ≤ discWeightedDist c φ x :=
  le_csInf ((nonempty_closedBall.2 zero_le_one).image _) (forall_mem_image.2 h)

/-- The weighted distance is attained on the closed disc. -/
theorem exists_discWeightedDist_eq {c : ℂ → ℝ} {φ : ℂ → ℂ} (hc : Continuous c) (hφ : Continuous φ) (x : ℂ) :
    ∃ v ∈ closedBall (0 : ℂ) 1, discWeightedDist c φ x = c v * ‖x - φ v‖ := by
  have hK : IsCompact ((fun v => c v * ‖x - φ v‖) '' closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall 0 1).image (hc.mul (continuous_const.sub hφ).norm)
  obtain ⟨v, hv, hve⟩ := hK.sInf_mem ((nonempty_closedBall.2 zero_le_one).image _)
  exact ⟨v, hv, hve.symm⟩

theorem discDist_le {φ : ℂ → ℂ} (hφ : Continuous φ) (x : ℂ) {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) 1) :
    discDist φ x ≤ ‖x - φ v‖ :=
  (discWeightedDist_le (c := fun _ => 1) continuous_const hφ x hv).trans_eq (one_mul _)

theorem discDist_nonneg (φ : ℂ → ℂ) (x : ℂ) : 0 ≤ discDist φ x :=
  le_discWeightedDist (c := fun _ => 1) fun _ _ => mul_nonneg zero_le_one (norm_nonneg _)

theorem exists_discDist_eq {φ : ℂ → ℂ} (hφ : Continuous φ) (x : ℂ) :
    ∃ v ∈ closedBall (0 : ℂ) 1, discDist φ x = ‖x - φ v‖ := by
  obtain ⟨v, hv, h⟩ := exists_discWeightedDist_eq (c := fun _ => 1) continuous_const hφ x
  exact ⟨v, hv, h.trans (one_mul _)⟩

theorem discDist_eq_zero_iff {φ : ℂ → ℂ} (hφ : Continuous φ) {x : ℂ} :
    discDist φ x = 0 ↔ x ∈ φ '' closedBall (0 : ℂ) 1 := by
  constructor
  · intro h
    obtain ⟨v, hv, hv'⟩ := exists_discDist_eq hφ x
    rw [h, eq_comm, norm_eq_zero, sub_eq_zero] at hv'
    exact ⟨v, hv, hv'.symm⟩
  · rintro ⟨v, hv, rfl⟩
    refine le_antisymm ?_ (discDist_nonneg φ _)
    calc discDist φ (φ v) ≤ ‖φ v - φ v‖ := discDist_le hφ _ hv
      _ = 0 := by rw [sub_self, norm_zero]

/-! ### The inverse on the image of the closed disc -/

/-- The graph of the inverse on `φ(𝔻̄)` at the point `x`: the pairs `(φ, v)` with `φ` injective on `𝔻̄`, `|v| ≤ 1`
and `φ(v) = x`. -/
def discInvGraph (x : ℂ) : Set (C(ℂ, ℂ) × ℂ) :=
  {p | InjOn p.1 (closedBall 0 1) ∧ p.2 ∈ closedBall (0 : ℂ) 1 ∧ p.1 p.2 = x}

open Classical in
/-- The inverse of `φ` at `x`: the point `v` of the closed disc with `φ(v) = x` (and `0` if there is none, or if `φ`
is not injective on the closed disc). -/
noncomputable def discInvAt (φ : C(ℂ, ℂ)) (x : ℂ) : ℂ :=
  if h : ∃ v, (φ, v) ∈ discInvGraph x then h.choose else 0

theorem discInvAt_apply {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) 1) :
    discInvAt φ (φ v) = v := by
  have h : ∃ w, (φ, w) ∈ discInvGraph (φ v) := ⟨v, hφ, hv, rfl⟩
  unfold discInvAt
  rw [dite_eq_left h]
  exact hφ h.choose_spec.2.1 hv h.choose_spec.2.2

theorem measurableSet_discInvGraph (x : ℂ) : MeasurableSet (discInvGraph x) := by
  have heq : discInvGraph x = (Prod.fst ⁻¹' {φ : C(ℂ, ℂ) | InjOn φ (closedBall 0 1)}) ∩
      ({p : C(ℂ, ℂ) × ℂ | p.2 ∈ closedBall (0 : ℂ) 1} ∩ {p : C(ℂ, ℂ) × ℂ | p.1 p.2 = x}) := rfl
  rw [heq]
  exact (measurableSet_setOf_injOn_closedBall.preimage measurable_fst).inter
    ((isClosed_closedBall.preimage continuous_snd).inter
      (isClosed_eq continuous_eval continuous_const)).measurableSet

/-- The inverse at a point is a Borel function of the map. -/
theorem measurable_discInvAt (x : ℂ) : Measurable fun φ : C(ℂ, ℂ) => discInvAt φ x := by
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  exact measurable_graphChoice (measurableSet_discInvGraph x)
    (fun _ _ _ hv hv' => hv.1 hv.2.1 hv'.2.1 (hv.2.2.trans hv'.2.2.symm)) 0

/-- The inverse of a continuous map injective on the closed disc is continuous on the image of the closed disc. -/
theorem continuousOn_discInvAt {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) :
    ContinuousOn (discInvAt φ) (φ '' closedBall (0 : ℂ) 1) := by
  have hbij : BijOn φ (closedBall (0 : ℂ) 1) (φ '' closedBall (0 : ℂ) 1) := hφ.bijOn_image
  let e : closedBall (0 : ℂ) 1 ≃ φ '' closedBall (0 : ℂ) 1 := hbij.equiv φ
  have hcon : ContinuousOn φ (closedBall (0 : ℂ) 1) := φ.continuous.continuousOn
  have he : Continuous e := hcon.domRestrict.subtype_mk _
  have : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  let k : closedBall (0 : ℂ) 1 ≃ₜ φ '' closedBall (0 : ℂ) 1 := he.homeoOfEquivCompactToT2
  refine continuousOn_iff_continuous_domRestrict.2
    ((continuous_subtype_val.comp k.symm.continuous).congr fun y => ?_)
  obtain ⟨w, rfl⟩ := k.surjective y
  rw [Function.comp_apply, k.symm_apply_apply]
  exact (discInvAt_apply hφ w.2).symm

/-! ### Dieudonné's extension -/

open Classical in
/-- **Dieudonné's extension** of `c ∘ φ⁻¹` from `K = φ(𝔻̄)` to `ℂ`: `c(φ⁻¹ x)` on `K`, and
`inf_{|v| ≤ 1} c(v) |x - φ(v)| / dist(x, K)` off `K`. -/
noncomputable def dieudonneExt (c : ℂ → ℝ) (φ : C(ℂ, ℂ)) (x : ℂ) : ℝ :=
  if x ∈ φ '' closedBall 0 1 then c (discInvAt φ x) else discWeightedDist c φ x / discDist φ x

theorem dieudonneExt_apply_image {c : ℂ → ℝ} {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) {v : ℂ}
    (hv : v ∈ closedBall (0 : ℂ) 1) : dieudonneExt c φ (φ v) = c v := by
  rw [dieudonneExt, ite_eq_left (mem_image_of_mem φ hv), discInvAt_apply hφ hv]

theorem dieudonneExt_of_notMem {c : ℂ → ℝ} {φ : C(ℂ, ℂ)} {x : ℂ} (hx : x ∉ φ '' closedBall (0 : ℂ) 1) :
    dieudonneExt c φ x = discWeightedDist c φ x / discDist φ x := by
  rw [dieudonneExt, ite_eq_right hx]

/-- **Dieudonné's extension is continuous** (Hausdorff): for a continuous weight with values in `[1, 3]` on the
closed disc and `φ` injective on the closed disc. Off `K` it is a quotient of continuous functions with a positive
denominator; at a point `φ(v₀)` of `K`, the infimum is close to `c(v₀) dist(x, K)` because the points `v` with `φ(v)`
far from `φ(v₀)` contribute at least `3 dist(x, K)`. -/
theorem continuous_dieudonneExt {c : ℂ → ℝ} (hc : Continuous c)
    (hc1 : ∀ v ∈ closedBall (0 : ℂ) 1, 1 ≤ c v) (hc3 : ∀ v ∈ closedBall (0 : ℂ) 1, c v ≤ 3)
    {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) : Continuous (dieudonneExt c φ) := by
  have hKc : IsCompact (φ '' closedBall (0 : ℂ) 1) := (isCompact_closedBall 0 1).image φ.continuous
  have hcinv : ContinuousOn (fun y => c (discInvAt φ y)) (φ '' closedBall (0 : ℂ) 1) :=
    hc.comp_continuousOn (continuousOn_discInvAt hφ)
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx₀ : x₀ ∈ φ '' closedBall (0 : ℂ) 1
  · obtain ⟨v₀, hv₀, rfl⟩ := hx₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ :=
      Metric.continuousOn_iff.1 hcinv (φ v₀) (mem_image_of_mem φ hv₀) (ε / 2) (half_pos hε)
    have hloc : ∀ v ∈ closedBall (0 : ℂ) 1, dist (φ v) (φ v₀) < δ → |c v - c v₀| < ε / 2 := by
      intro v hv hd
      have h := hδc (φ v) (mem_image_of_mem φ hv) hd
      simp only [discInvAt_apply hφ hv, discInvAt_apply hφ hv₀, Real.dist_eq] at h
      exact h
    refine ⟨δ / 4, by positivity, fun {x} hx => ?_⟩
    rw [dieudonneExt_apply_image hφ hv₀, Real.dist_eq]
    by_cases hxK : x ∈ φ '' closedBall (0 : ℂ) 1
    · obtain ⟨v, hv, rfl⟩ := hxK
      rw [dieudonneExt_apply_image hφ hv]
      exact (hloc v hv (by linarith)).trans (half_lt_self hε)
    · rw [dieudonneExt_of_notMem hxK]
      have hDpos : 0 < discDist φ x := lt_of_le_of_ne (discDist_nonneg φ x)
        (fun h => hxK ((discDist_eq_zero_iff φ.continuous).1 h.symm))
      have hDle : discDist φ x ≤ dist x (φ v₀) :=
        (discDist_le φ.continuous x hv₀).trans_eq (dist_eq_norm _ _).symm
      obtain ⟨w, hw, hwD⟩ := exists_discDist_eq φ.continuous x
      have hwd : dist (φ w) (φ v₀) < δ := by
        have h1 := dist_triangle (φ w) x (φ v₀)
        rw [dist_comm (φ w) x, dist_eq_norm x (φ w), ← hwD] at h1
        linarith
      have hcw := hloc w hw hwd
      have hNup : discWeightedDist c φ x ≤ c w * discDist φ x := by
        rw [hwD]
        exact discWeightedDist_le hc φ.continuous x hw
      have hNlow : (c v₀ - ε / 2) * discDist φ x ≤ discWeightedDist c φ x := by
        refine le_discWeightedDist fun v hv => ?_
        have h1 : discDist φ x ≤ ‖x - φ v‖ := discDist_le φ.continuous x hv
        by_cases hvd : dist (φ v) (φ v₀) < δ
        · have h2 : c v₀ - ε / 2 ≤ c v := by linarith [(abs_lt.1 (hloc v hv hvd)).1]
          calc (c v₀ - ε / 2) * discDist φ x ≤ c v * discDist φ x :=
                mul_le_mul_of_nonneg_right h2 hDpos.le
            _ ≤ c v * ‖x - φ v‖ := mul_le_mul_of_nonneg_left h1 (zero_le_one.trans (hc1 v hv))
        · have h3 : 3 * discDist φ x ≤ ‖x - φ v‖ := by
            have h4 := dist_triangle (φ v) x (φ v₀)
            rw [dist_comm (φ v) x, dist_eq_norm x (φ v)] at h4
            linarith [not_lt.1 hvd]
          calc (c v₀ - ε / 2) * discDist φ x ≤ 3 * discDist φ x :=
                mul_le_mul_of_nonneg_right (by linarith [hc3 v₀ hv₀]) hDpos.le
            _ ≤ 1 * ‖x - φ v‖ := by linarith
            _ ≤ c v * ‖x - φ v‖ := mul_le_mul_of_nonneg_right (hc1 v hv) (norm_nonneg _)
      have hlow : c v₀ - ε / 2 ≤ discWeightedDist c φ x / discDist φ x := (le_div_iff₀ hDpos).2 hNlow
      have hup : discWeightedDist c φ x / discDist φ x ≤ c w := (div_le_iff₀ hDpos).2 hNup
      rw [abs_lt]
      constructor
      · linarith
      · linarith [(abs_lt.1 hcw).2]
  · have hD₀ : discDist φ x₀ ≠ 0 := fun h => hx₀ ((discDist_eq_zero_iff φ.continuous).1 h)
    have hev : (fun x => discWeightedDist c φ x / discDist φ x) =ᶠ[𝓝 x₀] dieudonneExt c φ := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hx₀] with x hx
      exact (dieudonneExt_of_notMem hx).symm
    exact (continuousAt_congr hev).1 (((continuous_discWeightedDist_right hc φ.continuous).continuousAt).div
      (continuous_discDist φ.continuous).continuousAt hD₀)

/-- Dieudonné's extension at a point is a Borel function of the map. -/
theorem measurable_dieudonneExt_apply {c : ℂ → ℝ} (hc : Continuous c) (x : ℂ) :
    Measurable fun φ : C(ℂ, ℂ) => dieudonneExt c φ x := by
  have hK : MeasurableSet {φ : C(ℂ, ℂ) | x ∈ φ '' closedBall (0 : ℂ) 1} :=
    (isClosed_setOf_exists_mem_of_isCompact (isCompact_closedBall (0 : ℂ) 1)
      (P := fun (φ : C(ℂ, ℂ)) (v : ℂ) => φ v = x) (isClosed_eq continuous_eval continuous_const)).measurableSet
  unfold dieudonneExt
  exact Measurable.ite hK (hc.measurable.comp (measurable_discInvAt x))
    ((continuous_discWeightedDist_left hc x).measurable.div (continuous_discDist_left x).measurable)

/-! ### The extended inverse -/

theorem neg_one_le_re_of_mem_closedBall {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) 1) : -1 ≤ v.re ∧ v.re ≤ 1 :=
  abs_le.1 ((Complex.abs_re_le_norm v).trans (mem_closedBall_zero_iff.1 hv))

theorem neg_one_le_im_of_mem_closedBall {v : ℂ} (hv : v ∈ closedBall (0 : ℂ) 1) : -1 ≤ v.im ∧ v.im ≤ 1 :=
  abs_le.1 ((Complex.abs_im_le_norm v).trans (mem_closedBall_zero_iff.1 hv))

theorem continuous_re_add_two : Continuous fun v : ℂ => v.re + 2 :=
  Complex.continuous_re.add continuous_const

theorem continuous_im_add_two : Continuous fun v : ℂ => v.im + 2 :=
  Complex.continuous_im.add continuous_const

/-- The extended inverse of `φ`, coordinatewise by Dieudonné's formula with the weights `re + 2` and `im + 2`. -/
noncomputable def discInverseFun (φ : C(ℂ, ℂ)) (x : ℂ) : ℂ :=
  ((dieudonneExt (fun v => v.re + 2) φ x - 2 : ℝ) : ℂ) +
    ((dieudonneExt (fun v => v.im + 2) φ x - 2 : ℝ) : ℂ) * Complex.I

theorem continuous_discInverseFun {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) :
    Continuous (discInverseFun φ) := by
  have hre : Continuous (dieudonneExt (fun v => v.re + 2) φ) :=
    continuous_dieudonneExt continuous_re_add_two
      (fun v hv => by linarith [(neg_one_le_re_of_mem_closedBall hv).1])
      (fun v hv => by linarith [(neg_one_le_re_of_mem_closedBall hv).2]) hφ
  have him : Continuous (dieudonneExt (fun v => v.im + 2) φ) :=
    continuous_dieudonneExt continuous_im_add_two
      (fun v hv => by linarith [(neg_one_le_im_of_mem_closedBall hv).1])
      (fun v hv => by linarith [(neg_one_le_im_of_mem_closedBall hv).2]) hφ
  exact (Complex.continuous_ofReal.comp (hre.sub continuous_const)).add
    ((Complex.continuous_ofReal.comp (him.sub continuous_const)).mul continuous_const)

theorem measurable_discInverseFun_apply (x : ℂ) : Measurable fun φ : C(ℂ, ℂ) => discInverseFun φ x := by
  have h1 := measurable_dieudonneExt_apply continuous_re_add_two x
  have h2 := measurable_dieudonneExt_apply continuous_im_add_two x
  unfold discInverseFun
  exact (Complex.continuous_ofReal.measurable.comp (h1.sub_const 2)).add
    ((Complex.continuous_ofReal.measurable.comp (h2.sub_const 2)).mul_const Complex.I)

open Classical in
/-- **The extended inverse of a map of the closed disc**: for `φ` injective on the closed unit disc, a continuous
map of `ℂ` which inverts `φ` on the closed disc (Dieudonné's extension of `φ⁻¹`); `0` otherwise. -/
noncomputable def discInverseExt (φ : C(ℂ, ℂ)) : C(ℂ, ℂ) :=
  if h : InjOn φ (closedBall 0 1) then ⟨discInverseFun φ, continuous_discInverseFun h⟩ else 0

theorem discInverseExt_apply_of_injOn {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) (x : ℂ) :
    discInverseExt φ x = discInverseFun φ x := by
  rw [discInverseExt, dite_eq_left hφ, ContinuousMap.coe_mk]

theorem discInverseExt_apply_of_not_injOn {φ : C(ℂ, ℂ)} (hφ : ¬InjOn φ (closedBall 0 1)) (x : ℂ) :
    discInverseExt φ x = 0 := by
  rw [discInverseExt, dite_eq_right hφ, ContinuousMap.zero_apply]

/-- The extended inverse inverts `φ` on the closed disc. -/
theorem discInverseExt_apply_image {φ : C(ℂ, ℂ)} (hφ : InjOn φ (closedBall 0 1)) {v : ℂ}
    (hv : v ∈ closedBall (0 : ℂ) 1) : discInverseExt φ (φ v) = v := by
  rw [discInverseExt_apply_of_injOn hφ, discInverseFun, dieudonneExt_apply_image hφ hv,
    dieudonneExt_apply_image hφ hv, add_sub_cancel_right, add_sub_cancel_right]
  exact Complex.re_add_im v

open Classical in
/-- **The extended inverse is a Borel function of the map.** -/
theorem measurable_discInverseExt : Measurable discInverseExt := by
  refine LatticeProb.ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun x => ?_
  have heq : (fun φ : C(ℂ, ℂ) => discInverseExt φ x) =
      fun φ : C(ℂ, ℂ) => if InjOn φ (closedBall 0 1) then discInverseFun φ x else 0 := by
    funext φ
    by_cases h : InjOn φ (closedBall (0 : ℂ) 1)
    · rw [ite_eq_left h, discInverseExt_apply_of_injOn h]
    · rw [ite_eq_right h, discInverseExt_apply_of_not_injOn h]
  rw [heq]
  exact Measurable.ite measurableSet_setOf_injOn_closedBall (measurable_discInverseFun_apply x) measurable_const

/-! ### Inverse charts -/

/-- A continuous left inverse on the closed disc of a conformal map `φ` of the closed disc onto the closure of `U` is
an inverse chart of `U` at `φ 0`. -/
theorem IsDiscMap.isInverseChart_of_leftInvOn {U : Set ℂ} {φ : ℂ → ℂ} (h : IsDiscMap U φ) {ψ : C(ℂ, ℂ)}
    (hψφ : ∀ w ∈ closedBall (0 : ℂ) 1, ψ (φ w) = w) : IsInverseChart U (φ 0) ψ := by
  have hcl := h.image_closedBall
  have hφψ : ∀ y ∈ closure U, φ (ψ y) = y := fun y hy => by
    rw [← hcl] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hψφ w hw]
  have hinj : InjOn φ (ball 0 1) := h.injOn.mono ball_subset_closedBall
  let eU := QuantumZipper.CA.univalentOPH isOpen_ball h.differentiableOn hinj
  have heU : DifferentiableOn ℂ eU.symm (φ '' ball 0 1) :=
    QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball h.differentiableOn hinj
  refine ⟨h.apply_zero_mem, hψφ 0 (mem_closedBall_self zero_le_one), ?_, ?_, ?_, ?_⟩
  · intro y hy y' hy' hyy
    rw [← hφψ y hy, ← hφψ y' hy', hyy]
  · rw [← h.image_ball]
    refine heU.congr fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hψφ w (ball_subset_closedBall hw)]
    exact (QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball h.differentiableOn hinj hw).symm
  · ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w', hw', rfl⟩ := h.image_ball.symm ▸ hy
      rw [hψφ w' (ball_subset_closedBall hw')]
      exact hw'
    · intro hw
      exact ⟨φ w, h.image_ball ▸ mem_image_of_mem φ hw, hψφ w (ball_subset_closedBall hw)⟩
  · ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w', hw', rfl⟩ := h.image_sphere.symm ▸ hy
      rw [hψφ w' (sphere_subset_closedBall hw')]
      exact hw'
    · intro hw
      exact ⟨φ w, h.image_sphere ▸ mem_image_of_mem φ hw, hψφ w (sphere_subset_closedBall hw)⟩

/-- The extended inverse of a normalized conformal map of the closed disc onto the closure of `U` with `φ 0 = z` is an
inverse chart of `U` at `z`. -/
theorem IsNormalizedDiscMap.isInverseChart_discInverseExt {U : Set ℂ} {z : ℂ} {φ : C(ℂ, ℂ)}
    (h : IsNormalizedDiscMap U z φ) : IsInverseChart U z (discInverseExt φ) := by
  have hψ := h.isDiscMap.isInverseChart_of_leftInvOn (ψ := discInverseExt φ)
    (fun _ hw => discInverseExt_apply_image h.isDiscMap.injOn hw)
  rwa [h.apply_zero] at hψ

/-! ### The inverse chart of a window -/

/-- **The inverse chart of the window `(a, u, b)` of the curve `η`**: the extended inverse of the normalized conformal
map `windowDiscMap a u b η` of the window. -/
noncomputable def windowChart (a u b : ℝ) (η : C(ℝ, ℂ)) : C(ℂ, ℂ) :=
  discInverseExt (windowDiscMap a u b η)

/-- **The inverse chart of a window is a Borel function of the curve.** -/
theorem measurable_windowChart (a u b : ℝ) : Measurable (windowChart a u b) :=
  measurable_discInverseExt.comp (measurable_windowDiscMap a u b)

/-- If the window `(a, u, b)` has an inverse chart at `η(u)`, then `windowChart a u b η` is one. -/
theorem isInverseChart_windowChart {a u b : ℝ} {η : C(ℝ, ℂ)} {ψ : C(ℂ, ℂ)}
    (hψ : IsInverseChart (windowDomain η a u b) (η u) ψ) :
    IsInverseChart (windowDomain η a u b) (η u) (windowChart a u b η) :=
  (isNormalizedDiscMap_windowDiscMap hψ).isInverseChart_discInverseExt

/-- The curves whose window `(a, u, b)` has an inverse chart at `η(u)` form a Borel set. -/
theorem measurableSet_setOf_exists_isInverseChart (a u b : ℝ) :
    MeasurableSet {η : C(ℝ, ℂ) | ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ} := by
  have heq : {η : C(ℝ, ℂ) | ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ} =
      (fun η => (η, windowDiscMap a u b η)) ⁻¹' windowDiscMapGraph a u b := by
    ext η
    constructor
    · rintro ⟨ψ, hψ⟩
      exact windowDiscMap_mem (exists_mem_windowDiscMapGraph hψ)
    · intro h
      exact ⟨_, (mem_windowDiscMapGraph.1 h).1.isInverseChart_discInverseExt⟩
  rw [heq]
  exact (measurable_id.prodMk (measurable_windowDiscMap a u b)) (measurableSet_windowDiscMapGraph a u b)

/-! ### The chart input with the normalized inverse charts -/

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit, with the normalized inverse charts).** As `BG20ChartFieldInput`, with the inverse charts of the two windows
given by the Borel choice `windowChart` (the extended inverse of the normalized conformal map of the window), so that
only the kernel `K` of the chart Liouville Brownian motion is existential. For times `a < u < b < a' < u' < b'`:

* almost surely the two windows have inverse charts at the curve points;
* `K` and the chart fields and window chart laws depend measurably on the sample;
* (Lemma 7.20 without the time change; Berestycki (2015), Theorem 1.3) almost surely the chart image of the
  Liouville Brownian law of the field from `η(u)` is `K` of the chart field, and likewise for the second window;
* (Lemma 7.21) the pairs (chart field, window chart law) of the two windows are independent. -/
def BG20NormalizedChartInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure JointSample, IsProbabilityMeasure ν'' →
    (∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∀ a u b a' u' b' : ℝ, a < u → u < b → b < a' → a' < u' → u' < b' →
    ∃ K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ),
      (∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) ∧
      (∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a' u' b') (q.1.2 u') ψ) ∧
      Measurable K ∧ Measurable (fun q : JointSample => windowChartField γ a u b (windowChart a u b q.1.2) q) ∧
      Measurable (fun q : JointSample => windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q) ∧
      Measurable (fun q : JointSample => windowChartLaw a u b (windowChart a u b q.1.2) q) ∧
      Measurable (fun q : JointSample => windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
        K (windowChartField γ a u b (windowChart a u b q.1.2) q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (windowChart a' u' b' q.1.2) q =
        K (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q)) ∧
      IndepFun (fun q : JointSample => (windowChartField γ a u b (windowChart a u b q.1.2) q,
          windowChartLaw a u b (windowChart a u b q.1.2) q))
        (fun q : JointSample => (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q,
          windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q)) ν''

/-- The input with the normalized inverse charts implies `BG20ChartFieldInput` (take `ψ = windowChart`). -/
theorem bg20ChartFieldInput_of_normalizedChart {𝒮 : SpaceFillingSLEModel}
    (hC : BG20NormalizedChartInput 𝒮) : BG20ChartFieldInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  obtain ⟨K, hψ, hψ', hK, hhD, hhD', hm, hm', hb, hb', hind⟩ :=
    hC γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'
  exact ⟨K, fun q => windowChart a u b q.1.2, fun q => windowChart a' u' b' q.1.2,
    hψ.mono fun _ ⟨_, hq⟩ => isInverseChart_windowChart hq,
    hψ'.mono fun _ ⟨_, hq⟩ => isInverseChart_windowChart hq, hK, hhD, hhD', hm, hm', hb, hb', hind⟩

end MatedCRT
