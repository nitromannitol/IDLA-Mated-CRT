import MatedCRT.FirstPass.Derived.ChartFieldInputAssembly

/-!
# The window chart with the normalization of Berestycki–Gwynne

Berestycki–Gwynne (2020), arXiv:2003.10320, Section 7.3, framework of the proof of Lemma 7.18 (used in Lemmas 7.19-7.21),
parametrize the window `(a, u, b)` of the space-filling curve `η` by the unit disc as follows. `U` is the connected
component of the interior of `η([a, b])` containing `η(u)`, "there is a unique time interval `[a', b']` for which
`η([a', b']) = Ū`", and "`φ : 𝔻 → U` is the unique conformal map such that `φ(0) = η(u)` and `φ(1) = η(a')`". The chart
field `h ∘ φ + Q log |φ'|`, the chart image of the curve and the chart image of the stopped walk then depend only on
the curve-decorated quantum surface `(U, h, η|[a', b'], X|[0, T])`.

The inverse chart `windowChart a u b η` of `WindowInverseChart.lean` is normalized by `φ'(0) > 0` instead. This file
defines the inverse chart with the normalization of Berestycki–Gwynne and proves for it the facts used by the
`windowChart` route.

## Main definitions

* `windowStartBG a u b η`: the time `a'`, as the first time `s ∈ [a, u]` with `η([s, u]) ⊆ Ū` (it is the left end of
  the unique interval `[a', b']` with `η([a', b']) = Ū`, `windowStartBG_eq_of_image_Icc_eq`).
* `windowChartBG a u b η`: `windowChart a u b η` followed by the rotation of the unit disc taking the chart image of
  `η(a')` to the positive half-line, hence to `1` when it lies on the unit circle (`windowChartBG_apply_windowStartBG`).
* `IsBorelWindowChart a u b Ψ Φ`: `Ψ` is a Borel choice of inverse charts of the window, inverting the Borel choice `Φ`
  of conformal maps of the closed disc onto the closure of the window.

## Main statements

* `measurable_windowStartBG`, `measurable_windowChartBG`: `a'` and the chart are Borel functions of the curve.
* `measurable_windowChartField_windowChartBG`, `measurable_windowChartLaw_windowChartBG`,
  `measurable_windowLBMChartLaw_windowChartBG`: the chart field, the window chart law and the window chart law of the
  Liouville Brownian law field are measurable functions of the joint-limit sample.
* `ae_jointLimit_isInverseChart_windowChartBG`: under `WindowFrontierJordanInput`, on a joint weak limit `ν''`, almost
  surely `windowChartBG a u b η` is an inverse chart of the window at `η(u)`.
* `BG20ChartIndependenceInputBG`: the independence of the two windows (Berestycki–Gwynne (2020), Lemma 7.21) for the
  charts `windowChartBG`.
* `bg20ChartFieldInput_of_chartFieldLBMLimit_bg`: Lévy's conformal invariance, the coordinate change of Liouville
  Brownian motion, the window geometry and `BG20ChartIndependenceInputBG` give `BG20ChartFieldInput`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-! ### Rotations of inverse charts -/

/-- An inverse chart followed by a rotation of the unit disc is an inverse chart. -/
theorem IsInverseChart.of_apply_eq_mul {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)} (h : IsInverseChart U z ψ) {c : ℂ}
    (hc : ‖c‖ = 1) {ψ' : C(ℂ, ℂ)} (hψ' : ∀ x, ψ' x = c * ψ x) : IsInverseChart U z ψ' := by
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hcomp : ⇑ψ' = (fun w => c * w) ∘ ⇑ψ := funext hψ'
  refine ⟨h.mem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hψ', h.apply_point, mul_zero]
  · intro x hx y hy hxy
    rw [hψ', hψ'] at hxy
    exact h.injOn hx hy (mul_left_cancel₀ hc0 hxy)
  · rw [show (⇑ψ' : ℂ → ℂ) = fun x => c * ψ x from funext hψ']
    exact h.differentiableOn.const_mul c
  · rw [hcomp, image_comp, h.image_eq]
    exact image_mul_eq_of_norm_eq_one hc (fun r => r < 1) fun w => mem_ball_zero_iff
  · rw [hcomp, image_comp, h.image_frontier]
    exact image_mul_eq_of_norm_eq_one hc (fun r => r = 1) fun w => mem_sphere_zero_iff_norm

open Classical in
/-- The unit complex number which rotates `c` onto the positive half-line, `‖c‖ / c` (and `1` for `c = 0`). -/
noncomputable def unitRotation (c : ℂ) : ℂ :=
  if c = 0 then 1 else (‖c‖ : ℂ) * c⁻¹

theorem norm_unitRotation (c : ℂ) : ‖unitRotation c‖ = 1 := by
  unfold unitRotation
  by_cases hc : c = 0
  · rw [ite_eq_left hc, norm_one]
  · rw [ite_eq_right hc, norm_mul, norm_inv, Complex.norm_real, norm_norm,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hc)]

theorem unitRotation_mul_self {c : ℂ} (hc : ‖c‖ = 1) : unitRotation c * c = 1 := by
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  unfold unitRotation
  rw [ite_eq_right hc0, hc, Complex.ofReal_one, one_mul, inv_mul_cancel₀ hc0]

theorem measurable_unitRotation : Measurable unitRotation :=
  Measurable.ite (measurableSet_singleton 0) measurable_const
    ((Complex.measurable_ofReal.comp measurable_norm).mul measurable_inv)

/-- The rotation `(c, ψ) ↦ c ψ` of maps `ℂ → ℂ`, as a continuous map. -/
noncomputable def chartRotate : C(ℂ × C(ℂ, ℂ), C(ℂ, ℂ)) :=
  ContinuousMap.curry ⟨fun p : (ℂ × C(ℂ, ℂ)) × ℂ => p.1.1 * p.1.2 p.2,
    (continuous_fst.comp continuous_fst).mul
      (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))⟩

theorem chartRotate_apply (c : ℂ) (ψ : C(ℂ, ℂ)) (x : ℂ) : chartRotate (c, ψ) x = c * ψ x :=
  rfl

/-- The precomposition `(φ, c) ↦ φ(c ·)` of maps `ℂ → ℂ` with a multiplication, as a continuous map. -/
noncomputable def discPrecompose : C(C(ℂ, ℂ) × ℂ, C(ℂ, ℂ)) :=
  ContinuousMap.curry ⟨fun p : (C(ℂ, ℂ) × ℂ) × ℂ => p.1.1 (p.1.2 * p.2),
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul continuous_snd))⟩

theorem discPrecompose_apply (φ : C(ℂ, ℂ)) (c w : ℂ) : discPrecompose (φ, c) w = φ (c * w) :=
  rfl

/-! ### The time `a'` of Berestycki–Gwynne -/

/-- If the window `(a, u, b)` of `η` has no inverse chart, then its normalized inverse chart is `0`. -/
theorem windowChart_eq_zero_of_not {a u b : ℝ} {η : C(ℝ, ℂ)}
    (hη : ¬∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) : windowChart a u b η = 0 := by
  have hne : ¬∃ φ, (η, φ) ∈ windowDiscMapGraph a u b := by
    rintro ⟨φ, hφ⟩
    exact hη ⟨_, (mem_windowDiscMapGraph.1 hφ).1.isInverseChart_discInverseExt⟩
  have h0 : ¬InjOn ⇑(0 : C(ℂ, ℂ)) (closedBall 0 1) := fun h =>
    zero_ne_one (h (mem_closedBall_self zero_le_one) (mem_closedBall_zero_iff.2 norm_one.le) rfl)
  ext x
  rw [windowChart, windowDiscMap, dite_eq_right hne, discInverseExt_apply_of_not_injOn h0,
    ContinuousMap.zero_apply]

open Classical in
/-- **The time `a'` of Berestycki–Gwynne (2020), arXiv:2003.10320, Section 7.3** (framework of the proof of
Lemma 7.18): "there is a unique time interval `[a', b']` for which `η([a', b']) = Ū`", where `U` is the connected
component of the interior of `η([a, b])` containing `η(u)`. It is defined here as the first time `s ∈ [a, u]` with
`η([s, u]) ⊆ Ū`, which is `a'` whenever `[a', b']` is as printed (`windowStartBG_eq_of_image_Icc_eq`); it is `a` when
the window has no inverse chart. -/
noncomputable def windowStartBG (a u b : ℝ) (η : C(ℝ, ℂ)) : ℝ :=
  if ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ then
    sInf {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)}
  else a

/-- **`windowStartBG` is the time `a'` as printed.** If the window has an inverse chart and `[a', b']` is the unique
interval with `η([a', b']) = Ū`, with `a ≤ a' ≤ u ≤ b'`, then `windowStartBG a u b η = a'`. -/
theorem windowStartBG_eq_of_image_Icc_eq {a u b a' b' : ℝ} {η : C(ℝ, ℂ)}
    (hη : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) (ha : a ≤ a') (hau : a' ≤ u) (hub : u ≤ b')
    (himg : η '' Icc a' b' = closure (windowDomain η a u b))
    (huniq : ∀ s t : ℝ, η '' Icc s t = closure (windowDomain η a u b) → s = a' ∧ t = b') :
    windowStartBG a u b η = a' := by
  rw [windowStartBG, ite_eq_left hη]
  refine IsLeast.csInf_eq ⟨⟨⟨ha, hau⟩, fun t ht => ?_⟩, fun s hs => ?_⟩
  · rw [← himg]
    exact mem_image_of_mem η ⟨ht.1, ht.2.trans hub⟩
  · by_contra hlt
    rw [not_le] at hlt
    have hs' : η '' Icc s b' = closure (windowDomain η a u b) := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        by_cases htu : t ≤ u
        · exact hs.2 t ⟨ht.1, htu⟩
        · rw [← himg]
          exact mem_image_of_mem η ⟨hau.trans (not_le.1 htu).le, ht.2⟩
      · rw [← himg]
        exact image_mono (Icc_subset_Icc hlt.le le_rfl)
    exact absurd (huniq s b' hs').1 hlt.ne

/-- An infimum of an up-closed set of reals as an infimum over the rationals. -/
theorem csInf_eq_iInf_rat {T : Set ℝ} {a u : ℝ} (hT : T ⊆ Icc a u) (huT : u ∈ T)
    (hup : ∀ s ∈ T, ∀ s', s ≤ s' → s' ≤ u → s' ∈ T) {g : ℚ → ℝ}
    (hg₁ : ∀ r : ℚ, (r : ℝ) ∈ T → g r = r) (hg₂ : ∀ r : ℚ, (r : ℝ) ∉ T → g r = u) :
    sInf T = ⨅ r, g r := by
  have hne : T.Nonempty := ⟨u, huT⟩
  have hbdd : BddBelow T := ⟨a, fun s hs => (hT hs).1⟩
  have hge : ∀ r, sInf T ≤ g r := by
    intro r
    by_cases hr : (r : ℝ) ∈ T
    · rw [hg₁ r hr]
      exact csInf_le hbdd hr
    · rw [hg₂ r hr]
      exact csInf_le hbdd huT
  have hle : ∀ r, g r ≤ u := by
    intro r
    by_cases hr : (r : ℝ) ∈ T
    · rw [hg₁ r hr]
      exact (hT hr).2
    · rw [hg₂ r hr]
  have hbddg : BddBelow (range g) := ⟨sInf T, by
    rintro _ ⟨r, rfl⟩
    exact hge r⟩
  refine le_antisymm (le_ciInf hge) (not_lt.1 fun hlt => ?_)
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
  have hqu : (q : ℝ) ≤ u := (hq₂.le.trans (ciInf_le hbddg 0)).trans (hle 0)
  obtain ⟨s, hsT, hsq⟩ := exists_lt_of_csInf_lt hne hq₁
  have hqT : (q : ℝ) ∈ T := hup s hsT q hsq.le hqu
  have h1 := ciInf_le hbddg q
  rw [hg₁ q hqT] at h1
  exact lt_irrefl _ (hq₂.trans_le h1)

open Classical in
/-- The rational approximation of `windowStartBG`: `r` if `r ∈ [a, u]` and `η([r, u])` lies in the image of the closed
disc under the normalized conformal map of the window, and `u` otherwise. -/
noncomputable def windowStartRat (a u b : ℝ) (η : C(ℝ, ℂ)) (r : ℚ) : ℝ :=
  if (r : ℝ) ∈ Icc a u ∧ ∀ t ∈ Icc (r : ℝ) u, η t ∈ windowDiscMap a u b η '' closedBall 0 1 then r else u

/-- The pairs `(φ, η)` with `η([s, u]) ⊆ φ(B̄(0, 1))` form a closed set. -/
theorem isClosed_setOf_forall_Icc_mem_image_closedBall (s u : ℝ) :
    IsClosed {p : C(ℂ, ℂ) × C(ℝ, ℂ) | ∀ t ∈ Icc s u, p.2 t ∈ p.1 '' closedBall 0 1} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_setOf_exists_mem_of_isCompact (isCompact_closedBall (0 : ℂ) 1)
      (P := fun (p : C(ℂ, ℂ) × C(ℝ, ℂ)) (y : ℂ) => p.1 y = p.2 t)
      (isClosed_eq (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
        ((continuous_eval_const t).comp (continuous_snd.comp continuous_fst)))

theorem measurable_windowStartRat (a u b : ℝ) (r : ℚ) :
    Measurable fun η : C(ℝ, ℂ) => windowStartRat a u b η r := by
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  have hp : Measurable fun η : C(ℝ, ℂ) => (windowDiscMap a u b η, η) :=
    (measurable_windowDiscMap a u b).prodMk measurable_id
  have hset : {η : C(ℝ, ℂ) | (r : ℝ) ∈ Icc a u ∧
      ∀ t ∈ Icc (r : ℝ) u, η t ∈ windowDiscMap a u b η '' closedBall 0 1} =
      {_η : C(ℝ, ℂ) | (r : ℝ) ∈ Icc a u} ∩ (fun η : C(ℝ, ℂ) => (windowDiscMap a u b η, η)) ⁻¹'
        {p : C(ℂ, ℂ) × C(ℝ, ℂ) | ∀ t ∈ Icc (r : ℝ) u, p.2 t ∈ p.1 '' closedBall 0 1} := rfl
  have hS : MeasurableSet {η : C(ℝ, ℂ) | (r : ℝ) ∈ Icc a u ∧
      ∀ t ∈ Icc (r : ℝ) u, η t ∈ windowDiscMap a u b η '' closedBall 0 1} := by
    rw [hset]
    exact (MeasurableSet.const _).inter
      (hp (isClosed_setOf_forall_Icc_mem_image_closedBall (r : ℝ) u).measurableSet)
  unfold windowStartRat
  exact Measurable.ite hS measurable_const measurable_const

theorem windowStartBG_eq_iInf {a u b : ℝ} (hau : a ≤ u) {η : C(ℝ, ℂ)}
    (hη : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) :
    windowStartBG a u b η = ⨅ r : ℚ, windowStartRat a u b η r := by
  obtain ⟨ψ, hψ⟩ := hη
  have hcl : windowDiscMap a u b η '' closedBall 0 1 = closure (windowDomain η a u b) :=
    (isNormalizedDiscMap_windowDiscMap hψ).isDiscMap.image_closedBall
  have hP : ∀ r : ℚ, ((r : ℝ) ∈ Icc a u ∧
      ∀ t ∈ Icc (r : ℝ) u, η t ∈ windowDiscMap a u b η '' closedBall 0 1) ↔
      (r : ℝ) ∈ {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)} := fun r => by
    rw [hcl, mem_ofPred_eq]
  have hT : {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)} ⊆ Icc a u :=
    fun s hs => hs.1
  have huT : u ∈ {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)} := by
    refine ⟨⟨hau, le_rfl⟩, fun t ht => ?_⟩
    rw [show t = u from le_antisymm ht.2 ht.1]
    exact subset_closure hψ.mem
  have hup : ∀ s ∈ {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)}, ∀ s', s ≤ s' →
      s' ≤ u → s' ∈ {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)} := by
    intro s hs s' hss' hs'u
    exact ⟨⟨hs.1.1.trans hss', hs'u⟩, fun t ht => hs.2 t ⟨hss'.trans ht.1, ht.2⟩⟩
  rw [windowStartBG, ite_eq_left ⟨ψ, hψ⟩]
  refine csInf_eq_iInf_rat hT huT hup (fun r hr => ?_) (fun r hr => ?_)
  · unfold windowStartRat
    exact ite_eq_left ((hP r).2 hr)
  · unfold windowStartRat
    exact ite_eq_right fun h => hr ((hP r).1 h)

/-- **The time `a'` is a Borel function of the curve.** -/
theorem measurable_windowStartBG (a u b : ℝ) : Measurable (windowStartBG a u b) := by
  classical
  by_cases hau : a ≤ u
  · have heq : windowStartBG a u b = fun η =>
        if ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ then ⨅ r : ℚ, windowStartRat a u b η r
        else a := funext fun η => by
      by_cases hη : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ
      · rw [ite_eq_left hη]
        exact windowStartBG_eq_iInf hau hη
      · rw [ite_eq_right hη, windowStartBG, ite_eq_right hη]
    rw [heq]
    exact Measurable.ite (measurableSet_setOf_exists_isInverseChart a u b)
      (Measurable.iInf fun r => measurable_windowStartRat a u b r) measurable_const
  · have heq : windowStartBG a u b = fun η =>
        if ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ then (0 : ℝ) else a := funext fun η => by
      by_cases hη : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ
      · rw [ite_eq_left hη, windowStartBG, ite_eq_left hη]
        have hempty : {s : ℝ | s ∈ Icc a u ∧ ∀ t ∈ Icc s u, η t ∈ closure (windowDomain η a u b)} = ∅ :=
          eq_empty_of_forall_notMem fun s hs => hau (hs.1.1.trans hs.1.2)
        rw [hempty, Real.sInf_empty]
      · rw [ite_eq_right hη, windowStartBG, ite_eq_right hη]
    rw [heq]
    exact Measurable.ite (measurableSet_setOf_exists_isInverseChart a u b) measurable_const measurable_const

/-! ### The inverse chart with the normalization of Berestycki–Gwynne -/

/-- The rotation of the unit disc taking the chart image `windowChart a u b η (η(a'))` of the point `η(a')` to the
positive half-line. -/
noncomputable def windowRotBG (a u b : ℝ) (η : C(ℝ, ℂ)) : ℂ :=
  unitRotation (windowChart a u b η (η (windowStartBG a u b η)))

theorem norm_windowRotBG (a u b : ℝ) (η : C(ℝ, ℂ)) : ‖windowRotBG a u b η‖ = 1 :=
  norm_unitRotation _

theorem measurable_windowRotBG (a u b : ℝ) : Measurable (windowRotBG a u b) := by
  have h1 : Measurable fun η : C(ℝ, ℂ) => η (windowStartBG a u b η) :=
    (ContinuousEval.continuous_eval (F := C(ℝ, ℂ))).measurable.comp
      (measurable_id.prodMk (measurable_windowStartBG a u b))
  have h2 : Measurable fun η : C(ℝ, ℂ) => windowChart a u b η (η (windowStartBG a u b η)) :=
    (ContinuousEval.continuous_eval (F := C(ℂ, ℂ))).measurable.comp ((measurable_windowChart a u b).prodMk h1)
  exact measurable_unitRotation.comp h2

/-- **The inverse chart of the window `(a, u, b)` with the normalization of Berestycki–Gwynne (2020), Section 7.3**:
the normalized inverse chart `windowChart a u b η` followed by the rotation of the unit disc taking the chart image of
`η(a')` to the positive half-line (to `1` when it lies on the unit circle, the identity when it is `0`). Its inverse
`φ` satisfies `φ(0) = η(u)` and `φ(1) = η(a')`. -/
noncomputable def windowChartBG (a u b : ℝ) (η : C(ℝ, ℂ)) : C(ℂ, ℂ) :=
  chartRotate (windowRotBG a u b η, windowChart a u b η)

theorem windowChartBG_apply (a u b : ℝ) (η : C(ℝ, ℂ)) (x : ℂ) :
    windowChartBG a u b η x = windowRotBG a u b η * windowChart a u b η x :=
  rfl

theorem windowChartBG_eq_smul (a u b : ℝ) (η : C(ℝ, ℂ)) :
    windowChartBG a u b η = windowRotBG a u b η • windowChart a u b η := by
  ext x
  rw [windowChartBG_apply, ContinuousMap.smul_apply, smul_eq_mul]

/-- **The normalization of Berestycki–Gwynne**: if the chart image of `η(a')` lies on the unit circle, then
`windowChartBG a u b η` maps `η(a')` to `1`. -/
theorem windowChartBG_apply_windowStartBG {a u b : ℝ} {η : C(ℝ, ℂ)}
    (h : ‖windowChart a u b η (η (windowStartBG a u b η))‖ = 1) :
    windowChartBG a u b η (η (windowStartBG a u b η)) = 1 := by
  rw [windowChartBG_apply, windowRotBG]
  exact unitRotation_mul_self h

/-- **The inverse chart of Berestycki–Gwynne is a Borel function of the curve.** -/
theorem measurable_windowChartBG (a u b : ℝ) : Measurable (windowChartBG a u b) :=
  chartRotate.continuous.measurable.comp ((measurable_windowRotBG a u b).prodMk (measurable_windowChart a u b))

/-- The conformal map of the closed disc onto the closure of the window with the normalization of Berestycki–Gwynne:
`w ↦ φ(ρ⁻¹ w)` for the normalized conformal map `φ = windowDiscMap a u b η` and the rotation `ρ = windowRotBG a u b η`.
-/
noncomputable def windowDiscMapBG (a u b : ℝ) (η : C(ℝ, ℂ)) : C(ℂ, ℂ) :=
  discPrecompose (windowDiscMap a u b η, (windowRotBG a u b η)⁻¹)

theorem coe_windowDiscMapBG (a u b : ℝ) (η : C(ℝ, ℂ)) :
    ⇑(windowDiscMapBG a u b η) = fun w => windowDiscMap a u b η ((windowRotBG a u b η)⁻¹ * w) :=
  rfl

theorem measurable_windowDiscMapBG (a u b : ℝ) : Measurable (windowDiscMapBG a u b) :=
  discPrecompose.continuous.measurable.comp
    ((measurable_windowDiscMap a u b).prodMk (measurable_windowRotBG a u b).inv)

/-! ### Borel choices of inverse charts of a window -/

/-- **A Borel choice of inverse charts of the window `(a, u, b)`**: `Ψ` and `Φ` are Borel functions of the curve; when
the window has an inverse chart at `η(u)`, `Φ η` is a conformal map of the closed disc onto the closure of the window,
`Ψ η` inverts it on the closed disc and is an inverse chart of the window at `η(u)`; otherwise `Ψ η = 0`. -/
structure IsBorelWindowChart (a u b : ℝ) (Ψ Φ : C(ℝ, ℂ) → C(ℂ, ℂ)) : Prop where
  measurable_chart : Measurable Ψ
  measurable_discMap : Measurable Φ
  isDiscMap : ∀ η : C(ℝ, ℂ), (∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) →
    IsDiscMap (windowDomain η a u b) (Φ η)
  chart_discMap : ∀ η : C(ℝ, ℂ), (∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) →
    ∀ v ∈ closedBall (0 : ℂ) 1, Ψ η (Φ η v) = v
  isInverseChart : ∀ η : C(ℝ, ℂ), (∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) →
    IsInverseChart (windowDomain η a u b) (η u) (Ψ η)
  eq_zero : ∀ η : C(ℝ, ℂ), (¬∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) → Ψ η = 0

/-- **The inverse charts of Berestycki–Gwynne are a Borel choice of inverse charts of the window.** -/
theorem isBorelWindowChart_windowChartBG (a u b : ℝ) :
    IsBorelWindowChart a u b (windowChartBG a u b) (windowDiscMapBG a u b) where
  measurable_chart := measurable_windowChartBG a u b
  measurable_discMap := measurable_windowDiscMapBG a u b
  isDiscMap η hη := by
    obtain ⟨ψ, hψ⟩ := hη
    rw [coe_windowDiscMapBG]
    exact (isNormalizedDiscMap_windowDiscMap hψ).isDiscMap.comp_mul (c := (windowRotBG a u b η)⁻¹)
      (by rw [norm_inv, norm_windowRotBG, inv_one])
  chart_discMap η hη v hv := by
    obtain ⟨ψ, hψ⟩ := hη
    have hρ := norm_windowRotBG a u b η
    have hρ0 : windowRotBG a u b η ≠ 0 := norm_ne_zero_iff.1 (by rw [hρ]; exact one_ne_zero)
    have hw : (windowRotBG a u b η)⁻¹ * v ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, norm_mul, norm_inv, hρ, inv_one, one_mul]
      exact mem_closedBall_zero_iff.1 hv
    have hψφ : windowChart a u b η (windowDiscMap a u b η ((windowRotBG a u b η)⁻¹ * v)) =
        (windowRotBG a u b η)⁻¹ * v :=
      discInverseExt_apply_image (isNormalizedDiscMap_windowDiscMap hψ).isDiscMap.injOn hw
    rw [windowChartBG_apply, coe_windowDiscMapBG, hψφ, mul_inv_cancel_left₀ hρ0]
  isInverseChart η hη := by
    obtain ⟨ψ, hψ⟩ := hη
    exact (isInverseChart_windowChart hψ).of_apply_eq_mul (norm_windowRotBG a u b η) (windowChartBG_apply a u b η)
  eq_zero η hη := by
    ext x
    rw [windowChartBG_apply, windowChart_eq_zero_of_not hη, ContinuousMap.zero_apply, mul_zero]

/-! ### Measurability of the chart field for a Borel choice of inverse charts -/

namespace IsBorelWindowChart

variable {a u b : ℝ} {Ψ Φ : C(ℝ, ℂ) → C(ℂ, ℂ)}

/-- **Membership in the window, read off the conformal map and its inverse chart.** -/
theorem mem_windowDomain_iff (hB : IsBorelWindowChart a u b Ψ Φ) {q : JointSample}
    (hq : q ∈ windowChartSet a u b) (x : ℂ) :
    x ∈ windowDomain q.1.2 a u b ↔ x ∈ Φ q.1.2 '' closedBall 0 1 ∧ ‖Ψ q.1.2 x‖ < 1 := by
  have hφ := hB.isDiscMap q.1.2 hq
  have hψφ := hB.chart_discMap q.1.2 hq
  constructor
  · intro hx
    rw [← hφ.image_ball] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨mem_image_of_mem _ (ball_subset_closedBall hv), ?_⟩
    rw [hψφ v (ball_subset_closedBall hv)]
    exact mem_ball_zero_iff.1 hv
  · rintro ⟨⟨v, hv, rfl⟩, h1⟩
    rw [hψφ v hv] at h1
    rw [← hφ.image_ball]
    exact mem_image_of_mem _ (mem_ball_zero_iff.2 h1)

end IsBorelWindowChart

open Classical in
/-- The transported test function `x ↦ f(ψ x) |ψ'(x)|²` for the inverse chart `ψ = Ψ η` of the window of `q`, with
membership in the window read off the conformal map `Φ η` and `ψ`. -/
noncomputable def borelWindowTestValue (Ψ Φ : C(ℝ, ℂ) → C(ℂ, ℂ)) (f : ℂ → ℝ) (q : JointSample) (x : ℂ) : ℝ :=
  if x ∈ Φ q.1.2 '' closedBall 0 1 ∧ ‖Ψ q.1.2 x‖ < 1 then f (Ψ q.1.2 x) * ‖deriv (Ψ q.1.2) x‖ ^ 2 else 0

theorem measurable_borelWindowTestValue {Ψ Φ : C(ℝ, ℂ) → C(ℂ, ℂ)} (hΨ : Measurable Ψ) (hΦ : Measurable Φ)
    {f : ℂ → ℝ} (hf : Continuous f) (x : ℂ) :
    Measurable fun q : JointSample => borelWindowTestValue Ψ Φ f q x := by
  have hφ : Measurable fun q : JointSample => Φ q.1.2 := hΦ.comp measurable_jointSample_curve
  have hψ : Measurable fun q : JointSample => Ψ q.1.2 := hΨ.comp measurable_jointSample_curve
  have hψx : Measurable fun q : JointSample => Ψ q.1.2 x := (continuous_eval_const x).measurable.comp hψ
  have h1 : MeasurableSet ((fun q : JointSample => Φ q.1.2) ⁻¹'
      {φ : C(ℂ, ℂ) | ∃ v ∈ closedBall (0 : ℂ) 1, φ v = x}) :=
    hφ (isClosed_setOf_exists_mem_of_isCompact (isCompact_closedBall (0 : ℂ) 1)
      (P := fun (φ : C(ℂ, ℂ)) (v : ℂ) => φ v = x) (isClosed_eq continuous_eval continuous_const)).measurableSet
  have h2 : MeasurableSet {q : JointSample | ‖Ψ q.1.2 x‖ < 1} :=
    measurableSet_lt hψx.norm measurable_const
  have hS : MeasurableSet {q : JointSample | x ∈ Φ q.1.2 '' closedBall 0 1 ∧ ‖Ψ q.1.2 x‖ < 1} := h1.inter h2
  have hd : Measurable fun q : JointSample => deriv (Ψ q.1.2) x :=
    (measurable_deriv_with_param (f := fun (ψ : C(ℂ, ℂ)) (z : ℂ) => ψ z) continuous_eval).comp
      (hψ.prodMk measurable_const)
  unfold borelWindowTestValue
  exact Measurable.ite hS ((hf.measurable.comp hψx).mul (hd.norm.pow_const 2)) measurable_const

theorem chartTestFun_windowDomain_eq_zero {a u b : ℝ} {R : ℕ} {q : JointSample}
    (hq : ∀ t ∈ Icc a b, q.1.2 t ∈ closedBall (0 : ℂ) R) (ψ : C(ℂ, ℂ)) (f : ℂ → ℝ) {x : ℂ}
    (hx : x ∉ (closedBallCompacts R : Set ℂ)) :
    chartTestFun (windowDomain q.1.2 a u b) ψ f x = 0 := by
  unfold chartTestFun
  refine indicator_of_notMem (fun hxU => hx ?_) _
  obtain ⟨t, ht, rfl⟩ := windowDomain_subset_image q.1.2 a u b hxU
  exact hq t ht

/-- The log-derivative term `∫ log |φ'| f` of the chart field, for a Borel choice `Φ` of conformal maps, is a
measurable function of the sample. -/
theorem measurable_borelWindowLogDerivIntegral {Φ : C(ℝ, ℂ) → C(ℂ, ℂ)} (hΦ : Measurable Φ)
    (f : 𝓓(unitDiscOpens, ℝ)) :
    Measurable fun q : JointSample => ∫ w, Real.log ‖deriv (Φ q.1.2) w‖ * f w := by
  have hφ : Measurable fun q : JointSample => Φ q.1.2 := hΦ.comp measurable_jointSample_curve
  have hd : Measurable fun p : JointSample × ℂ => deriv (Φ p.1.1.2) p.2 :=
    (measurable_deriv_with_param (f := fun (φ : C(ℂ, ℂ)) (z : ℂ) => φ z) continuous_eval).comp
      ((hφ.comp measurable_fst).prodMk measurable_snd)
  have hj : Measurable fun p : JointSample × ℂ => Real.log ‖deriv (Φ p.1.1.2) p.2‖ * f p.2 :=
    (Real.measurable_log.comp hd.norm).mul (f.contDiff.continuous.measurable.comp measurable_snd)
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

namespace IsBorelWindowChart

variable {a u b : ℝ} {Ψ Φ : C(ℝ, ℂ) → C(ℂ, ℂ)}

theorem chartTestFun_eq_testValue (hB : IsBorelWindowChart a u b Ψ Φ) {q : JointSample}
    (hq : q ∈ windowChartSet a u b) (f : ℂ → ℝ) (x : ℂ) :
    chartTestFun (windowDomain q.1.2 a u b) (Ψ q.1.2) f x = borelWindowTestValue Ψ Φ f q x := by
  unfold chartTestFun borelWindowTestValue
  by_cases hx : x ∈ windowDomain q.1.2 a u b
  · rw [indicator_of_mem hx, ite_eq_left ((hB.mem_windowDomain_iff hq x).1 hx)]
  · rw [indicator_of_notMem hx, ite_eq_right fun h => hx ((hB.mem_windowDomain_iff hq x).2 h)]

open Classical in
/-- **The transported test function `(f ∘ ψ) |ψ'|²`** for the inverse chart `ψ = Ψ η` of the window `(a, u, b)` of
`q`, as an element of `𝓓_{K_R}` when the window has an inverse chart and the curve segment lies in the closed disc
of radius `R` (and `0` otherwise). -/
noncomputable def chartTestK (hB : IsBorelWindowChart a u b Ψ Φ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ)
    (q : JointSample) : 𝓓^{⊤}_{closedBallCompacts R}(ℂ, ℝ) :=
  if hq : q ∈ windowChartSetR a u b R then
    { toFun := chartTestFun (windowDomain q.1.2 a u b) (Ψ q.1.2) f
      contDiff' := contDiff_chartTestFun (hB.isInverseChart q.1.2 hq.1)
        (isOpen_windowDomain _ _ _ _) (isBounded_windowDomain _ _ _ _) f
      zero_on_compl' := fun _ hx => chartTestFun_windowDomain_eq_zero hq.2 _ f hx }
  else 0

open Classical in
theorem chartTestK_apply (hB : IsBorelWindowChart a u b Ψ Φ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ)
    (q : JointSample) (x : ℂ) :
    hB.chartTestK f R q x = if q ∈ windowChartSetR a u b R then borelWindowTestValue Ψ Φ f q x else 0 := by
  by_cases hq : q ∈ windowChartSetR a u b R
  · rw [ite_eq_left hq, ← hB.chartTestFun_eq_testValue hq.1]
    unfold IsBorelWindowChart.chartTestK
    rw [dite_eq_left hq]
    rfl
  · rw [ite_eq_right hq]
    unfold IsBorelWindowChart.chartTestK
    rw [dite_eq_right hq]
    rfl

/-- **The transported test function is a measurable `𝓓_{K_R}`-valued function of the sample.** -/
theorem measurable_chartTestK (hB : IsBorelWindowChart a u b Ψ Φ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) :
    Measurable (hB.chartTestK f R) := by
  classical
  refine (measurable_testK_iff (closedBallCompacts R)).2 fun x => ?_
  have heq : (fun q => hB.chartTestK f R q x) =
      fun q => if q ∈ windowChartSetR a u b R then borelWindowTestValue Ψ Φ f q x else 0 :=
    funext fun q => hB.chartTestK_apply f R q x
  rw [heq]
  exact Measurable.ite (measurableSet_windowChartSetR a u b R)
    (measurable_borelWindowTestValue hB.measurable_chart hB.measurable_discMap f.contDiff.continuous x)
    measurable_const

theorem measurable_chartPairingK (hB : IsBorelWindowChart a u b Ψ Φ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) :
    Measurable fun q : JointSample =>
      LQGMetric.pairJInv ⊤ q.1.1.1 (testKToTestC (closedBallCompacts R) (hB.chartTestK f R q)) :=
  (measurable_distC_apply_testK (closedBallCompacts R)).comp
    ((hB.measurable_chartTestK f R).prodMk measurable_jointSample_field)

/-- On the samples of `windowChartSetR a u b R`, the chart field of the window for the inverse chart `Ψ η` is the
pairing of the field with the transported test function in `𝓓_{K_R}`, plus `Q ∫ log |φ'| f` for `φ = Φ η`. -/
theorem windowChartField_eq (hB : IsBorelWindowChart a u b Ψ Φ) {γ : ℝ} {R : ℕ} {q : JointSample}
    (hq : q ∈ windowChartSetR a u b R) (f : 𝓓(unitDiscOpens, ℝ)) :
    windowChartField γ a u b (Ψ q.1.2) q f =
      LQGMetric.pairJInv ⊤ q.1.1.1 (testKToTestC (closedBallCompacts R) (hB.chartTestK f R q)) +
        MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (Φ q.1.2) w‖ * f w := by
  have hψ := hB.isInverseChart q.1.2 hq.1
  have hc : IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (Ψ q.1.2) ∧
      IsOpen (windowDomain q.1.2 a u b) ∧ Bornology.IsBounded (windowDomain q.1.2 a u b) :=
    ⟨hψ, isOpen_windowDomain _ _ _ _, isBounded_windowDomain _ _ _ _⟩
  have htest : chartTest hc.1 hc.2.1 hc.2.2 f =
      testKToTestC (closedBallCompacts R) (hB.chartTestK f R q) := by
    ext x
    rw [chartTest_apply, testKToTestC_apply]
    unfold IsBorelWindowChart.chartTestK
    rw [dite_eq_left hq]
    rfl
  have hint : ∀ w, Real.log ‖deriv (chartMap (windowDomain q.1.2 a u b) (Ψ q.1.2)) w‖ * f w =
      Real.log ‖deriv (Φ q.1.2) w‖ * f w := by
    intro w
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · rw [deriv_chartMap_eq_of_isDiscMap (hB.isDiscMap q.1.2 hq.1) hψ
        (fun v hv => hB.chart_discMap q.1.2 hq.1 v hv) hw]
    · have hf0 : f w = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (f.tsupport_subset h)
      rw [hf0, mul_zero, mul_zero]
  unfold windowChartField chartFieldPairing
  rw [dite_eq_left hc]
  simp only [htest, integral_congr_ae (Eventually.of_forall hint)]

/-- **The chart field of a window for a Borel choice of inverse charts is measurable, tested against a test
function on the disc.** -/
theorem measurable_windowChartField_apply (hB : IsBorelWindowChart a u b Ψ Φ) (γ : ℝ)
    (f : 𝓓(unitDiscOpens, ℝ)) :
    Measurable fun q : JointSample => windowChartField γ a u b (Ψ q.1.2) q f := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun (R : ℕ) (q : JointSample) =>
      if q ∈ windowChartSetR a u b R then
        LQGMetric.pairJInv ⊤ q.1.1.1 (testKToTestC (closedBallCompacts R) (hB.chartTestK f R q)) +
          MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (Φ q.1.2) w‖ * f w
      else 0)
    (fun R => Measurable.ite (measurableSet_windowChartSetR a u b R)
      ((hB.measurable_chartPairingK f R).add
        ((measurable_borelWindowLogDerivIntegral hB.measurable_discMap f).const_mul _)) measurable_const)
    (tendsto_pi_nhds.2 fun q => ?_)
  by_cases hq : q ∈ windowChartSet a u b
  · obtain ⟨r, hr⟩ := (isCompact_Icc.image q.1.2.continuous).isBounded.subset_closedBall (0 : ℂ)
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈r⌉₊) fun R hR => ?_
    have hqR : q ∈ windowChartSetR a u b R := ⟨hq, fun t ht =>
      closedBall_subset_closedBall ((Nat.le_ceil r).trans (Nat.cast_le.2 hR)) (hr (mem_image_of_mem _ ht))⟩
    rw [ite_eq_left hqR]
    exact (hB.windowChartField_eq hqR f).symm
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun R _ => ?_
    have hc : ¬ (IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (Ψ q.1.2) ∧
        IsOpen (windowDomain q.1.2 a u b) ∧ Bornology.IsBounded (windowDomain q.1.2 a u b)) :=
      fun h => hq ⟨_, h.1⟩
    rw [ite_eq_right fun h => hq h.1]
    unfold windowChartField chartFieldPairing
    rw [dite_eq_right hc]

/-- **The chart field of a window for a Borel choice of inverse charts is a measurable function of the sample.** -/
theorem measurable_windowChartField (hB : IsBorelWindowChart a u b Ψ Φ) (γ : ℝ) :
    Measurable fun q : JointSample => windowChartField γ a u b (Ψ q.1.2) q :=
  measurable_pi_iff.2 fun f => hB.measurable_windowChartField_apply γ f

end IsBorelWindowChart

/-! ### Measurability of the window chart laws for a Borel choice of inverse charts -/

/-- The chart image `ψ ∘ f(· ∧ τ)` of the path `f = p.2` stopped at its exit time `τ` from the window `(a, u, b)` of
the sample `p.1`, for the inverse chart `ψ = Ψ η` of the window. -/
noncomputable def borelWindowStopPath (a u b : ℝ) (Ψ : C(ℝ, ℂ) → C(ℂ, ℂ))
    (p : JointSample × ContinuousPath ℂ) : ContinuousPath ℂ :=
  (Ψ p.1.1.2).comp (p.2.comp (exitClamp (windowExitTime a u b p)))

/-- **The stopped chart path is a measurable function of the sample and the path.** -/
theorem measurable_borelWindowStopPath (a u b : ℝ) {Ψ : C(ℝ, ℂ) → C(ℂ, ℂ)} (hΨ : Measurable Ψ) :
    Measurable (borelWindowStopPath a u b Ψ) := by
  have hτ := measurable_windowExitTime a u b
  have hψ : Measurable fun p : JointSample × ContinuousPath ℂ => Ψ p.1.1.2 :=
    hΨ.comp (measurable_jointSample_curve.comp measurable_fst)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hT : Measurable fun p : JointSample × ContinuousPath ℂ => exitClamp (windowExitTime a u b p) t := by
    simp only [exitClamp_apply]
    exact Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const
      (measurable_const.min (ENNReal.measurable_toNNReal.comp hτ))
  have hf : Measurable fun p : JointSample × ContinuousPath ℂ =>
      p.2 (exitClamp (windowExitTime a u b p) t) :=
    (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp (measurable_snd.prodMk hT)
  exact (ContinuousEval.continuous_eval (F := C(ℂ, ℂ))).measurable.comp (hψ.prodMk hf)

namespace IsBorelWindowChart

variable {a u b : ℝ} {Ψ Φ : C(ℝ, ℂ) → C(ℂ, ℂ)}

theorem borelWindowStopPath_eq (hB : IsBorelWindowChart a u b Ψ Φ) (p : JointSample × ContinuousPath ℂ) :
    borelWindowStopPath a u b Ψ p = chartStopPath (windowDomain p.1.1.2 a u b) (Ψ p.1.1.2) p.2 := by
  by_cases hp : p.1 ∈ windowChartSet a u b
  · rw [borelWindowStopPath, windowExitTime_of_mem hp]
    rfl
  · rw [borelWindowStopPath, chartStopPath, hB.eq_zero p.1.1.2 hp]
    ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.zero_apply]

theorem windowChartLaw_apply (hB : IsBorelWindowChart a u b Ψ Φ) (q : JointSample)
    {s : Set (ContinuousPath ℂ)} (hs : MeasurableSet s) :
    windowChartLaw a u b (Ψ q.1.2) q s =
      windowPointLawKernel u q (Prod.mk q ⁻¹' (borelWindowStopPath a u b Ψ ⁻¹' s)) := by
  have hf : chartStopPath (windowDomain q.1.2 a u b) (Ψ q.1.2) =
      fun f => borelWindowStopPath a u b Ψ (q, f) :=
    funext fun f => (hB.borelWindowStopPath_eq (q, f)).symm
  have hG : Measurable fun f : ContinuousPath ℂ => borelWindowStopPath a u b Ψ (q, f) :=
    (measurable_borelWindowStopPath a u b hB.measurable_chart).comp measurable_prodMk_left
  rw [windowChartLaw, chartLaw, hf, Measure.map_apply hG hs]
  rfl

/-- **The chart law of a window for a Borel choice of inverse charts is a measurable function of the sample.** -/
theorem measurable_windowChartLaw (hB : IsBorelWindowChart a u b Ψ Φ) :
    Measurable fun q : JointSample => windowChartLaw a u b (Ψ q.1.2) q := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  convert Kernel.measurable_kernel_prodMk_left (κ := windowPointLawKernel u)
    (measurable_borelWindowStopPath a u b hB.measurable_chart hs) using 1
  funext q
  exact hB.windowChartLaw_apply q hs

/-- **The chart image of the Liouville Brownian law of a window, for a Borel choice of inverse charts, is a
measurable function of the sample.** -/
theorem measurable_windowLBMChartLaw (hB : IsBorelWindowChart a u b Ψ Φ) (γ : ℝ) :
    Measurable (fun q : JointSample => windowLBMChartLaw γ a u b (Ψ q.1.2) q) := by
  have hg : Measurable fun q : JointSample => ((q.1, lbmPathLawField γ q.1.1.1) : JointSample) :=
    measurable_fst.prodMk ((measurable_lbmPathLawField γ).comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  have h : (fun q : JointSample => windowLBMChartLaw γ a u b (Ψ q.1.2) q) =
      (fun q : JointSample => windowChartLaw a u b (Ψ q.1.2) q) ∘
        fun q : JointSample => ((q.1, lbmPathLawField γ q.1.1.1) : JointSample) := rfl
  rw [h]
  exact hB.measurable_windowChartLaw.comp hg

end IsBorelWindowChart

/-! ### The chart image of Liouville Brownian motion for a Borel choice of inverse charts -/

/-- **The chart image of the rescaled Liouville Brownian law on the joint limit, for any choice of inverse charts.**
As `ae_windowLBMChartLaw_eq_of_chartTransportLimit`, for a map `Ψ` from curves to maps `ℂ → ℂ` such that `Ψ η` is an
inverse chart of the window `(a, u, b)` at `η(u)` whenever the window has one. -/
theorem ae_windowLBMChartLaw_eq_of_chartTransportLimit_of_isInverseChart {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hLevy : LevyConformalChartStmt) {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {K₀ : (𝓓(unitDiscOpens, ℝ) → ℝ) → ProbabilityMeasure (ContinuousPath ℂ)} (hK₀m : Measurable K₀)
    (hK₀ : ∀ᵐ ω ∂S.P, ChartTransportLimit γ K₀ (LQGMetric.pairJ ⊤ (H ω)))
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') {E : Ω → LQGData} (hE : Measurable E)
    {Z : ℕ → Ω → PathLawFamily} {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν'')))
    (a u b : ℝ) {Ψ : C(ℝ, ℂ) → C(ℂ, ℂ)}
    (hΨ : ∀ η : C(ℝ, ℂ), (∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) →
      IsInverseChart (windowDomain η a u b) (η u) (Ψ η))
    (hLm : Measurable fun q : JointSample => windowLBMChartLaw γ a u b (Ψ q.1.2) q)
    (hFm : Measurable fun q : JointSample => windowChartField γ a u b (Ψ q.1.2) q) :
    ∀ᵐ q ∂ν'', (∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) →
      windowLBMChartLaw γ a u b (Ψ q.1.2) q =
        (K₀ (windowChartField γ a u b (Ψ q.1.2) q) : Measure (ContinuousPath ℂ)).map
          (timeScalePath (lbmExitMedian γ).toNNReal) := by
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  set m : ℝ≥0 := (lbmExitMedian γ).toNNReal with hm
  let Data := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)
  have hD : Measurable fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  have hmarg : ν''.map Prod.fst = S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hD hconv
  have hprob : ∀ q : JointSample, IsProbabilityMeasure (windowLBMChartLaw γ a u b (Ψ q.1.2) q) := fun q =>
    (Measure.isProbabilityMeasure_map_iff
      (measurable_chartStopPath _ (isOpen_windowDomain _ _ _ _) _).aemeasurable).2 inferInstance
  have hL' : Measurable fun q : JointSample =>
      (⟨windowLBMChartLaw γ a u b (Ψ q.1.2) q, hprob q⟩ : ProbabilityMeasure (ContinuousPath ℂ)) :=
    hLm.subtype_mk
  have hR' : Measurable fun q : JointSample => timeScaleLaw m (K₀ (windowChartField γ a u b (Ψ q.1.2) q)) :=
    (timeScaleLaw m).continuous.measurable.comp (hK₀m.comp hFm)
  have hEq : ∀ q : JointSample,
      ((⟨windowLBMChartLaw γ a u b (Ψ q.1.2) q, hprob q⟩ : ProbabilityMeasure (ContinuousPath ℂ)) =
          timeScaleLaw m (K₀ (windowChartField γ a u b (Ψ q.1.2) q))) ↔
        windowLBMChartLaw γ a u b (Ψ q.1.2) q =
          (K₀ (windowChartField γ a u b (Ψ q.1.2) q) : Measure (ContinuousPath ℂ)).map (timeScalePath m) := by
    intro q
    constructor
    · intro h
      have h' := congrArg ProbabilityMeasure.toMeasure h
      rw [coe_timeScaleLaw] at h'
      exact h'
    · intro h
      apply ProbabilityMeasure.toMeasure_injective
      rw [coe_timeScaleLaw]
      exact h
  let T : Set JointSample :=
    {q | q.1.2 ∈ {η : C(ℝ, ℂ) | ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ}}ᶜ ∪
      {q | (⟨windowLBMChartLaw γ a u b (Ψ q.1.2) q, hprob q⟩ : ProbabilityMeasure (ContinuousPath ℂ)) =
          timeScaleLaw m (K₀ (windowChartField γ a u b (Ψ q.1.2) q))}
  have hTm : MeasurableSet T :=
    ((measurable_snd.comp measurable_fst) (measurableSet_setOf_exists_isInverseChart a u b)).compl.union
      ((hL'.prodMk hR')
        (isClosed_diagonal : IsClosed (diagonal (ProbabilityMeasure (ContinuousPath ℂ)))).measurableSet)
  let p₀ : PathLawFamily :=
    ContinuousMap.const ℂ ⟨Measure.dirac (0 : ContinuousPath ℂ), inferInstance⟩
  let T' : Set Data := (fun d : Data => ((d, p₀) : JointSample)) ⁻¹' T
  have hT'm : MeasurableSet T' := (measurable_id.prodMk measurable_const) hTm
  have hω : ∀ᵐ ω ∂S.P, (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) ∈ T' := by
    filter_upwards [ae_chartLaw_lbmPathLawField_eq_of_chartTransportLimit hγ hγ2 hS hLevy hH hrep hK₀]
      with ω hω
    by_cases hIC : ∃ ψ, IsInverseChart (windowDomain (η' ω) a u b) (η' ω u) ψ
    · right
      exact (hEq _).2 (hω (windowDomain (η' ω) a u b) (η' ω u) (Ψ (η' ω))
        (isOpen_windowDomain _ _ _ _) (isBounded_windowDomain _ _ _ _) (hΨ (η' ω) hIC))
    · left
      exact hIC
  have hdata : ∀ᵐ d ∂(S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data)), d ∈ T' :=
    (ae_map_iff hD.aemeasurable hT'm).2 hω
  rw [← hmarg] at hdata
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdata] with q hq hIC
  rcases hq with h | h
  · exact absurd hIC h
  · exact (hEq (q.1, p₀)).1 h

/-- **The kernel of the chart image of Liouville Brownian motion, for every choice of inverse charts.** As
`exists_kernel_ae_windowLBMChartLaw_eq`, with one Borel kernel `K` serving every map `Ψ` from curves to maps `ℂ → ℂ`
such that `Ψ η` is an inverse chart of the window `(a, u, b)` at `η(u)` whenever the window has one. -/
theorem exists_kernel_ae_windowLBMChartLaw_eq_of_isInverseChart (hLevy : LevyConformalChartStmt) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hgap : ChartFieldLBMLimitStmt γ) :
    ∃ K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ), Measurable K ∧
      ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → ∀ E : Ω → LQGData, Measurable E →
      ∀ (Z : ℕ → Ω → PathLawFamily) (ν'' : Measure JointSample), IsProbabilityMeasure ν'' →
      (∀ f : JointSample →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
          (𝓝 (∫ q, f q ∂ν''))) →
      ∀ (a u b : ℝ) (Ψ : C(ℝ, ℂ) → C(ℂ, ℂ)),
      (∀ η : C(ℝ, ℂ), (∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) →
        IsInverseChart (windowDomain η a u b) (η u) (Ψ η)) →
      Measurable (fun q : JointSample => windowLBMChartLaw γ a u b (Ψ q.1.2) q) →
      Measurable (fun q : JointSample => windowChartField γ a u b (Ψ q.1.2) q) →
      ∀ᵐ q ∂ν'', (∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) →
        windowLBMChartLaw γ a u b (Ψ q.1.2) q = K (windowChartField γ a u b (Ψ q.1.2) q) := by
  obtain ⟨K₀, hK₀m, hK₀⟩ := hgap
  refine ⟨fun g => (K₀ g : Measure (ContinuousPath ℂ)).map (timeScalePath (lbmExitMedian γ).toNNReal), ?_, ?_⟩
  · have h : (fun g => (K₀ g : Measure (ContinuousPath ℂ)).map (timeScalePath (lbmExitMedian γ).toNNReal)) =
        fun g => ((timeScaleLaw (lbmExitMedian γ).toNNReal (K₀ g) : ProbabilityMeasure (ContinuousPath ℂ)) :
          Measure (ContinuousPath ℂ)) :=
      funext fun g => (coe_timeScaleLaw _ _).symm
    rw [h]
    exact measurable_subtype_coe.comp ((timeScaleLaw _).continuous.measurable.comp hK₀m)
  · intro 𝒮 Ω _ S hS H hH hrep η' hη' E hE Z ν'' hν'' hconv a u b Ψ hΨ hLm hFm
    exact ae_windowLBMChartLaw_eq_of_chartTransportLimit_of_isInverseChart hγ hγ2 hS hLevy hH hrep hK₀m
      (hK₀ 𝒮 Ω S hS H hH hrep) hη' hE hconv a u b hΨ hLm hFm

/-! ### The facts of the `windowChart` route for `windowChartBG` -/

/-- **The chart field of a window for the inverse chart of Berestycki–Gwynne is a measurable function of the
sample.** -/
theorem measurable_windowChartField_windowChartBG (γ a u b : ℝ) :
    Measurable fun q : JointSample => windowChartField γ a u b (windowChartBG a u b q.1.2) q :=
  (isBorelWindowChart_windowChartBG a u b).measurable_windowChartField γ

/-- **The chart law of a window for the inverse chart of Berestycki–Gwynne is a measurable function of the
sample.** -/
theorem measurable_windowChartLaw_windowChartBG (a u b : ℝ) :
    Measurable fun q : JointSample => windowChartLaw a u b (windowChartBG a u b q.1.2) q :=
  (isBorelWindowChart_windowChartBG a u b).measurable_windowChartLaw

/-- **The chart image of the Liouville Brownian law of a window, for the inverse chart of Berestycki–Gwynne, is a
measurable function of the sample.** -/
theorem measurable_windowLBMChartLaw_windowChartBG (γ a u b : ℝ) :
    Measurable (fun q : JointSample => windowLBMChartLaw γ a u b (windowChartBG a u b q.1.2) q) :=
  (isBorelWindowChart_windowChartBG a u b).measurable_windowLBMChartLaw γ

/-- **The inverse chart of Berestycki–Gwynne on the joint limit.** Under `WindowFrontierJordanInput 𝒮`, on a weak
limit `ν''` of the joint laws of the field coordinates, a measurable coordinate `E`, a version `η'` of the curve and a
sequence of path-law families, for fixed times `a < u < b`, for `ν''`-almost every sample `windowChartBG a u b η` is
an inverse chart of the window `(a, u, b)` at `η(u)`. -/
theorem ae_jointLimit_isInverseChart_windowChartBG {𝒮 : SpaceFillingSLEModel}
    (hG : WindowFrontierJordanInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν''))) {a u b : ℝ} (hau : a < u) (hub : u < b) :
    ∀ᵐ q ∂ν'', IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (windowChartBG a u b q.1.2) := by
  filter_upwards [ae_jointLimit_exists_isInverseChart_windowDomain hG hγ hγ2 hS hη' hae hH hE hconv hau hub]
    with q hq
  exact (isBorelWindowChart_windowChartBG a u b).isInverseChart q.1.2 hq

/-! ### The chart input with the inverse charts of Berestycki–Gwynne -/

/-- **Literature input (Berestycki–Gwynne (2020), arXiv:2003.10320, Lemma 7.21, on the joint limit, with the
normalization of Section 7.3).** PENDING TRUTH CHECK.

In the setting of `BG20NormalizedChartCoreInput`: let `ν''` be a weak limit of the joint laws of the field
coordinates, a measurable coordinate `E`, a version `η'` of the curve and the interpolated walk law, which is almost
surely a linear time change of the Liouville Brownian law field. For times `a < u < b < a' < u' < b'`, the pairs
(chart field, window chart law) of the two windows `(a, u, b)` and `(a', u', b')` are independent under `ν''`, for the
inverse charts `windowChartBG` of Berestycki–Gwynne: the inverse of the conformal map `φ : 𝔻 → U` with `φ(0) = η(u)`
and `φ(1) = η(a'')`, where `[a'', b'']` is the time interval with `η([a'', b'']) = Ū`. -/
def BG20ChartIndependenceInputBG (𝒮 : SpaceFillingSLEModel) : Prop :=
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
      IndepFun (fun q : JointSample => (windowChartField γ a u b (windowChartBG a u b q.1.2) q,
          windowChartLaw a u b (windowChartBG a u b q.1.2) q))
        (fun q : JointSample => (windowChartField γ a' u' b' (windowChartBG a' u' b' q.1.2) q,
          windowChartLaw a' u' b' (windowChartBG a' u' b' q.1.2) q)) ν''

/-- **The chart input of the joint limit with the inverse charts of Berestycki–Gwynne** (`BG20ChartFieldInput`) from
Lévy's conformal invariance, the coordinate change of Liouville Brownian motion (Berestycki (2015), Theorem 1.3), the
window geometry (Miller–Sheffield, *Imaginary geometry IV*) and the independence of the windows for the inverse charts
`windowChartBG` (Berestycki–Gwynne (2020), Lemma 7.21). The inverse charts of `BG20ChartFieldInput` are
`windowChartBG a u b η` and `windowChartBG a' u' b' η`, and the Borel kernel `K` of
`exists_kernel_ae_windowLBMChartLaw_eq_of_isInverseChart` serves both windows. -/
theorem bg20ChartFieldInput_of_chartFieldLBMLimit_bg {𝒮 : SpaceFillingSLEModel}
    (hLevy : LevyConformalChartStmt) (hgap : ∀ γ, 0 < γ → γ < 2 → ChartFieldLBMLimitStmt γ)
    (hG : WindowFrontierJordanInput 𝒮) (hI : BG20ChartIndependenceInputBG 𝒮) : BG20ChartFieldInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  have := hν''
  obtain ⟨K, hKm, hK⟩ := exists_kernel_ae_windowLBMChartLaw_eq_of_isInverseChart hLevy hγ hγ2 (hgap γ hγ hγ2)
  have hlaw : ∀ {s t r : ℝ}, s < t → t < r →
      ∀ᵐ q ∂ν'', windowLBMChartLaw γ s t r (windowChartBG s t r q.1.2) q =
        K (windowChartField γ s t r (windowChartBG s t r q.1.2) q) := by
    intro s t r hst htr
    filter_upwards [hK 𝒮 Ω S hS H hH hrep η' hη' E hE (fun n ω => interpWalkLaw S η' (ε n) ω) ν'' hν''
        hconv s t r (windowChartBG s t r) (isBorelWindowChart_windowChartBG s t r).isInverseChart
        (measurable_windowLBMChartLaw_windowChartBG γ s t r)
        (measurable_windowChartField_windowChartBG γ s t r),
      ae_jointLimit_exists_isInverseChart_windowDomain hG hγ hγ2 hS hη' hae hH hE
        (Z := fun n ω => interpWalkLaw S η' (ε n) ω) hconv hst htr] with q hq hψ
    exact hq hψ
  exact ⟨K, fun q => windowChartBG a u b q.1.2, fun q => windowChartBG a' u' b' q.1.2,
    ae_jointLimit_isInverseChart_windowChartBG hG hγ hγ2 hS hη' hae hH hE
      (Z := fun n ω => interpWalkLaw S η' (ε n) ω) hconv hau hub,
    ae_jointLimit_isInverseChart_windowChartBG hG hγ hγ2 hS hη' hae hH hE
      (Z := fun n ω => interpWalkLaw S η' (ε n) ω) hconv ha'u' hu'b',
    hKm, measurable_windowChartField_windowChartBG γ a u b, measurable_windowChartField_windowChartBG γ a' u' b',
    measurable_windowChartLaw_windowChartBG a u b, measurable_windowChartLaw_windowChartBG a' u' b',
    hlaw hau hub, hlaw ha'u' hu'b',
    hI γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'⟩

end MatedCRT
