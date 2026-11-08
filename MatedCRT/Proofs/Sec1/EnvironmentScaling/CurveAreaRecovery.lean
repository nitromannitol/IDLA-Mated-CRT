import MatedCRT.Proofs.Sec1.EnvironmentScaling.AreaScaling

/-!
# Deterministic area parametrization and measurable inversion

The interval identities are the pointwise hypotheses supplied by `areaParam`
in Leonardo Bonanno's `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`.
They implement the signed inverse formula of `env-steps.tex`, lines 749–765.
The measure itself can be supplied by the existing field-pairing recovery;
no field-to-curve map is assumed here.
-/

noncomputable section

open MeasureTheory Set

namespace MatedCRT.Sec1

/-- Transport an interval under the rooted order reparametrization. -/
theorem curve_image_interval_reparam (L η : ℝ → ℂ) (v : ℝ ≃o ℝ)
    (hη : ∀ t, η t = L (v t)) (a b : ℝ) :
    η '' Icc a b = L '' Icc (v a) (v b) := by
  have heq : η = L ∘ v := funext hη
  rw [heq, Set.image_comp, v.image_Icc]

/-- The inverse clock is the signed area of the reference curve segment.
The all-endpoints mass condition is exactly the one in `areaParam`. -/
theorem inverse_area_clock (μ : Measure ℂ) (L η : ℝ → ℂ) (v : ℝ ≃o ℝ)
    (hv : v 0 = 0) (hη : ∀ t, η t = L (v t))
    (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) :
    ∀ u : ℝ, v.symm u = if 0 ≤ u then (μ (L '' Icc 0 u)).toReal
      else -(μ (L '' Icc u 0)).toReal := by
  intro u
  have hv0 : v.symm 0 = 0 := by
    apply v.injective
    simpa only [OrderIso.apply_symm_apply] using hv.symm
  by_cases hu : 0 ≤ u
  · have hs : 0 ≤ v.symm u := by
      simpa only [hv0] using v.symm.monotone hu
    have hm := harea 0 (v.symm u) hs
    rw [curve_image_interval_reparam L η v hη, hv, OrderIso.apply_symm_apply] at hm
    rw [ite_eq_left hu, hm, sub_zero, ENNReal.toReal_ofReal hs]
  · have hs : v.symm u ≤ 0 := by
      simpa only [hv0] using v.symm.monotone (le_of_not_ge hu)
    have hm := harea (v.symm u) 0 hs
    rw [curve_image_interval_reparam L η v hη, hv, OrderIso.apply_symm_apply] at hm
    rw [ite_eq_right hu, hm, ENNReal.toReal_ofReal (sub_nonneg.mpr hs)]
    ring

/-- The rooted increasing clock is uniquely determined by area and ordered curve. -/
theorem area_clock_unique (μ : Measure ℂ) (L η₁ η₂ : ℝ → ℂ) (v₁ v₂ : ℝ ≃o ℝ)
    (hv₁ : v₁ 0 = 0) (hv₂ : v₂ 0 = 0)
    (hη₁ : ∀ t, η₁ t = L (v₁ t)) (hη₂ : ∀ t, η₂ t = L (v₂ t))
    (harea₁ : ∀ s t : ℝ, s ≤ t → μ (η₁ '' Icc s t) = ENNReal.ofReal (t - s))
    (harea₂ : ∀ s t : ℝ, s ≤ t → μ (η₂ '' Icc s t) = ENNReal.ofReal (t - s)) :
    v₁ = v₂ ∧ η₁ = η₂ := by
  have heq : v₁.symm = v₂.symm := by
    ext u
    rw [inverse_area_clock μ L η₁ v₁ hv₁ hη₁ harea₁ u,
      inverse_area_clock μ L η₂ v₂ hv₂ hη₂ harea₂ u]
  have hv : v₁ = v₂ := by
    have := congrArg OrderIso.symm heq
    simpa only [OrderIso.symm_symm] using this
  refine ⟨hv, funext fun t => ?_⟩
  rw [hη₁, hη₂, hv]

/-- Inversion of a measurable family of increasing order isomorphisms is
measurable jointly in the parameter and the target time. It suffices to know
measurability at rational input times. -/
theorem measurable_orderIso_inverse {Ω : Type} [MeasurableSpace Ω]
    (v : Ω → ℝ ≃o ℝ) (t : Ω → ℝ) (ht : Measurable t)
    (hv : ∀ q : ℚ, Measurable (fun ω => v ω q)) :
    Measurable (fun ω => (v ω).symm (t ω)) := by
  apply measurable_of_Iio
  intro x
  have hset : {ω | (v ω).symm (t ω) < x} =
      ⋃ q : {q : ℚ // (q : ℝ) < x}, {ω | t ω < v ω q.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨q, hq, hqx⟩ := exists_rat_btwn h
      refine ⟨⟨q, hqx⟩, ?_⟩
      have hh := (v ω).strictMono hq
      simpa only [OrderIso.apply_symm_apply] using hh
    · rintro ⟨q, hq⟩
      have h : (v ω).symm (t ω) < (q.1 : ℝ) := by
        simpa only [OrderIso.symm_apply_apply] using (v ω).symm.strictMono hq
      exact lt_trans h q.2
  change MeasurableSet {ω | (v ω).symm (t ω) < x}
  rw [hset]
  exact MeasurableSet.iUnion fun q => measurableSet_lt ht (hv q.1)

/-- Measurable segment masses recover the clock at a measurable time. The
segment-mass hypotheses are the remaining compact-image measurability
interface; no measurable clock is assumed. -/
theorem measurable_area_clock {Ω : Type} [MeasurableSpace Ω]
    (μ : Ω → Measure ℂ) (L η : Ω → ℝ → ℂ) (v : Ω → ℝ ≃o ℝ)
    (hv0 : ∀ ω, v ω 0 = 0) (hη : ∀ ω t, η ω t = L ω (v ω t))
    (harea : ∀ ω s t, s ≤ t →
      μ ω (η ω '' Icc s t) = ENNReal.ofReal (t - s))
    (hpos : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc 0 q)).toReal))
    (hneg : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc q 0)).toReal))
    (t : Ω → ℝ) (ht : Measurable t) : Measurable (fun ω => v ω (t ω)) := by
  have hclock : ∀ q : ℚ, Measurable (fun ω => (v ω).symm q) := by
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · have heq : (fun ω => (v ω).symm (q : ℝ)) =
          (fun ω => (μ ω (L ω '' Icc 0 q)).toReal) := by
        funext ω
        simpa only [ite_eq_left hq] using
          inverse_area_clock (μ ω) (L ω) (η ω) (v ω) (hv0 ω) (hη ω) (harea ω) q
      rw [heq]
      exact hpos q
    · have heq : (fun ω => (v ω).symm (q : ℝ)) =
          (fun ω => -(μ ω (L ω '' Icc q 0)).toReal) := by
        funext ω
        simpa only [ite_eq_right hq] using
          inverse_area_clock (μ ω) (L ω) (η ω) (v ω) (hv0 ω) (hη ω) (harea ω) q
      rw [heq]
      exact (hneg q).neg
  simpa only [OrderIso.symm_symm] using
    measurable_orderIso_inverse (fun ω => (v ω).symm) t ht hclock

/-- Measurable segment masses and a jointly measurable reference curve give
measurability of the area-parametrized curve at any measurable time. -/
theorem measurable_area_parametrized_curve {Ω : Type} [MeasurableSpace Ω]
    (μ : Ω → Measure ℂ) (L η : Ω → ℝ → ℂ) (v : Ω → ℝ ≃o ℝ)
    (hv0 : ∀ ω, v ω 0 = 0) (hη : ∀ ω t, η ω t = L ω (v ω t))
    (harea : ∀ ω s t, s ≤ t →
      μ ω (η ω '' Icc s t) = ENNReal.ofReal (t - s))
    (hpos : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc 0 q)).toReal))
    (hneg : ∀ q : ℚ, Measurable (fun ω => (μ ω (L ω '' Icc q 0)).toReal))
    (hL : Measurable (fun p : Ω × ℝ => L p.1 p.2))
    (t : Ω → ℝ) (ht : Measurable t) : Measurable (fun ω => η ω (t ω)) := by
  have hv := measurable_area_clock μ L η v hv0 hη harea hpos hneg t ht
  have hfun : (fun ω => η ω (t ω)) = (fun ω => L ω (v ω (t ω))) :=
    funext fun ω => hη ω (t ω)
  rw [hfun]
  exact hL.comp (measurable_id.prodMk hv)

/-- The existing field-pairing decoder supplies Borel interval masses for
any fixed continuous reference curve. The decoder also recovers the area
measure of every valid environment almost surely. -/
theorem exists_fieldCode_measure_fixed_curve_masses (γ : ℝ) :
    ∃ M : FieldPairingCode → Measure ℂ, Measurable M ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
        {𝒮 : SpaceFillingSLEModel}, S.IsValid 𝒮 γ →
        ∀ᵐ ω ∂S.P, M (fieldPairingCode S ω) = S.μ ω) ∧
      (∀ (L : ℝ → ℂ), Continuous L → ∀ a b : ℝ,
        Measurable (fun F => (M F (L '' Icc a b)).toReal)) := by
  obtain ⟨M, hM, hrec⟩ := exists_measurable_fieldCode_lqgMeasure γ
  refine ⟨M, hM, hrec, ?_⟩
  intro L hL a b
  have hK : MeasurableSet (L '' Icc a b) := (isCompact_Icc.image hL).measurableSet
  exact ((Measure.measurable_coe hK).comp hM).ennreal_toReal

end MatedCRT.Sec1
