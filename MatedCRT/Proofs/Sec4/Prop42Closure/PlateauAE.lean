import MatedCRT.Proofs.Sec4.Prop42Closure.HalfBallPlateau

/-! # Plateau probabilities under almost-everywhere measurable radii (closure of Proposition 4.2)

`plateau_measure_zero` (`HalfBallPlateau.lean`) needs the radii at positive rational times to be measurable for every
outcome. This file proves the almost-everywhere version of `plateau_measure_zero`: if the radii `R_q` (`q` a positive rational) are almost everywhere measurable and the scale invariance
of fact (1) holds, then `P[r ∈ plateau] = 0` for every `r > 0`.

Proof: replace each radius by a measurable version `R'_q =ᵐ R_q` (countably many `q`, `ae_all_iff`); the plateau sets
of `R` and `R'` agree almost surely; then the Tonelli argument of draft lines 264-268 applies to the measurable set of
plateau pairs of `R'`. The Tonelli step is stated for an arbitrary measurable set of pairs with countable `ω`-sections. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory
open scoped ENNReal

/-- The plateau values of a family of radii `R : ℚ → Ω → ℝ` at the outcome `ω`: the positive radii attained at two
positive rational times `s < t` (the radius form of `plateauValues`, draft lines 237-242). -/
def plateauValuesOf {Ω : Type} (R : ℚ → Ω → ℝ) (ω : Ω) : Set ℝ :=
  {r | 0 < r ∧ ∃ s t : ℚ, 0 < (s : ℝ) ∧ (s : ℝ) < t ∧ R s ω = r ∧ R t ω = r}

/-- The plateau values of a family of radii are countable (draft line 243). -/
theorem plateauValuesOf_countable {Ω : Type} (R : ℚ → Ω → ℝ) (ω : Ω) :
    (plateauValuesOf R ω).Countable := by
  refine (Set.countable_range fun s : ℚ => R s ω).mono (fun r hr => ?_)
  obtain ⟨-, s, -, -, -, hs, -⟩ := hr
  exact ⟨s, hs⟩

/-- The plateau values of two families agree at `ω` when the radii agree at the positive rational times. -/
theorem plateauValuesOf_congr {Ω : Type} {R R' : ℚ → Ω → ℝ} {ω : Ω}
    (h : ∀ q : ℚ, 0 < (q : ℝ) → R q ω = R' q ω) : plateauValuesOf R ω = plateauValuesOf R' ω := by
  ext r
  constructor
  · rintro ⟨hr, s, t, hs, hst, hsr, htr⟩
    refine ⟨hr, s, t, hs, hst, ?_, ?_⟩
    · rw [← h s hs]
      exact hsr
    · rw [← h t (hs.trans hst)]
      exact htr
  · rintro ⟨hr, s, t, hs, hst, hsr, htr⟩
    refine ⟨hr, s, t, hs, hst, ?_, ?_⟩
    · rw [h s hs]
      exact hsr
    · rw [h t (hs.trans hst)]
      exact htr

/-- The set of plateau pairs of a radius family is measurable when the radii at positive rational times are. -/
theorem measurableSet_plateauPairsOf {Ω : Type} [MeasurableSpace Ω] (R : ℚ → Ω → ℝ)
    (hR : ∀ q : ℚ, 0 < (q : ℝ) → Measurable (R q)) :
    MeasurableSet {p : Ω × ℝ | p.2 ∈ plateauValuesOf R p.1} := by
  have hpair : ∀ s t : ℚ, MeasurableSet {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
      R s p.1 = p.2 ∧ R t p.1 = p.2} := by
    intro s t
    by_cases h : 0 < (s : ℝ) ∧ (s : ℝ) < t
    · have hs : Measurable (R s) := hR s h.1
      have ht : Measurable (R t) := hR t (h.1.trans h.2)
      have hsm : MeasurableSet {p : Ω × ℝ | R s p.1 = p.2} :=
        measurableSet_eq_fun (hs.comp measurable_fst) measurable_snd
      have htm : MeasurableSet {p : Ω × ℝ | R t p.1 = p.2} :=
        measurableSet_eq_fun (ht.comp measurable_fst) measurable_snd
      have hpos : MeasurableSet {p : Ω × ℝ | 0 < p.2} :=
        measurableSet_lt measurable_const measurable_snd
      have hset : {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧ R s p.1 = p.2 ∧ R t p.1 = p.2} =
          {p : Ω × ℝ | 0 < p.2} ∩ {p : Ω × ℝ | R s p.1 = p.2} ∩ {p : Ω × ℝ | R t p.1 = p.2} := by
        ext p
        constructor
        · rintro ⟨h1, -, -, h2, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h.1, h.2, h2, h3⟩
      rw [hset]
      exact (hpos.inter hsm).inter htm
    · have hempty : {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧ R s p.1 = p.2 ∧ R t p.1 = p.2} = ∅ := by
        ext p
        constructor
        · rintro ⟨-, h1, h2, -, -⟩
          exact absurd ⟨h1, h2⟩ h
        · intro hp
          exact absurd hp (Set.notMem_empty p)
      rw [hempty]
      exact MeasurableSet.empty
  have heq : {p : Ω × ℝ | p.2 ∈ plateauValuesOf R p.1} =
      ⋃ (s : ℚ) (t : ℚ), {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
        R s p.1 = p.2 ∧ R t p.1 = p.2} := by
    ext p
    simp only [plateauValuesOf, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hp, s, t, hs, hst, hsr, htr⟩
      exact ⟨s, t, hp, hs, hst, hsr, htr⟩
    · rintro ⟨s, t, hp, hs, hst, hsr, htr⟩
      exact ⟨hp, s, t, hs, hst, hsr, htr⟩
  rw [heq]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun t => hpair s t

/-- **Tonelli step** (draft lines 264-268). For a measurable set `T` of pairs with countable `ω`-sections, whose
`r`-sections have scale-invariant measure, the measure of each `r`-section vanishes for `r > 0`. -/
theorem measure_section_zero_of_tonelli {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (T : Set (Ω × ℝ)) (hT : MeasurableSet T) (hcount : ∀ ω : Ω, {r : ℝ | (ω, r) ∈ T}.Countable)
    (hscale : ∀ a r : ℝ, 0 < a → 0 < r → P {ω | (ω, r) ∈ T} = P {ω | (ω, a * r) ∈ T}) :
    ∀ r : ℝ, 0 < r → P {ω | (ω, r) ∈ T} = 0 := by
  have hsec : ∀ r : ℝ, MeasurableSet {ω | (ω, r) ∈ T} := fun r =>
    hT.preimage (measurable_id.prodMk measurable_const)
  have hconst : ∀ r : ℝ, 0 < r → P {ω | (ω, r) ∈ T} = P {ω | (ω, (1 : ℝ)) ∈ T} := by
    intro r hr
    have h := hscale (1 / r) r (by positivity) hr
    rw [one_div, inv_mul_cancel₀ hr.ne'] at h
    exact h
  have hmeasT : Measurable (T.indicator (1 : Ω × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator hT
  have hfun : ∀ r : ℝ, P {ω | (ω, r) ∈ T} =
      ∫⁻ ω, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P := by
    intro r
    exact (lintegral_indicator_one (hsec r)).symm.trans rfl
  have hswap : ∫⁻ r in Icc (1 : ℝ) 2, (∫⁻ ω, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P)
      = ∫⁻ ω, (∫⁻ r in Icc (1 : ℝ) 2, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r)) ∂P := by
    refine lintegral_lintegral_swap ?_
    exact (hmeasT.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
  have hinner : ∀ ω : Ω, ∫⁻ r in Icc (1 : ℝ) 2, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) = 0 := by
    intro ω
    have hind : ∀ r : ℝ, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) =
        ({r' : ℝ | (ω, r') ∈ T}).indicator (1 : ℝ → ℝ≥0∞) r := by
      intro r
      by_cases h : (ω, r) ∈ T <;> simp [Set.indicator, h]
    simp only [hind]
    rw [lintegral_indicator_one (hcount ω).measurableSet]
    exact (hcount ω).measure_zero _
  have hzero : ∫⁻ ω, (∫⁻ r in Icc (1 : ℝ) 2, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r)) ∂P = 0 := by
    simp only [hinner, lintegral_zero]
  have hleft : ∫⁻ r in Icc (1 : ℝ) 2, P {ω | (ω, r) ∈ T} = P {ω | (ω, (1 : ℝ)) ∈ T} := by
    have hcongr : ∫⁻ r in Icc (1 : ℝ) 2, P {ω | (ω, r) ∈ T} =
        ∫⁻ _ in Icc (1 : ℝ) 2, P {ω | (ω, (1 : ℝ)) ∈ T} :=
      setLIntegral_congr_fun measurableSet_Icc (fun r hr => hconst r (by linarith [hr.1]))
    rw [hcongr, setLIntegral_const, Real.volume_Icc]
    norm_num
  have hc0 : P {ω | (ω, (1 : ℝ)) ∈ T} = 0 := by
    rw [← hleft]
    have hcongr2 : ∫⁻ r in Icc (1 : ℝ) 2, P {ω | (ω, r) ∈ T} =
        ∫⁻ r in Icc (1 : ℝ) 2, (∫⁻ ω, T.indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P) :=
      setLIntegral_congr_fun measurableSet_Icc (fun r _ => hfun r)
    rw [hcongr2, hswap, hzero]
  intro r hr
  rw [hconst r hr, hc0]

/-- **Plateau probabilities vanish under a.e. measurable radii.** For positive rational times `q`, let `R q` be a radius
that is almost everywhere measurable; if the scale invariance `P[r ∈ P] = P[a r ∈ P]` (fact (1), in terms of the
plateau values of `R`) holds, then `P[r ∈ P] = 0` for every `r > 0`. -/
theorem plateau_measure_zero_of_ae_radii {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (R : ℚ → Ω → ℝ) (hRae : ∀ q : ℚ, 0 < (q : ℝ) → AEMeasurable (R q) P)
    (hscale : ∀ a r : ℝ, 0 < a → 0 < r →
      P {ω | r ∈ plateauValuesOf R ω} = P {ω | a * r ∈ plateauValuesOf R ω}) :
    ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauValuesOf R ω} = 0 := by
  -- measurable versions of the radii
  have hex : ∀ q : ℚ, ∃ f : Ω → ℝ, Measurable f ∧ (0 < (q : ℝ) → f =ᵐ[P] R q) := by
    intro q
    by_cases hq : 0 < (q : ℝ)
    · exact ⟨(hRae q hq).mk (R q), (hRae q hq).measurable_mk, fun _ => (hRae q hq).ae_eq_mk.symm⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h hq⟩
  choose R' hR'm hR'ae using hex
  -- the radii agree with their measurable versions at all positive rational times, almost surely
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → R q ω = R' q ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hR'ae q hq] with ω hω
      exact fun _ => hω.symm
    · exact ae_of_all _ fun ω h => absurd h hq
  -- the plateau sets of `R` and of its modification agree almost surely
  have hplat : ∀ r : ℝ, {ω | r ∈ plateauValuesOf R ω} =ᵐ[P] {ω | r ∈ plateauValuesOf R' ω} := by
    intro r
    filter_upwards [hall] with ω hω
    show (r ∈ plateauValuesOf R ω) = (r ∈ plateauValuesOf R' ω)
    rw [plateauValuesOf_congr hω]
  have hscale' : ∀ a r : ℝ, 0 < a → 0 < r →
      P {ω | r ∈ plateauValuesOf R' ω} = P {ω | a * r ∈ plateauValuesOf R' ω} := by
    intro a r ha hr
    have e1 := measure_congr (hplat r)
    have e2 := measure_congr (hplat (a * r))
    rw [← e1, ← e2]
    exact hscale a r ha hr
  -- Tonelli on the measurable plateau pairs of the modification
  have hT : MeasurableSet {p : Ω × ℝ | p.2 ∈ plateauValuesOf R' p.1} :=
    measurableSet_plateauPairsOf R' (fun q hq => hR'm q)
  have hcount : ∀ ω : Ω, {r : ℝ | (ω, r) ∈ {p : Ω × ℝ | p.2 ∈ plateauValuesOf R' p.1}}.Countable :=
    fun ω => plateauValuesOf_countable R' ω
  intro r hr
  rw [measure_congr (hplat r)]
  exact measure_section_zero_of_tonelli P _ hT hcount hscale' r hr

/-- **Plateau probabilities vanish for a family, under a.e. measurable radii.** The radii of a family `Λ` at positive
rational times are `R_q(ω) = familyRadius (Λ ω q)`; the plateau values of `Λ ω` are those of `R`. -/
theorem plateau_measure_zero_of_ae_radii_family {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Λ : Ω → ℝ → Set ℂ) (hRae : ∀ q : ℚ, 0 < (q : ℝ) → AEMeasurable (fun ω => familyRadius (Λ ω (q : ℝ))) P)
    (hscale : ∀ a r : ℝ, 0 < a → 0 < r →
      P {ω | r ∈ plateauValues (Λ ω)} = P {ω | a * r ∈ plateauValues (Λ ω)}) :
    ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauValues (Λ ω)} = 0 :=
  plateau_measure_zero_of_ae_radii P (fun q ω => familyRadius (Λ ω (q : ℝ))) hRae hscale

end MatedCRT
