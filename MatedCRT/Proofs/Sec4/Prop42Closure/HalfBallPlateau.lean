import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ContactEvent
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime

/-! # Plateau radii of the whole-plane harmonic-ball family (closure of Proposition 4.2, z5)

Written argument: `notes/prop42-proof/prop42-proof.tex`, lemma `l:plateau` (draft lines 230-268). This file

* states fact (1), used at draft lines 245-256, as the named Step Prop `PlateauScaleInvarianceStep` (fact (2) is
  `ConeWholePlaneFieldLawStep` in `ConeWholePlaneSteps.lean`);
* proves that the plateau values are countable (draft lines 237-243), and the Tonelli step of draft lines 264-268:
  `plateau_measure_zero` gives `P[r ∈ P] = 0` for every `r > 0`, from fact (1) and a measurability premise for the
  radii at rational times (draft lines 259-263), which is stated as an explicit hypothesis.

The radius of a family set is `R = sup {|x| : x ∈ Λ}` (draft line 232). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory
open scoped ENNReal

/-- The radius `sup {‖x‖ : x ∈ Λ}` of a set of a harmonic-ball family (`R_h(t)` of draft line 232). -/
noncomputable def familyRadius (Λ : Set ℂ) : ℝ :=
  sSup ((fun x : ℂ => ‖x‖) '' Λ)

/-- The plateau values of a time-indexed family (draft lines 237-242): the radii `r > 0` attained at two rational
times `0 < s < t`. Thus `r` is a plateau value exactly when the radius is constant `r` on a nondegenerate time
interval (the radius is increasing). -/
def plateauValues (Λ : ℝ → Set ℂ) : Set ℝ :=
  {r | 0 < r ∧ ∃ s t : ℚ, 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
    familyRadius (Λ s) = r ∧ familyRadius (Λ t) = r}

/-- **The plateau values are countable for every family** (draft line 243). Each plateau value is the radius at a
rational time. -/
theorem plateauValues_countable (Λ : ℝ → Set ℂ) : (plateauValues Λ).Countable := by
  refine (Set.countable_range fun s : ℚ => familyRadius (Λ (s : ℝ))).mono (fun r hr => ?_)
  obtain ⟨-, s, -, -, -, hs, -⟩ := hr
  exact ⟨s, hs⟩

/-- **Fact (1): scale invariance of the plateau probabilities of the whole-plane family.**

Written argument: draft lines 245-256 (the scaling `h_a` of the whole-plane field, `h_a =_d h^α`, and the identity
`Λ^{h_a}_t = a⁻¹ Λ^h_{e^{γ c_a} t}`), which give `p(r) = p(ar)` at draft line 265, where `p(r) = P[r ∈ P(h)]`.
Source of the scaling: the proof of [HB] Lemma 5.7 (Harmonic-Balls-LQG corrected tex lines 905-938), stated as
`ClusterScaleInvarianceStmt` (`Harmonic-Balls-LQG/HarmonicBalls/Draft/Section5.lean:226`).

Data: a whole-plane GFF `h^α` (`IsWholePlaneGFF`, insertion parameter `α < lqgQ γ`), its `γ`-LQG measure `μ`
(`IsLQGMeasureOfField P γ α`), and its global harmonic-ball family `Λ` centred at `0`
(`IsRegularizedClusterFamily`, the family of [HB] Theorem 5.5). The conclusion: for `a, r > 0` the probability that
`r` is a plateau value equals the probability that `a r` is one. This is the law invariance under `h ↦ h_a`
combined with the random positive time change, which preserves plateau values. -/
def PlateauScaleInvarianceStep : Prop :=
  ∀ γ α : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (Λ : Ω → ℝ → Set ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ → (∀ᵐ ω ∂P, IsRegularizedClusterFamily (μ ω) (Λ ω) 0) →
    ∀ a r : ℝ, 0 < a → 0 < r →
      P {ω | r ∈ plateauValues (Λ ω)} = P {ω | a * r ∈ plateauValues (Λ ω)}

/-- The pairs `(ω, r)` with `r` a plateau value of `Λ ω`. -/
def plateauPairs {Ω : Type} (Λ : Ω → ℝ → Set ℂ) : Set (Ω × ℝ) :=
  {p | p.2 ∈ plateauValues (Λ p.1)}

/-- The set of pairs is measurable when the radii at positive rational times are measurable in `ω`
(draft lines 259-263; the premise `hR` is the measurability claim of that paragraph). -/
theorem measurableSet_plateauPairs {Ω : Type} [MeasurableSpace Ω] (Λ : Ω → ℝ → Set ℂ)
    (hR : ∀ q : ℚ, 0 < (q : ℝ) → Measurable (fun ω => familyRadius (Λ ω (q : ℝ)))) :
    MeasurableSet (plateauPairs Λ) := by
  have hpair : ∀ s t : ℚ, MeasurableSet {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
      familyRadius (Λ p.1 s) = p.2 ∧ familyRadius (Λ p.1 t) = p.2} := by
    intro s t
    by_cases h : 0 < (s : ℝ) ∧ (s : ℝ) < t
    · have hs : Measurable (fun ω => familyRadius (Λ ω (s : ℝ))) := hR s h.1
      have ht : Measurable (fun ω => familyRadius (Λ ω (t : ℝ))) := hR t (h.1.trans h.2)
      have hsm : MeasurableSet {p : Ω × ℝ | familyRadius (Λ p.1 s) = p.2} :=
        measurableSet_eq_fun (hs.comp measurable_fst) measurable_snd
      have htm : MeasurableSet {p : Ω × ℝ | familyRadius (Λ p.1 t) = p.2} :=
        measurableSet_eq_fun (ht.comp measurable_fst) measurable_snd
      have hpos : MeasurableSet {p : Ω × ℝ | 0 < p.2} :=
        measurableSet_lt measurable_const measurable_snd
      have hset : {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
          familyRadius (Λ p.1 s) = p.2 ∧ familyRadius (Λ p.1 t) = p.2} =
          {p : Ω × ℝ | 0 < p.2} ∩ {p : Ω × ℝ | familyRadius (Λ p.1 s) = p.2} ∩
            {p : Ω × ℝ | familyRadius (Λ p.1 t) = p.2} := by
        ext p
        constructor
        · rintro ⟨h1, -, -, h2, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h.1, h.2, h2, h3⟩
      rw [hset]
      exact (hpos.inter hsm).inter htm
    · have hempty : {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
          familyRadius (Λ p.1 s) = p.2 ∧ familyRadius (Λ p.1 t) = p.2} = ∅ := by
        ext p
        constructor
        · rintro ⟨-, h1, h2, -, -⟩
          exact absurd ⟨h1, h2⟩ h
        · intro hp
          exact absurd hp (Set.notMem_empty p)
      rw [hempty]
      exact MeasurableSet.empty
  have heq : plateauPairs Λ = ⋃ (s : ℚ) (t : ℚ), {p : Ω × ℝ | 0 < p.2 ∧ 0 < (s : ℝ) ∧ (s : ℝ) < t ∧
      familyRadius (Λ p.1 s) = p.2 ∧ familyRadius (Λ p.1 t) = p.2} := by
    ext p
    simp only [plateauPairs, plateauValues, Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hp, s, t, hs, hst, hsr, htr⟩
      exact ⟨s, t, hp, hs, hst, hsr, htr⟩
    · rintro ⟨s, t, hp, hs, hst, hsr, htr⟩
      exact ⟨hp, s, t, hs, hst, hsr, htr⟩
  rw [heq]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun t => hpair s t

/-- **Plateau probabilities vanish** (draft lines 245-268: `p` is constant by fact (1), and Tonelli with the countable
sections gives `∫_1^2 p = 0`). Hypotheses: the measurability premise `hR` of the radii at positive rational times, and
the scale invariance `hscale` of fact (1) for the data. -/
theorem plateau_measure_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Λ : Ω → ℝ → Set ℂ)
    (hR : ∀ q : ℚ, 0 < (q : ℝ) → Measurable (fun ω => familyRadius (Λ ω (q : ℝ))))
    (hscale : ∀ a r : ℝ, 0 < a → 0 < r →
      P {ω | r ∈ plateauValues (Λ ω)} = P {ω | a * r ∈ plateauValues (Λ ω)}) :
    ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauValues (Λ ω)} = 0 := by
  have hT : MeasurableSet (plateauPairs Λ) := measurableSet_plateauPairs Λ hR
  have hsec : ∀ r : ℝ, MeasurableSet {ω | r ∈ plateauValues (Λ ω)} := fun r =>
    hT.preimage (measurable_id.prodMk measurable_const)
  have hconst : ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauValues (Λ ω)} =
      P {ω | (1 : ℝ) ∈ plateauValues (Λ ω)} := by
    intro r hr
    have h := hscale (1 / r) r (by positivity) hr
    rw [one_div, inv_mul_cancel₀ hr.ne'] at h
    exact h
  -- the Tonelli identity on `[1, 2]`
  have hmeasT : Measurable ((plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞)) :=
    (measurable_one.indicator hT)
  have hfun : ∀ r : ℝ, P {ω | r ∈ plateauValues (Λ ω)} =
      ∫⁻ ω, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P := by
    intro r
    exact (lintegral_indicator_one (hsec r)).symm.trans rfl
  have hswap : ∫⁻ r in Icc (1 : ℝ) 2, (∫⁻ ω, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P)
      = ∫⁻ ω, (∫⁻ r in Icc (1 : ℝ) 2, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r)) ∂P := by
    refine lintegral_lintegral_swap ?_
    exact (hmeasT.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
  have hinner : ∀ ω : Ω, ∫⁻ r in Icc (1 : ℝ) 2, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) = 0 := by
    intro ω
    have hcount : (plateauValues (Λ ω)).Countable := plateauValues_countable (Λ ω)
    have hind : ∀ r : ℝ, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) =
        (plateauValues (Λ ω)).indicator (1 : ℝ → ℝ≥0∞) r := by
      intro r
      by_cases h : r ∈ plateauValues (Λ ω) <;> simp [Set.indicator, plateauPairs, h]
    simp only [hind]
    rw [lintegral_indicator_one hcount.measurableSet]
    exact hcount.measure_zero _
  have hzero : ∫⁻ ω, (∫⁻ r in Icc (1 : ℝ) 2, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r)) ∂P = 0 := by
    simp only [hinner, lintegral_zero]
  have hleft : ∫⁻ r in Icc (1 : ℝ) 2, P {ω | r ∈ plateauValues (Λ ω)} =
      P {ω | (1 : ℝ) ∈ plateauValues (Λ ω)} := by
    have hcongr : ∫⁻ r in Icc (1 : ℝ) 2, P {ω | r ∈ plateauValues (Λ ω)} =
        ∫⁻ _ in Icc (1 : ℝ) 2, P {ω | (1 : ℝ) ∈ plateauValues (Λ ω)} :=
      setLIntegral_congr_fun measurableSet_Icc (fun r hr => hconst r (by linarith [hr.1]))
    rw [hcongr, setLIntegral_const, Real.volume_Icc]
    norm_num
  have hc0 : P {ω | (1 : ℝ) ∈ plateauValues (Λ ω)} = 0 := by
    rw [← hleft]
    have hcongr2 : ∫⁻ r in Icc (1 : ℝ) 2, P {ω | r ∈ plateauValues (Λ ω)} =
        ∫⁻ r in Icc (1 : ℝ) 2, (∫⁻ ω, (plateauPairs Λ).indicator (1 : Ω × ℝ → ℝ≥0∞) (ω, r) ∂P) :=
      setLIntegral_congr_fun measurableSet_Icc (fun r _ => hfun r)
    rw [hcongr2, hswap, hzero]
  intro r hr
  rw [hconst r hr, hc0]

end MatedCRT
