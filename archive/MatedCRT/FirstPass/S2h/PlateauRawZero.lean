import MatedCRT.FirstPass.S2g.PlateauZero

/-!
# Zero law of the plateau radii from almost everywhere measurable raw radii (fp-S2h, z1, round 12)

Step M1 of CHATGPT-cone-good-set.md Section 5.2-5.3: the Tonelli step (39) and the scaling step (44)-(45) for the
plateau radii `plateauRadii (μ ω)` of a random measure, when every raw radius `ω ↦ rawRadius (μ ω) N p` is
almost everywhere measurable. The measurable versions `R (N, p)` agree with the raw radii outside one null set
(countably many rational times and integer discs), so the plateau events agree up to that null set, and the
graph of the measurable plateau values is measurable (`measurableSet_plateauOf`). The countable sections, the
Tonelli identity `lintegral_plateau_sections_eq_zero` and the scale invariance `eq_zero_of_scale_invariant`
(FirstPass/S2g/PlateauZero.lean) then give the zero law at every positive radius. No new mathematics: this is measure
theory on `Ω × ℝ`; the input `hraw` (measurability of the raw radii of the LQG measure) and the input `hscale`
(scale invariance of the probability of the plateau event) are the open NEW steps of HalfPlateauNullStep.
-/

namespace MatedCRT

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The plateau radii of a family of raw radii `R : ℕ × ℚ → Ω → ℝ` at an outcome `ω`: the values `r < N` at which
`R (N, p) ω = R (N, q) ω = r` for rationals `0 < p < q` and a positive integer `N` (the set `plateauRadii` with the raw
radii replaced by the family; CHATGPT-cone-good-set.md (37)). -/
def plateauOf (R : ℕ × ℚ → Ω → ℝ) (ω : Ω) : Set ℝ :=
  {r | ∃ N : ℕ, 0 < N ∧ ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ r < (N : ℝ) ∧
    R (N, p) ω = r ∧ R (N, q) ω = r}

omit [MeasurableSpace Ω] in
/-- The plateau values of one outcome are countable: each is a value of the countable family `R`. -/
theorem plateauOf_countable (R : ℕ × ℚ → Ω → ℝ) (ω : Ω) : (plateauOf R ω).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range (fun q : ℕ × ℚ => R q ω))
  rintro r ⟨N, _, p, _, _, _, _, hr, _⟩
  exact ⟨(N, p), hr⟩

/-- The graph of the plateau values is measurable in `Ω × ℝ` when every member of the family is measurable: a
countable union of the sets where two measurable functions of `ω` take the value `r`. -/
theorem measurableSet_plateauOf (R : ℕ × ℚ → Ω → ℝ) (hR : ∀ q, Measurable (R q)) :
    MeasurableSet {x : Ω × ℝ | x.2 ∈ plateauOf R x.1} := by
  have hset : {x : Ω × ℝ | x.2 ∈ plateauOf R x.1} = ⋃ N : ℕ, ⋃ p : ℚ, ⋃ q : ℚ,
      ({x : Ω × ℝ | 0 < N ∧ 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ)} ∩ {x : Ω × ℝ | x.2 < (N : ℝ)} ∩
        {x : Ω × ℝ | R (N, p) x.1 = x.2} ∩ {x : Ω × ℝ | R (N, q) x.1 = x.2}) := by
    ext x
    simp only [plateauOf, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨N, hN, p, q, hp, hpq, hr, h1, h2⟩
      exact ⟨N, p, q, ⟨⟨⟨hN, hp, hpq⟩, hr⟩, h1⟩, h2⟩
    · rintro ⟨N, p, q, ⟨⟨⟨hN, hp, hpq⟩, hr⟩, h1⟩, h2⟩
      exact ⟨N, hN, p, q, hp, hpq, hr, h1, h2⟩
  rw [hset]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun q => ?_
  refine ((MeasurableSet.const _).inter (measurableSet_lt measurable_snd measurable_const)).inter ?_ |>.inter ?_
  · exact measurableSet_eq_fun ((hR (N, p)).comp measurable_fst) measurable_snd
  · exact measurableSet_eq_fun ((hR (N, q)).comp measurable_fst) measurable_snd

/-- **Zero law of the plateau radii (fp-S2h, round 12, step M1).** Let `P` be a finite measure on `Ω` and `μ : Ω → Measure ℂ`
with almost everywhere measurable raw radii `ω ↦ rawRadius (μ ω) N p` (for integer `N` and rational `p`). If the
probability of the plateau event is invariant under the scalings `r ↦ s r`, then for every positive radius the
probability that `r` is a plateau radius of `μ ω` is zero. -/
theorem plateauRadii_zero_of_ae_raw (P : Measure Ω) [IsFiniteMeasure P] (μ : Ω → Measure ℂ)
    (hraw : ∀ (N : ℕ) (p : ℚ), 0 < N → 0 < (p : ℝ) → AEMeasurable (fun ω => rawRadius (μ ω) N (p : ℝ)) P)
    (hscale : ∀ s r : ℝ, 0 < s → 0 < r →
      P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (μ ω)}) :
    ∀ r : ℝ, 0 < r → P {ω | r ∈ plateauRadii (μ ω)} = 0 := by
  -- the raw radii enter the plateau only for `0 < N` and `0 < p` (fp-S2h, z1, round 16)
  obtain ⟨R, hRm, hRae⟩ : ∃ R : ℕ × ℚ → Ω → ℝ, (∀ q, Measurable (R q)) ∧
      ∀ q : ℕ × ℚ, 0 < q.1 → 0 < (q.2 : ℝ) → (fun ω => rawRadius (μ ω) q.1 (q.2 : ℝ)) =ᵐ[P] R q := by
    refine ⟨fun q => if h : 0 < q.1 ∧ 0 < (q.2 : ℝ) then (hraw q.1 q.2 h.1 h.2).mk _ else fun _ => 0, ?_, ?_⟩
    · intro q
      by_cases h : 0 < q.1 ∧ 0 < (q.2 : ℝ)
      · simp only [h]
        exact (hraw q.1 q.2 h.1 h.2).measurable_mk
      · simp only [h]
        exact measurable_const
    · intro q h1 h2
      have h : 0 < q.1 ∧ 0 < (q.2 : ℝ) := ⟨h1, h2⟩
      simp only [h]
      exact (hraw q.1 q.2 h.1 h.2).ae_eq_mk
  have hZ : ∀ᵐ ω ∂P, ∀ q : ℕ × ℚ, 0 < q.1 → 0 < (q.2 : ℝ) → rawRadius (μ ω) q.1 (q.2 : ℝ) = R q ω := by
    rw [ae_all_iff]
    intro q
    by_cases h : 0 < q.1 ∧ 0 < (q.2 : ℝ)
    · filter_upwards [hRae q h.1 h.2] with ω hω
      intro _ _
      exact hω
    · exact Filter.Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h
  have hpl : ∀ r : ℝ, P {ω | r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauOf R ω} := by
    intro r
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hZ] with ω hω
    have hω' : ∀ (N : ℕ) (p : ℚ), 0 < N → 0 < (p : ℝ) → rawRadius (μ ω) N (p : ℝ) = R (N, p) ω :=
      fun N p hN hp => hω (N, p) hN hp
    simp only [plateauRadii, plateauOf, mem_ofPred_eq]
    constructor
    · rintro ⟨N, hN, p, q, hp, hpq, hrN, h1, h2⟩
      have hq : (0 : ℝ) < q := lt_trans hp hpq
      exact ⟨N, hN, p, q, hp, hpq, hrN, (hω' N p hN hp).symm.trans h1, (hω' N q hN hq).symm.trans h2⟩
    · rintro ⟨N, hN, p, q, hp, hpq, hrN, h1, h2⟩
      have hq : (0 : ℝ) < q := lt_trans hp hpq
      exact ⟨N, hN, p, q, hp, hpq, hrN, (hω' N p hN hp).trans h1, (hω' N q hN hq).trans h2⟩
  have hEm := measurableSet_plateauOf R hRm
  have hcount : ∀ ω : Ω, {r : ℝ | (ω, r) ∈ {x : Ω × ℝ | x.2 ∈ plateauOf R x.1}}.Countable :=
    fun ω => plateauOf_countable R ω
  have hsec : ∀ r : ℝ, P {ω | (ω, r) ∈ {x : Ω × ℝ | x.2 ∈ plateauOf R x.1}}
      = P {ω | r ∈ plateauRadii (μ ω)} := fun r => (hpl r).symm
  have hscale' : ∀ s r : ℝ, 0 < s → 0 < r →
      P {ω | (ω, s * r) ∈ {x : Ω × ℝ | x.2 ∈ plateauOf R x.1}}
        = P {ω | (ω, r) ∈ {x : Ω × ℝ | x.2 ∈ plateauOf R x.1}} := by
    intro s r hs hr
    rw [hsec, hsec]
    exact hscale s r hs hr
  intro r hr
  rw [← hsec r]
  exact eq_zero_of_scale_invariant (f := fun r : ℝ => P {ω | (ω, r) ∈ {x : Ω × ℝ | x.2 ∈ plateauOf R x.1}})
    hscale' (lintegral_plateau_sections_eq_zero P hEm hcount) r hr

end MatedCRT
