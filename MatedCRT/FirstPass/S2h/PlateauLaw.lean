import MatedCRT.FirstPass.S2h.PlateauRawZero
import MatedCRT.FirstPass.S2h.LogScale

/-!
# Equality in law transfers the plateau event (fp-S2h, z1, round 14)

Abstract measure theory behind the two hypotheses `hraw` and `hscale` of `plateauRadii_zero_of_ae_raw`
(`FirstPass/S2h/PlateauRawZero.lean`). A measurable class `R` of measures and a measurable code `G : Measure ℂ → ℕ × ℚ → ℝ`
equal to the raw radii on `R` express the plateau event `r ∈ plateauRadii ν` as the membership `G ν ∈ plateauCodeSet r`
(a measurable set of codes). Equality in law of the random measure and of its dilation then transfers the plateau event
(CHATGPT-z1-logcert-null.md Section 5, (25)-(27)). Nothing here is specific to the log-GFF except through the hypotheses.
-/

namespace MatedCRT

open MeasureTheory Filter Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The plateau event on codes: the plateau condition of `plateauRadii` with the raw radii replaced by a code
`x : ℕ × ℚ → ℝ` (CHATGPT-cone-good-set.md (37)). -/
def plateauCodeSet (r : ℝ) : Set (ℕ × ℚ → ℝ) :=
  {x | ∃ N : ℕ, 0 < N ∧ ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ r < (N : ℝ) ∧
    x (N, p) = r ∧ x (N, q) = r}

/-- The plateau event on codes is measurable in the product σ-algebra: a countable union of coordinate equalities. -/
theorem measurableSet_plateauCodeSet (r : ℝ) : MeasurableSet (plateauCodeSet r) := by
  have hset : plateauCodeSet r = ⋃ N : ℕ, ⋃ p : ℚ, ⋃ q : ℚ,
      (({x : ℕ × ℚ → ℝ | 0 < N ∧ 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ r < (N : ℝ)} ∩
        {x | x (N, p) = r}) ∩ {x | x (N, q) = r}) := by
    ext x
    simp only [plateauCodeSet, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨N, hN, p, q, hp, hpq, hr, h1, h2⟩
      exact ⟨N, p, q, ⟨⟨hN, hp, hpq, hr⟩, h1⟩, h2⟩
    · rintro ⟨N, p, q, ⟨⟨hN, hp, hpq, hr⟩, h1⟩, h2⟩
      exact ⟨N, hN, p, q, hp, hpq, hr, h1, h2⟩
  rw [hset]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun q => ?_
  refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.const _) ?_) ?_
  · exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  · exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const

/-- Preimages of a measurable set under two maps with equal laws agree (CHATGPT-z1-logcert-null.md Section 5.3). -/
theorem measure_preimage_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] [IsProbabilityMeasure P]
    (S X : Ω → Ω') (hS : AEMeasurable S P) (hX : AEMeasurable X P) (hlaw : P.map S = P.map X) {E : Set Ω'}
    (hE : MeasurableSet E) :
    P (S ⁻¹' E) = P (X ⁻¹' E) := by
  rw [← Measure.map_apply_of_aemeasurable hS hE, hlaw, Measure.map_apply_of_aemeasurable hX hE]

/-- **Plateau event by equality in law (fp-S2h, z1, round 14).** Let `μ`, `S` be random measures with `P.map S = P.map μ`,
`μ ω ∈ R` almost surely for a measurable class `R` of measures, and `G` a measurable code of the raw radii on `R`. Then the
plateau events of `S` and of `μ` have the same probability at every radius `r`. -/
theorem plateau_event_eq_of_law [IsProbabilityMeasure P] (μ S : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (hS : AEMeasurable S P)
    (hlaw : P.map S = P.map μ) (R : Set (Measure ℂ)) (hR : MeasurableSet R)
    (G : Measure ℂ → ℕ × ℚ → ℝ) (hGm : Measurable G)
    (hG : ∀ ν ∈ R, ∀ q : ℕ × ℚ, G ν q = rawRadius ν q.1 (q.2 : ℝ))
    (hμR : ∀ᵐ ω ∂P, μ ω ∈ R) (r : ℝ) :
    P {ω | r ∈ plateauRadii (S ω)} = P {ω | r ∈ plateauRadii (μ ω)} := by
  have hSR : ∀ᵐ ω ∂P, S ω ∈ R := by
    have h := measure_preimage_eq_of_map_eq S μ hS hμ hlaw hR.compl
    have h0 : P (μ ⁻¹' Rᶜ) = 0 := by
      have := hμR
      rw [ae_iff] at this
      exact this
    rw [ae_iff]
    have : {ω | ¬ S ω ∈ R} = S ⁻¹' Rᶜ := rfl
    rw [this, h, h0]
  have hcode : ∀ ν ∈ R, (r ∈ plateauRadii ν ↔ G ν ∈ plateauCodeSet r) := by
    intro ν hν
    constructor
    · rintro ⟨N, hN, p, q, hp, hpq, hr, h1, h2⟩
      exact ⟨N, hN, p, q, hp, hpq, hr, (hG ν hν (N, p)).trans h1, (hG ν hν (N, q)).trans h2⟩
    · rintro ⟨N, hN, p, q, hp, hpq, hr, h1, h2⟩
      exact ⟨N, hN, p, q, hp, hpq, hr, (hG ν hν (N, p)).symm.trans h1, (hG ν hν (N, q)).symm.trans h2⟩
  have hE : MeasurableSet (G ⁻¹' plateauCodeSet r) := hGm (measurableSet_plateauCodeSet r)
  calc P {ω | r ∈ plateauRadii (S ω)}
      = P {ω | G (S ω) ∈ plateauCodeSet r} := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [hSR] with ω hω
        exact hcode _ hω
    _ = P (S ⁻¹' (G ⁻¹' plateauCodeSet r)) := rfl
    _ = P (μ ⁻¹' (G ⁻¹' plateauCodeSet r)) := measure_preimage_eq_of_map_eq S μ hS hμ hlaw hE
    _ = P {ω | G (μ ω) ∈ plateauCodeSet r} := rfl
    _ = P {ω | r ∈ plateauRadii (μ ω)} := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [hμR] with ω hω
        exact (hcode _ hω).symm

/-- **Dilation of the plateau event (fp-S2h, z1, round 14; CHATGPT Section 5, (26)-(27)).** If `S ω = c ω • (dilation by s⁻¹)
of μ ω` with `c > 0` and the dilation law `P.map S = P.map μ`, and the clusters of `μ ω` are monotone and compatible almost
surely, then `P{s r ∈ plateauRadii (μ ω)} = P{r ∈ plateauRadii (μ ω)}` for every `s > 0`. -/
theorem plateau_scale_eq_of_law [IsProbabilityMeasure P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (c : Ω → ℝ) (hc : ∀ ω, 0 < c ω) (s : ℝ) (hs : 0 < s)
    (hSm : AEMeasurable (fun ω => ENNReal.ofReal (c ω) • Measure.map (fun x : ℂ => s⁻¹ • x) (μ ω)) P)
    (hlaw : P.map (fun ω => ENNReal.ofReal (c ω) • Measure.map (fun x : ℂ => s⁻¹ • x) (μ ω)) = P.map μ)
    (R : Set (Measure ℂ)) (hR : MeasurableSet R)
    (G : Measure ℂ → ℕ × ℚ → ℝ) (hGm : Measurable G)
    (hG : ∀ ν ∈ R, ∀ q : ℕ × ℚ, G ν q = rawRadius ν q.1 (q.2 : ℝ))
    (hμR : ∀ᵐ ω ∂P, μ ω ∈ R) (hgood : ∀ᵐ ω ∂P, ClusterMonoAt (μ ω) ∧ ClusterCompatAt (μ ω)) (r : ℝ) :
    P {ω | s * r ∈ plateauRadii (μ ω)} = P {ω | r ∈ plateauRadii (μ ω)} := by
  have h1 : P {ω | s * r ∈ plateauRadii (μ ω)} =
      P {ω | r ∈ plateauRadii (ENNReal.ofReal (c ω) • Measure.map (fun x : ℂ => s⁻¹ • x) (μ ω))} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hgood] with ω hω
    exact (mem_plateauRadii_smul_iff hω.1 hω.2 hs (hc ω) r).symm
  rw [h1]
  exact plateau_event_eq_of_law μ _ hμ hSm hlaw R hR G hGm hG hμR r

/-- **Raw radii are almost everywhere measurable (fp-S2h, z1, round 14).** Under the same measurable code, the raw radius
`ω ↦ rawRadius (μ ω) N p` is almost everywhere measurable: it agrees almost surely with the measurable `G (μ ω) (N, p)`. -/
theorem aemeasurable_rawRadius_of_code [IsProbabilityMeasure P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (R : Set (Measure ℂ)) (G : Measure ℂ → ℕ × ℚ → ℝ) (hGm : Measurable G)
    (hG : ∀ ν ∈ R, ∀ q : ℕ × ℚ, G ν q = rawRadius ν q.1 (q.2 : ℝ))
    (hμR : ∀ᵐ ω ∂P, μ ω ∈ R) (N : ℕ) (p : ℚ) :
    AEMeasurable (fun ω => rawRadius (μ ω) N (p : ℝ)) P := by
  have hm : AEMeasurable (fun ω => G (μ ω) (N, p)) P :=
    ((measurable_pi_apply (N, p)).comp hGm).comp_aemeasurable hμ
  refine hm.congr ?_
  filter_upwards [hμR] with ω hω
  exact hG (μ ω) hω (N, p)

end MatedCRT
