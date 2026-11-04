import MatedCRT.Draft.Section6
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6

/-!
# Lemma 6.6: transfer from Leonardo Bonanno's formalization

The near-independence estimate is `LQGMetric.LM.lmLem3_1a`, Leonardo Bonanno's proof of
Gwynne–Miller, *Local metrics of the Gaussian free field*, Lemma 3.1. The remaining input is the
law transfer between the Harmonic Balls pairing interface and the distribution-valued GFF.
It is stated for countable families of local events and preserves exactly the probabilities used.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- Law transfer for a countable family of events determined by the whole-plane GFF on annuli
modulo constants. The target events are measurable for the normalized distribution restricted to
each annulus. This is the missing bridge between the two GFF interfaces (IR-x1-1). -/
def AnnulusGFFLawTransferStep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
  ∀ (s₁ s₂ : ℝ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
    0 < s₁ → s₁ < s₂ → s₂ < 1 → (∀ k, 0 < r k) →
    (∀ k, ∃ E' : Set Ω, MeasurableSet[modConstSigma hC (annulus 0 (s₁ * r k) (s₂ * r k))] E' ∧
      E k =ᵐ[P] E') →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (h : Ω' → LQGMetric.DistC)
      (F : ℕ → Set Ω'),
      IsProbabilityMeasure P' ∧ LQGMetric.IsNormalizedWPGFF h P' ∧
      (∀ k, MeasurableSet[LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
        (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k))] (F k)) ∧
      (∀ k, P (E k) = P' (F k)) ∧
      ∀ K, P {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} =
        P' {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ F k}

/-- Lemma 6.6 follows from Bonanno's Lemma 3.1 and the GFF law transfer. -/
theorem annulusIterate_of_leo (htransfer : AnnulusGFFLawTransferStep) : AnnulusIterateStmt := by
  intro s₁ s₂ hs₁ hs₁₂ hs₂ α hα
  obtain ⟨p, c, hp, hp1, hc, hleo⟩ :=
    LQGMetric.LM.lmLem3_1a s₁ s₂ hs₁ hs₁₂ hs₂ α hα (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, max c 1, hp, hp1, lt_of_lt_of_le hc (le_max_left _ _), ?_⟩
  intro Ω _ P hC hcirc hP hwp r E hr hrpos hratio hlocal hprob K
  let : IsProbabilityMeasure P := hP
  obtain ⟨Ω', mΩ', P', h, F, hP', hfield, hF, hsingle, hnone⟩ :=
    htransfer Ω P hC hcirc hP hwp s₁ s₂ r E hs₁ hs₁₂ hs₂ hrpos hlocal
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  have hbound : ∀ k, ENNReal.ofReal p ≤ P' (F k) := by
    intro k
    rw [← hsingle k]
    exact hprob k
  by_cases hK : K = 0
  · subst K
    simp
  · have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
    have hsub : {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ F k} ⊆
        {ω | (LQGMetric.Blueprint.countOcc F K ω : ℝ) < (1 / 2 : ℝ) * K} := by
      intro ω hω
      have hz : LQGMetric.Blueprint.countOcc F K ω = 0 := by
        classical
        simp only [LQGMetric.Blueprint.countOcc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk
        exact hω k hk
      change (LQGMetric.Blueprint.countOcc F K ω : ℝ) < (1 / 2 : ℝ) * K
      rw [hz]
      simp only [Nat.cast_zero]
      positivity
    rw [hnone K]
    exact (measure_mono hsub).trans ((hleo P' h hfield r F ⟨hrpos, hr, hratio, hF⟩ hbound K).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left c 1) (le_of_lt (Real.exp_pos _)))))

end MatedCRT
