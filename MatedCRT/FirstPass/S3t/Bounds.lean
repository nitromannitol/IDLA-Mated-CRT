import MatedCRT.FirstPass.S3t.Defs
import MatedCRT.FirstPass.Frozen.S3S4b

/-!
# Truncated quenched laws, Step 1: uniform deterministic bounds

If `|g| ≤ M`, then the stopped occupation
satisfies `|stoppedOccupation D T g w| ≤ T * M`, and the quenched discrete occupation satisfies
`|quenchedDiscreteOccupation S ω D g T ε q| ≤ T * M` for `m_ε > 0`. Both bounds are deterministic, so bad mesh events are
discarded through their environment probabilities alone.

The answer's second bound omits the hypothesis `0 ≤ T`. It is needed: for `T < 0` the occupation is `0` while `T * M < 0`
whenever `M > 0`. So `hT : 0 ≤ T` is added to `abs_quenchedDiscreteOccupation_le`. The first bound already has it.
-/

open MeasureTheory Set
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- A bounded integrand on `(0, a]` has integral of absolute value at most `M * a`. -/
theorem abs_setIntegral_Ioc_le_of_bound {M a : ℝ} (f : ℝ → ℝ) (hf : ∀ t, |f t| ≤ M) (ha : 0 ≤ a) :
    |∫ t in Ioc (0 : ℝ) a, f t| ≤ M * a := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a) (f := f) (C := M)
    (by simp) (fun t _ => by rw [Real.norm_eq_abs]; exact hf t)
  rw [Real.volume_real_Ioc_of_le ha, sub_zero, Real.norm_eq_abs] at h
  exact h

/-- Step 1, stopped occupation: `|stoppedOccupation D T g w| ≤ T * M` when `|g| ≤ M` and `0 ≤ T`. -/
theorem abs_stoppedOccupation_le {D : Set ℂ} {T M : ℝ} {g : ℂ → ℝ} (hg : ∀ x, |g x| ≤ M) (hT : 0 ≤ T)
    (w : ℝ≥0 → ℂ) : |stoppedOccupation D T g w| ≤ T * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have ha0 : 0 ≤ (min (ENNReal.ofReal T) (pathExitTime D w)).toReal := ENNReal.toReal_nonneg
  have haT : (min (ENNReal.ofReal T) (pathExitTime D w)).toReal ≤ T := by
    have h1 : min (ENNReal.ofReal T) (pathExitTime D w) ≤ ENNReal.ofReal T := min_le_left _ _
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hT] at h2
  have key := abs_setIntegral_Ioc_le_of_bound (fun t : ℝ => g (w t.toNNReal)) (fun t => hg _) ha0
  unfold stoppedOccupation
  calc |∫ t in Ioc (0 : ℝ) (min (ENNReal.ofReal T) (pathExitTime D w)).toReal, g (w t.toNNReal)|
      ≤ M * (min (ENNReal.ofReal T) (pathExitTime D w)).toReal := key
    _ ≤ M * T := mul_le_mul_of_nonneg_left haT hM
    _ = T * M := mul_comm _ _

/-- A finite sum of terms bounded by `M` has absolute value at most `n * M`. -/
theorem abs_sum_range_le_of_bound {f : ℕ → ℝ} {M : ℝ} (n : ℕ) (hf : ∀ k, |f k| ≤ M) :
    |∑ k ∈ Finset.range n, f k| ≤ n * M := by
  calc |∑ k ∈ Finset.range n, f k| ≤ ∑ k ∈ Finset.range n, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, M := Finset.sum_le_sum fun k _ => hf k
    _ = n * M := by simp

open Classical in
/-- Step 1, quenched discrete occupation: `|quenchedDiscreteOccupation S ω D g T ε q| ≤ T * M` when `|g| ≤ M`,
`0 ≤ T` and `m_ε > 0`. The proof uses `⌊T m_ε⌋ ≤ T m_ε`. -/
theorem abs_quenchedDiscreteOccupation_le {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {D : Set ℂ} {g : ℂ → ℝ} {M T ε : ℝ} (hg : ∀ x, |g x| ≤ M) (hT : 0 ≤ T) (hm : 0 < S.mε ε) (q : ℕ → ℤ) :
    |quenchedDiscreteOccupation S ω D g T ε q| ≤ T * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hm' : 0 ≤ (S.mε ε)⁻¹ := (inv_pos.2 hm).le
  have hbd := abs_sum_range_le_of_bound (M := M) ⌊T * S.mε ε⌋₊ (f := fun k : ℕ =>
    if ∀ j ≤ k, q j ∈ interiorCellVertices ε (S.η ω) D then g (vertexPoint ε (S.η ω) (q k)) else 0)
    (fun k => by
      split_ifs
      · exact hg _
      · simp [hM])
  have hfloor : (⌊T * S.mε ε⌋₊ : ℝ) ≤ T * S.mε ε := Nat.floor_le (mul_nonneg hT hm.le)
  unfold quenchedDiscreteOccupation
  rw [abs_mul, abs_of_nonneg hm']
  calc (S.mε ε)⁻¹ * |∑ k ∈ Finset.range ⌊T * S.mε ε⌋₊,
        if ∀ j ≤ k, q j ∈ interiorCellVertices ε (S.η ω) D then g (vertexPoint ε (S.η ω) (q k)) else 0|
      ≤ (S.mε ε)⁻¹ * ((⌊T * S.mε ε⌋₊ : ℝ) * M) := mul_le_mul_of_nonneg_left hbd hm'
    _ ≤ (S.mε ε)⁻¹ * ((T * S.mε ε) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfloor hM) hm'
    _ = T * M := by rw [show T * S.mε ε * M = S.mε ε * (T * M) by ring, inv_mul_cancel_left₀ hm.ne']

#print axioms abs_stoppedOccupation_le
#print axioms abs_quenchedDiscreteOccupation_le

end MatedCRT.TruncatedLaws
