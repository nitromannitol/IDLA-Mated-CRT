import MatedCRT.Proofs.Sec5.MeanValueInequality.Reversibility
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-!
# FIRST PASS, interior-ball Green ratio (GAP 2, operator note 20:31): Steps 5-6 of CHATGPT-q3-questions §1.4

Step 5 (eq. (18)): reversibility gives the sum identity `∑_{b∈I} G_I(b,a) = deg(a) ∑_{b∈I} g_I(a,b)`.
Step 6: with the mass bound `q_I(a) ≥ m_r ε⁻¹` (eq. (17)), the event `m_r ≥ ε^{1/4}` and `G_I(a,a) ≤ ε^{-1/2}` (eq. (19)),
the ratio `∑_{b∈I} G_I(b,a) / G_I(a,a)` is at least `ε^{-1/4}` (target (4)).
The inputs (17), (19) and the event are hypotheses here; their probabilistic sources are not part of this file.
-/

namespace MatedCRT.S5c

open Set

/-- **Reversibility sum identity** (§1.4 Step 5, eq. (18)): for a finite domain `I` and `a ∈ I`,
`∑_{b∈I} G_I(b,a) = deg(a) ∑_{b∈I} g_I(a,b)`, where `g_I(a,b) = G_I(a,b)/deg(b)`. -/
theorem tsum_greenFn_eq_deg_mul_tsum_kernel {m : ℤ → ℤ → ℕ} {I : Set ℤ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0) (hI : I.Finite) {a : ℤ} :
    ∑' b : I, greenFn m I b a = (mdeg m a : ℝ) * ∑' b : I, greenKernel m I a b := by
  have hdeg : ∀ x, mdeg m x ≠ 0 := fun x => mdeg_ne_zero_of_ne_zero hlf (hcons x)
  have hfirst : ∀ b, ∀ x ∈ I, mLaplacian m (fun y => greenFn m I y b) x = -(if x = b then 1 else 0) :=
    fun b => MatedCRT.WalkPotential.mLaplacian_greenFn hlf hcons hI b
  have hda : (mdeg m a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg a)
  have hsym := greenKernel_symm_of_firstStep hsymm hlf hI hdeg hfirst
  calc ∑' b : I, greenFn m I b a = ∑' b : I, (mdeg m a : ℝ) * greenKernel m I b a :=
        tsum_congr fun b => by unfold greenKernel; field_simp
    _ = (mdeg m a : ℝ) * ∑' b : I, greenKernel m I a b := by
        rw [tsum_mul_left]
        congr 1
        exact tsum_congr fun b => hsym _ _

/-- **Quarter-power ratio** (§1.4 Step 6, target (4)): if `q ≥ m ε⁻¹`, `m ≥ ε^{1/4}`, `0 < G ≤ ε^{-1/2}`, `D ≥ 1`
and `Q ≥ 0`, then `ε^{-1/4} ≤ D Q / G`. -/
theorem quarter_le_ratio {ε D Q G m : ℝ} (hε : 0 < ε) (hD : 1 ≤ D) (hQ0 : 0 ≤ Q) (hmQ : m * ε⁻¹ ≤ Q)
    (hm : ε ^ (1 / 4 : ℝ) ≤ m) (hG0 : 0 < G) (hG : G ≤ ε ^ (-(1 / 2) : ℝ)) :
    ε ^ (-(1 / 4) : ℝ) ≤ D * Q / G := by
  set A := ε ^ (-(1 / 4) : ℝ) with hAdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos hε _
  have hAne : A ≠ 0 := hA0.ne'
  have h1 : ε ^ (1 / 4 : ℝ) = A⁻¹ := by
    rw [hAdef, Real.rpow_neg hε.le, inv_inv]
  have h2 : ε⁻¹ = A ^ 4 := by
    rw [hAdef, ← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_neg_one]; norm_num
  have h3 : ε ^ (-(1 / 2) : ℝ) = A ^ 2 := by
    rw [hAdef, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  rw [h1] at hm
  rw [h2] at hmQ
  rw [h3] at hG
  have hA3 : A⁻¹ * A ^ 4 = A ^ 3 := by
    rw [show A ^ 4 = A * A ^ 3 by ring, ← mul_assoc, inv_mul_cancel₀ hAne, one_mul]
  have hQ3 : A ^ 3 ≤ Q := by
    have := mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ A ^ 4)
    linarith
  have hDQ : A ^ 3 ≤ D * Q := le_trans hQ3 (le_mul_of_one_le_left hQ0 hD)
  rw [le_div_iff₀ hG0]
  have := mul_le_mul_of_nonneg_left hG hA0.le
  nlinarith

/-- **Step 6 ratio on a finite domain** (§1.4 Steps 5-6, eq. (20), target (4)): given the mass bound (17)
`m_r ε⁻¹ ≤ ∑_{b∈I} g_I(a,b)`, the event `ε^{1/4} ≤ m_r`, and the crude bound (19) `G_I(a,a) ≤ ε^{-1/2}`, the ratio
`∑_{b∈I} G_I(b,a) / G_I(a,a)` is at least `ε^{-1/4}`. -/
theorem green_ratio_ge_quarter {m : ℤ → ℤ → ℕ} {I : Set ℤ} {ε mr : ℝ} {a : ℤ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0) (hI : I.Finite) (ha : a ∈ I)
    (hε : 0 < ε) (hq : mr * ε⁻¹ ≤ ∑' b : I, greenKernel m I a b) (hmr : ε ^ (1 / 4 : ℝ) ≤ mr)
    (hGup : greenFn m I a a ≤ ε ^ (-(1 / 2) : ℝ)) :
    ε ^ (-(1 / 4) : ℝ) ≤ (∑' b : I, greenFn m I b a) / greenFn m I a a := by
  have hfirst : ∀ b, ∀ x ∈ I, mLaplacian m (fun y => greenFn m I y b) x = -(if x = b then 1 else 0) :=
    fun b => MatedCRT.WalkPotential.mLaplacian_greenFn hlf hcons hI b
  have hG0 : 0 < greenFn m I a a := greenFn_diag_pos_of_firstStep ha hfirst
  have hdeg : mdeg m a ≠ 0 := mdeg_ne_zero_of_ne_zero hlf (hcons a)
  have hD : (1 : ℝ) ≤ (mdeg m a : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hdeg
  have hQ0 : 0 ≤ ∑' b : I, greenKernel m I a b :=
    tsum_nonneg fun b => div_nonneg (greenFn_nonnegative m I a b) (Nat.cast_nonneg _)
  rw [tsum_greenFn_eq_deg_mul_tsum_kernel hsymm hlf hcons hI]
  exact quarter_le_ratio hε hD hQ0 hq hmr hG0 hGup

end MatedCRT.S5c
