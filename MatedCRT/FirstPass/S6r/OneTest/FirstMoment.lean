import MatedCRT.FirstPass.S6r.OneTest.Count
import MatedCRT.FirstPass.S6r.LocalBudget
import MatedCRT.FirstPass.S6r.Constants
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S6j.StateLocal
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit

/-!
# The first moment of the one-test count (PRO notes step 8 `one_test_from_boundary`; fp-S6r)

Written argument: `notes/fp-gaps/CHATGPT-lemma68-open-parts.md` §B3-B5 (eqs. B8, B10, B13, B14) and PRO step 8.
Notation: `x = η(y)`, `D = B_{R/4}(x)`, `D₀ = B_{c₀R}(x)`, `ID` the discrete interior `I(D)` (exit set of `σ_D`),
`m₀ = μ(D₀)`, `S = V^ε(D₀) \ A`.

* (B13) Green lower bound at each `b ∈ S`: `1/2 ≤ G_{I(D)}(y, b)`, from Lemma 2.16 at radius `R/8`
  (`GreenTest68.hG_of_green`, which needs the ω-wise Lemma 2.16 input `hGr`).
* (B14) `E_y[V_occ] ≥ ∑_{b∈S} G_{I(D)}(y,b) ≥ |S|/2`: pathwise `V_occ ≥ ∑_{b∈S} visits_b` (up to the null set
  `{σ_D = ∞}`) and Tonelli (`lintegral_tsum`).
* (B10) `|S| ≥ ε⁻¹ m₀/2`: the lower count of Lemma 2.9 with `f = 1` (input `hL29`) and the sparsity at the centre `x`
  (`localCount_of_ball`), under the scale condition `4ε^α ≤ m₀` (input `hsc`, B2).

Result: `(1/4) ε⁻¹ μ(D₀) ≤ E_y[V_occ]` with `V_occ = occCount A σ_D` (`OneTest/Count.lean`). The constant `1/4` depends
on no parameter, in particular not on `(γ, ρ)`.

Terminology: Green function of the killed walk (Armitage-Gardiner; Berestycki-Gwynne BG20 Lemma 4.4 for Lemma 2.16);
occupation count and exit time (PRO step 8). Not used: the goodness of `R` at `z` and `b ∈ V(∂B_{4R/3}(z))`; the
first moment needs neither (the conclusion holds without them).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

/-- The occupation count is nonnegative. -/
lemma occCount_nonneg_fm (A : Set ℤ) (σ : (ℕ → ℤ) → ℕ) (w : ℕ → ℤ) : 0 ≤ occCount A σ w :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- On `{σ_D < ∞}` the occupation count is the number of visits to `Aᶜ` before the exit time `σ_D`. -/
lemma ofReal_occCount_eq_visitCount_fm {A ID : Set ℤ} {w : ℕ → ℤ} (hτ : vExitTime ID w < ⊤) :
    ENNReal.ofReal (occCount A (fun w => (vExitTime ID w).toNat) w)
      = ConstantOrderDiv.visitCount ID Aᶜ w := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hτ.ne
  have hσ : (vExitTime ID w).toNat = k := by rw [← hk]; simp
  unfold occCount ConstantOrderDiv.visitCount
  simp only [hσ]
  rw [ENNReal.ofReal_sum_of_nonneg fun n _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _,
    tsum_eq_sum (s := Finset.range k)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnk : (n : ℕ∞) < vExitTime ID w := by
      rw [← hk]
      have : n < k := Finset.mem_range.1 hn
      exact_mod_cast this
    by_cases hm : w n ∈ A <;> simp [hnk, hm]
  · intro n hn
    have hnk : ¬ (n : ℕ∞) < vExitTime ID w := by
      rw [← hk]
      have : ¬ n < k := fun h => hn (Finset.mem_range.2 h)
      exact_mod_cast this
    simp [hnk]

/-- Visits to a smaller set are dominated by visits to a larger set, pathwise. -/
lemma visitCount_mono_set_fm {W E F : Set ℤ} (h : E ⊆ F) (x : ℕ → ℤ) :
    ConstantOrderDiv.visitCount W E x ≤ ConstantOrderDiv.visitCount W F x := by
  unfold ConstantOrderDiv.visitCount
  refine ENNReal.tsum_le_tsum fun n => ?_
  by_cases hx : (n : ℕ∞) < vExitTime W x ∧ x n ∈ E
  · simp [hx.1, hx.2, h hx.2]
  · simp [hx]

/-- A finite expected exit time gives almost sure exit: `{σ = ∞}` is measurable and null. -/
lemma ae_exitTime_lt_top_fm {m : ℤ → ℤ → ℕ} {ID : Set ℤ} {y : ℤ}
    (hfin : expectedExitTime m ID y ≠ ⊤) : ∀ᵐ w ∂(srwLaw m y), vExitTime ID w < ⊤ := by
  rw [ae_iff]
  have hN : MeasurableSet {w : ℕ → ℤ | ¬ vExitTime ID w < ⊤} := by
    have hset : {w : ℕ → ℤ | ¬ vExitTime ID w < ⊤}
        = ⋂ n : ℕ, {w : ℕ → ℤ | (n : ℕ∞) < vExitTime ID w} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h n
        rw [top_le_iff.1 (not_lt.1 h)]
        exact ENat.natCast_lt_top n
      · intro h hlt
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlt.ne
        have hk' := h k
        rw [← hk] at hk'
        exact lt_irrefl _ hk'
    rw [hset]
    exact MeasurableSet.iInter fun n => ConstantOrderDiv.measurableSet_lt_vExitTime ID n
  have hμ : srwLaw m y {w : ℕ → ℤ | ¬ vExitTime ID w < ⊤} = 0 := by
    by_contra hne
    apply hfin
    apply top_unique
    have h1 : ∫⁻ w, {w : ℕ → ℤ | ¬ vExitTime ID w < ⊤}.indicator (fun _ => (⊤ : ℝ≥0∞)) w ∂srwLaw m y
        ≤ ∫⁻ w, (vExitTime ID w : ℝ≥0∞) ∂srwLaw m y := by
      refine lintegral_mono fun w => ?_
      by_cases hw : ¬ vExitTime ID w < ⊤
      · rw [Set.indicator_of_mem (show w ∈ {w : ℕ → ℤ | ¬ vExitTime ID w < ⊤} from hw),
          top_le_iff.1 (not_lt.1 hw)]
        simp
      · rw [Set.indicator_of_notMem (show w ∉ {w : ℕ → ℤ | ¬ vExitTime ID w < ⊤} from hw)]
        exact zero_le
    rw [lintegral_indicator_const hN, ENNReal.top_mul hne] at h1
    exact h1
  exact hμ

/-- **The first moment of the one-test count** (PRO step 8, `E_b[V_occ | h, η] ≥ c₁ ε⁻¹ m₀`, with `c₁ = 1/4`).
`D = B_{R/4}(η y)`, `ID = I(D)` the discrete interior (`hID`), `σ_D = vExitTime ID`, `D₀ = B_{c₀R}(η y)`, `m₀ = μ(D₀)`,
`A` the set of occupied sites. The start is the vertex `y`, the walk law `srwLaw m y` with `m = S.mult ε ω`.

ω-wise named inputs (hypotheses, not frozen Props):
* `hGr`: Lemma 2.16 (`GreenKernelLowerBoundStmt`) at `a = y`, radius `R/8`, for `b ∈ V^ε(D₀)` (as in
  `perState_local_bound_window`); `K.c0 ≤ 1/24` makes `V(D₀) ⊆ V(B_{R/24})` (`Constants68`).
* `hsp`: the Lemma 6.8 sparsity at every centre, radius `r`; `hvol`: the volume lower bound (Lemma 2.7).
* `hfinE`: finite expected exit time of `ID` (Lemma 2.18, second display, with Lemma 2.17).
* `hL29`: the lower count of Lemma 2.9 with `f = 1` on `D₀` (`ε⁻¹ μ(D₀) - ε^{-1+α} ≤ |V^ε(D₀)|`).
* `hsc`: the scale condition `4 ε^α ≤ μ(D₀)` (B2). -/
theorem firstMoment_occCount_fm {γ ρ : ℝ} (K : Constants68 γ ρ) {μ : Measure ℂ} {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} {A ID : Set ℤ} {ε R r α : ℝ} {y : ℤ}
    (hη : Continuous η) (hprop : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hεc : ε ≤ 16 * K.c0) (hR : 0 < R) (hr : 0 < r) (hr2 : r ^ 2 ≤ R) (hcR : K.c0 * R ≤ r)
    (hID : ID = interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 4)))
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η y) (R / 4)).Nonempty →
      diam (cell ε η k) ≤ K.c0 * R)
    (hsp : ∀ w : ℂ, ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) < K.s1 * r ^ (2 * K.βm) / ε)
    (hvol : (K.c0 * R) ^ K.βm ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal)
    (hGr : ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b
          ≤ greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b ∧
        K.C⁻¹ * Real.log (if vertexPoint ε η y = vertexPoint ε η b then ε⁻¹
            else min ((R / 8) / ‖vertexPoint ε η y - vertexPoint ε η b‖) ε⁻¹) - 1
          ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η y) (R / 8))) y b)
    (hfinE : expectedExitTime m ID y ≠ ⊤)
    (hL29 : ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal - ε ^ (-1 + α)
      ≤ ((cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).ncard : ℝ))
    (hsc : 4 * ε ^ α ≤ (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal) :
    (1 / 4 : ℝ) * ε⁻¹ * (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal
      ≤ ∫ w, occCount A (fun w => (vExitTime ID w).toNat) w ∂(srwLaw m y) := by
  have hfinD : (cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R))).Finite :=
    S6j.perState_cellVertices_ball_finite hη hprop hε _ _
  -- the sparsity at the centre `x` (B4/B3: `|A ∩ V(D₀)| ≤ m₀/(4ε)`)
  have hloc := localCount_of_ball (μ := μ) (ε := ε) (η := η) (A := A) (x := vertexPoint ε η y)
    (R := R) (r := r) (s1 := K.s1) (β := K.βm) (c0 := K.c0) hε K.hs1.le
    (by linarith [K.one_le_βm]) hr hR K.hc0 hcR hr2 K.hs1small
    (fun z => S6j.perState_cellVertices_ball_finite hη hprop hε z r) hsp hvol
  set V := cellVertices ε η (ball (vertexPoint ε η y) (K.c0 * R)) with hVdef
  set m0 := (μ (ball (vertexPoint ε η y) (K.c0 * R))).toReal with hm0
  obtain ⟨S, hS⟩ : ∃ S : Set ℤ, S = V \ A := ⟨_, rfl⟩
  have hSV : S ⊆ V := by rw [hS]; exact Set.sdiff_subset
  have hSA : ∀ b ∈ S, b ∉ A := by
    intro b hb
    rw [hS] at hb
    exact hb.2
  have hSfin : S.Finite := hfinD.subset hSV
  -- (B10): `|S| ≥ ε⁻¹ m₀ / 2`
  have hcardSum : ((V \ A).ncard : ℝ) + ((V ∩ A).ncard : ℝ) = V.ncard := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard V A hfinD
    have h2 : (V \ A).ncard + (V ∩ A).ncard = V.ncard := by rw [add_comm]; exact h
    exact_mod_cast h2
  have hrpow : ε ^ (-1 + α) = ε⁻¹ * ε ^ α := by
    rw [Real.rpow_add hε, Real.rpow_neg_one]
  have hloc' : ((V ∩ A).ncard : ℝ) ≤ m0 / (4 * ε) := by
    rw [Set.inter_comm]
    exact hloc
  have hS_lower : ε⁻¹ * m0 / 2 ≤ (S.ncard : ℝ) := by
    have e1 : m0 / (4 * ε) = ε⁻¹ * (m0 / 4) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    have e2 : ε⁻¹ * ε ^ α ≤ ε⁻¹ * (m0 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hε.le)
    rw [hrpow] at hL29
    rw [hS]
    linarith [e1, e2, hL29, hloc', hcardSum]
  -- (B13): the Green lower bound `1/2 ≤ G_{I(D)}(y, b)` for `b ∈ S`
  have hG : ∀ b ∈ S, ENNReal.ofReal (1 / 2) ≤ ∫⁻ w, visitsBeforeExit ID b w ∂srwLaw m y := by
    intro b hb
    have hbV : b ∈ V := hSV hb
    rw [GreenTest68.lintegral_visits_eq_tsum, hID]
    exact GreenTest68.hG_of_green hη hε hR K.hC K.hc0 K.c0_lt_eighth K.hc0C hεc hdiam hbV (hGr b hbV)
  -- (B14): Tonelli, `∫⁻ visitCount ID S = ∑_{b∈S} ∫⁻ visits_b`
  have hsum : ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y
      = ∑' b : S, ∫⁻ w, visitsBeforeExit ID (b : ℤ) w ∂srwLaw m y := by
    calc ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y
        = ∫⁻ w, ∑' b : S, visitsBeforeExit ID (b : ℤ) w ∂srwLaw m y :=
          lintegral_congr fun w => (ConstantOrderDiv.tsum_visitsBeforeExit ID S w).symm
      _ = ∑' b : S, ∫⁻ w, visitsBeforeExit ID (b : ℤ) w ∂srwLaw m y :=
          lintegral_tsum fun b => (ConstantOrderDiv.measurable_visitsBeforeExit ID b).aemeasurable
  have hlow : ∑' _ : S, ENNReal.ofReal (1 / 2)
      ≤ ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y := by
    rw [hsum]
    exact ENNReal.tsum_le_tsum fun b => hG b.1 b.2
  have hcard : ∑' _ : S, ENNReal.ofReal (1 / 2) = (S.ncard : ℝ≥0∞) * ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.tsum_set_const, ← hSfin.cast_ncard_eq]
    simp
  -- the upper side is finite, and `V_occ ≤ σ` and the visit count are dominated by `σ`
  have hVA_ne : ∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y ≠ ⊤ :=
    ne_top_of_le_ne_top hfinE (lintegral_mono fun w => ConstantOrderDiv.visitCount_le ID Aᶜ w)
  have hle : ∫⁻ w, ConstantOrderDiv.visitCount ID S w ∂srwLaw m y
      ≤ ∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y :=
    lintegral_mono fun w => visitCount_mono_set_fm (fun b hb => hSA b hb) w
  have hfinal : (S.ncard : ℝ≥0∞) * ENNReal.ofReal (1 / 2)
      ≤ ∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y := by
    rw [← hcard]
    exact hlow.trans hle
  have hreal := ENNReal.toReal_mono hVA_ne hfinal
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by norm_num)] at hreal
  -- identify the Bochner integral with the lintegral of the visit count (a.e., on `{σ < ∞}`)
  have hae : ∀ᵐ w ∂srwLaw m y,
      ENNReal.ofReal (occCount A (fun w => (vExitTime ID w).toNat) w)
        = ConstantOrderDiv.visitCount ID Aᶜ w := by
    filter_upwards [ae_exitTime_lt_top_fm hfinE] with w hw
    exact ofReal_occCount_eq_visitCount_fm hw
  have hmeas : AEStronglyMeasurable (fun w => occCount A (fun w => (vExitTime ID w).toNat) w)
      (srwLaw m y) := by
    refine ((ENNReal.measurable_toReal.comp
      (ConstantOrderDiv.measurable_visitCount ID Aᶜ)).aestronglyMeasurable).congr ?_
    filter_upwards [hae] with w hw
    simp only [Function.comp_apply]
    rw [← hw, ENNReal.toReal_ofReal (occCount_nonneg_fm _ _ w)]
  have hint : ∫ w, occCount A (fun w => (vExitTime ID w).toNat) w ∂srwLaw m y
      = (∫⁻ w, ConstantOrderDiv.visitCount ID Aᶜ w ∂srwLaw m y).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => occCount_nonneg_fm _ _ w)
      hmeas]
    exact congrArg ENNReal.toReal (lintegral_congr_ae hae)
  rw [hint]
  linarith [hS_lower, hreal]

end Lemma68Window
end MatedCRT
