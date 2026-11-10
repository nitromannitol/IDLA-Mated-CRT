import MatedCRT.FirstPass.S4S6c.ShellConstants68
import HarmonicBalls.Defs.Notation

/-!
# The constants of the shell chain in dependency order (q2, fp-S4S6c-constants-order, Q1)

The order of `notes/fp-gaps/CHATGPT-234-idla-6-8-q2-constants-PRO.md` (Q1, "Correct dependency order" and "Lean interface
ruling"): the exponents and the mesh constants first; then `c₀ := K.c0` with `K := shellK68`; then the window prevalence
constants `C_good`, `C_fail` from `hprev` at `(shortExp ζ, γ, c₀)`; then the constant `C_hone` of the one-test bound; only
then `q₀ ≤ 1/(64 C_hone)`, and only then the radius cutoff and `s₀`.

* `AnnulusCover68 N`: for every `R > 0` and centre `z`, the open annulus `𝔸_{R,2R}(z)` is covered by at most `N` balls of
  radius `R` centred in the annulus. This is the deterministic covering behind the hypothesis `hN` of
  `shellOneTest_of_direct` (ShellHoneInst68.lean). Proof: compactness of the closed unit annulus `{1 ≤ |w| ≤ 2}` and scaling.
* `shellNcov68`: a universal count `N_cov` with `AnnulusCover68 N_cov` (independent of the environment, `r` and `s₀`).
* `shellC068 = (shellK68 …).c0` (`Real.exp (-2) / 32`, ShellConstants68.lean `shellK68_c0`): the common constant of the good
  annulus event and of the one-test bound.
* `shellDbl68 C := max 1 C` (the doubling constant `Dbl`), `shellChone68 CE C` (the constant `C_hone`, with `C_exit := CE`
  and `C_good := C`). The deterministic side condition `hCw` holds by `le_max_right`.

Terminology: Euclidean annulus covering (Armitage-Gardiner), good annuli and the one-test bound (Armstrong-Kuusi-Mourrat).
-/

open Set Filter Metric

namespace MatedCRT
namespace Lemma68ConstOrder

/-- **The annulus cover property.** `AnnulusCover68 N`: for all `R > 0` and `z ∈ ℂ`, the open annulus
`𝔸_{R,2R}(z) = B_{2R}(z) \ closedBall z R` is covered by at most `N` balls of radius `R` centred in the annulus. -/
def AnnulusCover68 (N : ℕ) : Prop :=
  ∀ (R : ℝ) (z : ℂ), 0 < R → ∃ t : Finset ℂ, t.card ≤ N ∧ (∀ v ∈ t, v ∈ HarmonicBalls.annulus z R (2 * R)) ∧
    HarmonicBalls.annulus z R (2 * R) ⊆ ⋃ v ∈ t, ball v R

/-- The closed unit annulus `{1 ≤ |w| ≤ 2}` is covered by finitely many unit balls centred in the open annulus
`{1 < |v| < 2}`. -/
theorem unit_annulus_cover : ∃ T : Finset ℂ, (∀ v ∈ T, 1 < ‖v‖ ∧ ‖v‖ < 2) ∧
    ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ ≤ 2 → ∃ v ∈ T, ‖w - v‖ < 1 := by
  set S : Set ℂ := {v | 1 < ‖v‖ ∧ ‖v‖ < 2} with hS
  set K : Set ℂ := {w | 1 ≤ ‖w‖ ∧ ‖w‖ ≤ 2} with hK
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · exact Metric.isBounded_closedBall.subset (fun w hw => mem_closedBall_zero_iff.2 hw.2)
  have hcov : K ⊆ ⋃ i : S, ball (i : ℂ) 1 := by
    rintro w ⟨h1, h2⟩
    have ha : 0 < ‖w‖ := by linarith
    set v : ℂ := ((3 / 2 : ℝ) / ‖w‖) • w with hv
    have hvn : ‖v‖ = 3 / 2 := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ ha.ne']
    have hwv : ‖w - v‖ < 1 := by
      have e : w - v = (1 - (3 / 2 : ℝ) / ‖w‖) • w := by rw [hv, sub_smul, one_smul]
      have e2 : ‖w - v‖ = |‖w‖ - 3 / 2| := by
        rw [e, norm_smul, Real.norm_eq_abs]
        have h3 : 1 - (3 / 2 : ℝ) / ‖w‖ = (‖w‖ - 3 / 2) / ‖w‖ := by field_simp
        rw [h3, abs_div, abs_of_pos ha, div_mul_cancel₀ _ ha.ne']
      rw [e2, abs_lt]
      constructor <;> linarith
    have hvS : v ∈ S := by
      refine ⟨?_, ?_⟩ <;> rw [hvn] <;> norm_num
    exact mem_iUnion.2 ⟨⟨v, hvS⟩, by rw [mem_ball, dist_eq_norm]; exact hwv⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun i : S => ball (i : ℂ) 1) (fun _ => isOpen_ball) hcov
  refine ⟨t.image (fun i : S => (i : ℂ)), ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
    exact i.2
  · intro w h1 h2
    obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.1 (ht ⟨h1, h2⟩)
    refine ⟨(i : ℂ), Finset.mem_image_of_mem _ hi, ?_⟩
    rw [mem_ball, dist_eq_norm] at hwi
    exact hwi

/-- **Existence of the annulus cover count.** Scaling and translating the unit cover gives `AnnulusCover68 N` with
`N` the cardinality of the unit cover. -/
theorem annulusCover68_exists : ∃ N : ℕ, AnnulusCover68 N := by
  obtain ⟨T, hT, hcov⟩ := unit_annulus_cover
  refine ⟨T.card, fun R z hR => ?_⟩
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  refine ⟨T.image (fun v : ℂ => z + (R : ℂ) * v), Finset.card_image_le, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, h2⟩ := hT v hv
    have hd : dist (z + (R : ℂ) * v) z = R * ‖v‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    unfold HarmonicBalls.annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, hd]
      nlinarith
    · rw [mem_closedBall, hd, not_le]
      nlinarith
  · intro w hw
    unfold HarmonicBalls.annulus at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [mem_ball, dist_eq_norm] at hw1
    rw [mem_closedBall, dist_eq_norm, not_le] at hw2
    set u : ℂ := (R : ℂ)⁻¹ * (w - z) with hu
    have hun : ‖u‖ = ‖w - z‖ / R := by
      rw [hu, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
      ring
    have hu1 : 1 ≤ ‖u‖ := by
      rw [hun, le_div_iff₀ hR]
      linarith
    have hu2 : ‖u‖ ≤ 2 := by
      rw [hun, div_le_iff₀ hR]
      linarith
    obtain ⟨v, hv, huv⟩ := hcov u hu1 hu2
    refine mem_iUnion₂.2 ⟨z + (R : ℂ) * v, Finset.mem_image_of_mem _ hv, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have e : w - (z + (R : ℂ) * v) = (R : ℂ) * (u - v) := by
      rw [hu, mul_sub, ← mul_assoc, mul_inv_cancel₀ hRc, one_mul]
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact (mul_lt_iff_lt_one_right hR).2 huv

/-- The universal count `N_cov` of balls covering an annulus (`N_cov` of the one-test bound, hypothesis `hN`). -/
noncomputable def shellNcov68 : ℕ := Classical.choose annulusCover68_exists

theorem shellNcov68_spec : AnnulusCover68 shellNcov68 := Classical.choose_spec annulusCover68_exists

/-- `c₀ = K.c0` for `K := shellK68 γ ρ ω₀ ζ` (`shellK68_c0`, ShellConstants68.lean): the single constant of the good
annulus event `IsGoodAnnulusEvent` and of the one-test bound. It does not depend on `γ, ρ, ω₀, ζ`. -/
noncomputable def shellC068 : ℝ := Real.exp (-2) / 32

/-- The doubling constant `Dbl := max 1 C_good` of the one-test bound. -/
noncomputable def shellDbl68 (Cg : ℝ) : ℝ := max 1 Cg

/-- The constant `C_hone` of the one-test bound (`hone_exitQ_walk_of_env_direct`, side conditions `hCw`, `hC`), with
`C_exit := CE` and `C_good := Cg`: `max 1 (32 CE² ((1 + N_cov log 4) Cg)² Dbl²)`. -/
noncomputable def shellChone68 (CE Cg : ℝ) : ℝ :=
  max 1 (32 * CE ^ 2 * ((1 + (shellNcov68 : ℝ) * Real.log 4) * Cg) ^ 2 * shellDbl68 Cg ^ 2)

theorem one_le_shellChone68 (CE Cg : ℝ) : 1 ≤ shellChone68 CE Cg :=
  le_max_left _ _

/-- The side condition `hCw` of the one-test bound, at the constant `C_hone`. -/
theorem shellChone68_hCw (CE Cg : ℝ) :
    32 * CE ^ 2 * ((1 + (shellNcov68 : ℝ) * Real.log 4) * Cg) ^ 2 * shellDbl68 Cg ^ 2 ≤ shellChone68 CE Cg :=
  le_max_right _ _

/-- An admissible `q₀` exists once `C_hone` is known: `0 < q₀ ≤ (1/4)²/(4 C_hone)`. -/
theorem exists_shellQ0_68 (CE Cg : ℝ) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE Cg) := by
  have hC : 0 < shellChone68 CE Cg := lt_of_lt_of_le one_pos (one_le_shellChone68 CE Cg)
  have hbig : 0 < (1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE Cg) := by positivity
  exact ⟨(1 / 4 : ℝ) ^ 2 / (4 * shellChone68 CE Cg) / 2, by positivity, by linarith⟩

/-- **The ball ratio at the Green constant `CG` (q2, fp-S4S6c-cg-param, lead item 3: parameterize).** `shellC0 CG =
exp(-2CG)/32`: the Lemma 6.8 constant `c₀` with `c₀ ≤ exp(-2CG)/16` (`Constants68.hc0C` at `C = CG`, S6r/Constants.lean:71).
At `CG = 1` it is `shellC068`. Used by the CG Eps family (Guard68S10 `shellEps0ZCG`, `shellS1CG`; ShellChainCore68;
ShellHoneInst68). -/
noncomputable def shellC0 (CG : ℝ) : ℝ := Real.exp (-(2 * CG)) / 32

/-- `shellC0 1 = shellC068`. -/
theorem shellC0_one : shellC0 1 = shellC068 := by
  unfold shellC0 shellC068
  norm_num

/-- For `CG > 0`: `0 < shellC0 CG < 1/5` (the range `0 < c₀ < 1/5` of `ShortWindowGoodRadiusPrevalenceStmt`,
S6r/ShortWindow.lean:61-62). -/
theorem shellC0_bounds (CG : ℝ) (hCG : 0 < CG) : 0 < shellC0 CG ∧ shellC0 CG < 1 / 5 := by
  unfold shellC0
  have h := Real.exp_le_one_iff.2 (show -(2 * CG) ≤ 0 by linarith)
  exact ⟨by positivity, by linarith⟩

end Lemma68ConstOrder
end MatedCRT

#print axioms MatedCRT.Lemma68ConstOrder.annulusCover68_exists
#print axioms MatedCRT.Lemma68ConstOrder.shellNcov68_spec
#print axioms MatedCRT.Lemma68ConstOrder.exists_shellQ0_68
