import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MatedCRT.FirstPass.S6r.OneTest.SecondMoment
import MatedCRT.FirstPass.S6f.UniformEvents

/-!
# Common mesh preparation (PRO step 5 `common_mesh_preparation`; Lemma 6.8 redesign)

Deterministic consequences of the step-1 exponent choice (PRO notes, step 1: `2ω < κ, ω_G` and `2βω < α_cnt, α_ex`) for
the four mesh inequalities of step 5, for scales `0 < ε ≤ ε₀` and radii `r ≥ 10 ε^ω` with `r² ≤ d`. Since
`d ≥ r² ≥ 100 ε^{2ω}`, the mesh bound `h ≤ ε^κ` (cell-size event of Lemma 2.8) gives `h ≤ d/100`.

Smallness. PRO step 5 justifies the constant-carrying inequalities `ε^{α_cnt} ≤ (1/8) c_vol c0^β d^β` and
`ε^{α_ex} ≤ (1/8) c_vol 4^{-β} d^β` by "the exponent inequalities in Step 1 are strict". Strictness alone does not absorb
the constants `(1/8) c_vol c0^β 100^β`; they are absorbed for `ε ≤ ε₀`, with `ε₀` depending only on `(γ, ρ)` through the
constants. `mesh_prep_uniform` makes that threshold explicit.

Volume exponent `β ≥ 1` (PRO notes, `β := β⁻`; `Constants68.one_le_βm` gives it from `β⁻ > (2+γ)²/2 ≥ 2`).
-/

open MeasureTheory Metric HarmonicBalls

namespace MatedCRT
namespace Lemma68Window

/-- `ε^(2ω) = (ε^ω)²` for `ε ≥ 0`. -/
lemma rpow_two_mul_eq_sq {ε ω : ℝ} (hε : 0 ≤ ε) : ε ^ (2 * ω) = (ε ^ ω) ^ 2 := by
  rw [mul_comm, Real.rpow_mul hε, Real.rpow_two]

/-- `(100 ε^{2ω})^β = 100^β ε^{2βω}` for `ε ≥ 0`. -/
lemma mul_rpow_hundred_eq {ε ω β : ℝ} (hε : 0 ≤ ε) :
    (100 * ε ^ (2 * ω)) ^ β = (100 : ℝ) ^ β * ε ^ (2 * β * ω) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε _), ← Real.rpow_mul hε,
    show 2 * ω * β = 2 * β * ω by ring]

/-- Splitting `ε^α = ε^{2βω} ε^{α - 2βω}`: a bound on the remainder exponent with constant `K 100^β` and the lower
bound `100^β ε^{2βω} ≤ d^β` give `ε^α ≤ K d^β`. -/
lemma rpow_le_of_split {ε α β ω K d : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hpow : (100 : ℝ) ^ β * ε ^ (2 * β * ω) ≤ d ^ β)
    (hexp : ε ^ (α - 2 * β * ω) ≤ K * 100 ^ β) : ε ^ α ≤ K * d ^ β := by
  have e : ε ^ α = ε ^ (2 * β * ω) * ε ^ (α - 2 * β * ω) := by
    rw [← Real.rpow_add hε]; congr 1; ring
  rw [e]
  calc ε ^ (2 * β * ω) * ε ^ (α - 2 * β * ω)
      ≤ ε ^ (2 * β * ω) * (K * 100 ^ β) :=
        mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hε.le _)
    _ = K * (100 ^ β * ε ^ (2 * β * ω)) := by ring
    _ ≤ K * d ^ β := mul_le_mul_of_nonneg_left hpow hK

/-- PRO step 5, deterministic form: on a scale `ε ≤ 1` with `10 ε^ω ≤ r`, `r² ≤ d`, and mesh bound `h ≤ ε^κ`, the four
mesh inequalities hold, given the step-1 exponent conditions and the smallness inputs `hεcnt`, `hεex`. -/
theorem mesh_prep_inequalities {ε ω κ ωG αcnt αex β cvol c0 h r d : ℝ}
    (hω : 0 < ω) (hβ : 1 ≤ β) (hκ : 2 * ω < κ) (hωG : 2 * ω < ωG)
    (hex : 2 * β * ω < αex) (hcvol : 0 < cvol) (hc0 : 0 < c0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεcnt : ε ^ (αcnt - 2 * β * ω) ≤ 1 / 8 * cvol * c0 ^ β * 100 ^ β)
    (hεex : ε ^ (αex - 2 * β * ω) ≤ 1 / 8 * cvol * 4 ^ (-β) * 100 ^ β)
    (hεκ : ε ^ (κ - 2 * ω) ≤ c0)
    (hr : 10 * ε ^ ω ≤ r) (hd : r ^ 2 ≤ d) (hh : h ≤ ε ^ κ) :
    h ≤ d / 100 ∧ ε ^ ωG ≤ d / 8 ∧ ε ^ αcnt ≤ 1 / 8 * cvol * c0 ^ β * d ^ β ∧
      ε ^ αex ≤ min (d / 100) (1 / 8 * cvol * 4 ^ (-β) * d ^ β) ∧ ε ^ κ ≤ c0 * d / 100 := by
  have hεω : 0 ≤ ε ^ ω := Real.rpow_nonneg hε.le ω
  -- d ≥ r² ≥ 100 ε^{2ω}
  have hd100 : 100 * ε ^ (2 * ω) ≤ d := by
    rw [rpow_two_mul_eq_sq hε.le]
    have h1 : (10 * ε ^ ω) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hr 2
    have h2 : (10 * ε ^ ω) ^ 2 = 100 * (ε ^ ω) ^ 2 := by ring
    linarith
  have hdpos : 0 < d := by
    have := Real.rpow_pos_of_pos hε (2 * ω)
    linarith
  have hpow : (100 : ℝ) ^ β * ε ^ (2 * β * ω) ≤ d ^ β := by
    rw [← mul_rpow_hundred_eq hε.le]
    exact Real.rpow_le_rpow (by positivity) hd100 (by linarith)
  have hε2 : ε ^ (2 * ω) ≤ d / 100 := by linarith
  have hκ' : ε ^ κ ≤ ε ^ (2 * ω) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hκ.le
  have hωG' : ε ^ ωG ≤ ε ^ (2 * ω) := Real.rpow_le_rpow_of_exponent_ge hε hε1 hωG.le
  have h2αex : 2 * ω ≤ αex := by nlinarith
  have hαex' : ε ^ αex ≤ ε ^ (2 * ω) := Real.rpow_le_rpow_of_exponent_ge hε hε1 h2αex
  have hKc : 0 ≤ 1 / 8 * cvol * c0 ^ β :=
    mul_nonneg (mul_nonneg (by norm_num) hcvol.le) (Real.rpow_nonneg hc0.le β)
  have hKe : 0 ≤ 1 / 8 * cvol * 4 ^ (-β) :=
    mul_nonneg (mul_nonneg (by norm_num) hcvol.le) (Real.rpow_nonneg (by norm_num) _)
  have hκc : ε ^ κ ≤ c0 * d / 100 := by
    have e : ε ^ κ = ε ^ (2 * ω) * ε ^ (κ - 2 * ω) := by
      rw [← Real.rpow_add hε]; congr 1; ring
    calc ε ^ κ = ε ^ (2 * ω) * ε ^ (κ - 2 * ω) := e
      _ ≤ ε ^ (2 * ω) * c0 := mul_le_mul_of_nonneg_left hεκ (Real.rpow_nonneg hε.le _)
      _ ≤ (d / 100) * c0 := mul_le_mul_of_nonneg_right hε2 hc0.le
      _ = c0 * d / 100 := by ring
  refine ⟨?_, ?_, ?_, ?_, hκc⟩
  · linarith
  · linarith
  · exact rpow_le_of_split hε hKc hpow hεcnt
  · exact le_min (le_trans hαex' hε2) (rpow_le_of_split hε hKe hpow hεex)

/-- Smallness threshold: for `δ > 0` and `K > 0`, `ε^δ ≤ K` for all `0 < ε ≤ ε₀`, with `ε₀ = K^{1/δ}`. -/
theorem exists_eps_threshold {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ε ^ δ ≤ K :=
  ⟨K ^ δ⁻¹, Real.rpow_pos_of_pos hK _, fun ε hε hle => by
    calc ε ^ δ ≤ (K ^ δ⁻¹) ^ δ := Real.rpow_le_rpow hε.le hle hδ.le
      _ = K := Real.rpow_inv_rpow hK.le hδ.ne'⟩

/-- PRO step 5, uniform form: there is `ε₀ > 0` (depending on `ω, κ, ω_G, α_cnt, α_ex, β, c_vol, c0` only) such that for
every `0 < ε ≤ ε₀`, every radius `r ≥ 10 ε^ω`, every `d ≥ r²` and every mesh bound `h ≤ ε^κ`, the mesh inequalities hold.
The last conjunct `ε^κ ≤ c0 d/100` is open-parts B2 (`d := ε^κ ≤ c0 δ/100`), not PRO step 5. -/
theorem mesh_prep_uniform (ω κ ωG αcnt αex β cvol c0 : ℝ)
    (hω : 0 < ω) (hβ : 1 ≤ β) (hκ : 2 * ω < κ) (hωG : 2 * ω < ωG)
    (hcnt : 2 * β * ω < αcnt) (hex : 2 * β * ω < αex) (hcvol : 0 < cvol) (hc0 : 0 < c0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε h r d : ℝ, 0 < ε → ε ≤ ε₀ → 10 * ε ^ ω ≤ r → r ^ 2 ≤ d → h ≤ ε ^ κ →
      h ≤ d / 100 ∧ ε ^ ωG ≤ d / 8 ∧ ε ^ αcnt ≤ 1 / 8 * cvol * c0 ^ β * d ^ β ∧
        ε ^ αex ≤ min (d / 100) (1 / 8 * cvol * 4 ^ (-β) * d ^ β) ∧ ε ^ κ ≤ c0 * d / 100 := by
  obtain ⟨e₁, he₁, h₁⟩ := exists_eps_threshold (δ := αcnt - 2 * β * ω)
    (K := 1 / 8 * cvol * c0 ^ β * 100 ^ β) (by linarith)
    (mul_pos (mul_pos (mul_pos (by norm_num) hcvol) (Real.rpow_pos_of_pos hc0 β))
      (Real.rpow_pos_of_pos (by norm_num) β))
  obtain ⟨e₂, he₂, h₂⟩ := exists_eps_threshold (δ := αex - 2 * β * ω)
    (K := 1 / 8 * cvol * 4 ^ (-β) * 100 ^ β) (by linarith)
    (mul_pos (mul_pos (mul_pos (by norm_num) hcvol) (Real.rpow_pos_of_pos (by norm_num) _))
      (Real.rpow_pos_of_pos (by norm_num) β))
  obtain ⟨e₃, he₃, h₃⟩ := exists_eps_threshold (δ := κ - 2 * ω) (K := c0) (by linarith) hc0
  refine ⟨min 1 (min e₁ (min e₂ e₃)), lt_min one_pos (lt_min he₁ (lt_min he₂ he₃)),
    fun ε h r d hε hle hr hd hh => ?_⟩
  have hε1 : ε ≤ 1 := le_trans hle (min_le_left _ _)
  have hle1 : ε ≤ e₁ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle2 : ε ≤ e₂ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hle3 : ε ≤ e₃ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  exact mesh_prep_inequalities hω hβ hκ hωG hex hcvol hc0 hε hε1 (h₁ ε hε hle1) (h₂ ε hε hle2)
    (h₃ ε hε hle3) hr hd hh

/-- **Second-moment inputs discharged from the prepared event** (PRO step 8; the omega-wise hypotheses of
`secondMoment_occCount`). For a shell test `(z, R, r, d, b)` with `d ≤ R ≤ 1`, `r² ≤ d`, `10 ε^ω ≤ r`, and
`ρ < 1`, `‖z‖ + 3R ≤ ρ` (the relevant `B_{3R}(z)` lies in the prepared region), the four events of the Draft
statements at `ω` discharge `hmom` (Lemma 2.18, `exitTimeEvent68`), `hvol` (Lemma 2.7, `ballMassLowerEvent68`), the
cell-size input `hcell`, `hh` (Lemma 2.8, `cellSizeEvent68`), the `hεα`, `hεmass`, `hx1`, `hρ` side conditions, and the
mesh inequalities of `mesh_prep_uniform`. Remaining named inputs: `IsGoodAnnulusEvent` (`hgood`), the a.s. properties
`hpos`, `hfin`, `hatom`, `hfinD` of the field, and the covering `hN`. -/
theorem secondMoment_of_events {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {γ ρ ζc αex CE ωm ωG αcnt βm c0 C_good : ℝ} (N_cov : ℕ)
    (hωm : 0 < ωm) (hβ : 1 ≤ βm) (hκ : 2 * ωm < 2 / (2 + γ) ^ 2 - ζc) (hωG : 2 * ωm < ωG)
    (hcnt : 2 * βm * ωm < αcnt) (hex : 2 * βm * ωm < αex) (hc0 : 0 < c0) (hc0' : c0 < 1 / 5)
    (hCg : 0 ≤ C_good) (hρ1 : ρ < 1)
    (hN : ∀ (R' : ℝ) (z' : ℂ), 0 < R' → ∃ t : Finset ℂ, t.card ≤ N_cov ∧
      (∀ v ∈ t, v ∈ annulus z' R' (2 * R')) ∧ annulus z' R' (2 * R') ⊆ ⋃ v ∈ t, ball v R') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (ω : Ω) (z x : ℂ) (R r d : ℝ) (b : ℤ) (A : Set ℤ),
      Continuous (S.η ω) → ω ∈ cellSizeEvent68 S γ ζc ρ ε → ω ∈ exitTimeEvent68 S αex ρ CE ε →
      ω ∈ ballMassLowerEvent68 S βm (R / 4) → 0 < R → R ≤ 1 → d ≤ R → r ^ 2 ≤ d → 10 * ε ^ ωm ≤ r →
      ‖z‖ + 3 * R ≤ ρ → b ∈ cellVertices ε (S.η ω) (sphere z (4 * R / 3)) → x = S.η ω (ε * b) →
      IsGoodAnnulusEvent (S.μ ω) c0 C_good R z → 0 < ⨅ w ∈ annulus z R (2 * R), S.μ ω (ball w (c0 * R)) →
      S.μ ω (ball z (3 * R)) ≠ ⊤ → (∀ v ∈ annulus z R (2 * R), S.μ ω {v} = 0) →
      S.μ ω (ball x (3 * c0 * R)) ≠ ⊤ →
      ∫ w, occCount A (fun w => (vExitTime (interiorCellVertices ε (S.η ω) (ball x (R / 4))) w).toNat) w ^ 2
          ∂(srwLaw (S.mult ε ω) b)
        ≤ 32 * CE ^ 2 * ((1 + N_cov * Real.log 4) * C_good) ^ 2 * ε⁻¹ ^ 2 * (1 + Real.log (1 / R)) ^ 2
          * (S.μ ω (ball x (3 * c0 * R))).toReal ^ 2 := by
  obtain ⟨ε₀, hε₀, hmesh⟩ := mesh_prep_uniform ωm (2 / (2 + γ) ^ 2 - ζc) ωG αcnt αex βm 1 c0
    hωm hβ hκ hωG hcnt hex one_pos hc0
  refine ⟨ε₀, hε₀, fun ε hε hεle ω z x R r d b A hηc hcell hexit hvol hR hR1 hdR hr2 hr hreg hb hx
    hgood hpos hfin hatom hfinD => ?_⟩
  obtain ⟨_, _, _, m4, m5⟩ := hmesh ε (ε ^ (2 / (2 + γ) ^ 2 - ζc)) r d hε hεle hr hr2 le_rfl
  have hd0 : 0 ≤ d := le_trans (sq_nonneg r) hr2
  have hcellω := hcell
  simp only [cellSizeEvent68, Set.mem_ofPred_eq] at hcellω
  have hexit' := hexit
  simp only [exitTimeEvent68, Set.mem_ofPred_eq] at hexit'
  have hvol' := hvol
  simp only [ballMassLowerEvent68, Set.mem_ofPred_eq] at hvol'
  -- the boundary point p of the cell of b (`b ∈ V^ε(∂B_{4R/3}(z))`)
  obtain ⟨p, hp1, hp2⟩ := id hb
  have hpz : ‖p - z‖ = 4 * R / 3 := by
    rw [← dist_eq_norm]; exact mem_sphere.1 hp2
  have hpball : p ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' p z
    linarith
  have hbd : Bornology.IsBounded (cell ε (S.η ω) b) :=
    (isCompact_Icc.image hηc).isBounded
  have hdiam : diam (cell ε (S.η ω) b) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) :=
    (hcellω b ⟨p, hp1, hpball⟩).2
  have hxcell : x ∈ cell ε (S.η ω) b := by
    refine ⟨ε * b, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, hx.symm⟩
  have hkR : ε ^ (2 / (2 + γ) ^ 2 - ζc) ≤ R / 100 := by
    have hc0d : c0 * d ≤ R := by nlinarith
    linarith [m5]
  have hdistpx : dist x p ≤ R / 100 := by
    have := Metric.dist_le_diam_of_mem hbd hxcell hp1
    linarith [hdiam, hkR]
  have hxz : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100 := by
    have h3 := abs_norm_sub_norm_le (x - z) (p - z)
    rw [show (x - z) - (p - z) = x - p by ring, ← dist_eq_norm x p, hpz] at h3
    have h5 := abs_le.1 (h3.trans hdistpx)
    constructor <;> linarith [h5.1, h5.2]
  have hxnorm : ‖x‖ < ρ - R / 4 := by
    have hn := norm_add_le (x - z) z
    rw [sub_add_cancel] at hn
    linarith [hxz.2, hreg]
  have hx1 : ‖x‖ < 1 - R / 4 := by linarith
  have hxball : x ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball, dist_zero_right]; linarith
  have hρ' : ball x (R / 4) ⊆ ball (0 : ℂ) ρ := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    rw [mem_ball, dist_zero_right]
    have hn := norm_add_le (u - x) x
    rw [sub_add_cancel] at hn
    linarith
  have hεα : ε ^ αex ≤ R / 100 := by
    have := le_trans m4 (min_le_left _ _)
    linarith
  have hpow : d ^ βm ≤ R ^ βm := Real.rpow_le_rpow hd0 hdR (by linarith)
  have h4 : (0 : ℝ) ≤ 4 ^ (-βm) := Real.rpow_nonneg (by norm_num) _
  have hR4 : (R / 4) ^ βm = 4 ^ (-βm) * R ^ βm := by
    rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_inv_mul]
  have hX : 0 ≤ 4 ^ (-βm) * d ^ βm := mul_nonneg h4 (Real.rpow_nonneg hd0 _)
  have hεmass : ε ^ αex ≤ (R / 4) ^ βm := by
    have m4b := le_trans m4 (min_le_right _ _)
    rw [hR4]
    nlinarith [mul_le_mul_of_nonneg_left hpow h4]
  have hcellb : ∀ q ∈ cell ε (S.η ω) b, ∀ q' ∈ cell ε (S.η ω) b, dist q q' ≤ ε ^ (2 / (2 + γ) ^ 2 - ζc) :=
    fun q hq q' hq' => (Metric.dist_le_diam_of_mem hbd hq hq').trans hdiam
  have hmom := hexit'.1
  have hvol'' : ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ βm) ≤ S.μ ω (ball y (R / 4)) :=
    hvol'
  exact secondMoment_occCount (m := S.mult ε ω) (μ := S.μ ω) (η := S.η ω)
    (ID := interiorCellVertices ε (S.η ω) (ball x (R / 4))) (A := A) (ε := ε) (R := R) (α := αex)
    (ρ := ρ) (C_exit := CE) (c₀ := c0) (C_good := C_good) (βm := βm)
    (h := ε ^ (2 / (2 + γ) ^ 2 - ζc)) N_cov (z := z) (x := x) (b := b) rfl hε hR hR1 hc0 hc0'
    hCg hεα hεmass hb hx hcellb hkR hx1 hvol'' hρ' hmom hgood hN hpos hfin hatom hfinD

end Lemma68Window
end MatedCRT
