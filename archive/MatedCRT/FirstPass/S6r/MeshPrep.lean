import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

end Lemma68Window
end MatedCRT
