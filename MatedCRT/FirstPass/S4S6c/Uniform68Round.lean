import Mathlib

/-!
# Grid rounding of LEMMA68 (`Q_δ`, eq (C2)) (q2, task fp-S4S6c-envscaling-6-7-6-8)

The write-up (`notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, line 674) uses the Borel rounding map
`Q_δ(x₁, x₂) = g (⌊x₁/g + 1/2⌋, ⌊x₂/g + 1/2⌋)` with the grid spacing `g = g_δ = δ/100`, and states
`|Q_δ(x) - x| ≤ g/√2 < g` (eq (C2)). The Lean statement below proves the weaker bound `≤ g`, which is
what the trace bound `hctr : dist (ctr v) (vertexPoint v) ≤ g` of `Uniform68.config_exit_lower_bound` needs.
The grid centre `z_j = Q_δ(η(X_{T_j}))` of the good radii (write-up line 697) is `gridRound`.

Terminology: Gwynne-Miller annulus iteration (grid of centres); the centres are deterministic functions of the
embedding point, so the rounding carries no probability.
-/

namespace MatedCRT
namespace Uniform68Round

/-- The Borel rounding of one real coordinate to the grid `g ℤ`: `g ⌊t/g + 1/2⌋`. -/
noncomputable def gridRound1 (g t : ℝ) : ℝ := g * (⌊t / g + 1 / 2⌋ : ℝ)

/-- The grid rounding `Q_δ` of a point of the plane, with grid spacing `g` (LEMMA68 line 674). -/
noncomputable def gridRound (g : ℝ) (x : ℂ) : ℂ := ⟨gridRound1 g x.re, gridRound1 g x.im⟩

/-- One coordinate is moved by at most `g/2`: `|g ⌊t/g + 1/2⌋ - t| ≤ g/2` for `g > 0`. -/
theorem abs_gridRound1_sub_le {g : ℝ} (hg : 0 < g) (t : ℝ) : |gridRound1 g t - t| ≤ g / 2 := by
  have hg0 : g ≠ 0 := hg.ne'
  have h1 := Int.floor_le (t / g + 1 / 2)
  have h2 := Int.lt_floor_add_one (t / g + 1 / 2)
  have e : gridRound1 g t - t = g * ((⌊t / g + 1 / 2⌋ : ℝ) - t / g) := by
    unfold gridRound1
    field_simp
  have hk : |(⌊t / g + 1 / 2⌋ : ℝ) - t / g| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [e, abs_mul, abs_of_pos hg]
  have := mul_le_mul_of_nonneg_left hk hg.le
  linarith

/-- **The grid rounding moves a point by at most `g`** (LEMMA68 eq (C2), with the weaker constant `g`
used by the trace bound `hctr`). -/
theorem dist_gridRound_le {g : ℝ} (hg : 0 < g) (x : ℂ) : dist (gridRound g x) x ≤ g := by
  have hre := abs_gridRound1_sub_le hg x.re
  have him := abs_gridRound1_sub_le hg x.im
  have hre' := abs_le.1 hre
  have him' := abs_le.1 him
  rw [Complex.dist_eq_re_im]
  apply Real.sqrt_le_iff.2
  refine ⟨hg.le, ?_⟩
  have hsq1 : (gridRound1 g x.re - x.re) ^ 2 ≤ (g / 2) ^ 2 :=
    sq_le_sq' (by linarith [hre'.1]) (by linarith [hre'.2])
  have hsq2 : (gridRound1 g x.im - x.im) ^ 2 ≤ (g / 2) ^ 2 :=
    sq_le_sq' (by linarith [him'.1]) (by linarith [him'.2])
  simp only [gridRound]
  nlinarith

end Uniform68Round
end MatedCRT

#print axioms MatedCRT.Uniform68Round.dist_gridRound_le
