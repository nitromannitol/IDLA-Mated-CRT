import MatedCRT.FirstPass.S6r.Constants

/-!
# Lemma 6.8, window S7': two-sided shells, parameters and grid cover

Steps 1 and 2 of S7' (displayed (7.0)-(7.13)).
Terminology: `K = closure Θ`, `f = dist(·, K)` (`Metric.infDist`), the open thickening `K + B_r = {f < r}`
(`Metric.thickening r K`), and the two-sided shell `Σ_j = {|f - r/2| = λ_j}` of Armstrong, Kuusi and Mourrat's
level-set construction. Radii `d`, `s = d^a`, `g = d/100` and the grid `gℤ²` are as in the note.

Named hypotheses (not derivable from the printed S7' text; see the report):
* `hEligReg`: a grid centre whose `3s`-ball lies in the good-radius region is eligible for the S2 field
  (the note uses "eligible" without defining it);
* `hReg`: the good-radius region contains the annulus `{9 s₀/10 ≤ |x| ≤ 3ρ/4}` (the region is used, not defined).
-/

namespace MatedCRT.Lemma68Window

open Metric Set

/-- Number of shells `N = ⌊r/(400 s)⌋` (displayed (7.4)). -/
noncomputable def shellCount (r s : ℝ) : ℕ := ⌊r / (400 * s)⌋₊

/-- Offset `λ_j = 20 j s` of the `j`-th shell (displayed (7.4)). -/
def shellOffset (s : ℝ) (j : ℕ) : ℝ := 20 * (j : ℝ) * s

/-- The two-sided shell `Σ = {x : |f(x) - r/2| = λ}` with `f = dist(·, K)` (displayed (7.6)). -/
noncomputable def twoSidedShell (K : Set ℂ) (r lam : ℝ) : Set ℂ :=
  {x | |infDist x K - r / 2| = lam}

/-- Nearest-grid rounding `Q_d` to `gℤ²` (displayed (7.11)). -/
noncomputable def gridRound (g : ℝ) (x : ℂ) : ℂ :=
  ⟨g * (round (x.re / g) : ℝ), g * (round (x.im / g) : ℝ)⟩

/-- `z` is a point of the grid `gℤ²`. -/
def IsGridPoint (g : ℝ) (z : ℂ) : Prop :=
  ∃ m n : ℤ, z = ⟨g * (m : ℝ), g * (n : ℝ)⟩

/-- The relevant centres `Z` of a shell `S` (displayed (7.12)): grid points at distance at most `g` from `S`
(closed-ball reading of `B_g(z) ∩ Σ_j ≠ ∅`). -/
def shellCentres (g : ℝ) (S : Set ℂ) : Set ℂ :=
  {z | IsGridPoint g z ∧ ∃ y ∈ S, dist y z ≤ g}

lemma abs_sub_grid_round_le {g : ℝ} (hg : 0 < g) (t : ℝ) :
    |g * (round (t / g) : ℝ) - t| ≤ g / 2 := by
  have hgt : g * (t / g) = t := by field_simp
  have h2 : g * (round (t / g) : ℝ) - t = -(g * (t / g - round (t / g))) := by
    rw [mul_sub, hgt]; ring
  rw [h2, abs_neg, abs_mul, abs_of_pos hg]
  nlinarith [abs_sub_round (t / g)]

/-- The nearest-grid rounding moves a point by at most `g` (displayed (7.11)). -/
lemma dist_gridRound_le {g : ℝ} (hg : 0 < g) (x : ℂ) : dist (gridRound g x) x ≤ g := by
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre := abs_sub_grid_round_le hg x.re
  have him := abs_sub_grid_round_le hg x.im
  simp only [gridRound, Complex.sub_re, Complex.sub_im]
  linarith

/-- Displayed (7.8): a point of `Σ_j` lies in the band `{9r/20 ≤ f ≤ 11r/20}`. -/
lemma shell_band {K : Set ℂ} {r lam : ℝ} (hlam : lam ≤ r / 20) {x : ℂ}
    (hx : x ∈ twoSidedShell K r lam) :
    9 / 20 * r ≤ infDist x K ∧ infDist x K ≤ 11 / 20 * r := by
  have hx' : |infDist x K - r / 2| = lam := hx
  have h := abs_le.mp (hx'.le.trans hlam)
  constructor <;> linarith [h.1, h.2]

lemma mem_thickening_iff_infDist_lt {K : Set ℂ} (hK : K.Nonempty) {δ : ℝ} {x : ℂ} :
    x ∈ thickening δ K ↔ infDist x K < δ := by
  rw [Metric.mem_thickening_iff, Metric.infDist_lt_iff hK]

/-- The frontier of the thickening `K + B_δ` lies in the level set `{f = δ}`. -/
lemma frontier_thickening_subset_level {K : Set ℂ} (hK : K.Nonempty) (δ : ℝ) :
    frontier (thickening δ K) ⊆ {x | infDist x K = δ} := by
  rintro x ⟨hx_cl, hx_int⟩
  rw [Metric.isOpen_thickening.interior_eq] at hx_int
  have hle : closure (thickening δ K) ⊆ {x | infDist x K ≤ δ} := by
    apply closure_minimal
    · intro y hy
      exact le_of_lt ((mem_thickening_iff_infDist_lt hK).mp hy)
    · exact isClosed_le (Metric.continuous_infDist_pt K) continuous_const
  have h1 : infDist x K ≤ δ := hle hx_cl
  have h2 : δ ≤ infDist x K := by
    by_contra hcon
    exact hx_int ((mem_thickening_iff_infDist_lt hK).mpr (not_le.mp hcon))
  exact le_antisymm h1 h2

/-- A point at distance at most `c` from `K ⊆ B_ρ` has norm at most `ρ + c`. -/
lemma norm_le_of_infDist_le {K : Set ℂ} (hKne : K.Nonempty) {ρ c : ℝ} (hKb : K ⊆ ball (0 : ℂ) ρ)
    {y : ℂ} (hy : infDist y K ≤ c) : ‖y‖ ≤ ρ + c := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨k, hk, hdist⟩ := (infDist_lt_iff hKne).mp (show infDist y K < c + ε by linarith)
  have hk0 : ‖k‖ < ρ := mem_ball_zero_iff.mp (hKb hk)
  have htri : ‖y‖ ≤ ‖y - k‖ + ‖k‖ := by
    simpa using norm_add_le (y - k) k
  have hyk : ‖y - k‖ = dist y k := (dist_eq_norm y k).symm
  linarith

/-- Displayed (7.4), (7.5), (7.9), (7.10): the shell parameters `λ_j = 20 j s`, `N = ⌊r/(400 s)⌋`. -/
theorem shell_parameters {r d ζ s : ℝ} (hr : 0 < r) (hd : 0 < d) (hζ : 0 ≤ ζ)
    (hs : s = d ^ shortExp ζ) (_hsq : r ^ 2 ≤ d) (hd2 : d < 2 * r ^ 2) (hsr : s ≤ r / 4000) :
    0 < s ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ shellCount r s →
      20 * s ≤ shellOffset s j ∧ shellOffset s j ≤ 20 * (shellCount r s : ℝ) * s ∧
        20 * (shellCount r s : ℝ) * s ≤ r / 20) ∧
    r / (800 * s) ≤ (shellCount r s : ℝ) ∧
    (2 : ℝ) ^ (-shortExp ζ) / 800 * r ^ (-ζ) ≤ (shellCount r s : ℝ) := by
  have hspos : 0 < s := by
    rw [hs]; exact Real.rpow_pos_of_pos hd _
  have hN_le : (shellCount r s : ℝ) ≤ r / (400 * s) := Nat.floor_le (by positivity)
  have hN_lt : r / (400 * s) < (shellCount r s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx10 : 10 ≤ r / (400 * s) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hNs : (shellCount r s : ℝ) * (400 * s) ≤ r := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 400 * s)).mp hN_le
    linarith
  have hNr : r / (800 * s) ≤ (shellCount r s : ℝ) := by
    have e : r / (800 * s) = r / (400 * s) / 2 := by
      rw [div_div]; congr 1; ring
    rw [e]; linarith
  have hsle : s ≤ (2:ℝ) ^ shortExp ζ * r ^ (1 + ζ) := by
    have ha0 : 0 ≤ shortExp ζ := shortExp_nonneg hζ
    have h1 : d ^ shortExp ζ ≤ (2 * r ^ 2) ^ shortExp ζ :=
      Real.rpow_le_rpow hd.le (by linarith) ha0
    have h2 : (2 * r ^ 2 : ℝ) ^ shortExp ζ = (2:ℝ) ^ shortExp ζ * r ^ (1 + ζ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← two_mul_shortExp ζ, Real.rpow_mul hr.le,
        Real.rpow_two]
    rw [hs]
    have := h1
    rw [h2] at this
    exact this
  have hpos2 : 0 < (2:ℝ) ^ shortExp ζ := by positivity
  have hpos_rz : 0 < r ^ ζ := Real.rpow_pos_of_pos hr ζ
  have hne2 := hpos2.ne'
  have hnerz := hpos_rz.ne'
  have hner := hr.ne'
  have e2 : (2:ℝ) ^ (-shortExp ζ) / 800 * r ^ (-ζ)
      = r / (800 * ((2:ℝ) ^ shortExp ζ * r ^ (1 + ζ))) := by
    rw [Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num), Real.rpow_neg hr.le, Real.rpow_add hr,
      Real.rpow_one]
    field_simp
  have hmono : r / (800 * ((2:ℝ) ^ shortExp ζ * r ^ (1 + ζ))) ≤ r / (800 * s) :=
    div_le_div_of_nonneg_left hr.le (by positivity)
      (mul_le_mul_of_nonneg_left hsle (by norm_num))
  refine ⟨hspos, ?_, hNr, ?_⟩
  · intro j hj1 hjN
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjN' : (j : ℝ) ≤ shellCount r s := by exact_mod_cast hjN
    unfold shellOffset
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
  · rw [e2]; exact hmono.trans hNr

/-- Displayed (7.12)–(7.13): the shell `Σ` (offset `lam`) is covered by the balls `B_{R_z/2}(z)` over its relevant
centres `z`, and every relevant centre is eligible with its `3R_z`-ball in the good-radius region. -/
theorem shell_grid_cover {K : Set ℂ} {r ρ s0 d s g lam : ℝ}
    (R : ℂ → ℝ) (Elig : ℂ → Prop) (Reg : Set ℂ)
    (hKne : K.Nonempty) (hs0 : ball (0 : ℂ) s0 ⊆ K) (hKb : K ⊆ ball (0 : ℂ) (ρ / 2))
    (hr : 0 < r) (hd : 0 < d) (hg : g = d / 100) (hlam : lam ≤ r / 20)
    (hR : ∀ z, Elig z → d ≤ R z ∧ R z ≤ s)
    (hEligReg : ∀ z : ℂ, closedBall z (3 * s) ⊆ Reg → Elig z)
    (hReg : ∀ x : ℂ, 9 * s0 / 10 ≤ ‖x‖ → ‖x‖ ≤ 3 * ρ / 4 → x ∈ Reg)
    (hcut1 : g + 3 * s < s0 / 10) (hcut2 : ρ / 2 + 11 / 20 * r + g + 3 * s < 3 * ρ / 4) :
    (∀ y ∈ twoSidedShell K r lam,
        ∃ z ∈ shellCentres g (twoSidedShell K r lam), y ∈ ball z (R z / 2)) ∧
    (∀ z ∈ shellCentres g (twoSidedShell K r lam), Elig z ∧ closedBall z (3 * R z) ⊆ Reg) := by
  have hgpos : 0 < g := by rw [hg]; positivity
  have hlow : ∀ y ∈ twoSidedShell K r lam, s0 ≤ ‖y‖ := by
    intro y hy
    have hf := (shell_band hlam hy).1
    by_contra hcon
    have hmem : y ∈ ball (0 : ℂ) s0 := mem_ball_zero_iff.mpr (not_le.mp hcon)
    have h0 : infDist y K = 0 := infDist_zero_of_mem (hs0 hmem)
    linarith
  have hup : ∀ y ∈ twoSidedShell K r lam, ‖y‖ ≤ ρ / 2 + 11 / 20 * r :=
    fun y hy => norm_le_of_infDist_le hKne hKb (shell_band hlam hy).2
  have helig : ∀ z ∈ shellCentres g (twoSidedShell K r lam), Elig z ∧ closedBall z (3 * R z) ⊆ Reg := by
    rintro z ⟨-, y, hy, hyz⟩
    have hsub : closedBall z (3 * s) ⊆ Reg := by
      intro x hx
      rw [mem_closedBall] at hx
      have hxy : dist x y ≤ 3 * s + g := by
        have := dist_triangle x z y
        rw [dist_comm z y] at this
        linarith
      have hlo := hlow y hy
      have hhi := hup y hy
      have hn1 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      have hn2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      rw [← dist_eq_norm, dist_comm] at hn1
      rw [← dist_eq_norm] at hn2
      apply hReg x
      · linarith
      · linarith
    have hEl : Elig z := hEligReg z hsub
    refine ⟨hEl, ?_⟩
    have hRs := (hR z hEl).2
    exact (closedBall_subset_closedBall (by linarith)).trans hsub
  refine ⟨?_, helig⟩
  intro y hy
  have hdy : dist y (gridRound g y) ≤ g := by
    rw [dist_comm]; exact dist_gridRound_le hgpos y
  have hmem : gridRound g y ∈ shellCentres g (twoSidedShell K r lam) :=
    ⟨⟨round (y.re / g), round (y.im / g), rfl⟩, y, hy, hdy⟩
  have hz := helig (gridRound g y) hmem
  obtain ⟨hd1, -⟩ := hR _ hz.1
  refine ⟨gridRound g y, hmem, ?_⟩
  rw [mem_ball]
  linarith

end MatedCRT.Lemma68Window
