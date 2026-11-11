import HarmonicBalls.Steps.SecA.Basic

/-!
# FIRST PASS, Lemma 5.3: pole blow-up of the rescaled obstacle (G-5-3 Section 1, `R_n(0) → ∞`)

The rescaled obstacles `R_n = -w_{s_n} / s_n` are mean-value superharmonic on the disk, nondecreasing in `n`
(mass scaling), continuous off the pole, and eventually equal to the Green function `G = G_{B_ρ}(0, ·)` at each
point of the punctured disk (eq. (4)). The Green function is bounded below on small circles by the logarithm
(`log_div_le_greenFunction`). Then the circle average of `R_n` over a small circle is bounded below, and the
mean-value inequality at the centre gives `R_n(0) → ∞`. The compact cover of the circle is the uniform form of
eq. (4) on the punctured disk (open cover by increasing sets `{R_n - G + 1 > 0}`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped Real
open _root_.HarmonicBalls

/-- Compact cover on an open set: an increasing family of open sets, each defined by a continuous function on `U`,
covering a compact `K ⊆ U`, has a member containing `K` (G-5-3 Section 1, uniform form of eq. (5)). -/
lemma exists_forall_pos_on_open {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (A : ℕ → ℂ → ℝ) (hA : ∀ n, ContinuousOn (A n) U) (hmono : ∀ x ∈ U, Monotone fun n => A n x)
    (hpos : ∀ x ∈ K, ∃ n, 0 < A n x) : ∃ n, ∀ x ∈ K, 0 < A n x := by
  have hO : ∀ n, IsOpen (U ∩ {x | 0 < A n x}) := fun n => (hA n).isOpen_inter_preimage hU isOpen_Ioi
  have hdir : Monotone (fun n => U ∩ {x | 0 < A n x}) := fun n m hnm x hx =>
    ⟨hx.1, lt_of_lt_of_le hx.2 (hmono x hx.1 hnm)⟩
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => U ∩ {x | 0 < A n x}) hO
    (fun x hx => by
      obtain ⟨n, hn⟩ := hpos x hx
      exact mem_iUnion.2 ⟨n, hKU hx, hn⟩)
    hdir.directed_le
  exact ⟨n, fun x hx => (hn hx).2⟩

/-- **Pole blow-up** (G-5-3 Section 1): for the rescaled obstacles `R n`, the values `R n 0` tend to `+∞`, given
the mean-value superharmonicity on `B_ρ`, the eventual equality with the Green function off the pole, and the
logarithmic lower bound of the Green function on circles. -/
theorem eventually_ge_pole_of_superharmonic {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') (hρρ' : ρ' ≤ ρ)
    {R : ℕ → ℂ → ℝ} {G : ℂ → ℝ}
    (hsup : ∀ n, IsSuperharmonicOn (ball (0 : ℂ) ρ) (R n))
    (hRc : ∀ n, ContinuousOn (R n) (ball (0 : ℂ) ρ))
    (hGc : ContinuousOn G (ball (0 : ℂ) ρ \ {0}))
    (hmono : ∀ x ∈ ball (0 : ℂ) ρ \ {0}, Monotone fun n => R n x)
    (heq : ∀ x ∈ ball (0 : ℂ) ρ \ {0}, ∀ᶠ n in atTop, R n x = G x)
    (hGlow : ∀ r : ℝ, 0 < r → r < ρ' → ∀ x ∈ sphere (0 : ℂ) r, (2 * π)⁻¹ * Real.log (ρ' / r) ≤ G x)
    (M : ℝ) : ∀ᶠ n in atTop, M ≤ R n 0 := by
  set m : ℝ := |M| + 1 with hm
  set r : ℝ := ρ' * Real.exp (-(2 * π * m)) with hr
  have hexp : 0 < Real.exp (-(2 * π * m)) := Real.exp_pos _
  have hrpos : 0 < r := mul_pos hρ' hexp
  have hm0 : 0 < m := by positivity
  have hlt1 : Real.exp (-(2 * π * m)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
  have hrlt : r < ρ' := by
    have := mul_lt_mul_of_pos_left hlt1 hρ'
    linarith
  have hratio : ρ' / r = Real.exp (2 * π * m) := by
    have h1 : Real.exp (2 * π * m) * Real.exp (-(2 * π * m)) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hr]
    field_simp
    linarith [h1]
  have hlog : (2 * π)⁻¹ * Real.log (ρ' / r) = m := by
    rw [hratio, Real.log_exp]
    field_simp
  have hGs : ∀ x ∈ sphere (0 : ℂ) r, m ≤ G x := fun x hx => by
    have := hGlow r hrpos hrlt x hx
    rw [hlog] at this
    exact this
  have hrρ : r < ρ := lt_of_lt_of_le hrlt hρρ'
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) ρ := closedBall_subset_ball hrρ
  -- compact cover of the circle by the increasing sets `{R n - G + 1 > 0}`
  have hU : IsOpen (ball (0 : ℂ) ρ \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hKU : sphere (0 : ℂ) r ⊆ ball (0 : ℂ) ρ \ {0} := by
    intro x hx
    rw [mem_sphere_zero_iff_norm] at hx
    refine ⟨mem_ball_zero_iff.2 (by rw [hx]; exact hrρ), ?_⟩
    intro h0
    rw [mem_singleton_iff] at h0
    rw [h0, norm_zero] at hx
    linarith
  set A : ℕ → ℂ → ℝ := fun n x => R n x - G x + 1 with hA_def
  have hA : ∀ n, ContinuousOn (A n) (ball (0 : ℂ) ρ \ {0}) := fun n =>
    (((hRc n).mono sdiff_subset).sub hGc).add continuousOn_const
  have hAmono : ∀ x ∈ ball (0 : ℂ) ρ \ {0}, Monotone fun n => A n x := fun x hx n k hnk => by
    have := hmono x hx hnk
    simp only [hA_def]
    linarith
  have hApos : ∀ x ∈ sphere (0 : ℂ) r, ∃ n, 0 < A n x := fun x hx => by
    obtain ⟨n, hn⟩ := (heq x (hKU hx)).exists
    exact ⟨n, by simp only [hA_def, hn]; linarith⟩
  obtain ⟨N, hN⟩ := exists_forall_pos_on_open hU (isCompact_sphere (0 : ℂ) r) hKU A hA hAmono hApos
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsph : ∀ x ∈ sphere (0 : ℂ) r, M ≤ R n x := fun x hx => by
    have h1 : 0 < A n x := lt_of_lt_of_le (hN x hx) (hAmono x (hKU hx) hn)
    simp only [hA_def] at h1
    have h2 := hGs x hx
    have h3 : M ≤ |M| := le_abs_self M
    rw [hm] at h2
    linarith
  -- mean-value inequality at the centre
  have hmean := (hsup n).2 0 (mem_ball_self hρ) r hrpos hsub
  have hcirc : CircleIntegrable (R n) 0 r := hmean.1
  have hlow : Real.circleAverage (fun _ => M) 0 r ≤ Real.circleAverage (R n) 0 r := by
    refine Real.circleAverage_mono (circleIntegrable_const _ _ _) hcirc ?_
    intro x hx
    rw [abs_of_pos hrpos] at hx
    exact hsph x hx
  rw [Real.circleAverage_const] at hlow
  linarith [hmean.2]

end MatedCRT.S5c
