import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseConvergence

/-!
# Lemma 3.4 (item 4): locally uniform convergence of inverse clocks

Deterministic core of `LBMPathFunctionalMeasurableStep`: if strictly increasing clocks `F i` converge to a time-change
clock `G` uniformly on compact time intervals, then their right-continuous inverses `clockInverse (F i)` converge to
`clockInverse G` uniformly on compact level intervals. The proof uses that `G(s + e) - G(s)` is bounded below by a
positive constant for `s` in a compact interval (continuity and strict monotonicity of `G`).

Terminology: time change of Brownian motion; clock inverse `F⁻¹` (Garban–Rhodes–Vargas, Liouville Brownian motion,
the path `b(F⁻¹(t))`, Definition 2.17).
-/

namespace MatedCRT

open Filter Topology Set
open scoped NNReal
open _root_.HarmonicBalls

/-- Uniform convergence on compacts of strictly increasing clocks to a time-change clock implies uniform convergence
on compacts of the right-continuous clock inverses. -/
theorem clockInverse_tendsto_uniform {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hG : IsTimeChangeClock G) (hF : ∀ i, StrictMono (F i))
    (hunb : ∀ i, ∀ u : ℝ≥0, ∃ s : ℝ≥0, (u : ℝ) < F i s)
    (hconv : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ t ≤ T, |F i t - G t| < η)
    (U : ℝ≥0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ i in l, ∀ u ≤ U, |((clockInverse (F i) u : ℝ≥0) : ℝ) - ((clockInverse G u : ℝ≥0) : ℝ)| < η := by
  set S : ℝ≥0 := clockInverse G U with hSdef
  set e : ℝ≥0 := Real.toNNReal (min (η / 2) 1) with hedef
  have he_pos : 0 < e := by
    rw [hedef, Real.toNNReal_pos]
    exact lt_min (by linarith) one_pos
  have he_le : (e : ℝ) ≤ η / 2 := by
    rw [hedef, Real.coe_toNNReal _ (le_min (by linarith) zero_le_one)]
    exact min_le_left _ _
  -- positive gap: `G (s + e) - G s ≥ m` for `s ∈ [0, S]`
  obtain ⟨m, hmpos, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Icc (0 : ℝ≥0) S, m ≤ G (s + e) - G s := by
    have hcont : Continuous fun s : ℝ≥0 => G (s + e) - G s :=
      (hG.continuous.comp (continuous_id.add continuous_const)).sub hG.continuous
    obtain ⟨s₁, hs₁, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := S)).exists_isMinOn
      (Set.nonempty_Icc.2 (by simp)) hcont.continuousOn
    refine ⟨G (s₁ + e) - G s₁, ?_, fun s hs => hmin hs⟩
    have : G s₁ < G (s₁ + e) := hG.strictMono (lt_add_of_pos_right _ he_pos)
    linarith
  set δ : ℝ := m / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith
  have hcl := hconv (S + e) δ hδpos
  filter_upwards [hcl] with i hi u hu
  -- the level `u` is attained by `G` at `r₀ = clockInverse G u`
  obtain ⟨r₀, hr₀⟩ := IsTimeChangeClock.surjective_toNNReal hG u
  have hGr₀ : G r₀ = (u : ℝ) := by
    have hnn : 0 ≤ G r₀ := by
      have h0 := hG.strictMono.monotone (show (0 : ℝ≥0) ≤ r₀ by simp)
      rw [hG.map_zero] at h0
      exact h0
    rw [← hr₀, Real.coe_toNNReal _ hnn]
  have hinv : clockInverse G u = r₀ := by
    rw [← hr₀]
    exact clockInverse_clockValue hG.map_zero hG.strictMono r₀
  have hr₀S : r₀ ≤ S := by
    have hmono := (IsTimeChangeClock.strictMono_clockInverse hG).monotone
    have h1 : clockInverse G u ≤ clockInverse G U := hmono hu
    rw [hinv] at h1
    exact h1
  rw [hinv]
  -- upper bound: `clockInverse (F i) u ≤ r₀ + e`
  have hup : clockInverse (F i) u ≤ r₀ + e := by
    apply csInf_le ⟨0, fun _ _ => by simp⟩
    show (u : ℝ) < F i (r₀ + e)
    have h1 := hi (r₀ + e) (add_le_add hr₀S le_rfl)
    rw [abs_lt] at h1
    have h2 : m ≤ G (r₀ + e) - G r₀ := hm r₀ ⟨by simp, hr₀S⟩
    rw [hGr₀] at h2
    linarith [h1.1]
  -- lower bound: `r₀ - e ≤ clockInverse (F i) u`
  have hlow : r₀ - e ≤ clockInverse (F i) u := by
    by_cases her : e ≤ r₀
    · obtain ⟨s, hs⟩ := hunb i u
      apply le_csInf ⟨s, hs⟩
      intro s' hs'
      by_contra hlt
      rw [not_le] at hlt
      -- `s ≔ r₀ - e` satisfies `s + e = r₀` and `s ∈ [0, S]`
      have hsadd : r₀ - e + e = r₀ := tsub_add_cancel_of_le her
      have hsS : r₀ - e ≤ S := le_trans tsub_le_self hr₀S
      have h1 : F i s' ≤ F i (r₀ - e) := (hF i).monotone hlt.le
      have h2 := hi (r₀ - e) (le_trans hsS (le_self_add))
      rw [abs_lt] at h2
      have h3 : m ≤ G (r₀ - e + e) - G (r₀ - e) := hm (r₀ - e) ⟨by simp, hsS⟩
      rw [hsadd, hGr₀] at h3
      have h4 : (u : ℝ) < F i s' := hs'
      linarith [h2.2]
    · have h0 : r₀ - e = 0 := tsub_eq_zero_of_le (not_le.1 her).le
      rw [h0]
      exact zero_le
  -- conclude
  have hupR : (clockInverse (F i) u : ℝ) ≤ (r₀ : ℝ) + (e : ℝ) := by
    have h := NNReal.coe_le_coe.2 hup
    rw [NNReal.coe_add] at h
    exact h
  have hlowR : (r₀ : ℝ) - (e : ℝ) ≤ (clockInverse (F i) u : ℝ) := by
    by_cases her : e ≤ r₀
    · have h := NNReal.coe_le_coe.2 hlow
      rw [NNReal.coe_sub her] at h
      exact h
    · have hlt : (r₀ : ℝ) < e := by exact_mod_cast (not_le.1 her)
      have h0 : (0 : ℝ) ≤ (clockInverse (F i) u : ℝ) := NNReal.coe_nonneg _
      linarith
  rw [abs_lt]
  constructor <;> linarith

end MatedCRT
