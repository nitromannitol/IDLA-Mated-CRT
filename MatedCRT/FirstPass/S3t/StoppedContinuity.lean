import MatedCRT.FirstPass.S3t.LBMRegular
import MatedCRT.Proofs.LBM.LocalUniformDistance
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope

/-!
# Truncated quenched laws, Step 3: continuity of the exit time and of the stopped occupation (fp-S3t, z2)

Step 3 of `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md` (section 3). For a continuous path `w` which exits the disk
`ball z r` regularly (`RegularExit`, `MatedCRT/FirstPass/S3t/LBMRegular.lean`), the truncated exit time
`v ↦ min (T, τ_D(v))` is continuous at `w` for the local uniform distance (`PathFunctionalContinuousAt`, the continuity
notion of `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PathEnvelope.lean`).

Two hypotheses are added to the answer's statement, each needed and flagged: `Continuous w` (the compactness of
`w '' [0, s]` in the proof needs it; a jump of the path inside `D` near `∂D` breaks the argument) and `0 ≤ T`.
-/

open MeasureTheory Set Filter Topology HarmonicBalls Metric
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- A path that stays in `D` up to the time `s` has exit time at least `s`. -/
theorem le_pathExitTime_of_forall_mem {D : Set ℂ} {v : ℝ≥0 → ℂ} {s : ℝ≥0}
    (h : ∀ t : ℝ≥0, t ≤ s → v t ∈ D) : (s : ℝ≥0∞) ≤ pathExitTime D v := by
  refine le_sInf ?_
  rintro e ⟨t, rfl, ht⟩
  by_contra hlt
  have hlt' := not_le.1 hlt
  exact ht (h t (ENNReal.coe_le_coe.1 hlt'.le))

/-- A path outside `D` at time `t` has exit time at most `t`. -/
theorem pathExitTime_le_of_not_mem {D : Set ℂ} {v : ℝ≥0 → ℂ} {t : ℝ≥0} (h : v t ∉ D) :
    pathExitTime D v ≤ (t : ℝ≥0∞) :=
  sInf_le ⟨t, rfl, h⟩

/-- Before the exit time the path is in `D`. -/
theorem mem_of_lt_pathExitTime {D : Set ℂ} {v : ℝ≥0 → ℂ} {t : ℝ≥0} (h : (t : ℝ≥0∞) < pathExitTime D v) :
    v t ∈ D := by
  by_contra hn
  exact absurd (pathExitTime_le_of_not_mem hn) (not_le.2 h)

/-- The truncated real exit time: `(min (ofReal T) e).toReal = min T e.toReal` for `0 ≤ T` and `e ≠ ⊤`. -/
theorem toReal_min_ofReal {T : ℝ} (hT : 0 ≤ T) {e : ℝ≥0∞} (he : e ≠ ⊤) :
    (min (ENNReal.ofReal T) e).toReal = min T e.toReal := by
  rcases le_total (ENNReal.ofReal T) e with h | h
  · rw [min_eq_left h, ENNReal.toReal_ofReal hT, min_eq_left]
    exact (ENNReal.ofReal_le_iff_le_toReal he).1 h
  · rw [min_eq_right h, min_eq_right]
    exact ENNReal.toReal_le_of_le_ofReal hT h

/-- Lower half of the continuity: for `v` close to a continuous `w`, the truncated exit time of `v` is at least
that of `w` minus `η`. -/
theorem truncExit_lower {z : ℂ} {r T : ℝ} {w : ℝ≥0 → ℂ} (hw : Continuous w) (hT : 0 ≤ T) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : ℝ≥0 → ℂ, localUniformDist v w < ρ →
      (min (ENNReal.ofReal T) (pathExitTime (ball z r) w)).toReal - η ≤
        (min (ENNReal.ofReal T) (pathExitTime (ball z r) v)).toReal := by
  set D := ball z r with hD
  set τ := pathExitTime D w with hτ
  set A := (min (ENNReal.ofReal T) τ).toReal with hA
  have hAT : A ≤ T := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left (ENNReal.ofReal T) τ)
    rwa [ENNReal.toReal_ofReal hT] at this
  by_cases hsmall : A - η ≤ 0
  · refine ⟨1, one_pos, fun v _ => ?_⟩
    linarith [ENNReal.toReal_nonneg (a := min (ENNReal.ofReal T) (pathExitTime D v))]
  have hsmall' := not_le.1 hsmall
  set s : ℝ≥0 := (A - η).toNNReal with hs
  have hs_eq : (s : ℝ≥0∞) = ENNReal.ofReal (A - η) := rfl
  have hmin_ne : min (ENNReal.ofReal T) τ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hA_eq : ENNReal.ofReal A = min (ENNReal.ofReal T) τ := ENNReal.ofReal_toReal hmin_ne
  have hsτ : (s : ℝ≥0∞) < τ := by
    rw [hs_eq]
    calc ENNReal.ofReal (A - η) < ENNReal.ofReal A :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      _ = min (ENNReal.ofReal T) τ := hA_eq
      _ ≤ τ := min_le_right _ _
  have hwD : ∀ t : ℝ≥0, t ≤ s → w t ∈ D := fun t ht =>
    mem_of_lt_pathExitTime (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hsτ)
  have hK : IsCompact (w '' Icc (0 : ℝ≥0) s) := isCompact_Icc.image hw
  have hKD : w '' Icc (0 : ℝ≥0) s ⊆ D := by
    rintro _ ⟨t, ht, rfl⟩
    exact hwD t ht.2
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open isOpen_ball hKD
  refine ⟨(2 : ℝ)⁻¹ ^ (⌈s⌉₊ + 1) * min 1 δ, mul_pos (pow_pos (by norm_num) _) (lt_min one_pos hδ),
    fun v hv => ?_⟩
  have hcore : ∀ t : ℝ≥0, t ≤ s → v t ∈ D := by
    intro t ht
    have hk : t ≤ ((⌈s⌉₊ + 1 : ℕ) : ℝ≥0) :=
      ht.trans ((Nat.le_ceil s).trans (by exact_mod_cast Nat.le_succ _))
    have hdist := weighted_min_dist_le_localUniformDist v w ⌈s⌉₊ hk
    have hlt : (2 : ℝ)⁻¹ ^ (⌈s⌉₊ + 1) * min 1 (dist (v t) (w t)) <
        (2 : ℝ)⁻¹ ^ (⌈s⌉₊ + 1) * min 1 δ := lt_of_le_of_lt hdist hv
    have hmin_lt : min 1 (dist (v t) (w t)) < min 1 δ :=
      lt_of_mul_lt_mul_left hlt (pow_nonneg (by norm_num) _)
    have hdist_lt : dist (v t) (w t) < δ := by
      by_contra hcon
      have hcon' := not_lt.1 hcon
      have : min 1 δ ≤ min 1 (dist (v t) (w t)) := min_le_min le_rfl hcon'
      linarith
    exact hthick (Metric.mem_thickening_iff.2 ⟨w t, ⟨t, ⟨zero_le, ht⟩, rfl⟩, hdist_lt⟩)
  have hτv : (s : ℝ≥0∞) ≤ pathExitTime D v := le_pathExitTime_of_forall_mem hcore
  have hTne : min (ENNReal.ofReal T) (pathExitTime D v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have h1 : ENNReal.ofReal (A - η) ≤ ENNReal.ofReal T :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have h2 : ENNReal.ofReal (A - η) ≤ pathExitTime D v := hs_eq ▸ hτv
  have hmono : ENNReal.ofReal (A - η) ≤ min (ENNReal.ofReal T) (pathExitTime D v) := le_min h1 h2
  linarith [ENNReal.toReal_mono hTne hmono, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ A - η by linarith)]

/-- Upper half of the continuity at a regular path: for `v` close to `w`, the truncated exit time of `v` is at most that
of `w` plus `η`. The regular exit point `t` of `w` (`RegularExit`, Frequently in `𝓝[>] τ`) gives `v t ∉ D`. -/
theorem truncExit_upper {z : ℂ} {r T : ℝ} {w : ℝ≥0 → ℂ} (hT : 0 ≤ T) (hreg : RegularExit (ball z r) w) {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : ℝ≥0 → ℂ, localUniformDist v w < ρ →
      (min (ENNReal.ofReal T) (pathExitTime (ball z r) v)).toReal ≤
        (min (ENNReal.ofReal T) (pathExitTime (ball z r) w)).toReal + η := by
  set D := ball z r with hD
  by_cases htop : pathExitTime D w = ⊤
  · refine ⟨1, one_pos, fun v _ => ?_⟩
    have h1 : (min (ENNReal.ofReal T) (pathExitTime D v)).toReal ≤ T := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_left (ENNReal.ofReal T) (pathExitTime D v))
      rwa [ENNReal.toReal_ofReal hT] at this
    have h2 : (min (ENNReal.ofReal T) (pathExitTime D w)).toReal = T := by
      rw [htop, min_top_right, ENNReal.toReal_ofReal hT]
    linarith
  have hfreq : ∃ᶠ t in 𝓝[>] (pathExitTime D w).toNNReal, w t ∉ closure D := by
    rcases hreg with h | h
    · exact absurd h htop
    · exact h
  set τ := pathExitTime D w with hτ
  have hη' : (0 : ℝ≥0) < η.toNNReal := Real.toNNReal_pos.2 hη
  obtain ⟨t, ht_out, ht_mem⟩ := (hfreq.and_eventually
    (Ioo_mem_nhdsGT (lt_add_of_pos_right (τ.toNNReal) hη'))).exists
  have ht_lt : (t : ℝ) < τ.toReal + η := by
    have h := NNReal.coe_lt_coe.2 ht_mem.2
    rw [NNReal.coe_add, Real.coe_toNNReal η hη.le] at h
    exact h
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl (w t) ht_out
  refine ⟨(2 : ℝ)⁻¹ ^ (⌈t⌉₊ + 1) * min 1 δ, mul_pos (pow_pos (by norm_num) _) (lt_min one_pos hδ),
    fun v hv => ?_⟩
  have hk : t ≤ ((⌈t⌉₊ + 1 : ℕ) : ℝ≥0) := (Nat.le_ceil t).trans (by exact_mod_cast Nat.le_succ _)
  have hdist := weighted_min_dist_le_localUniformDist v w ⌈t⌉₊ hk
  have hlt : (2 : ℝ)⁻¹ ^ (⌈t⌉₊ + 1) * min 1 (dist (v t) (w t)) <
      (2 : ℝ)⁻¹ ^ (⌈t⌉₊ + 1) * min 1 δ := lt_of_le_of_lt hdist hv
  have hmin_lt : min 1 (dist (v t) (w t)) < min 1 δ :=
    lt_of_mul_lt_mul_left hlt (pow_nonneg (by norm_num) _)
  have hdist_lt : dist (v t) (w t) < δ := by
    by_contra hcon
    have hcon' := not_lt.1 hcon
    have : min 1 δ ≤ min 1 (dist (v t) (w t)) := min_le_min le_rfl hcon'
    linarith
  have hvD : v t ∉ D := fun hmem => hball (Metric.mem_ball.2 hdist_lt) (subset_closure hmem)
  have hτv : pathExitTime D v ≤ (t : ℝ≥0∞) := pathExitTime_le_of_not_mem hvD
  have hA1 : (min (ENNReal.ofReal T) (pathExitTime D v)).toReal ≤
      (min (ENNReal.ofReal T) (t : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)) (min_le_min le_rfl hτv)
  have hA2 : (min (ENNReal.ofReal T) (t : ℝ≥0∞)).toReal = min T (t : ℝ) := by
    rw [toReal_min_ofReal hT ENNReal.coe_ne_top, ENNReal.coe_toReal]
  have hA3 : (min (ENNReal.ofReal T) τ).toReal = min T τ.toReal := toReal_min_ofReal hT htop
  have hA4 : min T (t : ℝ) ≤ min T τ.toReal + η := by
    rcases le_total T τ.toReal with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right hη.le)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans ht_lt.le
  linarith

/-- **Step 3, continuity of the truncated exit time.** For a continuous path `w` that exits `ball z r` regularly, the map
`v ↦ min (T, τ_D(v))` is continuous at `w` for the local uniform distance. -/
theorem continuousAt_pathExitTime_ball {z : ℂ} {r T : ℝ} {w : ℝ≥0 → ℂ} (hw : Continuous w) (hT : 0 ≤ T)
    (hreg : RegularExit (ball z r) w) :
    MatedCRT.PathFunctionalContinuousAt (fun v => (min (ENNReal.ofReal T) (pathExitTime (ball z r) v)).toReal) w := by
  intro η hη
  obtain ⟨ρ₁, hρ₁, h₁⟩ := truncExit_lower (z := z) (r := r) hw hT (half_pos hη)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := truncExit_upper (z := z) (r := r) hT hreg (half_pos hη)
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun v hv => ?_⟩
  have e1 := h₁ v (lt_of_lt_of_le hv (min_le_left _ _))
  have e2 := h₂ v (lt_of_lt_of_le hv (min_le_right _ _))
  dsimp only
  rw [abs_le]
  constructor <;> linarith

end MatedCRT.TruncatedLaws
