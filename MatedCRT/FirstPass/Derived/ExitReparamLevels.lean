import MatedCRT.FirstPass.Derived.ExitReparamClass

/-!
# Level reparametrizations at exit times from balls of increasing radii

Deterministic pieces of the exact-reparametrization argument:

* `exactReparam_of_orderIso`: an order automorphism `e` of the unit interval carrying the
  normalized prefix of `w` of duration `a` onto that of `v` of duration `b` gives an exact
  reparametrization `φ` of `[0,a]` onto `[0,b]` (`φ t = b * e (t / a)`);
* `toNNReal_pathExitTime_pos`: a continuous path that starts in an open set leaves it after a
  positive time;
* `exists_strictMono_of_levels`: if continuous planar paths `f`, `g` leave every ball of radius
  `r k` (`r` monotone, tending to infinity) and `g` is, at each level, an exact reparametrization
  of `f` up to the exit times, then `f = g ∘ τ` for a strictly increasing continuous `τ` with
  `τ 0 = 0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric HarmonicBalls MarkovProcess LatticeProb
open scoped ENNReal NNReal unitInterval

namespace MatedCRT.ExitReparamLevels

open MatedCRT.ExitReparamPatch

/-- An order automorphism of the unit interval identifying the normalized prefixes of durations
`a` and `b` gives an exact reparametrization of `[0,a]` onto `[0,b]`. -/
theorem exactReparam_of_orderIso {α : Type*} [TopologicalSpace α] {w v : C(ℝ≥0, α)}
    {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) (e : unitInterval ≃o unitInterval)
    (he : ∀ s : unitInterval, normalizedPathPrefix w a s = normalizedPathPrefix v b (e s)) :
    ∃ φ : ℝ≥0 → ℝ≥0, ExactReparam (⇑w) (⇑v) a b φ := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  let x : ℝ≥0 → unitInterval := fun t => Set.projIcc (0 : ℝ) 1 zero_le_one ((t : ℝ) / a)
  have hx : ∀ t, t ≤ a → ((x t : unitInterval) : ℝ) = (t : ℝ) / a := fun t ht => by
    have h0 : (0 : ℝ) ≤ (t : ℝ) / a := div_nonneg t.2 ha'.le
    have h1 : (t : ℝ) / a ≤ 1 := (div_le_one ha').2 (by exact_mod_cast ht)
    simp only [x]
    rw [Set.projIcc_of_mem _ ⟨h0, h1⟩]
  let φ : ℝ≥0 → ℝ≥0 := fun t => ⟨(b : ℝ) * (e (x t) : ℝ), mul_nonneg b.2 (e (x t)).2.1⟩
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro t ht t' ht' htt'
    have hxt : x t < x t' := by
      rw [← Subtype.coe_lt_coe, hx t (mem_Iic.1 ht), hx t' (mem_Iic.1 ht')]
      exact div_lt_div_of_pos_right (by exact_mod_cast htt') ha'
    have h1 : (e (x t) : ℝ) < (e (x t') : ℝ) := e.lt_iff_lt.2 hxt
    show φ t < φ t'
    rw [← NNReal.coe_lt_coe]
    exact mul_lt_mul_of_pos_left h1 hb'
  · intro t _
    refine mem_Iic.2 ?_
    show φ t ≤ b
    rw [← NNReal.coe_le_coe]
    exact mul_le_of_le_one_right b.2 (e (x t)).2.2
  · intro y hy
    have hy' : y ≤ b := mem_Iic.1 hy
    let u : unitInterval := ⟨(y : ℝ) / b, div_nonneg y.2 hb'.le,
      (div_le_one hb').2 (by exact_mod_cast hy')⟩
    let s : unitInterval := e.symm u
    let t : ℝ≥0 := ⟨(s : ℝ) * a, mul_nonneg s.2.1 a.2⟩
    have hta : t ≤ a := by
      show (s : ℝ) * a ≤ a
      exact mul_le_of_le_one_left a.2 s.2.2
    have hxt : x t = s := by
      apply Subtype.ext
      rw [hx t hta]
      show (s : ℝ) * a / a = s
      field_simp
    refine ⟨t, mem_Iic.2 hta, ?_⟩
    apply NNReal.eq
    show (b : ℝ) * (e (x t) : ℝ) = y
    rw [hxt, OrderIso.apply_symm_apply]
    show (b : ℝ) * ((y : ℝ) / b) = y
    field_simp
  · intro t ht
    have h := he (x t)
    simp only [normalizedPathPrefix_apply] at h
    have h1 : (⟨((x t : unitInterval) : ℝ) * (a : ℝ), mul_nonneg (x t).2.1 a.2⟩ : ℝ≥0) = t := by
      apply NNReal.eq
      show ((x t : unitInterval) : ℝ) * a = t
      rw [hx t ht]
      field_simp
    have h2 : (⟨((e (x t) : unitInterval) : ℝ) * (b : ℝ), mul_nonneg (e (x t)).2.1 b.2⟩ : ℝ≥0)
        = φ t := by
      apply NNReal.eq
      show (e (x t) : ℝ) * b = b * (e (x t) : ℝ)
      ring
    rw [h1, h2] at h
    exact h

/-- A continuous path that starts in an open set and leaves it, leaves it after a positive
time. -/
theorem toNNReal_pathExitTime_pos {U : Set ℂ} (hU : IsOpen U) {f : ContinuousPath ℂ}
    (h0 : f 0 ∈ U) (hlt : pathExitTime U f < ⊤) : 0 < (pathExitTime U f).toNNReal := by
  obtain ⟨m, hm, hfm⟩ := MatedCRT.M0Cdf.exists_exit_eq hU f hlt
  rw [hm, ENNReal.toNNReal_coe]
  rcases eq_zero_or_pos m with h | h
  · subst h
    exact absurd h0 hfm
  · exact h

/-- The exit time from a ball is monotone in the radius. -/
theorem pathExitTime_ball_mono {f : ContinuousPath ℂ} {r r' : ℝ} (h : r ≤ r') :
    pathExitTime (ball (0 : ℂ) r) f ≤ pathExitTime (ball (0 : ℂ) r') f :=
  MatedCRT.M0Cdf.le_pathExitTime fun _ ht =>
    MatedCRT.M0Cdf.pathExitTime_le_of_not_mem fun hmem => ht (ball_subset_ball h hmem)

/-- Along radii tending to infinity, the exit times of a continuous path from the balls are
eventually above any given time. -/
theorem exists_le_toNNReal_pathExitTime {r : ℕ → ℝ} (hrt : Tendsto r atTop atTop)
    {f : ContinuousPath ℂ} (hf : ∀ k, pathExitTime (ball (0 : ℂ) (r k)) f < ⊤) (T : ℝ≥0) :
    ∃ k, T ≤ (pathExitTime (ball (0 : ℂ) (r k)) f).toNNReal := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  obtain ⟨k, hk⟩ := (hrt.eventually_gt_atTop M).exists
  refine ⟨k, ENNReal.le_toNNReal_of_coe_le ?_ (hf k).ne⟩
  refine MatedCRT.M0Cdf.le_pathExitTime fun t ht => ?_
  by_contra hlt
  have htT : t ≤ T := ENNReal.coe_le_coe.1 (not_le.1 hlt).le
  exact ht (mem_ball_zero_iff.2 ((hM t ⟨bot_le, htT⟩).trans_lt hk))

/-- **Patching level reparametrizations at exit times from balls.** If `f` and `g` leave all balls
of radii `r k` (`r` monotone, tending to infinity) and at each level `g` is an exact
reparametrization of `f` up to the exit times, then `f = g ∘ τ` with `τ` strictly increasing,
continuous, `τ 0 = 0`. -/
theorem exists_strictMono_of_levels {f g : ContinuousPath ℂ} {r : ℕ → ℝ} (hr : Monotone r)
    (hrt : Tendsto r atTop atTop)
    (hf : ∀ k, pathExitTime (ball (0 : ℂ) (r k)) f < ⊤)
    (hg : ∀ k, pathExitTime (ball (0 : ℂ) (r k)) g < ⊤)
    (hφ : ∀ k, ∃ φ : ℝ≥0 → ℝ≥0, ExactReparam (⇑f) (⇑g)
      (pathExitTime (ball (0 : ℂ) (r k)) f).toNNReal
      (pathExitTime (ball (0 : ℂ) (r k)) g).toNNReal φ) :
    ∃ τ : ℝ≥0 → ℝ≥0, StrictMono τ ∧ Continuous τ ∧ τ 0 = 0 ∧ ∀ u, f u = g (τ u) := by
  choose φ hφ using hφ
  set s : ℕ → ℝ≥0 := fun k => (pathExitTime (ball (0 : ℂ) (r k)) f).toNNReal with hs
  set s' : ℕ → ℝ≥0 := fun k => (pathExitTime (ball (0 : ℂ) (r k)) g).toNNReal with hs'
  have hcompat : ∀ j k, j ≤ k → φ k (s j) = s' j := by
    intro j k hjk
    obtain ⟨m, hm, hfm⟩ := MatedCRT.M0Cdf.exists_exit_eq (isOpen_ball (x := (0 : ℂ)) (ε := r k))
      f (hf k)
    have hsk : s k = m := by simp only [hs, hm, ENNReal.toNNReal_coe]
    have hnot : f (s k) ∉ ball (0 : ℂ) (r j) := fun hmem =>
      (hsk ▸ hfm) (ball_subset_ball (hr hjk) hmem)
    obtain ⟨m', hm'a, hm'f, -, hm'g⟩ := exitTime_transport (hφ k) isOpen_ball hnot
    simp only [hs, hs', hm'f, hm'g, ENNReal.toNNReal_coe]
  have hmono : Monotone s := fun j k hjk =>
    ENNReal.toNNReal_mono (hf k).ne (pathExitTime_ball_mono (hr hjk))
  obtain ⟨τ, hstrict, hcont, h0, -, hfg⟩ := exists_strictMono_patch hφ hcompat hmono
    (exists_le_toNNReal_pathExitTime hrt hf) (exists_le_toNNReal_pathExitTime hrt hg)
  exact ⟨τ, hstrict, hcont, h0, hfg⟩

end MatedCRT.ExitReparamLevels
