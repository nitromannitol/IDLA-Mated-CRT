import MatedCRT.FirstPass.Derived.ExitReparamPatch
import MatedCRT.FirstPass.Derived.StopAtExitLevyProkhorov

/-!
# Exact reparametrizations give equal finite-prefix curve classes

If `f = g ∘ φ` on `[0,a]` for a strictly increasing `φ` carrying `[0,a]` onto `[0,b]`, the
normalized prefixes of `f` on `[0,a]` and of `g` on `[0,b]` differ by an order automorphism of the
unit interval, so they have the same curve class (`normalizedPrefixCurve_eq_of_exactReparam`).
For planar continuous paths stopped at their first exit time from an open set this says that the
stopped curve classes of `f` and `g` agree whenever `f` leaves the set and `g` is an exact
reparametrization of `f` up to that time (`stoppedExitCurve_eq_of_exactReparam`).
-/

set_option autoImplicit false

open HarmonicBalls MarkovProcess Set LatticeProb LatticeProb.CurveSpaceComparison
open scoped ENNReal NNReal unitInterval

namespace MatedCRT.ExitReparamClass

open MatedCRT.ExitReparamPatch

/-- An exact increasing reparametrization carrying `[0,a]` onto `[0,b]` identifies the curve
classes of the normalized prefixes of duration `a` and `b`. -/
theorem normalizedPrefixCurve_eq_of_exactReparam {d : ℕ}
    {w v : C(ℝ≥0, EuclideanSpace ℝ (Fin d))} {a b : ℝ≥0} {φ : ℝ≥0 → ℝ≥0}
    (h : ExactReparam (⇑w) (⇑v) a b φ) :
    normalizedPrefixCurve w a = normalizedPrefixCurve v b := by
  rcases eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : b = 0 := by rw [← h.map_self, h.map_zero]
    subst hb
    have h0 : w 0 = v 0 := by simpa [h.map_zero] using h.eq 0 le_rfl
    unfold normalizedPrefixCurve
    congr 1
    refine ContinuousMap.ext fun x => ?_
    simp only [normalizedPathPrefix_apply, NNReal.coe_zero, mul_zero]
    exact h0
  · have hb : 0 < b := by
      have h1 : φ 0 < φ a :=
        h.strictMonoOn (mem_Iic.2 bot_le) (mem_Iic.2 le_rfl) ha
      rwa [h.map_zero, h.map_self] at h1
    have hsle : ∀ x : unitInterval, (⟨(x : ℝ) * (a : ℝ), mul_nonneg x.property.1 a.property⟩ : ℝ≥0)
        ≤ a := fun x => by
      show (x : ℝ) * (a : ℝ) ≤ (a : ℝ)
      exact mul_le_of_le_one_left a.property x.property.2
    set s : unitInterval → ℝ≥0 := fun x =>
      ⟨(x : ℝ) * (a : ℝ), mul_nonneg x.property.1 a.property⟩ with hs
    have hφle : ∀ x, φ (s x) ≤ b := fun x => mem_Iic.1 (h.mapsTo (mem_Iic.2 (hsle x)))
    let e0 : unitInterval → unitInterval := fun x =>
      ⟨(φ (s x) : ℝ) / b, div_nonneg (φ (s x)).property b.property,
        (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hφle x)⟩
    have hmono : StrictMono e0 := by
      intro x y hxy
      have hsxy : s x < s y := by
        show (x : ℝ) * (a : ℝ) < (y : ℝ) * (a : ℝ)
        exact mul_lt_mul_of_pos_right hxy (by exact_mod_cast ha)
      have := h.strictMonoOn (mem_Iic.2 (hsle x)) (mem_Iic.2 (hsle y)) hsxy
      show (φ (s x) : ℝ) / b < (φ (s y) : ℝ) / b
      exact div_lt_div_of_pos_right (by exact_mod_cast this) (by exact_mod_cast hb)
    have hsurj : Function.Surjective e0 := by
      intro y
      have hyb : (⟨(y : ℝ) * (b : ℝ), mul_nonneg y.property.1 b.property⟩ : ℝ≥0) ≤ b := by
        show (y : ℝ) * (b : ℝ) ≤ (b : ℝ)
        exact mul_le_of_le_one_left b.property y.property.2
      obtain ⟨t, ht, htφ⟩ := h.surjOn (mem_Iic.2 hyb)
      have hta : t ≤ a := mem_Iic.1 ht
      let x : unitInterval := ⟨(t : ℝ) / a, div_nonneg t.property a.property,
        (div_le_one (by exact_mod_cast ha)).2 (by exact_mod_cast hta)⟩
      have hxs : s x = t := by
        apply NNReal.eq
        show ((t : ℝ) / a) * (a : ℝ) = t
        exact div_mul_cancel₀ _ (by exact_mod_cast ha.ne')
      refine ⟨x, ?_⟩
      apply Subtype.ext
      show (φ (s x) : ℝ) / b = y
      rw [hxs, htφ]
      show (y : ℝ) * (b : ℝ) / b = y
      exact mul_div_cancel_right₀ _ (by exact_mod_cast hb.ne')
    let e : unitInterval ≃o unitInterval := StrictMono.orderIsoOfSurjective e0 hmono hsurj
    unfold normalizedPrefixCurve CurveSpace.project
    rw [CurveSpace.mk_eq_mk_iff]
    apply le_antisymm _ bot_le
    refine (iInf_le _ e).trans ?_
    refine iSup_le fun t => ?_
    have hEq : (NormalizedCurve.ofPath (normalizedPathPrefix w a)).path t =
        (NormalizedCurve.ofPath (normalizedPathPrefix v b)).path (e t) := by
      show w (s t) = v ⟨((φ (s t) : ℝ) / b) * (b : ℝ), _⟩
      have : (⟨((φ (s t) : ℝ) / b) * (b : ℝ), mul_nonneg (div_nonneg (φ (s t)).property
          b.property) b.property⟩ : ℝ≥0) = φ (s t) := by
        apply NNReal.eq
        exact div_mul_cancel₀ _ (by exact_mod_cast hb.ne')
      rw [this]
      exact h.eq (s t) (hsle t)
    rw [hEq, edist_self]
    exact le_rfl

/-- If `g` is an exact reparametrization of the continuous planar path `f` up to a time `a` at
which `f` is outside the open set `U`, then `f` and `g` have the same stopped curve class at
their first exit times from `U`. -/
theorem stoppedExitCurve_eq_of_exactReparam {f g : ContinuousPath ℂ} {a b : ℝ≥0}
    {φ : ℝ≥0 → ℝ≥0} (h : ExactReparam (⇑f) (⇑g) a b φ) {U : Set ℂ} (hU : IsOpen U)
    (ha : f a ∉ U) :
    MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve U f =
      MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve U g := by
  obtain ⟨m, hma, hσf, -, hσg⟩ := exitTime_transport h hU ha
  have hm : ExactReparam (⇑f) (⇑g) m (φ m) φ :=
    { strictMonoOn := h.strictMonoOn.mono (Iic_subset_Iic.2 hma)
      mapsTo := fun t ht =>
        mem_Iic.2 (h.strictMonoOn.monotoneOn (mem_Iic.2 (ht.trans hma)) (mem_Iic.2 hma) ht)
      surjOn := fun y hy => by
        have hyb : y ≤ b := hy.trans
          (h.strictMonoOn.monotoneOn (mem_Iic.2 hma) (mem_Iic.2 le_rfl) hma |>.trans
            (mem_Iic.1 (h.mapsTo (mem_Iic.2 le_rfl))))
        obtain ⟨t, ht, rfl⟩ := h.surjOn (mem_Iic.2 hyb)
        refine ⟨t, mem_Iic.2 ?_, rfl⟩
        by_contra hlt
        have hlt' : m < t := not_le.1 hlt
        have := h.strictMonoOn (mem_Iic.2 hma) ht hlt'
        exact absurd (mem_Iic.1 hy) (not_le.2 this)
      eq := fun t ht => h.eq t (ht.trans hma) }
  have hcls := normalizedPrefixCurve_eq_of_exactReparam
    (w := ReparamDistanceIsometry.complexToEuclideanPath f)
    (v := ReparamDistanceIsometry.complexToEuclideanPath g)
    (a := m) (b := φ m) (φ := φ)
    { strictMonoOn := hm.strictMonoOn
      mapsTo := hm.mapsTo
      surjOn := hm.surjOn
      eq := fun t ht => by simp [ReparamDistanceIsometry.complexToEuclideanPath, hm.eq t ht] }
  unfold MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve
  rw [hσf, hσg]
  simpa using congrArg (isometryEquiv 2) hcls

end MatedCRT.ExitReparamClass
