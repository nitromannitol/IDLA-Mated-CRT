import MatedCRT.FirstPass.Derived.BrownianTemplateScales
import MatedCRT.FirstPass.S6j.LitUniformStartInvariance

/-!
# The robust disconnection event is open modulo time parametrization

The template-piece event `templatePieceEvent r` (some piece `f|[a,b]` of the path follows the polar
template moved to radius `r` within Fréchet distance `r / 2000`, and the path stays in the disc of
radius `1/2` up to time `b`) and the robust disconnection event `E_δ = templateDisconnectionEvent δ`
(a finite union of template-piece events) are open for the distance of curves modulo time
parametrization `cmpEDist` of the invariance principle: for every `f` in the event there is `η > 0`
such that every path `g` with `cmpEDist g f < η` (or `cmpEDist f g < η`) is in the event.

Proof: both strict inequalities in the definition hold with a slack `η > 0`, because the suprema
involved are maxima of continuous functions on compact intervals. If `sup_t |g(t) - f(ψ(t))| < η`
for an increasing homeomorphism `ψ` of `[0, ∞)`, then `g` is in the event with the witnesses
`ψ⁻¹(a)`, `ψ⁻¹(b)` and the reparametrization of the unit interval obtained by composing the given
one with `ψ` read on the two pieces. This is the openness step of the robust disconnection event
used to transfer the Brownian disconnection estimate to the interpolated walk by the invariance
principle.
-/

namespace MatedCRT.TemplateEventOpen

open MatedCRT Set Metric MarkovProcess MatedCRTHarmonic.CellularEmbedding
open scoped NNReal ENNReal

/-- The real value of the linear time `segmentTime a b s = a + s (b - a)`. -/
theorem coe_segmentTime {a b : ℝ≥0} (hab : a ≤ b) (s : unitInterval) :
    (segmentTime a b s : ℝ) = a + (s : ℝ) * ((b : ℝ) - a) := by
  simp only [segmentTime, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hab,
    Real.coe_toNNReal _ s.2.1]

theorem segmentTime_mem {a b : ℝ≥0} (hab : a ≤ b) (s : unitInterval) :
    segmentTime a b s ∈ Icc a b := by
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.2 (NNReal.coe_le_coe.2 hab)
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  constructor
  · rw [← NNReal.coe_le_coe, coe_segmentTime hab]
    nlinarith
  · rw [← NNReal.coe_le_coe, coe_segmentTime hab]
    nlinarith

theorem strictMono_segmentTime {a b : ℝ≥0} (hab : a < b) : StrictMono (segmentTime a b) := by
  intro s s' hss'
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 (NNReal.coe_lt_coe.2 hab)
  have hlt : (s : ℝ) < s' := hss'
  rw [← NNReal.coe_lt_coe, coe_segmentTime hab.le, coe_segmentTime hab.le]
  have := mul_lt_mul_of_pos_right hlt hba
  linarith

/-- The fraction `(x - a) / (b - a)`, inverse of the linear time `segmentTime a b`. -/
noncomputable def segFrac (a b x : ℝ≥0) : ℝ :=
  ((x : ℝ) - a) / ((b : ℝ) - a)

theorem segFrac_mem {a b x : ℝ≥0} (hab : a < b) (hx : x ∈ Icc a b) :
    segFrac a b x ∈ Icc (0 : ℝ) 1 := by
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 (NNReal.coe_lt_coe.2 hab)
  have h1 : (a : ℝ) ≤ x := NNReal.coe_le_coe.2 hx.1
  have h2 : (x : ℝ) ≤ b := NNReal.coe_le_coe.2 hx.2
  exact ⟨div_nonneg (by linarith) hba.le, (div_le_one hba).2 (by linarith)⟩

theorem segmentTime_segFrac {a b x : ℝ≥0} (hab : a < b) (hx : x ∈ Icc a b) :
    segmentTime a b ⟨segFrac a b x, segFrac_mem hab hx⟩ = x := by
  have hne : (b : ℝ) - a ≠ 0 := (sub_pos.2 (NNReal.coe_lt_coe.2 hab)).ne'
  apply NNReal.eq
  rw [coe_segmentTime hab.le]
  have h : ((x : ℝ) - a) / ((b : ℝ) - a) * ((b : ℝ) - a) = (x : ℝ) - a := by
    field_simp
  change (a : ℝ) + ((x : ℝ) - a) / ((b : ℝ) - a) * ((b : ℝ) - a) = x
  rw [h]
  ring

/-- **Reparametrization of a piece.** If `ψ` is an increasing homeomorphism of `[0, ∞)` mapping
`a'` to `a` and `b'` to `b` (`a < b`, `a' < b'`), there is an increasing reparametrization `χ` of the
unit interval with `segmentTime a b (χ s) = ψ (segmentTime a' b' s)`. -/
theorem exists_segmentTime_reparam {a b a' b' : ℝ≥0} (hab : a < b) (hab' : a' < b')
    (ψ : ℝ≥0 ≃o ℝ≥0) (ha : ψ a' = a) (hb : ψ b' = b) :
    ∃ χ : MatedCRTHarmonic.Topology.IncreasingParametrization,
      ∀ s, segmentTime a b (χ s) = ψ (segmentTime a' b' s) := by
  have hmem : ∀ s, ψ (segmentTime a' b' s) ∈ Icc a b := fun s => by
    obtain ⟨h1, h2⟩ := segmentTime_mem hab'.le s
    refine ⟨?_, ?_⟩
    · rw [← ha]
      exact ψ.monotone h1
    · rw [← hb]
      exact ψ.monotone h2
  let F : unitInterval → unitInterval := fun s =>
    ⟨segFrac a b (ψ (segmentTime a' b' s)), segFrac_mem hab (hmem s)⟩
  have hF : ∀ s, segmentTime a b (F s) = ψ (segmentTime a' b' s) := fun s =>
    segmentTime_segFrac hab (hmem s)
  have hmono : StrictMono F := by
    intro s s' hss'
    have h1 := ψ.strictMono (strictMono_segmentTime hab' hss')
    rw [← hF s, ← hF s'] at h1
    exact (strictMono_segmentTime hab).lt_iff_lt.1 h1
  have hsurj : Function.Surjective F := by
    intro u
    obtain ⟨h1, h2⟩ := segmentTime_mem hab.le u
    have hx : ψ.symm (segmentTime a b u) ∈ Icc a' b' := by
      refine ⟨ψ.le_symm_apply.2 ?_, ψ.symm_apply_le.2 ?_⟩
      · rw [ha]
        exact h1
      · rw [hb]
        exact h2
    refine ⟨⟨segFrac a' b' (ψ.symm (segmentTime a b u)), segFrac_mem hab' hx⟩, ?_⟩
    apply (strictMono_segmentTime hab).injective
    rw [hF, segmentTime_segFrac hab' hx, ψ.apply_symm_apply]
  exact ⟨StrictMono.orderIsoOfSurjective F hmono hsurj, fun s => hF s⟩

/-- Slack in the disc condition: a strict bound on `‖f‖` over `[0, b]` holds with a smaller constant. -/
theorem exists_lt_forall_le_norm_le {f : ContinuousPath ℂ} {b : ℝ≥0} {c : ℝ}
    (h : ∀ t ≤ b, ‖f t‖ < c) : ∃ m < c, ∀ t ≤ b, ‖f t‖ ≤ m := by
  obtain ⟨t0, ht0, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := b)).exists_isMaxOn
    (nonempty_Icc.2 (by simp)) f.continuous.norm.continuousOn
  exact ⟨‖f t0‖, h t0 ht0.2, fun t ht => isMaxOn_iff.1 hmax t ⟨by simp, ht⟩⟩

/-- Slack in the template condition: the strict Fréchet bound on a piece holds with a smaller
constant. -/
theorem exists_lt_forall_norm_sub_movedTemplate_le {f : ContinuousPath ℂ} {a b : ℝ≥0} {r ϑ c : ℝ}
    {φ : MatedCRTHarmonic.Topology.IncreasingParametrization}
    (h : ∀ s : unitInterval, ‖f (segmentTime a b s) - movedTemplate 0 r ϑ (φ s)‖ < c) :
    ∃ m < c, ∀ s : unitInterval, ‖f (segmentTime a b s) - movedTemplate 0 r ϑ (φ s)‖ ≤ m := by
  have hseg : Continuous (segmentTime a b) :=
    continuous_const.add ((continuous_real_toNNReal.comp continuous_subtype_val).mul
      continuous_const)
  have hcont : Continuous fun s : unitInterval =>
      ‖f (segmentTime a b s) - movedTemplate 0 r ϑ (φ s)‖ :=
    ((f.continuous.comp hseg).sub
      ((continuous_movedTemplate_right 0 r ϑ).comp (continuous_subtype_val.comp φ.continuous))).norm
  obtain ⟨s0, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.continuousOn
  exact ⟨_, h s0, fun s => isMaxOn_iff.1 hmax s (mem_univ s)⟩

/-- **The template-piece event is open modulo time parametrization** (uniform form). For `f` in
`templatePieceEvent r` there is `η > 0` such that every path `g` with
`sup_t |g(t) - f(ψ(t))| < η` for some increasing homeomorphism `ψ` of `[0, ∞)` is in the event. -/
theorem exists_pos_forall_dist_comp_lt_mem_templatePieceEvent {r : ℝ} {f : ContinuousPath ℂ}
    (hf : f ∈ templatePieceEvent r) :
    ∃ η > 0, ∀ (g : ContinuousPath ℂ) (ψ : ℝ≥0 ≃o ℝ≥0), (∀ t, dist (g t) (f (ψ t)) < η) →
      g ∈ templatePieceEvent r := by
  obtain ⟨ϑ, a, b, hab, hdisc, φ, hφ⟩ := hf
  obtain ⟨m1, hm1, hm1le⟩ := exists_lt_forall_le_norm_le hdisc
  obtain ⟨m2, hm2, hm2le⟩ := exists_lt_forall_norm_sub_movedTemplate_le hφ
  refine ⟨min (1 / 2 - m1) (r / 2000 - m2), lt_min (by linarith) (by linarith), ?_⟩
  intro g ψ hg
  have hab' : ψ.symm a < ψ.symm b := ψ.symm.strictMono hab
  obtain ⟨χ, hχ⟩ := exists_segmentTime_reparam hab hab' ψ (ψ.apply_symm_apply a)
    (ψ.apply_symm_apply b)
  refine ⟨ϑ, ψ.symm a, ψ.symm b, hab', fun t ht => ?_, χ.trans φ, fun s => ?_⟩
  · have hψt : ψ t ≤ b := ψ.le_symm_apply.1 ht
    have h1 := hm1le (ψ t) hψt
    have h2 := hg t
    have h3 := norm_sub_norm_le (g t) (f (ψ t))
    rw [dist_eq_norm] at h2
    have h4 := min_le_left (1 / 2 - m1) (r / 2000 - m2)
    linarith
  · have h1 := hm2le (χ s)
    have h2 := hg (segmentTime (ψ.symm a) (ψ.symm b) s)
    rw [dist_eq_norm, ← hχ s] at h2
    have h3 := norm_sub_le_norm_sub_add_norm_sub (g (segmentTime (ψ.symm a) (ψ.symm b) s))
      (f (segmentTime a b (χ s))) (movedTemplate 0 r ϑ (φ (χ s)))
    have h4 := min_le_right (1 / 2 - m1) (r / 2000 - m2)
    change ‖g (segmentTime (ψ.symm a) (ψ.symm b) s) - movedTemplate 0 r ϑ (φ (χ s))‖ < r / 2000
    linarith

/-- A strict bound on `cmpEDist g f` is witnessed by one increasing homeomorphism of `[0, ∞)`. -/
theorem exists_orderIso_dist_lt_of_cmpEDist_lt {f g : ℝ≥0 → ℂ} {η : ℝ}
    (h : cmpEDist g f < ENNReal.ofReal η) :
    ∃ ψ : ℝ≥0 ≃o ℝ≥0, ∀ t, dist (g t) (f (ψ t)) < η := by
  obtain ⟨ψ, hψ⟩ := iInf_lt_iff.1 h
  refine ⟨ψ, fun t => ?_⟩
  have := (le_iSup (fun t => edist (g t) (f (ψ t))) t).trans_lt hψ
  rw [edist_dist] at this
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1

/-- The same with the arguments of `cmpEDist` exchanged. -/
theorem exists_orderIso_dist_lt_of_cmpEDist_lt' {f g : ℝ≥0 → ℂ} {η : ℝ}
    (h : cmpEDist f g < ENNReal.ofReal η) :
    ∃ ψ : ℝ≥0 ≃o ℝ≥0, ∀ t, dist (g t) (f (ψ t)) < η := by
  obtain ⟨ψ, hψ⟩ := exists_orderIso_dist_lt_of_cmpEDist_lt h
  refine ⟨ψ.symm, fun t => ?_⟩
  have := hψ (ψ.symm t)
  rwa [ψ.apply_symm_apply, dist_comm] at this

/-- **The template-piece event is open for `cmpEDist`.** -/
theorem exists_pos_forall_cmpEDist_lt_mem_templatePieceEvent {r : ℝ} {f : ContinuousPath ℂ}
    (hf : f ∈ templatePieceEvent r) :
    ∃ η > 0, ∀ g : ContinuousPath ℂ,
      (cmpEDist g f < ENNReal.ofReal η ∨ cmpEDist f g < ENNReal.ofReal η) →
        g ∈ templatePieceEvent r := by
  obtain ⟨η, hη, h⟩ := exists_pos_forall_dist_comp_lt_mem_templatePieceEvent hf
  refine ⟨η, hη, fun g hg => ?_⟩
  rcases hg with hg | hg
  · obtain ⟨ψ, hψ⟩ := exists_orderIso_dist_lt_of_cmpEDist_lt hg
    exact h g ψ hψ
  · obtain ⟨ψ, hψ⟩ := exists_orderIso_dist_lt_of_cmpEDist_lt' hg
    exact h g ψ hψ

/-- **The robust disconnection event `E_δ` is open for `cmpEDist`.** For `f ∈ E_δ` there is `η > 0`
such that every path `g` with `cmpEDist g f < η` or `cmpEDist f g < η` is in `E_δ`. -/
theorem exists_pos_forall_cmpEDist_lt_mem_templateDisconnectionEvent {δ : ℝ}
    {f : ContinuousPath ℂ} (hf : f ∈ templateDisconnectionEvent δ) :
    ∃ η > 0, ∀ g : ContinuousPath ℂ,
      (cmpEDist g f < ENNReal.ofReal η ∨ cmpEDist f g < ENNReal.ofReal η) →
        g ∈ templateDisconnectionEvent δ := by
  simp only [templateDisconnectionEvent, mem_iUnion] at hf
  obtain ⟨k, hk, hfk⟩ := hf
  obtain ⟨η, hη, h⟩ := exists_pos_forall_cmpEDist_lt_mem_templatePieceEvent hfk
  refine ⟨η, hη, fun g hg => ?_⟩
  simp only [templateDisconnectionEvent, mem_iUnion]
  exact ⟨k, hk, h g hg⟩

/-- `E_δ` is invariant under increasing time changes. -/
theorem comp_mem_templateDisconnectionEvent {δ : ℝ} {f g : ContinuousPath ℂ}
    (hf : f ∈ templateDisconnectionEvent δ) (ψ : ℝ≥0 ≃o ℝ≥0) (hg : ∀ t, g t = f (ψ t)) :
    g ∈ templateDisconnectionEvent δ := by
  obtain ⟨η, hη, h⟩ := exists_pos_forall_cmpEDist_lt_mem_templateDisconnectionEvent hf
  refine h g (Or.inl ?_)
  refine lt_of_le_of_lt (iInf_le_of_le ψ ?_) (ENNReal.ofReal_pos.2 hη)
  simp [hg]

end MatedCRT.TemplateEventOpen

/-! ## Audit -/

#print axioms MatedCRT.TemplateEventOpen.exists_segmentTime_reparam
#print axioms MatedCRT.TemplateEventOpen.exists_pos_forall_dist_comp_lt_mem_templatePieceEvent
#print axioms MatedCRT.TemplateEventOpen.exists_pos_forall_cmpEDist_lt_mem_templatePieceEvent
#print axioms MatedCRT.TemplateEventOpen.exists_pos_forall_cmpEDist_lt_mem_templateDisconnectionEvent
#print axioms MatedCRT.TemplateEventOpen.comp_mem_templateDisconnectionEvent
