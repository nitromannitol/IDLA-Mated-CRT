import MatedCRT.FirstPass.Derived.TemplateWalkSeparation
import MatedCRT.FirstPass.Derived.LinInterpHalfStep
import MatedCRT.FirstPass.Derived.BrownianTemplateScales
import LatticeProb.Euclidean.TemplateItinerary

/-!
# A walk whose interpolation follows a template piece disconnects a small disc from the unit circle

Discrete side of the Brownian disconnection estimate behind condition 3 of Lemma 3.14 of Gwynne, Miller
and Sheffield, *An invariance principle for ergodic scale-free random environments* (arXiv 1807.07515),
in the robust form of the template events of `BrownianTemplateEvent` and `BrownianTemplateScales`.

Setting: a cellular embedding `H` of a locally finite multigraph on `ℤ`, a point `v k` of each cell, a
walk `ξ` along edges of the graph whose consecutive cells meet, and the linear interpolation of the
points `v (ξ m)` run at speed `m > 0` (`interpPathCM v hm ξ`).

* `graphSeparates_traceBefore_of_mem_templatePieceEvent`: if the interpolation lies in the template
  piece event at scale `r` (some piece of the path, linearly normalized, follows the polar template
  moved to radius `r` within `r / 2000` up to an increasing reparametrization, and the path stays in
  the disc of radius `1/2` until the end of the piece), every cell meeting the unit disc has diameter
  at most `d ≤ r / 2000`, and the template separation property holds at `(0, r)`, then the trace of
  the walk before its first visit to the cells meeting the unit circle separates the cells meeting
  `closedBall 0 δ` (`δ ≤ 3r/4`) from the cells meeting the unit circle.
* `graphSeparates_traceBefore_of_mem_templateDisconnectionEvent`: the same for the robust
  disconnection event `templateDisconnectionEvent δ` (a union of template piece events over the
  scales `4^{-k}`, `1 ≤ k ≤ K(δ)`), with cells of diameter at most `4^{-K(δ)} / 2000`.

Proof: the piece of the path gives, after the time change `t ↦ m t` and the clamped itinerary of
`LatticeProb.PolarTemplate.isTemplateWalk_of_uniform_approx`, a template walk; the endpoint and
half-step estimates come from `TemplateWalkSeparation.dist_lt_and_diam_le_of_meet` and
`LinInterpHalfStep.dist_linInterp_le_of_half_step`; the separation is
`TemplateWalkSeparation.graphSeparates_traceBefore_sphere_of_isTemplateWalk_of_points`.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal
open MatedCRT.TemplateWalkSeparation MatedCRT.LinInterpHalfStep
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.CellularEmbedding

namespace MatedCRT.TemplateDisconnectionWalk

/-- The linear interpolation passes through its nodes. -/
theorem linInterp_natCast (a : ℕ → ℂ) (k : ℕ) : linInterp a (k : ℝ) = a k := by
  rw [linInterp_of_floor_eq (Nat.floor_natCast k), sub_self, Complex.ofReal_zero, zero_mul,
    add_zero]

/-- An increasing reparametrization of the unit interval fixes `0`. -/
theorem coe_apply_eq_zero (φ : MatedCRTHarmonic.Topology.IncreasingParametrization)
    {x : unitInterval} (hx : (x : ℝ) = 0) : (φ x : ℝ) = 0 := by
  have h : φ x ≤ φ (φ.symm ⟨0, unitInterval.zero_mem⟩) :=
    φ.monotone (Subtype.coe_le_coe.1 (by rw [hx]; exact (φ.symm _).2.1))
  rw [OrderIso.apply_symm_apply] at h
  exact le_antisymm (Subtype.coe_le_coe.2 h) (φ x).2.1

/-- An increasing reparametrization of the unit interval fixes `1`. -/
theorem coe_apply_eq_one (φ : MatedCRTHarmonic.Topology.IncreasingParametrization)
    {x : unitInterval} (hx : (x : ℝ) = 1) : (φ x : ℝ) = 1 := by
  have h : φ (φ.symm ⟨1, unitInterval.one_mem⟩) ≤ φ x :=
    φ.monotone (Subtype.coe_le_coe.1 (by rw [hx]; exact (φ.symm _).2.2))
  rw [OrderIso.apply_symm_apply] at h
  exact le_antisymm (φ x).2.2 (Subtype.coe_le_coe.2 h)

variable {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} {H : CellularEmbedding G o}

/-- **Template piece ⇒ disconnection (one scale).** If the interpolation of the walk lies in the
template piece event at scale `r`, then the trace of the walk before the cells meeting the unit circle
separates the cells meeting `closedBall 0 δ` from them. -/
theorem graphSeparates_traceBefore_of_mem_templatePieceEvent {v : ℤ → ℂ}
    (hv : ∀ k, v k ∈ H.cell k) {ξ : ℕ → ℤ} (hadj : ∀ m, G.adj.Adj (ξ m) (ξ (m + 1)))
    (hmeet : ∀ m, (H.cell (ξ m) ∩ H.cell (ξ (m + 1))).Nonempty) {m : ℝ} (hm : 0 < m)
    {r δ d : ℝ} (hr : 0 < r) (hr1 : 5 * r / 4 ≤ 1) (hδ : δ ≤ 3 * r / 4) (hd : 0 ≤ d)
    (hdr : d ≤ r / 2000) (hdiam : ∀ k, (H.cell k ∩ ball 0 1).Nonempty → diam (H.cell k) ≤ d)
    (hTS : H.TemplateSeparation 0 r) (hf : interpPathCM v hm.le ξ ∈ templatePieceEvent r) :
    GraphSeparates G.adj (traceBefore (id : ℤ → ℤ) (verticesMeeting H.cell (sphere 0 1)) ξ)
      {y | ∃ x ∈ H.cell y, dist x 0 ≤ δ} (verticesMeeting H.cell (sphere 0 1)) := by
  obtain ⟨ϑ, a, b, hab, hball, φ, htube⟩ := hf
  set q : ℕ → ℂ := fun k => v (ξ k) with hq_def
  have hqJ : ∀ k, q k ∈ H.cell (ξ k) := fun k => hv (ξ k)
  have hf_apply : ∀ t : ℝ≥0, interpPathCM v hm.le ξ t = linInterp q (m * t) := fun t => rfl
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hba : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 hab'
  have hA0 : 0 ≤ m * (a : ℝ) := mul_nonneg hm.le a.2
  have hAB : m * (a : ℝ) ≤ m * b := mul_le_mul_of_nonneg_left hab'.le hm.le
  have hBA : 0 < m * (b : ℝ) - m * a := by nlinarith [mul_pos hm hba]
  -- the reparametrization of the piece in walk-step time
  have : OrderTopology unitInterval := orderTopology_of_ordConnected
  set φ' : ℝ → ℝ := fun s =>
    (φ (projIcc 0 1 zero_le_one ((s - m * a) / (m * b - m * a))) : ℝ) with hφ'
  have hφm : MonotoneOn φ' (Icc (m * (a : ℝ)) (m * b)) := by
    refine (Monotone.monotoneOn (fun s t hst => ?_) _)
    have h1 : (s - m * a) / (m * b - m * a) ≤ (t - m * a) / (m * b - m * a) :=
      (div_le_div_iff_of_pos_right hBA).2 (by linarith)
    exact Subtype.coe_le_coe.2 (φ.monotone (monotone_projIcc zero_le_one h1))
  have hφcont : Continuous φ' := by
    have h1 : Continuous fun s : ℝ =>
        projIcc (0 : ℝ) 1 zero_le_one ((s - m * a) / (m * b - m * a)) :=
      continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _)
    exact continuous_subtype_val.comp (φ.continuous.comp h1)
  have hφc : ContinuousOn φ' (Icc (m * (a : ℝ)) (m * b)) := hφcont.continuousOn
  have hφa : φ' (m * a) = 0 := by
    refine coe_apply_eq_zero φ ?_
    rw [sub_self, zero_div, projIcc_left]
  have hφb : φ' (m * b) = 1 := by
    refine coe_apply_eq_one φ ?_
    rw [div_self hBA.ne', projIcc_right]
  have htube' : ∀ s ∈ Icc (m * (a : ℝ)) (m * b),
      ‖linInterp q s - movedTemplate 0 r ϑ (φ' s)‖ < r / 2000 := by
    intro s hs
    set u : unitInterval := projIcc 0 1 zero_le_one ((s - m * a) / (m * b - m * a)) with hu_def
    have hu : (u : ℝ) = (s - m * a) / (m * b - m * a) := by
      rw [hu_def, coe_projIcc]
      have h0 : 0 ≤ (s - m * a) / (m * b - m * a) := div_nonneg (by linarith [hs.1]) hBA.le
      have h1 : (s - m * a) / (m * b - m * a) ≤ 1 := (div_le_one hBA).2 (by linarith [hs.2])
      rw [min_eq_right h1, max_eq_right h0]
    have ht : m * (segmentTime a b u : ℝ) = s := by
      have key : (s - m * a) / (m * b - m * a) * ((b : ℝ) - a) = (s - m * a) / m := by
        rw [div_mul_eq_mul_div, show m * (b : ℝ) - m * a = m * ((b : ℝ) - a) by ring,
          mul_div_mul_right _ _ hba.ne']
      have hm' : m ≠ 0 := hm.ne'
      rw [segmentTime, NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ u.2.1,
        NNReal.coe_sub hab.le, hu, key]
      have hc : m * ((s - m * a) / m) = s - m * a := by field_simp
      rw [mul_add, hc]
      ring
    have h := htube u
    rw [hf_apply, ht] at h
    exact h
  -- itinerary indices and the template walk
  obtain ⟨m₀, n, ha₁, ha₂, hb₁, hb₂⟩ :=
    LatticeProb.PolarTemplate.exists_itinerary_indices hA0 hAB
  have hρ : (1 / 2 : ℝ) + 3 * d < 1 := by linarith
  have hqb : ∀ M : ℕ, (M : ℝ) ≤ m * b → dist (q M) 0 < 1 / 2 := by
    intro M hM
    have hM0 : (0 : ℝ) ≤ (M : ℝ) / m := div_nonneg (Nat.cast_nonneg M) hm.le
    have ht : Real.toNNReal ((M : ℝ) / m) ≤ b := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hM0, div_le_iff₀ hm]
      linarith
    have h := hball _ ht
    rw [hf_apply, Real.coe_toNNReal _ hM0] at h
    have hmM : m * ((M : ℝ) / m) = M := by field_simp
    rw [hmM, linInterp_natCast] at h
    rwa [dist_zero_right]
  have hN : ((m₀ + n : ℕ) : ℝ) ≤ m * b + 1 / 2 := by push_cast; linarith
  have hR3 := dist_lt_and_diam_le_of_meet (fun k => (H.isCompact_cell k).isBounded) hdiam hd
    (by linarith) hqJ (fun M _ => hmeet M) (le_trans hA0 hAB) hqb hN
  have hdiam_succ : ∀ M ≤ m₀ + n, diam (H.cell (ξ (M + 1))) ≤ d := by
    intro M hM
    obtain ⟨hqM, hdM⟩ := hR3 M hM
    obtain ⟨w, hw1, hw2⟩ := hmeet M
    refine hdiam _ ⟨w, hw2, ?_⟩
    rw [mem_ball]
    have h := dist_le_diam_of_mem (H.isCompact_cell _).isBounded hw1 (hqJ M)
    linarith [dist_triangle w (q M) 0]
  have hstep : ∀ M ≤ m₀ + n, dist (q M) (q (M + 1)) ≤ 2 * d := fun M hM =>
    dist_le_two_mul_of_inter_nonempty (H.isCompact_cell _).isBounded
      (H.isCompact_cell _).isBounded (hqJ M) (hqJ (M + 1)) (hmeet M) (hR3 M hM).2
      (hdiam_succ M hM)
  have hfq : ∀ j ≤ n, ∀ t ∈ Icc (m * (a : ℝ)) (m * b), |t - ((m₀ : ℝ) + j)| ≤ 1 / 2 →
      ‖linInterp q t - q (m₀ + j)‖ ≤ d := by
    intro j hj t ht htj
    rw [← dist_eq_norm]
    refine dist_linInterp_le_of_half_step (le_trans hA0 ht.1) (by push_cast; exact htj)
      (hstep _ (by omega)) ?_
    intro k hk
    rw [← hk]
    exact hstep k (by omega)
  have hW := LatticeProb.PolarTemplate.isTemplateWalk_of_uniform_approx H 0 hAB hφm hφc hφa hφb
    htube' (v := ξ) (q := q) ha₁ ha₂ hb₁ hb₂ (fun j _ => hadj (m₀ + j)) (fun j _ => hqJ (m₀ + j))
    (fun j hj => (hR3 (m₀ + j) (by omega)).2) hfq (by linarith) (by linarith)
  exact graphSeparates_traceBefore_sphere_of_isTemplateWalk_of_points hr.le hδ (by linarith) hd hρ
    (le_trans hA0 hAB) hdiam hTS hW hqJ (fun M _ => hmeet M) hqb hN

/-- **Robust disconnection event ⇒ disconnection.** If the interpolation of the walk lies in
`templateDisconnectionEvent δ` (`0 < δ`), every cell meeting the unit disc has diameter at most
`d ≤ 4^{-K(δ)} / 2000`, and the template separation property holds at `(0, 4^{-k})` for
`1 ≤ k ≤ K(δ)`, then the trace of the walk before the cells meeting the unit circle separates the
cells meeting `closedBall 0 δ` from them. -/
theorem graphSeparates_traceBefore_of_mem_templateDisconnectionEvent {v : ℤ → ℂ}
    (hv : ∀ k, v k ∈ H.cell k) {ξ : ℕ → ℤ} (hadj : ∀ m, G.adj.Adj (ξ m) (ξ (m + 1)))
    (hmeet : ∀ m, (H.cell (ξ m) ∩ H.cell (ξ (m + 1))).Nonempty) {m : ℝ} (hm : 0 < m)
    {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (hdK : d ≤ (templateRadius (templateScaleCount δ) : ℝ) / 2000)
    (hdiam : ∀ k, (H.cell k ∩ ball 0 1).Nonempty → diam (H.cell k) ≤ d)
    (hTS : ∀ k ∈ Finset.Icc 1 (templateScaleCount δ),
      H.TemplateSeparation 0 (templateRadius k))
    (hf : interpPathCM v hm.le ξ ∈ templateDisconnectionEvent δ) :
    GraphSeparates G.adj (traceBefore (id : ℤ → ℤ) (verticesMeeting H.cell (sphere 0 1)) ξ)
      {y | ∃ x ∈ H.cell y, dist x 0 ≤ δ} (verticesMeeting H.cell (sphere 0 1)) := by
  simp only [templateDisconnectionEvent, mem_iUnion] at hf
  obtain ⟨k, hk, hfk⟩ := hf
  obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.1 hk
  have hr : (0 : ℝ) < templateRadius k := by exact_mod_cast templateRadius_pos k
  have hrk : (templateRadius k : ℝ) ≤ 1 / 4 := by
    rw [coe_templateRadius]
    calc (1 / 4 : ℝ) ^ k ≤ (1 / 4) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk1
      _ = 1 / 4 := pow_one _
  have hKk : (templateRadius (templateScaleCount δ) : ℝ) ≤ templateRadius k := by
    rw [coe_templateRadius, coe_templateRadius]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hkK
  have hδk := le_templateRadius_of_le_templateScaleCount hδ hk1 hkK
  exact graphSeparates_traceBefore_of_mem_templatePieceEvent hv hadj hmeet hm hr (by linarith)
    (by linarith) hd (by linarith) hdiam (hTS k hk) hfk

end MatedCRT.TemplateDisconnectionWalk

/-! ## Audit -/
#print axioms MatedCRT.TemplateDisconnectionWalk.graphSeparates_traceBefore_of_mem_templatePieceEvent
#print axioms MatedCRT.TemplateDisconnectionWalk.graphSeparates_traceBefore_of_mem_templateDisconnectionEvent
