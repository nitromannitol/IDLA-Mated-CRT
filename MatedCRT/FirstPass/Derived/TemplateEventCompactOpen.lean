import MatedCRT.FirstPass.Derived.TemplateEventOpen

/-!
# The robust disconnection event is open in the compact-open topology

The template-piece event `templatePieceEvent r` asks for a piece `f|[a,b]` of the path that stays
in the disc of radius `1/2` up to time `b` and follows a moved polar template within Fréchet distance
`r / 2000`. Both conditions concern the path on the compact time interval `[0, b]` only, and both are
strict inequalities between continuous functions on a compact set. Hence a path that is uniformly
close to `f` on `[0, b]` is again in the event: the event is open in the compact-open topology of
`C([0, ∞), ℂ)` (uniform convergence on compact time intervals), and so is the robust disconnection
event `E_δ` (a finite union).

This is the topology of the invariance principle of Gwynne, Miller and Sheffield
(arXiv 1807.07515, Theorem 1.16), stated for paths with values in `EuclideanSpace ℝ (Fin 2)`; the
last part transports the openness along the isometry `EuclideanSpace ℝ (Fin 2) ≃ ℂ`
(`e₀ ↦ 1`, `e₁ ↦ i`), so the open-set portmanteau theorem applies to `E_δ` (proof of Lemma 3.14 of
that paper, condition 3).

## Main statements

* `exists_pos_forall_dist_lt_mem_templatePieceEvent`: slack on a finite time window.
* `isOpen_templatePieceEvent`, `isOpen_templateDisconnectionEvent`.
* `eucPathToComplex` (continuous), `isOpen_preimage_eucPathToComplex_templateDisconnectionEvent`.
-/

namespace MatedCRT.TemplateEventCompactOpen

open MatedCRT MatedCRT.TemplateEventOpen Set Metric MarkovProcess Topology
  MatedCRTHarmonic.CellularEmbedding
open scoped NNReal ENNReal

/-- **Slack on a finite window.** A path in the template-piece event has a time `b` and a margin
`η > 0` such that every path within `η` of it, uniformly on `[0, b]`, is in the event. -/
theorem exists_pos_forall_dist_lt_mem_templatePieceEvent {r : ℝ} {f : ContinuousPath ℂ}
    (hf : f ∈ templatePieceEvent r) :
    ∃ η > 0, ∃ b : ℝ≥0, ∀ g : ContinuousPath ℂ, (∀ t ≤ b, dist (f t) (g t) < η) →
      g ∈ templatePieceEvent r := by
  obtain ⟨ϑ, a, b, hab, hdisc, φ, hφ⟩ := hf
  obtain ⟨m1, hm1, hm1le⟩ := exists_lt_forall_le_norm_le hdisc
  obtain ⟨m2, hm2, hm2le⟩ := exists_lt_forall_norm_sub_movedTemplate_le hφ
  refine ⟨min (1 / 2 - m1) (r / 2000 - m2), lt_min (by linarith) (by linarith), b, ?_⟩
  intro g hg
  refine ⟨ϑ, a, b, hab, fun t ht => ?_, φ, fun s => ?_⟩
  · have h1 := hm1le t ht
    have h2 := hg t ht
    have h3 := norm_sub_norm_le (g t) (f t)
    rw [dist_comm, dist_eq_norm] at h2
    have h4 := min_le_left (1 / 2 - m1) (r / 2000 - m2)
    linarith
  · have h1 := hm2le s
    have h2 := hg (segmentTime a b s) (segmentTime_mem hab.le s).2
    rw [dist_comm, dist_eq_norm] at h2
    have h3 := norm_sub_le_norm_sub_add_norm_sub (g (segmentTime a b s))
      (f (segmentTime a b s)) (movedTemplate 0 r ϑ (φ s))
    have h4 := min_le_right (1 / 2 - m1) (r / 2000 - m2)
    linarith

/-- A uniform neighbourhood on `[0, T]` is a neighbourhood in `C([0, ∞), ℂ)` (compact-open
topology). -/
theorem setOf_forall_dist_lt_mem_nhds (f : ContinuousPath ℂ) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    {g : ContinuousPath ℂ | ∀ t ≤ T, dist (f t) (g t) < η} ∈ 𝓝 f := by
  rw [UniformSpace.mem_nhds_iff]
  refine ⟨_, ContinuousMap.hasBasis_compactConvergenceUniformity.mem_of_mem
    (i := (Icc (0 : ℝ≥0) T, {p : ℂ × ℂ | dist p.1 p.2 < η}))
    ⟨isCompact_Icc, Metric.dist_mem_uniformity hη⟩, ?_⟩
  intro g hg t ht
  exact hg t ⟨zero_le, ht⟩

/-- **The template-piece event is open** in the compact-open topology of `C([0, ∞), ℂ)`. -/
theorem isOpen_templatePieceEvent (r : ℝ) : IsOpen (templatePieceEvent r) := by
  rw [isOpen_iff_mem_nhds]
  intro f hf
  obtain ⟨η, hη, b, h⟩ := exists_pos_forall_dist_lt_mem_templatePieceEvent hf
  exact Filter.mem_of_superset (setOf_forall_dist_lt_mem_nhds f b hη) fun g hg => h g hg

/-- **The robust disconnection event `E_δ` is open** in the compact-open topology of
`C([0, ∞), ℂ)`. -/
theorem isOpen_templateDisconnectionEvent (δ : ℝ) : IsOpen (templateDisconnectionEvent δ) :=
  isOpen_biUnion fun k _ => isOpen_templatePieceEvent (templateRadius k)

/-- A path in `EuclideanSpace ℝ (Fin 2)` read as a complex path through the isometry
`EuclideanSpace ℝ (Fin 2) ≃ ℂ` sending the standard basis to `1, i`. -/
noncomputable def eucPathToComplex (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) : ContinuousPath ℂ :=
  (⟨Complex.orthonormalBasisOneI.repr.symm, Complex.orthonormalBasisOneI.repr.symm.continuous⟩ :
    C(EuclideanSpace ℝ (Fin 2), ℂ)).comp f

@[simp] theorem eucPathToComplex_apply (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) (t : ℝ≥0) :
    eucPathToComplex f t = Complex.orthonormalBasisOneI.repr.symm (f t) := rfl

/-- Reading paths in the plane as complex paths is continuous for the compact-open topologies. -/
theorem continuous_eucPathToComplex : Continuous eucPathToComplex :=
  ContinuousMap.continuous_postcomp _

/-- `E_δ`, pulled back to paths in `EuclideanSpace ℝ (Fin 2)`, is open in the compact-open
topology: the form in which the open-set portmanteau theorem applies to the invariance principle. -/
theorem isOpen_preimage_eucPathToComplex_templateDisconnectionEvent (δ : ℝ) :
    IsOpen (eucPathToComplex ⁻¹' templateDisconnectionEvent δ) :=
  (isOpen_templateDisconnectionEvent δ).preimage continuous_eucPathToComplex

end MatedCRT.TemplateEventCompactOpen

/-! ## Audit -/
#print axioms MatedCRT.TemplateEventCompactOpen.isOpen_templatePieceEvent
#print axioms MatedCRT.TemplateEventCompactOpen.isOpen_templateDisconnectionEvent
#print axioms MatedCRT.TemplateEventCompactOpen.isOpen_preimage_eucPathToComplex_templateDisconnectionEvent
