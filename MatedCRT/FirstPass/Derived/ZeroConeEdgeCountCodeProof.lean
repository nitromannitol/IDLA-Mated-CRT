import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepairProofs
import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideIdentityProof
import LatticeProb.LQG.PeanosphereTimeChange
import LatticeProb.LQG.CoupledAreaTimeChange

/-!
# The edge counts of the zero-cone cells as a dilation-invariant Borel function of the curve

This file proves `ZeroConeEdgeCountCode` (`GMS21ZeroConeAnnulusRepairProofs.lean`), following the written answer
`notes/fp-gaps/CODEX-MQ-sbl-27.md`, section "(c) One dilation-invariant Borel decoder for all meshes" (lines 44-52),
and Gwynne–Miller–Sheffield, arXiv:1705.11161, (1.2) and the proof of Proposition 2.2.

The decoder is the frontier-side multiplicity of the unit cells, `Ψ q = cellSideMult 1 q` (`CellSideMult.lean`), on
all curves (`S = univ`). It is Borel (`measurable_cellSideMult`) and invariant under positive dilations of the plane
(`cellSideMult_smul`: a dilation preserves the continua of positive diameter in the intersections of the cell images).
Instead of the disintegration of the answer (lines 52), the identity of the edge counts with the decoder is read off
the deterministic identity `bmEdgeCount_eq_cellSideMult` (`MatingOfTreesCellSideIdentityProof.lean`) at mesh `1`,
applied to the Peanosphere `(bm ∘ e, η ∘ e)` with the increasing time change `e t = ψ ((t + θ)/n)`, where `ψ` is the
area clock between the zero-cone curve and the γ-cone curve (`LatticeProb.ae_coupled_area_clock`):

* the edge counts are invariant under the linear time change `t ↦ t/n` (`bmEdgeCount_comp_mul_left`), and
  `G((t + θ)/n) = bm(e t)` for a boundary-pair version `G`;
* the cell endpoints `(k + θ)/n` are almost surely visited once by the zero-cone curve (answer, line 48: "Almost surely
  the independent phase avoids all multiply visited endpoints, by area additivity on disjoint rational intervals and
  `(η₀)_* dt = μ_h`"): the images of two non-overlapping intervals meet in a null set of the area measure
  (`measure_image_Icc_inter_image_Icc_eq_zero`), so the times of a compact interval sent into a null compact set form a
  Lebesgue-null set (`volume_Icc_inter_preimage_eq_zero`), and the multiply visited times are covered by countably many
  such sets (`multipleVisitWitness`, `volume_multipleVisitWitness_eq_zero`); Fubini in the phase concludes;
* at a time visited once both Brownian coordinates descend on both sides (answer, line 48, `isTwoSidedDescent_of_forall_eq`):
  otherwise the first return of the coordinate to its value is a direct identification with a second visit
  (`exists_directRel_right`, `exists_directRel_left`).

Named hypotheses (literature, on general objects; PENDING TRUTH CHECK):
* `CorrelatedBMNoCommonLocalMin` (`MatingOfTreesCellSideIdentityProof.lean`): no common local minimum of the two
  coordinates of a correlated planar Brownian motion (Le Gall, two-sided cone points).
* `CorrelatedBMPeanosphereTriplePointsNoContinuum` (this file): for almost every correlated Brownian pair, the points
  visited three times by any Peanosphere curve of the pair contain no continuum of positive diameter (Gwynne–Holden–Miller,
  arXiv:1512.01223, Corollary 6.5; Duplantier–Miller–Sheffield, arXiv:1409.7055, (8.9), Lemmas 8.12-8.13, and the
  homeomorphism between two Peanosphere traversals of the same pair, answer line 50).
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-! ### The named hypothesis on triple points -/

/-- **Named hypothesis: the points visited three times by a Peanosphere curve of a correlated Brownian motion
contain no continuum.** PENDING TRUTH CHECK.

For `0 < γ < 2` and the law `μ` of a `γ`-correlated two-sided planar Brownian motion, for `μ`-almost every pair `p`,
every curve `η` forming a Peanosphere with `p` (`RouteM.Peanosphere p η`: the times identified by `η` are exactly
those identified by the contour functions) has no continuum of positive diameter among its points visited at least
three times. Two Peanosphere curves of the same pair differ by a homeomorphism of the plane (written answer
`notes/fp-gaps/CODEX-MQ-sbl-27.md`, line 50: "The two proper quotient maps induce a plane homeomorphism carrying one
ordered traversal to the other"), and for the space-filling SLE_{16/γ²} of the mating-of-trees theorem the set of
triple points contains no such continuum: Gwynne–Holden–Miller, arXiv:1512.01223, Corollary 6.5 (p. 40) for
`4 < κ' < 8`, Duplantier–Miller–Sheffield, arXiv:1409.7055, (8.9) and Lemmas 8.12-8.13 for `κ' ≥ 8`. -/
def CorrelatedBMPeanosphereTriplePointsNoContinuum : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
    ∀ᵐ p ∂μ, ∀ η : ℝ → ℂ, RouteM.Peanosphere p η → ¬ ContainsNondegenerateContinuum (curveTriplePoints η)

/-! ### Linear time changes of the edge counts -/

/-- The image of `[a, b]` under `t ↦ X (ε t)` is the image of `[ε a, ε b]` under `X`, for `ε > 0`. -/
theorem image_comp_mul_left_Icc {β : Type*} (X : ℝ → β) {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    (fun t => X (ε * t)) '' Icc a b = X '' Icc (ε * a) (ε * b) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ε * t, ⟨mul_le_mul_of_nonneg_left ht.1 hε.le, mul_le_mul_of_nonneg_left ht.2 hε.le⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s / ε, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hε]
      linarith [hs.1]
    · rw [div_le_iff₀ hε]
      linarith [hs.2]
    · show X (ε * (s / ε)) = X s
      rw [mul_div_cancel₀ s hε.ne']

/-- The adjacency condition at mesh `ε` is the adjacency condition at mesh `1` of the path `t ↦ X (ε t)`. -/
theorem bmAdjacent_comp_mul_left {X : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (j k : ℤ) :
    bmAdjacent 1 (fun t => X (ε * t)) j k ↔ bmAdjacent ε X j k := by
  have e1 : ∀ m : ℤ, ε * (1 * (m : ℝ) - 1) = ε * m - ε := fun m => by ring
  have e2 : ∀ m : ℤ, ε * (1 * (m : ℝ)) = ε * m := fun m => by ring
  simp only [bmAdjacent, image_comp_mul_left_Icc X hε, e1, e2]

/-- **The edge counts are invariant under linear time changes**: the edge counts at mesh `ε` of `(L, R)` are the
edge counts at mesh `1` of `t ↦ (L (ε t), R (ε t))`. -/
theorem bmEdgeCount_comp_mul_left {L R : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (j k : ℤ) :
    bmEdgeCount 1 (fun t => L (ε * t)) (fun t => R (ε * t)) j k = bmEdgeCount ε L R j k := by
  have hL : bmAdjacent 1 (fun t => L (ε * t)) = bmAdjacent ε L :=
    funext fun a => funext fun b => propext (bmAdjacent_comp_mul_left hε a b)
  have hR : bmAdjacent 1 (fun t => R (ε * t)) = bmAdjacent ε R :=
    funext fun a => funext fun b => propext (bmAdjacent_comp_mul_left hε a b)
  unfold bmEdgeCount
  rw [hL, hR]

/-! ### Dilation invariance of the frontier-side multiplicity -/

/-- A contact of two times persists after a nonzero real dilation of the plane. -/
theorem cellSideContact_smul {a d : ℝ} {η : ℝ → ℂ} {c : ℝ} (hc : c ≠ 0) {v w : ℝ}
    (h : cellSideContact a d η v w) : cellSideContact a d (fun t => (c : ℂ) * η t) v w := by
  intro p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  obtain ⟨K, hK, hKc, hKconn, hKd⟩ := h p₁ p₂ q₁ q₂ hv hw hdisj hP hQ
  have hcont : Continuous fun z : ℂ => (c : ℂ) * z := continuous_const.mul continuous_id
  refine ⟨(fun z : ℂ => (c : ℂ) * z) '' K, ?_, hKc.image hcont, hKconn.image _ hcont.continuousOn, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩ := hK hz
    exact ⟨⟨s, hs, by simp only [hsz]⟩, ⟨t, ht, by simp only [htz]⟩⟩
  · have hsub : ¬ K.Subsingleton := fun hs => by
      rw [Metric.diam_subsingleton hs] at hKd
      exact lt_irrefl _ hKd
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hsub
    have hb : Bornology.IsBounded ((fun z : ℂ => (c : ℂ) * z) '' K) := (hKc.image hcont).isBounded
    have hne : (c : ℂ) * x ≠ (c : ℂ) * y := fun h =>
      hxy (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hc) h)
    exact (dist_pos.2 hne).trans_le (Metric.dist_le_diam_of_mem hb ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

/-- Contacts are invariant under nonzero real dilations of the plane. -/
theorem cellSideContact_smul_iff {a d : ℝ} {η : ℝ → ℂ} {c : ℝ} (hc : c ≠ 0) {v w : ℝ} :
    cellSideContact a d (fun t => (c : ℂ) * η t) v w ↔ cellSideContact a d η v w := by
  refine ⟨fun h => ?_, cellSideContact_smul hc⟩
  have h' := cellSideContact_smul (η := fun t => (c : ℂ) * η t) (inv_ne_zero hc) h
  convert h' using 1
  funext t
  simp only [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_mul]

/-- **The frontier-side multiplicity is invariant under nonzero real dilations of the plane.** -/
theorem cellSideMult_smul {c : ℝ} (hc : c ≠ 0) (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) :
    cellSideMult ε (fun t => (c : ℂ) * η t) j k = cellSideMult ε η j k := by
  have hB : ∀ a b c' d : ℝ, cellSideBranchTimes a b c' d (fun t => (c : ℂ) * η t) =
      cellSideBranchTimes a b c' d η := fun a b c' d => by
    simp only [cellSideBranchTimes, cellSideContact_smul_iff hc]
  have hC : ∀ a b c' d : ℝ, cellSideCount a b c' d (fun t => (c : ℂ) * η t) = cellSideCount a b c' d η :=
    fun a b c' d => by
      unfold cellSideCount
      rw [hB]
  unfold cellSideMult
  rw [hC]

/-! ### Descent of the contour functions at a time visited once -/

/-- If a continuous recurrent path with distinct values at distinct local minima stays at or above its value at `u`
just after `u`, its first return to that value is a direct identification with `u`. -/
theorem exists_directRel_right {X : ℝ → ℝ} (hX : Continuous X) {u : ℝ}
    (hrec : ∀ T : ℝ, ∃ t ≥ T, X t < X u)
    (hdist : ∀ a b, a ≠ b → IsLocalMin X a → IsLocalMin X b → X a ≠ X b)
    {δ : ℝ} (hδ : 0 < δ) (hge : ∀ t, u < t → t < u + δ → X u ≤ X t) :
    ∃ t, RouteM.directRel X u t := by
  -- the path is strictly above its value on a right neighbourhood of `u`
  obtain ⟨δ', hδ', hstrict⟩ : ∃ δ' > 0, ∀ t, u < t → t < u + δ' → X u < X t := by
    by_cases hex : ∃ t₀, u < t₀ ∧ t₀ < u + δ ∧ X t₀ = X u
    · obtain ⟨t₀, h1, h2, h3⟩ := hex
      have hloc : ∀ t, u < t → t < u + δ → X t = X u → IsLocalMin X t := fun t ht1 ht2 ht3 =>
        Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht2) fun y hy => by
          rw [ht3]
          exact hge y hy.1 hy.2
      refine ⟨t₀ - u, by linarith, fun t ht1 ht2 => ?_⟩
      refine lt_of_le_of_ne (hge t ht1 (by linarith)) fun heq => ?_
      have htt₀ : t ≠ t₀ := by
        intro h
        linarith
      exact hdist t t₀ htt₀ (hloc t ht1 (by linarith) heq.symm) (hloc t₀ h1 h2 h3) (heq.symm.trans h3.symm)
    · exact ⟨δ, hδ, fun t ht1 ht2 => lt_of_le_of_ne (hge t ht1 ht2) fun heq => hex ⟨t, ht1, ht2, heq.symm⟩⟩
  -- the first return to the value after `u + δ'/2`
  obtain ⟨τ, hτS, hτmin⟩ : ∃ τ, (u + δ' / 2 ≤ τ ∧ X τ ≤ X u) ∧
      ∀ v, u + δ' / 2 ≤ v → X v ≤ X u → τ ≤ v := by
    obtain ⟨t₁, ht₁, hXt₁⟩ := hrec (u + δ' / 2)
    have hne : ({t | u + δ' / 2 ≤ t ∧ X t ≤ X u} : Set ℝ).Nonempty := ⟨t₁, ht₁, hXt₁.le⟩
    have hbdd : BddBelow {t | u + δ' / 2 ≤ t ∧ X t ≤ X u} := ⟨u + δ' / 2, fun t ht => ht.1⟩
    have hcl : IsClosed {t | u + δ' / 2 ≤ t ∧ X t ≤ X u} :=
      isClosed_Ici.inter (isClosed_le hX continuous_const)
    exact ⟨_, hcl.csInf_mem hne hbdd, fun v h1 h2 => csInf_le hbdd ⟨h1, h2⟩⟩
  have hτu : u < τ := by linarith [hτS.1]
  have hbelow : ∀ v ∈ Ioo u τ, X u < X v := by
    intro v hv
    by_cases hv' : v < u + δ'
    · exact hstrict v hv.1 hv'
    · refine not_le.1 fun hle => ?_
      have h1 := not_lt.1 hv'
      have := hτmin v (by linarith) hle
      linarith [hv.2]
  have hτge : X u ≤ X τ := by
    have hsub : Ioo u τ ⊆ {v | X u ≤ X v} := fun v hv => (hbelow v hv).le
    have hclo := (isClosed_le continuous_const hX).closure_subset_iff.2 hsub
    rw [closure_Ioo hτu.ne] at hclo
    exact hclo (right_mem_Icc.2 hτu.le)
  exact ⟨τ, hτu, le_antisymm hτge hτS.2, hbelow⟩

/-- The left-hand version of `exists_directRel_right`, by time reversal. -/
theorem exists_directRel_left {X : ℝ → ℝ} (hX : Continuous X) {u : ℝ}
    (hrec : ∀ T : ℝ, ∃ t ≤ T, X t < X u)
    (hdist : ∀ a b, a ≠ b → IsLocalMin X a → IsLocalMin X b → X a ≠ X b)
    {δ : ℝ} (hδ : 0 < δ) (hge : ∀ t, u - δ < t → t < u → X u ≤ X t) :
    ∃ t, RouteM.directRel X t u := by
  have hneg : ∀ a, IsLocalMin (fun t => X (-t)) a → IsLocalMin X (-a) := fun a ha => by
    have ha' : IsLocalMin (fun t => X (-t)) (-(-a)) := by rwa [neg_neg]
    have h := ha'.comp_continuous (continuous_neg.continuousAt (x := -a))
    simpa only [Function.comp_def, neg_neg] using h
  have hrec' : ∀ T : ℝ, ∃ t ≥ T, X (-t) < X (-(-u)) := fun T => by
    obtain ⟨t, ht, hlt⟩ := hrec (-T)
    exact ⟨-t, by linarith, by simpa only [neg_neg] using hlt⟩
  have hdist' : ∀ a b, a ≠ b → IsLocalMin (fun t => X (-t)) a → IsLocalMin (fun t => X (-t)) b →
      X (-a) ≠ X (-b) := fun a b hab ha hb =>
    hdist (-a) (-b) (fun h => hab (neg_injective h)) (hneg a ha) (hneg b hb)
  have hge' : ∀ t, -u < t → t < -u + δ → X (-(-u)) ≤ X (-t) := fun t h1 h2 => by
    simpa only [neg_neg] using hge (-t) (by linarith) (by linarith)
  obtain ⟨t, ht, heq, hlt⟩ :=
    exists_directRel_right (X := fun t => X (-t)) (hX.comp continuous_neg) hrec' hdist' hδ hge'
  have heq' : X (-t) = X u := by simpa only [neg_neg] using heq.symm
  refine ⟨-t, by linarith, heq', fun v hv => ?_⟩
  have h1 := hlt (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
  rw [heq']
  simpa only [neg_neg] using h1

/-- **At a time visited once by a Peanosphere curve, both contour functions descend on both sides** (written answer
`notes/fp-gaps/CODEX-MQ-sbl-27.md`, line 48). -/
theorem isTwoSidedDescent_of_forall_eq {p : Path2} {η : ℝ → ℂ} (P : RouteM.Peanosphere p η) {u : ℝ}
    (hu : ∀ t, η t = η u → t = u) :
    IsTwoSidedDescent (RouteM.lCoord p) u ∧ IsTwoSidedDescent (RouteM.rCoord p) u := by
  have key : ∀ X : ℝ → ℝ, Continuous X →
      (∀ a b, a ≠ b → IsLocalMin X a → IsLocalMin X b → X a ≠ X b) →
      (∀ T : ℝ, ∃ t ≥ T, X t < X u) → (∀ T : ℝ, ∃ t ≤ T, X t < X u) →
      (∀ s t, RouteM.directRel X s t → η s = η t) → IsTwoSidedDescent X u := by
    intro X hX hdist hR hL hmerge
    constructor
    · intro δ hδ
      by_contra hcon
      have hge : ∀ t, u < t → t < u + δ → X u ≤ X t := fun t h1 h2 =>
        not_lt.1 fun hlt => hcon ⟨t, h1, h2, hlt⟩
      obtain ⟨t, ht⟩ := exists_directRel_right hX hR hdist hδ hge
      exact absurd (hu t (hmerge u t ht).symm) ht.1.ne'
    · intro δ hδ
      by_contra hcon
      have hge : ∀ t, u - δ < t → t < u → X u ≤ X t := fun t h1 h2 =>
        not_lt.1 fun hlt => hcon ⟨t, h1, h2, hlt⟩
      obtain ⟨t, ht⟩ := exists_directRel_left hX hL hdist hδ hge
      exact absurd (hu t (hmerge t u ht)) ht.1.ne
  refine ⟨key _ (levelContactData_lCoord P).continuous (levelContactData_lCoord P).locMin_ne
      (fun T => ?_) (fun T => ?_) (fun s t h => P.merge s t (Or.inl h)),
    key _ (levelContactData_rCoord P).continuous (levelContactData_rCoord P).locMin_ne
      (fun T => ?_) (fun T => ?_) (fun s t h => P.merge s t (Or.inr h))⟩
  · exact (P.liminf_L _ T).1
  · obtain ⟨t, ht, hlt⟩ := (P.liminf_L (RouteM.lCoord p u) (-T)).2
    exact ⟨t, by simpa only [neg_neg] using ht, hlt⟩
  · exact (P.liminf_R _ T).1
  · obtain ⟨t, ht, hlt⟩ := (P.liminf_R (RouteM.rCoord p u) (-T)).2
    exact ⟨t, by simpa only [neg_neg] using ht, hlt⟩

/-- Two-sided descent is transported by an increasing time change. -/
theorem isTwoSidedDescent_comp_orderIso {X : ℝ → ℝ} (e : ℝ ≃o ℝ) {x : ℝ}
    (h : IsTwoSidedDescent X (e x)) : IsTwoSidedDescent (fun t => X (e t)) x := by
  constructor
  · intro δ hδ
    have hlt : e x < e (x + δ) := e.strictMono (by linarith)
    obtain ⟨t', h1, h2, h3⟩ := h.1 (e (x + δ) - e x) (by linarith)
    refine ⟨e.symm t', ?_, ?_, ?_⟩
    · rw [← e.lt_iff_lt, e.apply_symm_apply]
      exact h1
    · rw [← e.lt_iff_lt, e.apply_symm_apply]
      linarith
    · show X (e (e.symm t')) < X (e x)
      rw [e.apply_symm_apply]
      exact h3
  · intro δ hδ
    have hlt : e (x - δ) < e x := e.strictMono (by linarith)
    obtain ⟨t', h1, h2, h3⟩ := h.2 (e x - e (x - δ)) (by linarith)
    refine ⟨e.symm t', ?_, ?_, ?_⟩
    · rw [← e.lt_iff_lt, e.apply_symm_apply]
      linarith
    · rw [← e.lt_iff_lt, e.apply_symm_apply]
      exact h2
    · show X (e (e.symm t')) < X (e x)
      rw [e.apply_symm_apply]
      exact h3

/-! ### Almost every time is visited once by an area-parametrized curve -/

/-- **The images of two non-overlapping intervals meet in a null set** of any measure parametrizing the curve by
area. -/
theorem measure_image_Icc_inter_image_Icc_eq_zero {q : ℝ → ℂ} (hq : Continuous q) {μ : Measure ℂ}
    (harea : ∀ s t : ℝ, s ≤ t → μ (q '' Icc s t) = ENNReal.ofReal (t - s))
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    μ (q '' Icc a b ∩ q '' Icc c d) = 0 := by
  have hmeas : MeasurableSet (q '' Icc c d) := (isCompact_Icc.image hq).isClosed.measurableSet
  have hsub : q '' Icc a d ⊆ (q '' Icc a b ∪ q '' Icc c d) ∪ q '' Icc b c := by
    rintro _ ⟨t, ht, rfl⟩
    rcases le_total t b with h | h
    · exact Or.inl (Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩)
    rcases le_total t c with h' | h'
    · exact Or.inr ⟨t, ⟨h, h'⟩, rfl⟩
    · exact Or.inl (Or.inr ⟨t, ⟨h', ht.2⟩, rfl⟩)
  have h1 : ENNReal.ofReal (d - a) ≤ μ (q '' Icc a b ∪ q '' Icc c d) + μ (q '' Icc b c) := by
    rw [← harea a d (hab.trans (hbc.trans hcd))]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have h2 := measure_union_add_inter (μ := μ) (q '' Icc a b) hmeas
  rw [harea a b hab, harea c d hcd] at h2
  have h3 : ENNReal.ofReal (d - a) + μ (q '' Icc a b ∩ q '' Icc c d) ≤ ENNReal.ofReal (d - a) + 0 := by
    calc ENNReal.ofReal (d - a) + μ (q '' Icc a b ∩ q '' Icc c d)
        ≤ μ (q '' Icc a b ∪ q '' Icc c d) + μ (q '' Icc b c) + μ (q '' Icc a b ∩ q '' Icc c d) := by
          gcongr
      _ = μ (q '' Icc a b ∪ q '' Icc c d) + μ (q '' Icc a b ∩ q '' Icc c d) + μ (q '' Icc b c) :=
          add_right_comm _ _ _
      _ = ENNReal.ofReal (b - a) + ENNReal.ofReal (d - c) + ENNReal.ofReal (c - b) := by
          rw [h2, harea b c hbc]
      _ = ENNReal.ofReal (d - a) + 0 := by
          rw [add_zero, ← ENNReal.ofReal_add (sub_nonneg.2 hab) (sub_nonneg.2 hcd),
            ← ENNReal.ofReal_add (add_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hcd)) (sub_nonneg.2 hbc)]
          congr 1
          ring
  exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 h3)

/-- **The times of a compact interval sent into a null compact set form a Lebesgue-null set**, for a curve
parametrized by area: cut the interval into pieces of length `l`, small for the modulus of continuity; the pieces
meeting the set have total length the area of their images, which lie in the `r`-thickening of the compact set. -/
theorem volume_Icc_inter_preimage_eq_zero {q : ℝ → ℂ} (hq : Continuous q) {μ : Measure ℂ}
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ⊤)
    (harea : ∀ s t : ℝ, s ≤ t → μ (q '' Icc s t) = ENNReal.ofReal (t - s))
    (a b : ℝ) {K : Set ℂ} (hK : IsCompact K) (hK0 : μ K = 0) :
    volume (Icc a b ∩ q ⁻¹' K) = 0 := by
  classical
  have : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  have hle : ∀ r : ℝ, 0 < r → volume (Icc a b ∩ q ⁻¹' K) ≤ μ (cthickening r K) := by
    intro r hr
    obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := a) (b := b + 1)).uniformContinuousOn_of_continuous hq.continuousOn) r hr
    obtain ⟨l, hl, hlδ, hl1⟩ : ∃ l : ℝ, 0 < l ∧ l < δ ∧ l ≤ 1 :=
      ⟨min (δ / 2) 1, lt_min (half_pos hδ) one_pos, (min_le_left _ _).trans_lt (half_lt_self hδ),
        min_le_right _ _⟩
    have hpiece : ∀ m : ℤ, a + m * l ≤ a + (m + 1) * l := fun m => by linarith
    have hMl : (⌊(b - a) / l⌋ : ℝ) * l ≤ b - a := (le_div_iff₀ hl).1 (Int.floor_le _)
    let S : Finset ℤ := (Finset.Icc 0 ⌊(b - a) / l⌋).filter
      fun m => (Icc (a + m * l) (a + (m + 1) * l) ∩ (Icc a b ∩ q ⁻¹' K)).Nonempty
    have hcover : Icc a b ∩ q ⁻¹' K ⊆ ⋃ m ∈ S, Icc (a + m * l) (a + (m + 1) * l) := by
      intro s hs
      have h1 : (⌊(s - a) / l⌋ : ℝ) * l ≤ s - a := (le_div_iff₀ hl).1 (Int.floor_le _)
      have h2 : s - a < ((⌊(s - a) / l⌋ : ℝ) + 1) * l := (div_lt_iff₀ hl).1 (Int.lt_floor_add_one _)
      have hm0 : 0 ≤ ⌊(s - a) / l⌋ := Int.floor_nonneg.2 (div_nonneg (sub_nonneg.2 hs.1.1) hl.le)
      have hmM : ⌊(s - a) / l⌋ ≤ ⌊(b - a) / l⌋ :=
        Int.le_floor.2 ((le_div_iff₀ hl).2 (by linarith [hs.1.2]))
      have hsI : s ∈ Icc (a + (⌊(s - a) / l⌋ : ℝ) * l) (a + ((⌊(s - a) / l⌋ : ℝ) + 1) * l) :=
        ⟨by linarith, by linarith⟩
      exact mem_iUnion₂.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm0, hmM⟩, s, hsI, hs⟩, hsI⟩
    have hinto : ⋃ m ∈ S, q '' Icc (a + m * l) (a + (m + 1) * l) ⊆ cthickening r K := by
      intro z hz
      obtain ⟨m, hmS, t, ht, rfl⟩ := mem_iUnion₂.1 hz
      obtain ⟨hmIcc, s, hsI, hs⟩ := Finset.mem_filter.1 hmS
      obtain ⟨hm0, hmM⟩ := Finset.mem_Icc.1 hmIcc
      have hm0' : (0 : ℝ) ≤ m := Int.cast_nonneg hm0
      have hmM' : (m : ℝ) * l ≤ (⌊(b - a) / l⌋ : ℝ) * l :=
        mul_le_mul_of_nonneg_right (Int.cast_le.2 hmM) hl.le
      have hml : 0 ≤ (m : ℝ) * l := mul_nonneg hm0' hl.le
      have htD : t ∈ Icc a (b + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hsD : s ∈ Icc a (b + 1) := ⟨hs.1.1, by linarith [hs.1.2]⟩
      have hdist : dist t s < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2, hsI.1, hsI.2]
      exact mem_cthickening_of_dist_le (q t) (q s) r K hs.2 (hunif t htD s hsD hdist).le
    have hpair : Set.Pairwise (↑S)
        (Function.onFun (AEDisjoint μ) fun m : ℤ => q '' Icc (a + m * l) (a + (m + 1) * l)) := by
      intro m₁ _ m₂ _ hne
      show μ (q '' Icc (a + m₁ * l) (a + (m₁ + 1) * l) ∩ q '' Icc (a + m₂ * l) (a + (m₂ + 1) * l)) = 0
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hc : ((m₁ : ℝ) + 1) * l ≤ m₂ * l :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Int.add_one_le_iff.2 hlt) hl.le
        exact measure_image_Icc_inter_image_Icc_eq_zero hq harea (hpiece m₁) (by linarith) (hpiece m₂)
      · have hc : ((m₂ : ℝ) + 1) * l ≤ m₁ * l :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Int.add_one_le_iff.2 hlt) hl.le
        rw [inter_comm]
        exact measure_image_Icc_inter_image_Icc_eq_zero hq harea (hpiece m₂) (by linarith) (hpiece m₁)
    have hnm : ∀ m ∈ S, NullMeasurableSet
        ((fun m : ℤ => q '' Icc (a + m * l) (a + (m + 1) * l)) m) μ := fun m _ =>
      (isCompact_Icc.image hq).isClosed.measurableSet.nullMeasurableSet
    calc volume (Icc a b ∩ q ⁻¹' K) ≤ volume (⋃ m ∈ S, Icc (a + m * l) (a + (m + 1) * l)) :=
          measure_mono hcover
      _ ≤ ∑ m ∈ S, volume (Icc (a + m * l) (a + (m + 1) * l)) := measure_biUnion_finset_le _ _
      _ = ∑ m ∈ S, μ (q '' Icc (a + m * l) (a + (m + 1) * l)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Real.volume_Icc, harea _ _ (hpiece m)]
      _ = μ (⋃ m ∈ S, q '' Icc (a + m * l) (a + (m + 1) * l)) := by
          rw [measure_biUnion_finset₀ hpair hnm]
      _ ≤ μ (cthickening r K) := measure_mono hinto
  have hlim : Tendsto (fun r => μ (cthickening r K)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_cthickening_of_isCompact (μ := μ) hK
    rw [hK0] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun r hr => hle r hr))

/-- **Witnesses of multiple visits**: the times of `[a, b]` whose image is visited during `[c, d]`, or of `[c, d]`
whose image is visited during `[a, b]`, for rational `a ≤ b ≤ c ≤ d`. Every time visited twice lies in this set. -/
def multipleVisitWitness (q : ℝ → ℂ) : Set ℝ :=
  ⋃ (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) (_ : (a : ℝ) ≤ b ∧ (b : ℝ) ≤ c ∧ (c : ℝ) ≤ d),
    (Icc (a : ℝ) b ∩ q ⁻¹' (q '' Icc (c : ℝ) d)) ∪ (Icc (c : ℝ) d ∩ q ⁻¹' (q '' Icc (a : ℝ) b))

/-- A time outside `multipleVisitWitness q` is visited once by `q`. -/
theorem eq_of_notMem_multipleVisitWitness {q : ℝ → ℂ} {s : ℝ} (hs : s ∉ multipleVisitWitness q) {t : ℝ}
    (ht : q t = q s) : t = s := by
  by_contra hne
  apply hs
  simp only [multipleVisitWitness, mem_iUnion]
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨b, htb, hbs⟩ := exists_rat_btwn h
    obtain ⟨c, hbc, hcs⟩ := exists_rat_btwn hbs
    obtain ⟨a, hat⟩ := exists_rat_lt t
    obtain ⟨d, hsd⟩ := exists_rat_gt s
    exact ⟨a, b, c, d, ⟨hat.le.trans htb.le, hbc.le, hcs.le.trans hsd.le⟩,
      Or.inr ⟨⟨hcs.le, hsd.le⟩, t, ⟨hat.le, htb.le⟩, ht⟩⟩
  · obtain ⟨b, hsb, hbt⟩ := exists_rat_btwn h
    obtain ⟨c, hbc, hct⟩ := exists_rat_btwn hbt
    obtain ⟨a, has⟩ := exists_rat_lt s
    obtain ⟨d, htd⟩ := exists_rat_gt t
    exact ⟨a, b, c, d, ⟨has.le.trans hsb.le, hbc.le, hct.le.trans htd.le⟩,
      Or.inl ⟨⟨has.le, hsb.le⟩, t, ⟨hct.le, htd.le⟩, ht⟩⟩

/-- **Almost every time is visited once** by a curve parametrized by the area of a measure finite on compact sets. -/
theorem volume_multipleVisitWitness_eq_zero {q : ℝ → ℂ} (hq : Continuous q) {μ : Measure ℂ}
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ⊤)
    (harea : ∀ s t : ℝ, s ≤ t → μ (q '' Icc s t) = ENNReal.ofReal (t - s)) :
    volume (multipleVisitWitness q) = 0 := by
  refine measure_iUnion_null fun a => measure_iUnion_null fun b => measure_iUnion_null fun c =>
    measure_iUnion_null fun d => measure_iUnion_null fun h => measure_union_null ?_ ?_
  · refine measure_mono_null ?_ (volume_Icc_inter_preimage_eq_zero hq hfin harea (a : ℝ) b
      (((isCompact_Icc (a := (a : ℝ)) (b := b)).image hq).inter_right
        ((isCompact_Icc (a := (c : ℝ)) (b := d)).image hq).isClosed)
      (measure_image_Icc_inter_image_Icc_eq_zero hq harea h.1 h.2.1 h.2.2))
    exact fun s hs => ⟨hs.1, ⟨s, hs.1, rfl⟩, hs.2⟩
  · refine measure_mono_null ?_ (volume_Icc_inter_preimage_eq_zero hq hfin harea (c : ℝ) d
      (((isCompact_Icc (a := (c : ℝ)) (b := d)).image hq).inter_right
        ((isCompact_Icc (a := (a : ℝ)) (b := b)).image hq).isClosed)
      (by
        rw [inter_comm]
        exact measure_image_Icc_inter_image_Icc_eq_zero hq harea h.1 h.2.1 h.2.2))
    exact fun s hs => ⟨hs.1, ⟨s, hs.1, rfl⟩, hs.2⟩

/-- The condition "`x.2 ∈ [a, b]` and its image is visited during `[c, d]`" is closed jointly in the curve and the
time. -/
theorem isClosed_setOf_mem_Icc_inter_preimage_image (a b c d : ℝ) :
    IsClosed {x : C(ℝ, ℂ) × ℝ | x.2 ∈ Icc a b ∩ ⇑x.1 ⁻¹' (⇑x.1 '' Icc c d)} := by
  have : CompactSpace (Icc c d) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hcl : IsClosed {r : (C(ℝ, ℂ) × ℝ) × Icc c d | r.1.1 (r.2 : ℝ) = r.1.1 r.1.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hJ : IsClosed {x : C(ℝ, ℂ) × ℝ | x.1 x.2 ∈ ⇑x.1 '' Icc c d} := by
    convert isClosedMap_fst_of_compactSpace _ hcl using 1
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨(x, ⟨t, ht⟩), hx, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.2, r.2.2, hr⟩
  exact (isClosed_Icc.preimage continuous_snd).inter hJ

/-- The multiple-visit witnesses form a Borel set jointly in the curve and the time. -/
theorem measurableSet_multipleVisitWitness :
    MeasurableSet {x : C(ℝ, ℂ) × ℝ | x.2 ∈ multipleVisitWitness ⇑x.1} := by
  have h : {x : C(ℝ, ℂ) × ℝ | x.2 ∈ multipleVisitWitness ⇑x.1} =
      ⋃ (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) (_ : (a : ℝ) ≤ b ∧ (b : ℝ) ≤ c ∧ (c : ℝ) ≤ d),
        ({x : C(ℝ, ℂ) × ℝ | x.2 ∈ Icc (a : ℝ) b ∩ ⇑x.1 ⁻¹' (⇑x.1 '' Icc (c : ℝ) d)} ∪
          {x : C(ℝ, ℂ) × ℝ | x.2 ∈ Icc (c : ℝ) d ∩ ⇑x.1 ⁻¹' (⇑x.1 '' Icc (a : ℝ) b)}) := by
    ext x
    simp only [multipleVisitWitness, mem_ofPred_eq, mem_iUnion, mem_union]
  rw [h]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun c =>
    MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun _ =>
      (isClosed_setOf_mem_Icc_inter_preimage_image _ _ _ _).measurableSet.union
        (isClosed_setOf_mem_Icc_inter_preimage_image _ _ _ _).measurableSet

/-! ### The decoder -/

section EdgeCountCode

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **`ZeroConeEdgeCountCode`** (written answer `notes/fp-gaps/CODEX-MQ-sbl-27.md`, section "(c)", lines 44-52;
Gwynne–Miller–Sheffield, arXiv:1705.11161, (1.2) and the proof of Proposition 2.2): the decoder
`Ψ q = cellSideMult 1 q` on `S = univ` is Borel and invariant under positive dilations, and for every boundary-pair
version `G` and every `n ≥ 1`, for almost every `(ω, θ)`, the edge counts at mesh `1/n` of `t ↦ G(ω)(t + θ/n)` are
`Ψ` of the curve `t ↦ η₀(ω)((t + θ)/n)`. Named inputs: `CorrelatedBMNoCommonLocalMin` and
`CorrelatedBMPeanosphereTriplePointsNoContinuum`. -/
theorem zeroConeEdgeCountCode (hcone : CorrelatedBMNoCommonLocalMin)
    (htriple : CorrelatedBMPeanosphereTriplePointsNoContinuum)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : ZeroConeEdgeCountCode D hγ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  refine ⟨fun q j k => cellSideMult 1 ⇑q j k, univ,
    Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_cellSideMult 1 j k,
    fun q _ c hc => ⟨mem_univ _, ?_⟩, ?_⟩
  · funext j k
    have hcoe : ⇑(c • q) = fun t => (c : ℂ) * q t := by
      funext t
      rw [ContinuousMap.smul_apply, Complex.real_smul]
    show cellSideMult 1 ⇑(c • q) j k = cellSideMult 1 ⇑q j k
    rw [hcoe]
    exact cellSideMult_smul hc.ne' 1 q j k
  intro G hG n hn
  obtain ⟨-, hGae⟩ := hG
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hbm : AEMeasurable bm P := D.measurable_curves.2.2.2.aemeasurable
  have hη₀m : Measurable η₀ := D.measurable_curves.2.2.1
  -- the fibres of the curve are finite
  have hfinAE : ∀ᵐ ω ∂P, ∀ z, (⇑(η ω) ⁻¹' {z}).Finite := by
    obtain ⟨kv, hkv⟩ := D.visitBound
    filter_upwards [hkv, D.areaParam] with ω hk harea
    obtain ⟨⟨φ, -, hφ⟩, -⟩ := harea
    intro z
    have hset : ⇑(η ω) ⁻¹' {z} = φ ⁻¹' (ηL ω ⁻¹' {z}) := by
      ext t
      show η ω t = z ↔ ηL ω (φ t) = z
      rw [hφ]
    rw [hset]
    exact (Set.encard_lt_top_iff.1 ((hk z).trans_lt (ENat.natCast_lt_top kv))).preimage φ.injective.injOn
  -- almost every time is visited once by the zero-cone curve
  have hMV : ∀ᵐ ω ∂P, volume (multipleVisitWitness ⇑(η₀ ω)) = 0 := by
    filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ, D.areaParam₀]
      with ω hv hpar
    obtain ⟨μ, hμ⟩ := hv
    exact volume_multipleVisitWitness_eq_zero (η₀ ω).continuous hμ.1 (hpar.2 μ hμ)
  -- the phases for which a cell endpoint is visited twice form a null set
  set E : Set (Ω × ℝ) :=
    {p | ∃ k : ℤ, (n : ℝ)⁻¹ * ((k : ℝ) + p.2) ∈ multipleVisitWitness ⇑(η₀ p.1)} with hE
  have hEm : MeasurableSet E := by
    rw [hE, ofPred_exists]
    exact MeasurableSet.iUnion fun k => measurableSet_multipleVisitWitness.preimage
      (f := fun p : Ω × ℝ => (η₀ p.1, (n : ℝ)⁻¹ * ((k : ℝ) + p.2))) (by fun_prop)
  have hE0 : (P.prod zeroConePhase) E = 0 := by
    rw [Measure.measure_prod_null hEm]
    filter_upwards [hMV] with ω hω
    have hsub : Prod.mk ω ⁻¹' E ⊆ ⋃ k : ℤ, (fun θ : ℝ => (k : ℝ) + θ) ⁻¹'
        ((fun x : ℝ => (n : ℝ)⁻¹ * x) ⁻¹' multipleVisitWitness ⇑(η₀ ω)) := by
      rintro θ ⟨k, hk⟩
      exact mem_iUnion.2 ⟨k, hk⟩
    have hnull : volume (⋃ k : ℤ, (fun θ : ℝ => (k : ℝ) + θ) ⁻¹'
        ((fun x : ℝ => (n : ℝ)⁻¹ * x) ⁻¹' multipleVisitWitness ⇑(η₀ ω))) = 0 :=
      measure_iUnion_null fun k => by
        rw [measure_preimage_add, Real.volume_preimage_mul_left (inv_ne_zero hn'.ne'), hω, mul_zero]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self (measure_mono_null hsub hnull)
  have hEc : ∀ᵐ p ∂P.prod zeroConePhase, p ∉ E :=
    ae_iff.2 (by simpa only [not_not, ofPred_mem_eq] using hE0)
  have hlift : ∀ {Q : Ω → Prop}, (∀ᵐ ω ∂P, Q ω) → ∀ᵐ p ∂P.prod zeroConePhase, Q p.1 :=
    fun h => Measure.quasiMeasurePreserving_fst.ae h
  filter_upwards [hlift (ae_peanosphere_of_isMatingOfTreesCoupling D),
    hlift (LatticeProb.ae_coupled_area_clock D hγ), hlift hGae, hlift hfinAE,
    hlift (ae_of_ae_map hbm (htriple γ hγ.1 hγ.2 _ D.boundaryLawBM)),
    hlift (ae_of_ae_map hbm (hcone γ hγ.1 hγ.2 _ D.boundaryLawBM)), hEc]
    with p hPe hclk hGω hfin htr hcn hp
  set ω := p.1
  set θ := p.2
  obtain ⟨ψ, -, hη₀ψ, hψ⟩ := hclk
  refine ⟨mem_univ _, ?_⟩
  -- the cell endpoints are visited once
  have hunique : ∀ k : ℤ, ∀ s, η₀ ω s = η₀ ω ((n : ℝ)⁻¹ * ((k : ℝ) + θ)) →
      s = (n : ℝ)⁻¹ * ((k : ℝ) + θ) :=
    fun k s hs => eq_of_notMem_multipleVisitWitness (fun hk => hp ⟨k, hk⟩) hs
  -- the time change `e t = ψ ((t + θ)/n)`
  have hmono : StrictMono fun t : ℝ => ψ ((n : ℝ)⁻¹ * (t + θ)) :=
    ψ.strictMono.comp fun a b hab => mul_lt_mul_of_pos_left (by linarith) (inv_pos.2 hn')
  have hsurj : Function.Surjective fun t : ℝ => ψ ((n : ℝ)⁻¹ * (t + θ)) := fun y =>
    ⟨(n : ℝ) * ψ.symm y - θ, by
      show ψ ((n : ℝ)⁻¹ * ((n : ℝ) * ψ.symm y - θ + θ)) = y
      rw [sub_add_cancel, inv_mul_cancel_left₀ hn'.ne', ψ.apply_symm_apply]⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ∀ t, e t = ψ ((n : ℝ)⁻¹ * (t + θ)) :=
    ⟨StrictMono.orderIsoOfSurjective _ hmono hsurj, fun t => rfl⟩
  have Pe := hPe.comp_orderIso e
  set w : Path2 := ⟨fun t => bm ω (e t), (bm ω).continuous.comp e.continuous⟩
  -- the hypotheses of the deterministic identity
  have hfin' : ∀ z, ((fun t => η ω (e t)) ⁻¹' {z}).Finite := fun z =>
    (hfin z).preimage (f := ⇑e) e.injective.injOn
  have htr' : ¬ ContainsNondegenerateContinuum (curveTriplePoints fun t => η ω (e t)) := by
    rintro ⟨K, hK, hKc⟩
    exact htr _ hPe ⟨K, hK.trans fun z ⟨t₁, t₂, t₃, h12, h23, h1, h2, h3⟩ =>
      ⟨e t₁, e t₂, e t₃, e.strictMono h12, e.strictMono h23, h1, h2, h3⟩, hKc⟩
  have hmin : ∀ (Y : ℝ → ℝ) (x : ℝ), IsLocalMin (fun t => Y (e t)) x → IsLocalMin Y (e x) := by
    intro Y x hx
    have hx₀ : IsLocalMin (Y ∘ e) (e.symm (e x)) := by
      rw [e.symm_apply_apply]
      exact hx
    have h := hx₀.comp_continuous (e.symm.continuous.continuousAt (x := e x))
    simpa only [Function.comp_def, e.apply_symm_apply] using h
  have hcone' : ∀ u, ¬ (IsLocalMin (RouteM.lCoord w) u ∧ IsLocalMin (RouteM.rCoord w) u) := fun u hu =>
    hcn (e u) ⟨hmin (fun s => lrCoord 0 s (bm ω)) u hu.1, hmin (fun s => lrCoord 1 s (bm ω)) u hu.2⟩
  have hdesc' : ∀ k : ℤ, IsTwoSidedDescent (RouteM.lCoord w) ((1 : ℝ) * k) ∧
      IsTwoSidedDescent (RouteM.rCoord w) ((1 : ℝ) * k) := by
    intro k
    rw [one_mul]
    have hu : ∀ t, η ω t = η ω (e k) → t = e k := by
      intro t ht
      have h1 := hunique k (ψ.symm t) (by rw [hη₀ψ, hη₀ψ, ψ.apply_symm_apply, ht, he])
      rw [he, ← h1, ψ.apply_symm_apply]
    obtain ⟨hl, hr⟩ := isTwoSidedDescent_of_forall_eq hPe hu
    exact ⟨isTwoSidedDescent_comp_orderIso e hl, isTwoSidedDescent_comp_orderIso e hr⟩
  have hcurve : ⇑(phaseShiftedCurve 1 θ (curveMeshRescale n (η₀ ω))) = fun t => η ω (e t) := by
    funext t
    show η₀ ω ((t + 1 * θ) / n) = η ω (e t)
    rw [hη₀ψ, he]
    exact congrArg (fun x => η ω (ψ x)) (by ring)
  have hG' : ∀ t, G ω (1 / (n : ℝ) * t + 1 / (n : ℝ) * θ) = bm ω (e t) := fun t => by
    rw [hGω, hψ, he]
    exact congrArg (fun x => bm ω (ψ x)) (by ring)
  funext j k
  calc phaseShiftedEdgeCount (1 / (n : ℝ)) θ (G ω) j k
      = bmEdgeCount 1 (fun t => (G ω (1 / (n : ℝ) * t + 1 / (n : ℝ) * θ)).1)
          (fun t => (G ω (1 / (n : ℝ) * t + 1 / (n : ℝ) * θ)).2) j k :=
        (bmEdgeCount_comp_mul_left (L := fun t => (G ω (t + 1 / (n : ℝ) * θ)).1)
          (R := fun t => (G ω (t + 1 / (n : ℝ) * θ)).2) (one_div_pos.2 hn') j k).symm
    _ = bmEdgeCount 1 (RouteM.lCoord w) (RouteM.rCoord w) j k := by
        congr 1
        · funext t
          exact congrArg Prod.fst (hG' t)
        · funext t
          exact congrArg Prod.snd (hG' t)
    _ = cellSideMult 1 (fun t => η ω (e t)) j k :=
        bmEdgeCount_eq_cellSideMult Pe hfin' htr' hcone' one_pos hdesc' j k
    _ = cellSideMult 1 ⇑(phaseShiftedCurve 1 θ (curveMeshRescale n (η₀ ω))) j k := by
        rw [hcurve]

end EdgeCountCode

end MatedCRT.GMS310Transfer
