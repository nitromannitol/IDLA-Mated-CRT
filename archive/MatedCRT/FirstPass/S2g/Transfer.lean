import MatedCRT.FirstPass.S2g.PlateauZero

/-!
# The plateau at radius `1/2` from a certificate

Deterministic part of A certificate `CertSuper ν t w` on `B_{3/4}` identifies the
HB cluster `Λ_{B_{3/4};0}(t)` with its contact set `certCluster (3/4) t w` (leastness and the membership of
`w` in `S_{B_{3/4};0}(t)`). Compatibility of clusters across discs (HB Lemma 3.5, the hypothesis `hcomp`, to be
instantiated almost surely) identifies the cluster in `B_1` with it. Hence the raw radius of `B_1` at the two rational
times is `1/2`, and `1/2` is a plateau radius of `ν` (PlateauZero.lean, (37)).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Leastness at a certificate (4.1, Armitage-Gardiner comparison of supersolutions): for
`CertSuper ν t w` with `ν(B̄_{3/4}) < ∞` and `t > 0`, the least supersolution equals `w` at every point of `B̄_{3/4}`
other than the pole. The comparison `w ≤ v` for every supersolution `v` is `certificate_le_supersolution`, applied with
the open set `A = int (closure (certCluster))`, which contains the pole. -/
theorem leastSupersolution_eq_of_certSuper (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole) {ν : Measure ℂ} (hν : ν (closedBall (0 : ℂ) (3 / 4)) < ⊤) {t : ℝ} (ht : 0 < t)
    {w : ℂ → ℝ} (hc : CertSuper ν t w) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) (3 / 4)) (hx0 : x ≠ 0) :
    leastSupersolution ν (3 / 4) 0 t x = w x := by
  obtain ⟨⟨hcont, -, hbd, hclosed, -, hC4⟩, hS⟩ := hc
  have hCo : IsOpen (certCluster (3 / 4) t w) := isOpen_certCluster hpole (by norm_num) ht hcont
  have h0C : (0 : ℂ) ∈ certCluster (3 / 4) t w := ⟨mem_ball_self (by norm_num), Or.inl rfl⟩
  have hCA : certCluster (3 / 4) t w ⊆ interior (closure (certCluster (3 / 4) t w)) :=
    interior_maximal subset_closure hCo
  have hAball : interior (closure (certCluster (3 / 4) t w)) ⊆ ball (0 : ℂ) (3 / 4) :=
    interior_subset.trans (hclosed.trans (closedBall_subset_ball (by norm_num)))
  have hcov : ∀ y ∈ ball (0 : ℂ) (3 / 4), y ∉ interior (closure (certCluster (3 / 4) t w)) →
      w y ≤ -t * greenFunction (ball 0 (3 / 4)) 0 y :=
    fun y hy hyA => not_lt.mp (fun h => hyA (hCA ⟨hy, Or.inr h⟩))
  have hle : ∀ v ∈ supersolutions ν (3 / 4) 0 t, ∀ y ∈ closedBall (0 : ℂ) (3 / 4), w y ≤ v y :=
    certificate_le_supersolution hmin hν hS hbd isOpen_interior (hCA h0C) hAball hcov hC4
  have hwle : w x ≤ leastSupersolution ν (3 / 4) 0 t x :=
    le_csInf ⟨w x, w, hS, rfl⟩ (by rintro _ ⟨v, hv, rfl⟩; exact hle v hv x hx)
  exact le_antisymm (leastSupersolution_le hS hx hx0) hwle

/-- The HB cluster of the disc `B_{3/4}` is the contact set of the certificate (5.4). -/
theorem cluster_eq_certCluster_of_certSuper (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole) {ν : Measure ℂ} (hν : ν (closedBall (0 : ℂ) (3 / 4)) < ⊤) {t : ℝ} (ht : 0 < t)
    {w : ℂ → ℝ} (hc : CertSuper ν t w) :
    cluster ν (3 / 4) 0 t = certCluster (3 / 4) t w := by
  ext x
  simp only [cluster, certCluster, mem_ofPred_eq]
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨fun h => ⟨h.1, Or.inl rfl⟩, fun h => ⟨h.1, Or.inl rfl⟩⟩
  · by_cases hxb : x ∈ ball (0 : ℂ) (3 / 4)
    · rw [leastSupersolution_eq_of_certSuper hmin hpole hν ht hc (ball_subset_closedBall hxb) hx0]
    · simp [hxb]

/-- The raw radius of `B_1` at the time `t` is `1/2` when `CertSuper ν t w` and the compatibility of clusters across
discs (HB Lemma 3.5 with `R = 1`, `s₁ = s₂ = 3/4`, `z = 0`) holds at the time `t`. -/
theorem rawRadius_one_eq_half_of_certSuper (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole) {ν : Measure ℂ} (hν : ν (closedBall (0 : ℂ) (3 / 4)) < ⊤) {t : ℝ} (ht : 0 < t)
    {w : ℂ → ℝ} (hc : CertSuper ν t w)
    (hcomp : ∀ s ∈ Icc (3 / 4 : ℝ) 1, closure (cluster ν (3 / 4) 0 t) ⊆ ball 0 (3 / 4) →
      cluster ν s 0 t = cluster ν (3 / 4) 0 t) :
    rawRadius ν 1 t = 1 / 2 := by
  have hC := hc.1
  obtain ⟨-, -, -, hclosed, ⟨x, hxp, hxn⟩, -⟩ := hC
  have hcl := cluster_eq_certCluster_of_certSuper hmin hpole hν ht hc
  have hsub : closure (cluster ν (3 / 4) 0 t) ⊆ ball 0 (3 / 4) := by
    rw [hcl]
    exact hclosed.trans (closedBall_subset_ball (by norm_num))
  have h1 : cluster ν 1 0 t = certCluster (3 / 4) t w :=
    (hcomp 1 ⟨by norm_num, le_rfl⟩ hsub).trans hcl
  unfold rawRadius
  rw [Nat.cast_one, h1]
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hxp, hxn⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  simpa [mem_closedBall, dist_zero_right] using hclosed hy

/-- A rational plateau pair of certificates for `ν` gives the plateau radius `1/2` of `ν` in `B_1`
(5.4), provided the compatibility of clusters across discs holds for `ν` at every positive time
(HB Lemma 3.5 for the measure `ν`, a.s. for the LQG measure). -/
theorem half_mem_plateauRadii_of_hasRatPlateauCert (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole) {ν : Measure ℂ} (hν : ν (closedBall (0 : ℂ) (3 / 4)) < ⊤)
    (hcomp : ∀ t : ℝ, 0 < t → ∀ s ∈ Icc (3 / 4 : ℝ) 1, closure (cluster ν (3 / 4) 0 t) ⊆ ball 0 (3 / 4) →
      cluster ν s 0 t = cluster ν (3 / 4) 0 t)
    (h : HasRatPlateauCert ν) : (1 / 2 : ℝ) ∈ plateauRadii ν := by
  obtain ⟨p, q, hp, hpq, ⟨wp, hwp⟩, ⟨wq, hwq⟩⟩ := h
  have hq : (0 : ℝ) < (q : ℝ) := lt_trans hp hpq
  refine ⟨1, zero_lt_one, p, q, hp, hpq, by norm_num, ?_, ?_⟩
  · exact rawRadius_one_eq_half_of_certSuper hmin hpole hν hp hwp (hcomp _ hp)
  · exact rawRadius_one_eq_half_of_certSuper hmin hpole hν hq hwq (hcomp _ hq)

end MatedCRT
