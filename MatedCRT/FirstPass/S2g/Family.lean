import MatedCRT.FirstPass.S2g.GoodSet

/-!
# Good set, family side and the reduction to the null hull

Deterministic part of `ConeClosureGoodMeasureLawStep` (`FirstPass/S2f.lean`).
 (conditions C1-C4 of a certificate; a family
counterexample produces a certificate pair). In the real-variable form used here, a certificate needs no countable
coding; the coding and the zero cone law (Sections 1-3, 5-6) are the open probabilistic step `ConeBadNullHullStep`.

A closure failure at time `t` forces the raw radius to equal `1/2` at every time in `(t, T)` (monotonicity), so the
family gives a plateau pair of rational times `p < q` in `(t, T)`, each carrying a certificate.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The certificate `CertReal ν t w` on the disc `B_{3/4}` with pole `0` at time `t > 0` (Armitage-Gardiner notation;
 C1-C4 without countable coding). `w` is continuous on `B̄_{3/4}` (the candidate),
lies above the Green obstacle `-t G_{B_{3/4}}(0,·)` off the pole (C1), vanishes on `∂B_{3/4}` (C2), its contact set
`certCluster (3/4) t w` has closure in `B̄_{1/2}` which reaches the circle `|x| = 1/2` (C3), and `Δ w = ν` restricted to
the interior of the closure of the contact set (C4). -/
def CertReal (ν : Measure ℂ) (t : ℝ) (w : ℂ → ℝ) : Prop :=
  ContinuousOn w (closedBall (0 : ℂ) (3 / 4)) ∧
    (∀ x ∈ closedBall (0 : ℂ) (3 / 4), x ≠ 0 → -t * greenFunction (ball 0 (3 / 4)) 0 x ≤ w x) ∧
    (∀ x ∈ sphere (0 : ℂ) (3 / 4), w x = 0) ∧
    closure (certCluster (3 / 4) t w) ⊆ closedBall (0 : ℂ) (1 / 2) ∧
    (∃ x ∈ closure (certCluster (3 / 4) t w), ‖x‖ = 1 / 2) ∧
    HasLaplacian w (ν.restrict (interior (closure (certCluster (3 / 4) t w)))) 0 (ball 0 (3 / 4))

/-- A certificate which is also a supersolution on `B_{3/4}` (HB eq:super-solutions, line 583): `w ∈ S_{B_{3/4};0}(t)`.
The membership gives the Laplacian inequality `Δw ≤ ν` on all of `B_{3/4}`, which `CertReal` does not carry; it is what
makes the contact set of `w` the HB cluster (Lemma 3.1 of HB: the least supersolution lies in `S`). -/
def CertSuper (ν : Measure ℂ) (t : ℝ) (w : ℂ → ℝ) : Prop :=
  CertReal ν t w ∧ w ∈ supersolutions ν (3 / 4) 0 t

/-- The bad event of the good set: two rational times `0 < p < q` each carry a certificate for `ν` (a plateau pair of
raw radii, (37)). -/
def HasRatPlateauCert (ν : Measure ℂ) : Prop :=
  ∃ p q : ℚ, 0 < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (∃ w : ℂ → ℝ, CertSuper ν (p : ℝ) w) ∧
    ∃ w : ℂ → ℝ, CertSuper ν (q : ℝ) w

/-- The zero function is a supersolution on `B_{3/4}` for `t ≥ 0`, since the disc Green function is nonnegative
(`greenFunction_nonneg`). -/
theorem zero_mem_supersolutions_ball (μ : Measure ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (fun _ : ℂ => (0 : ℝ)) ∈ supersolutions μ (3 / 4) 0 t := by
  refine ⟨continuousOn_const, ⟨(locallyIntegrable_const (0 : ℝ)).locallyIntegrableOn _,
    fun φ _ hφ _ => ?_⟩, fun x _ _ => ?_⟩
  · simp only [zero_mul, integral_zero]
    exact integral_nonneg hφ
  · have hG : 0 ≤ greenFunction (ball 0 (3 / 4)) 0 x := greenFunction_nonneg isBounded_ball 0 x
    have := mul_nonneg ht hG
    show -t * greenFunction (ball 0 (3 / 4)) 0 x ≤ 0
    linarith

/-- The pointwise infimum argument at the pole: the least supersolution lies
above the Green obstacle at every point of `B̄_{3/4}` off the pole. -/
theorem leastSupersolution_obstacle (μ : Measure ℂ) {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) (3 / 4)) (hx0 : x ≠ 0) :
    -t * greenFunction (ball 0 (3 / 4)) 0 x ≤ leastSupersolution μ (3 / 4) 0 t x := by
  unfold leastSupersolution
  apply le_csInf
  · exact ⟨(fun _ : ℂ => (0 : ℝ)) x, (fun _ : ℂ => (0 : ℝ)), zero_mem_supersolutions_ball μ ht, rfl⟩
  · rintro b ⟨w, hw, rfl⟩
    exact hw.2.2 x hx hx0

/-- A point of the closure of the family at a time `s ∈ (0, T)` which lies outside `B_{1/2}` gives the certificate
`leastSupersolution ν (3/4) 0 s` at time `s`. -/
theorem certSuper_least_of_mem_closure (hpole : FrozenGreenDiscPole) {ν : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (hfam : IsConeHarmonicBallFamilyOn ν Λ T) (hst : IsStoppedAtHalfBall Λ T) {s : ℝ} (hs : s ∈ Ioo 0 T)
    {x : ℂ} (hxs : x ∈ closure (Λ s)) (hxb : x ∉ ball (0 : ℂ) (1 / 2))
    (hS : leastSupersolution ν (3 / 4) 0 s ∈ supersolutions ν (3 / 4) 0 s) :
    CertSuper ν s (leastSupersolution ν (3 / 4) 0 s) := by
  have hs0 : (0 : ℝ) < s := hs.1
  obtain ⟨hΛp, hcont, hlap, hbd⟩ :=
    hfam.2.2 s (1 / 2) hs (by norm_num) (hst.1 s hs) (3 / 4) (by norm_num)
  set w := leastSupersolution ν (3 / 4) 0 s with hwdef
  have hcl : certCluster (3 / 4) s w = cluster ν (3 / 4) 0 s := rfl
  have hC : IsOpen (certCluster (3 / 4) s w) :=
    isOpen_certCluster hpole (by norm_num) hs0 hcont
  have hint : certCluster (3 / 4) s w ⊆ interior (closure (certCluster (3 / 4) s w)) :=
    interior_maximal subset_closure hC
  have hΛeq : interior (closure (certCluster (3 / 4) s w)) = Λ s := by
    rw [hΛp, hcl]
  have hclΛ : closure (Λ s) = closure (certCluster (3 / 4) s w) := by
    apply le_antisymm
    · exact closure_minimal (by rw [← hΛeq]; exact interior_subset) isClosed_closure
    · exact closure_mono (by rw [← hΛeq]; exact hint)
  have hclosed_ball : closure (certCluster (3 / 4) s w) ⊆ closedBall (0 : ℂ) (1 / 2) := by
    rw [← hclΛ]
    exact (closure_mono (hst.1 s hs)).trans closure_ball_subset_closedBall
  have hxp : x ∈ closure (certCluster (3 / 4) s w) := by
    rw [← hclΛ]
    exact hxs
  have hxnorm : ‖x‖ = 1 / 2 := by
    have h1 : 1 / 2 ≤ ‖x‖ := by
      simpa [mem_ball, dist_zero_right, not_lt] using hxb
    have h2 : ‖x‖ ≤ 1 / 2 := by
      simpa [mem_closedBall, dist_zero_right] using hclosed_ball hxp
    linarith
  refine ⟨⟨hcont, fun y hy hy0 => leastSupersolution_obstacle ν hs0.le hy hy0, hbd, hclosed_ball,
    ⟨x, hxp, hxnorm⟩, ?_⟩, hS⟩
  rw [hΛeq]
  exact hlap

/-- A family counterexample gives a plateau pair: if the closure of `Λ_t` leaves `B_{1/2}`, then two rational times
`t < p < q < T` carry certificates, since `Λ_t ⊆ Λ_p ⊆ Λ_q` and the closure point stays on the circle `|x| = 1/2`. -/
theorem closure_ball_of_not_hasRatPlateauCert (hpole : FrozenGreenDiscPole) {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    {T : ℝ} (hfam : IsConeHarmonicBallFamilyOn ν Λ T) (hst : IsStoppedAtHalfBall Λ T)
    (hS : ∀ s ∈ Ioo 0 T, leastSupersolution ν (3 / 4) 0 s ∈ supersolutions ν (3 / 4) 0 s)
    (hno : ¬ HasRatPlateauCert ν) {t : ℝ} (ht : t ∈ Ioo 0 T) : closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2) := by
  by_contra hnot
  obtain ⟨x, hxcl, hxball⟩ := not_subset.mp hnot
  obtain ⟨p, htp, hpT⟩ := exists_rat_btwn ht.2
  obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hpT
  have hp : (p : ℝ) ∈ Ioo 0 T := ⟨lt_trans ht.1 htp, hpT⟩
  have hq : (q : ℝ) ∈ Ioo 0 T := ⟨lt_trans hp.1 hpq, hqT⟩
  have hxp : x ∈ closure (Λ (p : ℝ)) :=
    closure_mono (hfam.2.1.monotoneOn ht hp htp.le) hxcl
  have hxq : x ∈ closure (Λ (q : ℝ)) :=
    closure_mono (hfam.2.1.monotoneOn ht hq (lt_trans htp hpq).le) hxcl
  apply hno
  exact ⟨p, q, hp.1, hpq, ⟨_, certSuper_least_of_mem_closure hpole hfam hst hp hxp hxball (hS _ hp)⟩,
    ⟨_, certSuper_least_of_mem_closure hpole hfam hst hq hxq hxball (hS _ hq)⟩⟩

/-- The least supersolution on `B_{3/4}` lies in `S_{B_{3/4};0}(s)` at every positive time (HB Lemma 3.1,
`LeastSupersolutionMemStmt`, which holds almost surely for the LQG measure; not true for every measure). -/
def LeastSuperOK (ν : Measure ℂ) : Prop :=
  ∀ s : ℝ, 0 < s → leastSupersolution ν (3 / 4) 0 s ∈ supersolutions ν (3 / 4) 0 s

/-- The probabilistic core of the good set: the measures carrying a rational plateau pair of certificates, or failing
`LeastSuperOK`, are covered by a measurable set `N` of `Measure ℂ` whose preimage under `μ` is `P`-null. -/
def BadMeasureNullHull {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ) : Prop :=
  ∃ N : Set (Measure ℂ), MeasurableSet N ∧ {ν | HasRatPlateauCert ν ∨ ¬ LeastSuperOK ν} ⊆ N ∧
    P (μ ⁻¹' N) = 0

/-- The reduction of `ConeClosureGoodMeasureLawStep` to the bad null hull for every cone field. OPEN (NEW): the zero
cone law, (coding, Borel relation, analytic projection), 5 (plateau radii,
Tonelli, scaling, zero law) and 6 (null hull). -/
def ConeBadNullHullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → BadMeasureNullHull P μ

/-- A bad null hull gives the good measurable set: `G = N^c`. -/
theorem coneGoodMeasureLaw_of_badNullHull (hpole : FrozenGreenDiscPole) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (hN : BadMeasureNullHull P μ) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧
      (∀ ν ∈ G, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
        ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2)) ∧
      ∀ᵐ ω ∂P, μ ω ∈ G := by
  obtain ⟨N, hNm, hsub, hnull⟩ := hN
  have hgood : ∀ ν ∈ Nᶜ, ¬ HasRatPlateauCert ν ∧ LeastSuperOK ν := fun ν hν =>
    ⟨fun h => hν (hsub (Or.inl h)), not_not.mp (fun h => hν (hsub (Or.inr h)))⟩
  refine ⟨Nᶜ, hNm.compl, fun ν hν T Λ hfam hst t ht =>
    closure_ball_of_not_hasRatPlateauCert hpole hfam hst (fun s hs => (hgood ν hν).2 s hs.1)
      (hgood ν hν).1 ht, ?_⟩
  have hset : {ω | ¬ μ ω ∈ Nᶜ} = μ ⁻¹' N := by
    ext ω
    simp
  rw [ae_iff, hset]
  exact hnull

/-- `ConeClosureGoodMeasureLawStep` (FirstPass/S2f.lean) follows from the open step `ConeBadNullHullStep`. -/
theorem coneClosureGoodMeasureLawStep_of_badNullHull (hpole : FrozenGreenDiscPole)
    (hN : ConeBadNullHullStep) : ConeClosureGoodMeasureLawStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  exact coneGoodMeasureLaw_of_badNullHull hpole P μ (hN γ hγ hγ2 Ω P hC hcirc μ hcone)

end MatedCRT
