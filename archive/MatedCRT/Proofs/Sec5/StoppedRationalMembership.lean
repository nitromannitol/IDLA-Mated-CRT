import MatedCRT.Proofs.Sec5.StoppedCompactCode

/-!
# Shifted rational-ball membership code and measurable versions

It uses the cluster
code `A_{R,p}` (realised as `ConeOriginNull.codeAt`) and the family identity
(realised as `SatisfiesObstacleCharacterization`).

For fixed `t > 0` and integer radii `R = n + 1`, the shifted rational-ball predicate `RatBallPred` at a Gaussian rational
`q ∈ ℚ + iℚ` is a countable Boolean combination of the cluster codes. It is null-measurable
(`nullMeasurableSet_ratBallCode`). At every outcome where the family and the supersolution-section identity hold, its
truth is eventually in `n` the truth of `q ∈ Λ_t` (`eventually_mem_iff_ratBallCode`). The limsup over `n` and its measurable
hull give versions `ratVersion`, which agree with the membership events simultaneously for all Gaussian rationals almost
surely (`ae_forall_gaussRat_ratVersion_iff`). `exists_ratVersions_ae_codeCompact` supplies the premises `E`, `hE`, `hae`
of `StoppedCompactCode.ae_codeCompact_eq_closure`.

Explicit inputs, not discharged here: the Preston input `PrestonAnalyticUniversallyMeasurableStmt`; the Borel sections `𝒜 n`
with their almost-sure section identity (the output of `CodeSectionStmt` at radius `n + 1`); and the cone harmonic-ball
family `IsConeHarmonicBallFamily` of the random set `Λ`.
-/

open MeasureTheory Filter Topology TopologicalSpace Set Metric
open HarmonicBalls MatedCRT.CircleProcessSpace MatedCRT.ConeOriginNull

namespace MatedCRT
namespace StoppedRationalMembership

/-- The shifted rational-ball predicate of a membership predicate `M` at `q`: for some scale
`1/j`, `j ≥ 1`, every Gaussian rational `q'` of the ball `B_{1/j}(q)`, centred at `q` (shifted, not at `0`), is
approximated at every scale `1/k` by a Gaussian rational `p` with `M p`. Here `Q = ℚ + iℚ` is `gaussRat`. -/
def RatBallPred (M : ℂ → Prop) (q : ℂ) : Prop :=
  ∃ j : ℕ, 0 < j ∧ ∀ q' ∈ gaussRat ∩ ball q (1 / (j : ℝ)), ∀ k : ℕ, 0 < k →
    ∃ p ∈ gaussRat ∩ {p | dist p q' < 1 / (k : ℝ)}, M p

/-- The countable rational-point membership code at radius `R` (with `A_{R,p}`): `RatBallPred` with `M p = codeAt 𝒜 t p c`, the cluster code of the circle outcome `c`. -/
def ratBallCode {R : ℝ} (𝒜 : Set (PosCircleFns × BallFns R)) (t : ℝ) (q : ℂ) (c : PosCircleFns) : Prop :=
  RatBallPred (fun p => codeAt 𝒜 t p c) q

/-- **Raw deterministic identity.** For an open set `K`, a point `q` lies in `int closure K` iff the shifted
rational-ball predicate of the membership `p ∈ K` holds. Rational points of `K` replace `K`
(`subset_closure_iff_code`, for a dense set of Gaussian rationals). -/
theorem mem_interior_closure_iff_ratBallPred {K : Set ℂ} (hK : IsOpen K) (q : ℂ) :
    q ∈ interior (closure K) ↔ RatBallPred (fun p => p ∈ K) q := by
  unfold RatBallPred
  constructor
  · intro hq
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hq)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hrad : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < ε := by
      push_cast
      exact hn
    have hsub : ball q (1 / ((n + 1 : ℕ) : ℝ)) ⊆ closure K :=
      (ball_subset_ball hrad.le).trans hball
    refine ⟨n + 1, Nat.succ_pos n, fun q' hq' k hk => ?_⟩
    obtain ⟨p, ⟨hpD, hpK⟩, hd⟩ := (subset_closure_iff_code gaussRat_dense hK isOpen_ball).1 hsub q' hq' k hk
    exact ⟨p, ⟨hpD, hd⟩, hpK⟩
  · rintro ⟨j, hj, h⟩
    have hjpos : (0 : ℝ) < 1 / (j : ℝ) := one_div_pos.2 (by exact_mod_cast hj)
    have hsub : ball q (1 / (j : ℝ)) ⊆ closure K :=
      (subset_closure_iff_code gaussRat_dense hK isOpen_ball).2 fun q' hq' k hk => by
        obtain ⟨p, ⟨hpD, hd⟩, hpK⟩ := h q' hq' k hk
        exact ⟨p, ⟨hpD, hpK⟩, hd⟩
    have hint : ball q (1 / (j : ℝ)) ⊆ interior (closure K) := isOpen_ball.subset_interior_iff.2 hsub
    exact hint (mem_ball_self hjpos)

/-- Null-measurability of the shifted rational-ball predicate, from the countably many sets `A p`, `p ∈ ℂ`: the index
sets are countable because they lie in `gaussRat`, and the scales `j, k` are integers. -/
theorem nullMeasurableSet_RatBallPred {X : Type*} [MeasurableSpace X] (ν : Measure X) (A : ℂ → Set X)
    (hA : ∀ p : ℂ, NullMeasurableSet (A p) ν) (q : ℂ) :
    NullMeasurableSet {x | RatBallPred (fun p => x ∈ A p) q} ν := by
  have e : {x | RatBallPred (fun p => x ∈ A p) q} =
      ⋃ j ∈ {j : ℕ | 0 < j}, ⋂ q' ∈ gaussRat ∩ ball q (1 / (j : ℝ)), ⋂ k ∈ {k : ℕ | 0 < k},
        ⋃ p ∈ gaussRat ∩ {p | dist p q' < 1 / (k : ℝ)}, A p := by
    ext x
    simp only [RatBallPred, Set.mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
  rw [e]
  exact NullMeasurableSet.biUnion (Set.to_countable _) fun j _ =>
    NullMeasurableSet.biInter (gaussRat_countable.mono inter_subset_left) fun q' _ =>
      NullMeasurableSet.biInter (Set.to_countable _) fun k _ =>
        NullMeasurableSet.biUnion (gaussRat_countable.mono inter_subset_left) fun p _ => hA p

/-- The cluster code `codeAt` is null-measurable on the circle process for every finite measure, by
`univMeasurable_codeAt`; hence so is the shifted rational-ball code `ratBallCode` at every `q ∈ ℂ`. -/
theorem nullMeasurableSet_ratBallCode (hP : PrestonAnalyticUniversallyMeasurableStmt) {R t : ℝ}
    {𝒜 : Set (PosCircleFns × BallFns R)} (h𝒜 : MeasurableSet 𝒜) (q : ℂ) (ν : Measure PosCircleFns)
    [IsFiniteMeasure ν] : NullMeasurableSet {x | ratBallCode 𝒜 t q x} ν :=
  nullMeasurableSet_RatBallPred ν (fun p => {x | codeAt 𝒜 t p x})
    (fun p => univMeasurable_codeAt hP h𝒜 p ν) q

/-- The shifted rational-ball code of the circle process `c : Ω → PosCircleFns` is null-measurable on `Ω` (no
completeness of `P` is used, `nullMeasurableSet_preimage_of_univ`). -/
theorem nullMeasurableSet_ratBallCode_preimage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {c : Ω → PosCircleFns} (hc : Measurable c) (hP : PrestonAnalyticUniversallyMeasurableStmt) {R t : ℝ}
    {𝒜 : Set (PosCircleFns × BallFns R)} (h𝒜 : MeasurableSet 𝒜) (q : ℂ) :
    NullMeasurableSet {ω | ratBallCode 𝒜 t q (c ω)} P :=
  nullMeasurableSet_preimage_of_univ (B := {x : PosCircleFns | ratBallCode 𝒜 t q x}) P hc fun ν hν => by
    have := hν
    exact nullMeasurableSet_ratBallCode hP h𝒜 q ν

/-- The limsup (frequently) event of the rational membership codes at `z`: `ω` belongs to it iff the code at `z` holds for
infinitely many integer radii `n + 1`. -/
def ratLimsupEvent {Ω : Type*} (c : Ω → PosCircleFns)
    (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))) (t : ℝ) (z : ℂ) : Set Ω :=
  ⋂ N : ℕ, ⋃ n ∈ {n : ℕ | N ≤ n}, {ω | ratBallCode (𝒜 n) t z (c ω)}

theorem mem_ratLimsupEvent_iff {Ω : Type*} (c : Ω → PosCircleFns)
    (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))) (t : ℝ) (z : ℂ) (ω : Ω) :
    ω ∈ ratLimsupEvent c 𝒜 t z ↔ ∃ᶠ n in atTop, ratBallCode (𝒜 n) t z (c ω) := by
  simp only [ratLimsupEvent, mem_iInter, mem_iUnion, Set.mem_ofPred_eq, exists_prop, Filter.frequently_atTop]

theorem nullMeasurableSet_ratLimsupEvent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {c : Ω → PosCircleFns} (hc : Measurable c) (hP : PrestonAnalyticUniversallyMeasurableStmt)
    {𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))} (h𝒜 : ∀ n : ℕ, MeasurableSet (𝒜 n))
    (t : ℝ) (z : ℂ) : NullMeasurableSet (ratLimsupEvent c 𝒜 t z) P := by
  unfold ratLimsupEvent
  exact NullMeasurableSet.iInter fun N => NullMeasurableSet.biUnion (Set.to_countable _) fun n _ =>
    nullMeasurableSet_ratBallCode_preimage P hc hP (h𝒜 n) z

/-- A measurable version of the rational membership event at `z`: the measurable hull (`toMeasurable`) of the limsup
event. It is measurable for every `z`. -/
noncomputable def ratVersion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : Ω → PosCircleFns)
    (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))) (t : ℝ) (z : ℂ) : Set Ω :=
  toMeasurable P (ratLimsupEvent c 𝒜 t z)

theorem measurableSet_ratVersion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : Ω → PosCircleFns)
    (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))) (t : ℝ) (z : ℂ) :
    MeasurableSet (ratVersion P c 𝒜 t z) :=
  measurableSet_toMeasurable P _

/-- **Version identity at one Gaussian rational.** If almost surely the membership `z ∈ L ω` is eventually (in `n`) the
code at radius `n + 1`, then the measurable version `ratVersion` at `z` agrees with `z ∈ L ω` almost surely. -/
theorem ae_ratVersion_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {c : Ω → PosCircleFns}
    (hc : Measurable c) (hP : PrestonAnalyticUniversallyMeasurableStmt)
    {𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))} (h𝒜 : ∀ n : ℕ, MeasurableSet (𝒜 n)) {t : ℝ}
    (L : Ω → Set ℂ) (z : ℂ)
    (hz : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (z ∈ L ω ↔ ratBallCode (𝒜 n) t z (c ω))) :
    ∀ᵐ ω ∂P, (ω ∈ ratVersion P c 𝒜 t z ↔ z ∈ L ω) := by
  have hv : ∀ᵐ ω ∂P, (ω ∈ ratVersion P c 𝒜 t z ↔ ω ∈ ratLimsupEvent c 𝒜 t z) :=
    (NullMeasurableSet.toMeasurable_ae_eq (nullMeasurableSet_ratLimsupEvent P hc hP h𝒜 t z)).mono
      fun ω hω => eq_iff_iff.1 hω
  filter_upwards [hz, hv] with ω hzω hvω
  rw [hvω, mem_ratLimsupEvent_iff]
  constructor
  · intro hfreq
    by_contra hnot
    exact (Filter.not_frequently.2 (hzω.mono fun n hn hcode => hnot (hn.2 hcode))) hfreq
  · intro hzL
    exact (hzω.mono fun n hn => hn.1 hzL).frequently

/-- **One common almost-sure event for all Gaussian rationals.** The countably many versions `ratVersion P c 𝒜 t z`,
`z ∈ gaussRat`, agree simultaneously almost surely with the membership events of `L`. -/
theorem ae_forall_gaussRat_ratVersion_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {c : Ω → PosCircleFns} (hc : Measurable c) (hP : PrestonAnalyticUniversallyMeasurableStmt)
    {𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))} (h𝒜 : ∀ n : ℕ, MeasurableSet (𝒜 n)) {t : ℝ}
    (L : Ω → Set ℂ)
    (hL : ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ᶠ n in atTop, (z ∈ L ω ↔ ratBallCode (𝒜 n) t z (c ω))) :
    ∀ᵐ ω ∂P, ∀ z ∈ gaussRat, (ω ∈ ratVersion P c 𝒜 t z ↔ z ∈ L ω) := by
  refine (ae_ball_iff gaussRat_countable).2 fun z _ => ?_
  exact ae_ratVersion_iff P hc hP h𝒜 L z (hL.mono fun ω h => h z)

/-- **Raw eventual identity at an outcome.** Let `Λ` be a cone harmonic-ball family for `μ`, and let the section `𝒜 n`
satisfy the supersolution-trace identity at the circle outcome `c` for every integer radius `n + 1`. Then for every `z`,
the truth of `z ∈ Λ_t` is eventually in `n` the truth of the rational-ball code at `z`. The threshold depends only on a
bound `Λ_t ⊆ B_r`: for `R > r`, `Λ_t = int closure K_R`. -/
theorem eventually_mem_iff_ratBallCode {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hfam : IsConeHarmonicBallFamily μ Λ)
    {t : ℝ} (ht : 0 < t) (c : PosCircleFns) (𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1)))
    (hsec : ∀ (n : ℕ) (w : BallFns ((n : ℝ) + 1)), (c, w) ∈ 𝒜 n ↔ w ∈ superTraces μ ((n : ℝ) + 1) t)
    (z : ℂ) : ∀ᶠ n : ℕ in atTop, (z ∈ Λ t ↔ ratBallCode (𝒜 n) t z c) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 (hfam.2.1.isBounded t ht)
  have hR0 : (0 : ℝ) < |r| + 1 := by positivity
  have hsub : Λ t ⊆ ball (0 : ℂ) (|r| + 1) :=
    hr.trans (closedBall_subset_ball (by linarith [le_abs_self r]))
  obtain ⟨N0, hN0⟩ := exists_nat_gt (|r| + 1)
  filter_upwards [Filter.eventually_ge_atTop N0] with n hn
  have hρ : |r| + 1 < (n : ℝ) + 1 := by
    have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hΛeq, hv, -⟩ := hfam.2.2 t (|r| + 1) ht hR0 hsub ((n : ℝ) + 1) hρ
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hopen : IsOpen (cluster μ ((n : ℝ) + 1) 0 t) := isOpen_cluster_zero hpos ht hv
  have hcl : ∀ p : ℂ, p ∈ cluster μ ((n : ℝ) + 1) 0 t ↔ codeAt (𝒜 n) t p c :=
    fun p => mem_cluster_iff_codeAt hpos ht (hsec n) p
  rw [hΛeq, mem_interior_closure_iff_ratBallPred hopen]
  unfold ratBallCode
  simp only [hcl]

/-- **Almost-sure eventual identity.** If the family holds almost surely and the section identity holds almost surely
for all integer radii, then almost surely, for every `z`, the truth of `z ∈ Λ_t` is eventually the code at `z`. -/
theorem ae_forall_eventually_mem_iff_ratBallCode {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {Λ : Ω → ℝ → Set ℂ} {t : ℝ} (ht : 0 < t) {c : Ω → PosCircleFns}
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    {𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))}
    (hsec : ∀ᵐ ω ∂P, ∀ (n : ℕ) (w : BallFns ((n : ℝ) + 1)),
      (c ω, w) ∈ 𝒜 n ↔ w ∈ superTraces (μ ω) ((n : ℝ) + 1) t) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ᶠ n : ℕ in atTop, (z ∈ Λ ω t ↔ ratBallCode (𝒜 n) t z (c ω)) := by
  filter_upwards [hfam, hsec] with ω h1 h2 z
  exact eventually_mem_iff_ratBallCode h1 ht (c ω) 𝒜 h2 z

/-- **Premises of `StoppedCompactCode.ae_codeCompact_eq_closure` for the rational membership code.** Given a cone
harmonic-ball family `Λ_t(ω)` (almost surely), Borel sections `𝒜 n` of radius `n + 1` with their almost-sure section
identity (the output of `CodeSectionStmt`), and the Preston input, there are measurable selections `E z` (`hE`) for the
Gaussian rationals with the common almost-sure membership identity (`hae`). The random compact code is then `closure Λ_t`
almost surely. No geometry or margin closure is claimed. -/
theorem exists_ratVersions_ae_codeCompact {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : PrestonAnalyticUniversallyMeasurableStmt) {c : Ω → PosCircleFns} (hc : Measurable c)
    (μ : Ω → Measure ℂ) (Λ : Ω → ℝ → Set ℂ) {t : ℝ} (ht : 0 < t)
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    {𝒜 : ∀ n : ℕ, Set (PosCircleFns × BallFns ((n : ℝ) + 1))} (h𝒜 : ∀ n : ℕ, MeasurableSet (𝒜 n))
    (hsec : ∀ᵐ ω ∂P, ∀ (n : ℕ) (w : BallFns ((n : ℝ) + 1)),
      (c ω, w) ∈ 𝒜 n ↔ w ∈ superTraces (μ ω) ((n : ℝ) + 1) t) :
    ∃ E : ℂ → Set Ω, (∀ z ∈ gaussRat, MeasurableSet (E z)) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ gaussRat, (ω ∈ E z ↔ z ∈ Λ ω t)) ∧
      ∀ᵐ ω ∂P, ((StoppedCompactCode.codeCompact E ω : NonemptyCompacts ℂ) : Set ℂ) = closure (Λ ω t) := by
  have hL : ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ᶠ n in atTop, (z ∈ Λ ω t ↔ ratBallCode (𝒜 n) t z (c ω)) :=
    ae_forall_eventually_mem_iff_ratBallCode ht hfam hsec
  have hae := ae_forall_gaussRat_ratVersion_iff P hc hP h𝒜 (fun ω => Λ ω t) hL
  have hΛo : ∀ᵐ ω ∂P, IsOpen (Λ ω t) := hfam.mono fun ω h => (h.1 t ht).1
  have hΛb : ∀ᵐ ω ∂P, Bornology.IsBounded (Λ ω t) := hfam.mono fun ω h => h.2.1.isBounded t ht
  have hΛne : ∀ᵐ ω ∂P, (Λ ω t).Nonempty := hfam.mono fun ω h => ⟨0, (h.1 t ht).2.1⟩
  refine ⟨ratVersion P c 𝒜 t, fun z _ => measurableSet_ratVersion P c 𝒜 t z, hae, ?_⟩
  exact StoppedCompactCode.ae_codeCompact_eq_closure (Λ := fun ω => Λ ω t) hΛo hΛb hΛne hae

end StoppedRationalMembership
end MatedCRT
