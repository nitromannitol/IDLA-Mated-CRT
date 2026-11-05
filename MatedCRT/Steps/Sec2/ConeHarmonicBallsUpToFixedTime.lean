import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec2.ConeFamily

/-!
# Lemma 2.4 from named steps (harmonic balls of the quantum cone up to the exit time of `B_{1/2}`)

The proof of Lemma 2.4 (lines 540-545) is a transfer from the whole-plane GFF plus `-γ log |·|`, for which HB22 gives
the harmonic balls, to the quantum cone:
1. HB22 Theorems 1.1, 5.5 and Lemma 3.2 give, for `h^ℂ - γ log |·|`, a family `{Λ_t}_{t > 0}` with the properties
   (a), (b), (c) of Theorem 2.3 (`WholePlaneConeHarmonicBallsStep`); it starts inside `B_{1/2}`
   (`WholePlaneHarmonicBallsSmallTimeStep`), so stopping it when it reaches `∂B_{1/2}` gives a family of Lemma 2.4
   (`hasConeHarmonicBallsUpToHalfBall_of_isConeHarmonicBallFamily`, deterministic).
2. The restrictions to `B_1` of the cone field and of `h^ℂ - γ log |·|` agree in law (eq:gff, `ConeRestrictionStep`),
   and the existence of a family of Lemma 2.4 is a.s. the same measurable event of the restriction to `B_1` for both
   fields (harmonic balls depend locally on the field, HB22 Proposition 1.3, with the locality of the LQG measure,
   Fact 2.2 II: `ConeHarmonicBallLocalityStep`).
3. Uniqueness. Condition (c) determines every bounded `Λ_t` (`IsConeHarmonicBallFamilyOn.eqOn`, deterministic; this
   replaces the citation of HB22 Proposition 5.6 at line 543). The uniqueness of the stopping time `T` needs that the
   family does not stall at `∂B_{1/2}`: strict growth `cl Λ_s ⊆ Λ_t` for `s < t`
   (`ConeHarmonicBallStrictGrowthStep`; `IsStoppedAtHalfBall.eq_of_eqOn`, deterministic).
A sample of `h^ℂ` with the LQG measure of `h^ℂ - γ log |·|` exists (`WholePlaneLogLQGExistenceStep`).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The circles `∂B_r(z)` whose closed disk `cl B_r(z)` lies in the unit disk `B_1`. -/
abbrev UnitBallCircle : Type := {p : Ioi (0 : ℝ) × ℂ // closedBall p.2 p.1 ⊆ ball (0 : ℂ) 1}

/-- The restriction `h|_{B_1}` of a field to the unit disk, through its circle averages `h_r(z)` over the circles
`∂B_r(z)` with `cl B_r(z) ⊆ B_1`. -/
def unitBallCircleProcess (hcirc : ℝ → ℂ → ℝ) : UnitBallCircle → ℝ := fun p => hcirc p.1.1.1 p.1.2

/-- The event of Lemma 2.4 for a measure `ν`: there is a family of harmonic balls `{Λ_t}_{0 < t < T}`, `T > 0`, for `ν`
centred at `0` with the properties of Theorem 2.3 on `(0, T)`, stopped when it reaches `∂B_{1/2}`. -/
def HasConeHarmonicBallsUpToHalfBall (ν : Measure ℂ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn ν Λ T ∧ IsStoppedAtHalfBall Λ T

/-- Strict growth of a family on `(0, T)`: `cl Λ_s ⊆ Λ_t` for `0 < s < t < T`. -/
def IsStrictlyGrowingOn (Λ : ℝ → Set ℂ) (T : ℝ) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t → t < T → closure (Λ s) ⊆ Λ t

/-- **Step (a sample of the whole-plane GFF with the LQG measure of `h^ℂ - γ log |·|`).** For `γ ∈ (0, 2)` there is a
whole-plane GFF `h^ℂ` (normalized by `h^ℂ_1(0) = 0`) on a probability space, with a random measure which is a.s. the
`γ`-LQG measure of `h^ℂ - γ log |·|` (the circle average limit). Sources: Sheffield 2007 (the whole-plane GFF);
Duplantier-Sheffield 2011 Proposition 1.1 and Weyl scaling (the LQG measure of `h^ℂ - α log |·|`, `α < Q`; the setting
of HB22, line 531). -/
def WholePlaneLogLQGExistenceStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsProbabilityMeasure P ∧ IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ γ hcirc μ

/-- **Step (Theorem 2.3 for `h^ℂ - γ log |·|`: HB22 Theorems 1.1, 5.5 and Lemma 3.2).** For the whole-plane GFF `h^ℂ`
and the LQG measure `μ` of `h^ℂ - γ log |·|`, a.s. there is a family `{Λ_t}_{t > 0}` of harmonic balls for `μ`
centred at `0` with the properties (a), (b), (c) of Theorem 2.3. This is the combination of HB22 Theorem 1.1
(`HarmonicBalls.ExistenceUniquenessHarmonicBallsStmt`, with `α₀ = γ < Q`), Theorem 5.5 and Lemma 3.2 which the paper
cites in the header of Theorem 2.3 (line 509) and at line 542. -/
def WholePlaneConeHarmonicBallsStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → ∀ᵐ ω ∂P, ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily (μ ω) Λ

/-- **Step (the harmonic balls of `h^ℂ - γ log |·|` start at `0`).** A.s., every family of Theorem 2.3 for the LQG
measure of `h^ℂ - γ log |·|` satisfies `Λ_t ⊆ B_r` for small `t > 0`, for every `r > 0` (`Λ_t → {0}` as `t → 0`: the
continuity in `t` of Theorem 2.3 (b) at `t = 0`, with `Λ_0 = {0}`; HB22 Theorem 1.1, see the cluster upper bound
`HarmonicBalls.ClusterUpperBoundStmt`). Used implicitly in Lemma 2.4 (`T > 0`, line 537). -/
def WholePlaneHarmonicBallsSmallTimeStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → ∀ᵐ ω ∂P, ∀ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily (μ ω) Λ →
      ∀ r : ℝ, 0 < r → ∃ t : ℝ, 0 < t ∧ Λ t ⊆ ball 0 r

/-- **Step (eq:gff, line 444).** The restrictions to the unit disk of the quantum cone field `h` and of
`h^ℂ - γ log |·|` (`h^ℂ` a whole-plane GFF with `h^ℂ_1(0) = 0`) agree in law, through their circle averages over the
circles in `B_1`. Stated after Definition 2.1 as immediate from it (INPUT-REQUESTS IR-A1, IR-A3: provable; the IR-A1
text also includes the pairings with test functions supported in `B_1`). -/
def ConeRestrictionStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' →
    P.map (fun ω => unitBallCircleProcess (hcirc ω)) =
      P'.map (fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc' ω)))

/-- **Step (harmonic balls depend locally on the field: HB22 Proposition 1.3 with Fact 2.2 II).** For `γ ∈ (0, 2)`
there is one measurable set `S` of restrictions of fields to `B_1` such that, both for the quantum cone and for
`h^ℂ - γ log |·|`, a.s. the event of Lemma 2.4 for the LQG measure holds iff the restriction of the field to `B_1`
lies in `S`. Line 542 ("since harmonic balls depend locally on the field [HB22, Proposition 1.3]"): the family of
Lemma 2.4 lives in `B_{1/2}` and is determined by the LQG measure on `B_1` (condition (c) at the radii `ρ < 1` and
HB22's cluster compatibility, `HarmonicBalls.ClusterCompatibilityStmt`), which is determined by the circle averages in
`B_1` (Fact 2.2 II). The measurability of the event in `σ(h|_{B_1})` is implicit in the paper. -/
def ConeHarmonicBallLocalityStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ S : Set (UnitBallCircle → ℝ), MeasurableSet S ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      ∀ᵐ ω ∂P, (HasConeHarmonicBallsUpToHalfBall (μ ω) ↔ unitBallCircleProcess (hcirc ω) ∈ S)) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      ∀ᵐ ω ∂P, (HasConeHarmonicBallsUpToHalfBall (μ ω) ↔
        unitBallCircleProcess (fieldCircleAverage γ (hcirc ω)) ∈ S)

/-- **Step (strict growth of the harmonic balls of the cone).** A.s., every family of harmonic balls for `μ_h` with the
properties of Theorem 2.3 on an interval `(0, T)` grows strictly: `cl Λ_s ⊆ Λ_t` for `0 < s < t < T`. Not stated in the
paper; it is what makes the time `T = sup {t : Λ_t ⊆ B_{1/2}}` of Lemmas 2.4 and 2.5 unique among families which stop
at `∂B_{1/2}` (`IsStoppedAtHalfBall`): without it the radius of `Λ_t` could stay at `1/2` on an interval of times
(worker A's remark, reports 2026-11-04). Expected from HB22 (obstacle problem for a measure of full support). -/
def ConeHarmonicBallStrictGrowthStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (Λ : ℝ → Set ℂ), IsConeHarmonicBallFamilyOn (μ ω) Λ T → IsStrictlyGrowingOn Λ T

/-- The properties of Theorem 2.3 on `(0, T)`, `T > 0`, from the harmonic ball property and (a), (b) for all `t > 0`
and the obstacle characterization (c) on `(0, T)`. -/
theorem isConeHarmonicBallFamilyOn_of_conditions {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hball : ∀ t : ℝ, 0 < t → IsHarmonicBall ν (Λ t) 0) (hcond : SatisfiesHarmonicBallConditions ν Λ 0) {T : ℝ}
    (hobs : SatisfiesObstacleCharacterizationOn ν Λ T) (hT : 0 < T) : IsConeHarmonicBallFamilyOn ν Λ T := by
  refine ⟨fun t ht => hball t ht.1, ⟨fun t ht => hcond.measure_eq t ht.1, fun t ht => hcond.measure_frontier t ht.1,
    fun t ht => hcond.isRegularOpen t ht.1, fun t ht => hcond.isBounded t ht.1, fun t ht => hcond.isConnected t ht.1,
    fun t ht => hcond.mem t ht.1, hcond.monotoneOn.mono Ioo_subset_Ioi_self, ?_, ?_⟩, hobs⟩
  · intro t ht ε hε
    exact nhdsWithin_mono _ Ioo_subset_Ioi_self (hcond.hausdorffContinuousOn t ht.1 ε hε)
  · apply Subset.antisymm
    · intro x hx
      rw [← hcond.iInter_eq]
      simp only [mem_iInter] at hx ⊢
      intro t ht
      have ht' : 0 < t := ht
      have hs : min t (T / 2) ∈ Ioo 0 T :=
        ⟨lt_min ht' (half_pos hT), (min_le_right _ _).trans_lt (half_lt_self hT)⟩
      exact hcond.monotoneOn hs.1 ht (min_le_left _ _) (hx _ hs)
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      simp only [mem_iInter]
      exact fun t ht => hcond.mem t ht.1

/-- A family with the properties of Theorem 2.3 for all `t > 0` has them on every interval `(0, T)`, `T > 0`. -/
theorem IsConeHarmonicBallFamily.isConeHarmonicBallFamilyOn {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    (h : IsConeHarmonicBallFamily ν Λ) {T : ℝ} (hT : 0 < T) : IsConeHarmonicBallFamilyOn ν Λ T :=
  isConeHarmonicBallFamilyOn_of_conditions h.1 h.2.1 (fun t r ht hr hsub ρ hρ => h.2.2 t r ht.1 hr hsub ρ hρ) hT

/-- **Stopping a family at `∂B_{1/2}`** (deterministic), general form. If `{Λ_t}_{t > 0}` consists of harmonic balls
for a measure `ν` with `ν(B_{1/2}) < ∞`, satisfies (a), (b) of Theorem 2.3, satisfies the obstacle characterization
(c) at the times `t` with `Λ_t ⊆ B_{1/2}`, and `Λ_t ⊆ B_{1/2}` for some `t > 0`, then with
`T = sup {t > 0 : Λ_t ⊆ B_{1/2}}` the family `{Λ_t}_{0 < t < T}` is a family of Lemma 2.4: `0 < T < ∞` (as
`ν(Λ_t) = t`), and by Hausdorff continuity at `T` the family is not stopped before it reaches `∂B_{1/2}`. -/
theorem hasConeHarmonicBallsUpToHalfBall_of_conditions {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hball : ∀ t : ℝ, 0 < t → IsHarmonicBall ν (Λ t) 0) (hcond : SatisfiesHarmonicBallConditions ν Λ 0)
    (hobs : ∀ t r : ℝ, 0 < t → Λ t ⊆ ball 0 (1 / 2) → 0 < r → Λ t ⊆ ball 0 r → ∀ ρ : ℝ, r < ρ →
      Λ t = interior (closure (cluster ν ρ 0 t)) ∧
      ContinuousOn (leastSupersolution ν ρ 0 t) (closedBall 0 ρ) ∧
      HasLaplacian (leastSupersolution ν ρ 0 t) (ν.restrict (Λ t)) 0 (ball 0 ρ) ∧
      ∀ x ∈ sphere (0 : ℂ) ρ, leastSupersolution ν ρ 0 t x = 0)
    (hfin : ν (ball 0 (1 / 2)) ≠ ∞) (hsmall : ∃ t : ℝ, 0 < t ∧ Λ t ⊆ ball 0 (1 / 2)) :
    HasConeHarmonicBallsUpToHalfBall ν := by
  set A : Set ℝ := {t | 0 < t ∧ Λ t ⊆ ball 0 (1 / 2)} with hA
  obtain ⟨t₀, ht₀, hsub₀⟩ := hsmall
  have hne : t₀ ∈ A := ⟨ht₀, hsub₀⟩
  have hbdd : BddAbove A := by
    refine ⟨(ν (ball 0 (1 / 2))).toReal, fun t ht => ?_⟩
    have h1 : ENNReal.ofReal t ≤ ν (ball 0 (1 / 2)) := by
      rw [← hcond.measure_eq t ht.1]
      exact measure_mono ht.2
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
  set T := sSup A with hTdef
  have hT : 0 < T := ht₀.trans_le (le_csSup hbdd hne)
  have hsubT : ∀ t ∈ Ioo 0 T, Λ t ⊆ ball 0 (1 / 2) := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨t₀, hne⟩ ht.2
    exact (hcond.monotoneOn ht.1 hs.1 hts.le).trans hs.2
  refine ⟨T, hT, Λ, isConeHarmonicBallFamilyOn_of_conditions hball hcond
    (fun t r ht hr hsub ρ hρ => hobs t r ht.1 (hsubT t ht) hr hsub ρ hρ) hT, hsubT, fun r hr => ?_⟩
  by_contra hcon
  have hall : ∀ t ∈ Ioo 0 T, Λ t ⊆ ball 0 r := by
    intro t ht
    by_contra hnot
    exact hcon ⟨t, ht, hnot⟩
  -- Hausdorff continuity at `T`
  set δ : ℝ := (1 / 2 - r) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hcont := hcond.hausdorffContinuousOn T hT (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ0)
  rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds hT), Metric.eventually_nhds_iff] at hcont
  obtain ⟨η, hη, hη'⟩ := hcont
  set s₁ : ℝ := max (T - η / 2) (T / 2) with hs₁
  set s₂ : ℝ := T + η / 2 with hs₂
  have hs₁T : s₁ ∈ Ioo 0 T :=
    ⟨lt_max_of_lt_right (half_pos hT), max_lt (by linarith) (half_lt_self hT)⟩
  have hd₁ : dist s₁ T < η := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor
    · linarith [hs₁T.2]
    · linarith [le_max_left (T - η / 2) (T / 2)]
  have hd₂ : dist s₂ T < η := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  have hH₁ := hη' hd₁
  have hH₂ := hη' hd₂
  rw [Metric.hausdorffEDist_comm] at hH₁
  have hs₂A : s₂ ∈ A := by
    refine ⟨by linarith, fun x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hx hH₂
    obtain ⟨z, hz, hyz⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hy hH₁
    rw [edist_lt_ofReal] at hxy hyz
    have hz' : ‖z‖ < r := mem_ball_zero_iff.1 (hall s₁ hs₁T hz)
    rw [mem_ball_zero_iff]
    calc ‖x‖ = dist x 0 := (dist_zero_right x).symm
      _ ≤ dist x z + dist z 0 := dist_triangle x z 0
      _ ≤ dist x y + dist y z + dist z 0 := by linarith [dist_triangle x y z]
      _ = dist x y + dist y z + ‖z‖ := by rw [dist_zero_right]
      _ < δ + δ + r := by gcongr
      _ < 1 / 2 := by rw [hδ]; linarith
  have := le_csSup hbdd hs₂A
  rw [← hTdef] at this
  linarith

/-- **Stopping a family of Theorem 2.3 at `∂B_{1/2}`** (deterministic): the case of a family with the properties of
Theorem 2.3 for all `t > 0` (`hasConeHarmonicBallsUpToHalfBall_of_conditions`). -/
theorem hasConeHarmonicBallsUpToHalfBall_of_isConeHarmonicBallFamily {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    (h : IsConeHarmonicBallFamily ν Λ) (hfin : ν (ball 0 (1 / 2)) ≠ ∞)
    (hsmall : ∃ t : ℝ, 0 < t ∧ Λ t ⊆ ball 0 (1 / 2)) : HasConeHarmonicBallsUpToHalfBall ν :=
  hasConeHarmonicBallsUpToHalfBall_of_conditions h.1 h.2.1
    (fun t r ht _ hr hsub ρ hρ => h.2.2 t r ht hr hsub ρ hρ) hfin hsmall

/-- **Uniqueness of the stopping time, one inequality** (deterministic). If `Λ₁` and `Λ₂` stop at `∂B_{1/2}` at times
`T₁` and `T₂`, agree on `(0, min T₁ T₂)`, and `Λ₂` is monotone and grows strictly on `(0, T₂)`, then `T₂ ≤ T₁`. -/
theorem IsStoppedAtHalfBall.le_of_eqOn {Λ₁ Λ₂ : ℝ → Set ℂ} {T₁ T₂ : ℝ} (h₁ : IsStoppedAtHalfBall Λ₁ T₁)
    (h₂ : IsStoppedAtHalfBall Λ₂ T₂) (heq : EqOn Λ₂ Λ₁ (Ioo 0 (min T₁ T₂)))
    (hmono : MonotoneOn Λ₂ (Ioo 0 T₂)) (hgrow : IsStrictlyGrowingOn Λ₂ T₂) : T₂ ≤ T₁ := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨u, hu, -⟩ := h₁.2 0 (by norm_num)
  set s : ℝ := T₁ + (T₂ - T₁) / 3 with hs
  set t : ℝ := T₁ + 2 * (T₂ - T₁) / 3 with ht
  have hT₁ : 0 < T₁ := hu.1.trans hu.2
  have hs0 : 0 < s := by rw [hs]; linarith
  have hst : s < t := by rw [hs, ht]; linarith
  have htT : t < T₂ := by rw [ht]; linarith
  have hsT : s < T₂ := hst.trans htT
  have hcl : closure (Λ₂ s) ⊆ ball 0 (1 / 2) :=
    (hgrow s t hs0 hst htT).trans (h₂.1 t ⟨hs0.trans hst, htT⟩)
  obtain ⟨r', hr', hsub⟩ := exists_lt_subset_ball isClosed_closure hcl
  obtain ⟨v, hv, hnot⟩ := h₁.2 r' hr'
  apply hnot
  have hv2 : v ∈ Ioo 0 (min T₁ T₂) := ⟨hv.1, lt_min hv.2 (hv.2.trans hlt)⟩
  rw [← heq hv2]
  have hvs : v ≤ s := by rw [hs]; linarith [hv.2]
  exact (hmono ⟨hv.1, hv.2.trans hlt⟩ ⟨hs0, hsT⟩ hvs).trans (subset_closure.trans hsub)

/-- **Uniqueness of the stopping time** (deterministic): two monotone, strictly growing families which stop at
`∂B_{1/2}` at times `T₁`, `T₂` and agree on `(0, min T₁ T₂)` have `T₁ = T₂`. -/
theorem IsStoppedAtHalfBall.eq_of_eqOn {Λ₁ Λ₂ : ℝ → Set ℂ} {T₁ T₂ : ℝ} (h₁ : IsStoppedAtHalfBall Λ₁ T₁)
    (h₂ : IsStoppedAtHalfBall Λ₂ T₂) (heq : EqOn Λ₂ Λ₁ (Ioo 0 (min T₁ T₂)))
    (hmono₁ : MonotoneOn Λ₁ (Ioo 0 T₁)) (hmono₂ : MonotoneOn Λ₂ (Ioo 0 T₂))
    (hgrow₁ : IsStrictlyGrowingOn Λ₁ T₁) (hgrow₂ : IsStrictlyGrowingOn Λ₂ T₂) : T₁ = T₂ := by
  refine le_antisymm (h₂.le_of_eqOn h₁ ?_ hmono₁ hgrow₁) (h₁.le_of_eqOn h₂ heq hmono₂ hgrow₂)
  rw [min_comm]
  exact heq.symm

/-- **Lemma 2.4 for `h^ℂ - γ log |·|` (existence).** For the whole-plane GFF `h^ℂ` and the LQG measure `μ` of
`h^ℂ - γ log |·|`, a.s. there is a family of Lemma 2.4 for `μ`. Proved from HB22 in
`wholePlaneHalfBallFamilyStep_of_hb` (`MatedCRT/Proofs/Sec2/ConeHarmonicBallsUpToFixedTime/WholePlane.lean`), and
from the two steps above in `wholePlaneHalfBallFamilyStep_of_steps`. -/
def WholePlaneHalfBallFamilyStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → ∀ᵐ ω ∂P, HasConeHarmonicBallsUpToHalfBall (μ ω)

/-- `WholePlaneHalfBallFamilyStep` from the existence of a family of Theorem 2.3 for `h^ℂ - γ log |·|` and its small
time behaviour (stopping at `∂B_{1/2}`). -/
theorem wholePlaneHalfBallFamilyStep_of_steps (h1 : WholePlaneConeHarmonicBallsStep)
    (h2 : WholePlaneHarmonicBallsSmallTimeStep) : WholePlaneHalfBallFamilyStep := by
  intro γ hγ0 hγ2 Ω' _ P' hC' hcirc' μ' hP' hgff hlqg
  filter_upwards [h1 γ hγ0 hγ2 Ω' P' hC' hcirc' μ' hP' hgff hlqg,
    h2 γ hγ0 hγ2 Ω' P' hC' hcirc' μ' hP' hgff hlqg, hlqg] with ω hfam hsmall hlim
  obtain ⟨Λ, hΛ⟩ := hfam
  have := hlim.isLocallyFiniteMeasure
  exact hasConeHarmonicBallsUpToHalfBall_of_isConeHarmonicBallFamily hΛ measure_ball_lt_top.ne
    (hsmall Λ hΛ (1 / 2) (by norm_num))

/-- **Existence in Lemma 2.4** from the whole-plane case: transfer of the event of Lemma 2.4 from `h^ℂ - γ log |·|` to
the quantum cone through the equality in law of the restrictions to `B_1`. -/
theorem ae_hasConeHarmonicBallsUpToHalfBall_of_wholePlane (h0 : WholePlaneLogLQGExistenceStep)
    (hwp : WholePlaneHalfBallFamilyStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) : ∀ᵐ ω ∂P, HasConeHarmonicBallsUpToHalfBall (μ ω) := by
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨Ω', _, P', hC', hcirc', μ', hP', hgff, hlqg⟩ := h0 γ hγ0 hγ2
  obtain ⟨S, hS, hcS, hgS⟩ := h4 γ hγ0 hγ2
  -- the event of Lemma 2.4 holds a.s. for `h^ℂ - γ log |·|`
  have hE' : ∀ᵐ ω ∂P', HasConeHarmonicBallsUpToHalfBall (μ' ω) := hwp γ hγ0 hγ2 Ω' P' hC' hcirc' μ' hP' hgff hlqg
  have hgS' : ∀ᵐ ω ∂P', unitBallCircleProcess (fieldCircleAverage γ (hcirc' ω)) ∈ S := by
    filter_upwards [hE', hgS Ω' P' hC' hcirc' μ' hP' hgff hlqg] with ω hω hiff
    exact hiff.1 hω
  -- the law of the restriction to `B_1`
  have hmeas : Measurable fun ω => unitBallCircleProcess (hcirc ω) :=
    measurable_pi_iff.2 fun p : UnitBallCircle => hcone.2.1.measurable_circle p.1.1.1 p.1.2 p.1.1.2
  have hlaw := h3 γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 Ω' P' hC' hcirc' hP' hgff
  have hmeas' : Measurable fun ω => unitBallCircleProcess (fieldCircleAverage γ (hcirc' ω)) :=
    measurable_pi_iff.2 fun p : UnitBallCircle =>
      (hgff.measurable_circle p.1.1.1 p.1.2 p.1.1.2).sub_const _
  have hnull : P ((fun ω => unitBallCircleProcess (hcirc ω)) ⁻¹' Sᶜ) = 0 := by
    rw [← Measure.map_apply hmeas hS.compl, hlaw, Measure.map_apply hmeas' hS.compl]
    exact ae_iff.1 hgS'
  have hcS' : ∀ᵐ ω ∂P, unitBallCircleProcess (hcirc ω) ∈ S := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hcS', hcS Ω P hC hcirc μ hcone] with ω hω hiff
  exact hiff.2 hω

/-- **Existence in Lemma 2.4** from the steps. -/
theorem ae_hasConeHarmonicBallsUpToHalfBall (h0 : WholePlaneLogLQGExistenceStep)
    (h1 : WholePlaneConeHarmonicBallsStep) (h2 : WholePlaneHarmonicBallsSmallTimeStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) : ∀ᵐ ω ∂P, HasConeHarmonicBallsUpToHalfBall (μ ω) :=
  ae_hasConeHarmonicBallsUpToHalfBall_of_wholePlane h0 (wholePlaneHalfBallFamilyStep_of_steps h1 h2) h3 h4 hγ0 hγ2
    hcone

/-- **Lemma 2.4** from the whole-plane case, the transfer steps and strict growth. -/
theorem coneHarmonicBallsUpToFixedTime_of_wholePlane (h0 : WholePlaneLogLQGExistenceStep)
    (hwp : WholePlaneHalfBallFamilyStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (h5 : ConeHarmonicBallStrictGrowthStep) :
    ConeHarmonicBallsUpToFixedTimeStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [ae_hasConeHarmonicBallsUpToHalfBall_of_wholePlane h0 hwp h3 h4 hγ0 hγ2 hcone,
    h5 γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hex hgrow
  obtain ⟨T, hT, Λ, hΛ, hst⟩ := hex
  refine ⟨T, hT, Λ, hΛ, hst, fun T' Λ' hT' hΛ' hst' => ?_⟩
  have heq : EqOn Λ' Λ (Ioo 0 (min T T')) := hΛ.eqOn hΛ'
  have hTT : T = T' := hst.eq_of_eqOn hst' heq hΛ.2.1.monotoneOn hΛ'.2.1.monotoneOn (hgrow T Λ hΛ)
    (hgrow T' Λ' hΛ')
  subst hTT
  rw [min_self] at heq
  exact ⟨rfl, heq⟩

/-- **Lemma 2.4** from the steps. -/
theorem coneHarmonicBallsUpToFixedTime_of_steps (h0 : WholePlaneLogLQGExistenceStep)
    (h1 : WholePlaneConeHarmonicBallsStep) (h2 : WholePlaneHarmonicBallsSmallTimeStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (h5 : ConeHarmonicBallStrictGrowthStep) :
    ConeHarmonicBallsUpToFixedTimeStmt :=
  coneHarmonicBallsUpToFixedTime_of_wholePlane h0 (wholePlaneHalfBallFamilyStep_of_steps h1 h2) h3 h4 h5

end MatedCRT
