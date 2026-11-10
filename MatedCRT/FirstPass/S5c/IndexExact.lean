import MatedCRT.FirstPass.S5c.IndexPathwise

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), step M4b): the exact measurable index

Harmonic-Balls-LQG Defs/Obstacle.lean:69 defines `cluster μ r z t = {x ∈ B_r | x = z ∨ -t G_{B_r}(z,x) < v(x)}`, with
`v = leastSupersolution μ r z t`. Given exact versions `v e : Ω → ℝ` of `ω ↦ leastSupersolution (μ ω) ρ 0 t e` at the Gaussian
rational points `e` (ExactVersion / VersionField), this file builds the following exact sets of `Ω`:
* `ptSet e` : the point event `e ∈ cluster` (exact, measurable for the exact versions);
* `dclSet d` : `d` lies in the closure of the cluster, written as countably many point events (`mem_closure_iff_ratComplex`,
  valid for an open cluster);
* `idxSet q` : the closure index `q ∈ closureIndex` (IndexPathwise.lean) as a countable Boolean combination.
`idx_ae_eq`: almost surely, on the event where the cluster is open, `ω ∈ idxSet q ↔ q ∈ closureIndex (cluster (μ ω))` for all `q`.
No frozen input; the openness is a hypothesis (it is `isOpen_cluster_of_stopped` under `FrozenGreenDiscPole`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls

/-- The Gaussian rationals are countable. -/
theorem ratComplex_countable : ratComplex.Countable := Set.countable_range _

/-- The point event of the cluster for the family of exact versions `v e`:
`ω ∈ ptSet e` iff `e = 0` or `-t G(0,e) < v e ω` (with the membership `e ∈ B_ρ` for `e ≠ 0`). -/
def ptSet {Ω : Type*} (ρ t : ℝ) (v : ℂ → Ω → ℝ) (e : ℂ) : Set Ω :=
  {ω | e = 0 ∨ (e ∈ ball (0 : ℂ) ρ ∧ -t * greenFunction (ball (0 : ℂ) ρ) 0 e < v e ω)}

/-- The point event agrees with the cluster membership, pointwise, when `v e ω` is the least supersolution value. -/
theorem ptSet_iff {Ω : Type*} {μ : Measure ℂ} {ρ t : ℝ} (hρ : 0 < ρ) {v : ℂ → Ω → ℝ} {ω : Ω} {e : ℂ}
    (hv : e ≠ 0 → e ∈ ball (0 : ℂ) ρ → v e ω = leastSupersolution μ ρ 0 t e) :
    ω ∈ ptSet ρ t v e ↔ e ∈ cluster μ ρ 0 t := by
  unfold ptSet cluster
  rw [mem_sep_iff]
  by_cases he0 : e = 0
  · subst he0
    simp [mem_ball_self hρ]
  · constructor
    · rintro (h | ⟨hb, hlt⟩)
      · exact absurd h he0
      · exact ⟨hb, Or.inr (by rw [← hv he0 hb]; exact hlt)⟩
    · rintro ⟨hb, h | hlt⟩
      · exact absurd h he0
      · exact Or.inr ⟨hb, by rw [hv he0 hb]; exact hlt⟩

/-- A point event is measurable when the exact versions are `m`-measurable at the nonzero points. -/
theorem measurableSet_ptSet {Ω : Type*} {m : MeasurableSpace Ω} {ρ t : ℝ} {v : ℂ → Ω → ℝ}
    (hv : ∀ e : ℂ, e ≠ 0 → Measurable[m] (v e)) (e : ℂ) : MeasurableSet[m] (ptSet ρ t v e) := by
  by_cases he0 : e = 0
  · have h : ptSet ρ t v e = univ := by
      ext ω
      simp [ptSet, he0]
    rw [h]
    exact MeasurableSet.univ
  · have h : ptSet ρ t v e = {_ω : Ω | e ∈ ball (0 : ℂ) ρ} ∩
        {ω | -t * greenFunction (ball (0 : ℂ) ρ) 0 e < v e ω} := by
      ext ω
      simp [ptSet, he0]
    rw [h]
    exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hv e he0))

/-- The closure event of the cluster at `d`: for every `n`, a Gaussian rational `e` within `1/(n+1)` of `d` is a point of the
cluster. -/
def dclSet {Ω : Type*} (ρ t : ℝ) (v : ℂ → Ω → ℝ) (d : ℂ) : Set Ω :=
  ⋂ n : ℕ, ⋃ e ∈ ratComplex ∩ ball d (1 / ((n : ℝ) + 1)), ptSet ρ t v e

theorem measurableSet_imp_mem {Ω : Type*} {m : MeasurableSpace Ω} (p : Prop) {S : Set Ω}
    (hS : MeasurableSet[m] S) : MeasurableSet[m] {ω | p → ω ∈ S} := by
  by_cases hp : p
  · simp only [hp, true_implies]
    exact hS
  · simp only [hp, false_implies]
    exact MeasurableSet.univ

theorem measurableSet_dclSet {Ω : Type*} {m : MeasurableSpace Ω} {ρ t : ℝ} {v : ℂ → Ω → ℝ}
    (hv : ∀ e : ℂ, e ≠ 0 → Measurable[m] (v e)) (d : ℂ) : MeasurableSet[m] (dclSet ρ t v d) :=
  MeasurableSet.iInter fun _n => MeasurableSet.biUnion
    (ratComplex_countable.mono inter_subset_left) fun e _ => measurableSet_ptSet hv e

/-- The closure index as a countable Boolean combination of the closure events. -/
def idxSet {Ω : Type*} (ρ t δ : ℝ) (v : ℂ → Ω → ℝ) (q : ℂ) : Set Ω :=
  {ω | ‖q‖ < ρ ∧ ∃ r : ℚ, δ / 4 < (r : ℝ) ∧ ∀ d ∈ ratComplex, dist d q < (r : ℝ) → ω ∈ dclSet ρ t v d}

theorem measurableSet_idxSet {Ω : Type*} {m : MeasurableSpace Ω} {ρ t δ : ℝ} {v : ℂ → Ω → ℝ}
    (hv : ∀ e : ℂ, e ≠ 0 → Measurable[m] (v e)) (q : ℂ) : MeasurableSet[m] (idxSet ρ t δ v q) := by
  have h : idxSet ρ t δ v q = {_ω : Ω | ‖q‖ < ρ} ∩ ⋃ r : ℚ, ({_ω : Ω | δ / 4 < (r : ℝ)} ∩
      ⋂ d ∈ ratComplex, {ω | dist d q < (r : ℝ) → ω ∈ dclSet ρ t v d}) := by
    ext ω
    simp only [idxSet, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
  rw [h]
  refine (MeasurableSet.const _).inter (MeasurableSet.iUnion fun r => ?_)
  refine (MeasurableSet.const _).inter (MeasurableSet.biInter ratComplex_countable fun d _ => ?_)
  exact measurableSet_imp_mem _ (measurableSet_dclSet hv d)

/-- Closure of an open set through the Gaussian rationals: `d ∈ closure C` iff for every `n` some Gaussian rational `e` in
`B(d, 1/(n+1))` lies in `C`. Requires `C` open (the rationals are dense in every open set, `ratComplex_meets_open`). -/
theorem mem_closure_iff_ratComplex {C : Set ℂ} (hC : IsOpen C) (d : ℂ) :
    d ∈ closure C ↔ ∀ n : ℕ, ∃ e ∈ ratComplex ∩ ball d (1 / ((n : ℝ) + 1)), e ∈ C := by
  constructor
  · intro hd n
    obtain ⟨b, hbC, hbd⟩ := Metric.mem_closure_iff.1 hd (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨e, he, heU⟩ := ratComplex_meets_open (U := C ∩ ball d (1 / ((n : ℝ) + 1)))
      (hC.inter isOpen_ball) ⟨b, hbC, mem_ball.2 (by rw [dist_comm]; exact hbd)⟩
    exact ⟨e, ⟨he, heU.2⟩, heU.1⟩
  · intro h
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨e, he, heC⟩ := h n
    exact ⟨e, heC, by rw [dist_comm]; exact (mem_ball.1 he.2).trans hn⟩

/-- **Exact index is almost surely the closure index** (M4b). If the exact versions `v e` of the least supersolution agree
almost surely at the nonzero Gaussian rationals `e ∈ B_ρ`, and the cluster is open almost surely, then almost surely
`ω ∈ idxSet q` iff `q ∈ closureIndex (cluster (μ ω) ρ 0 t) ρ δ`, for every `q`. -/
theorem idx_ae_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ : Ω → Measure ℂ} {ρ t δ : ℝ} (hρ : 0 < ρ)
    {v : ℂ → Ω → ℝ}
    (hv : ∀ᵐ ω ∂P, ∀ e ∈ ratComplex, e ≠ 0 → e ∈ ball (0 : ℂ) ρ → v e ω = leastSupersolution (μ ω) ρ 0 t e)
    (hopen : ∀ᵐ ω ∂P, IsOpen (cluster (μ ω) ρ 0 t)) :
    ∀ᵐ ω ∂P, ∀ q : ℂ, ω ∈ idxSet ρ t δ v q ↔ q ∈ closureIndex (cluster (μ ω) ρ 0 t) ρ δ := by
  filter_upwards [hv, hopen] with ω hvω hopenω
  have hpt : ∀ e ∈ ratComplex, ω ∈ ptSet ρ t v e ↔ e ∈ cluster (μ ω) ρ 0 t := fun e he =>
    ptSet_iff hρ (fun h0 hb => hvω e he h0 hb)
  have hdcl : ∀ d : ℂ, ω ∈ dclSet ρ t v d ↔ d ∈ closure (cluster (μ ω) ρ 0 t) := by
    intro d
    rw [mem_closure_iff_ratComplex hopenω d]
    simp only [dclSet, mem_iInter, mem_iUnion, exists_prop]
    constructor
    · intro h n
      obtain ⟨e, he, hωe⟩ := h n
      exact ⟨e, he, (hpt e he.1).1 hωe⟩
    · intro h n
      obtain ⟨e, he, heC⟩ := h n
      exact ⟨e, he, (hpt e he.1).2 heC⟩
  intro q
  constructor
  · rintro ⟨hq, r, hr, h⟩
    exact ⟨hq, r, hr, fun d hd hdr => (hdcl d).1 (h d hd hdr)⟩
  · rintro ⟨hq, r, hr, h⟩
    exact ⟨hq, r, hr, fun d hd hdr => (hdcl d).2 (h d hd hdr)⟩

end MatedCRT.S5c
