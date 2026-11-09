import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.InfDistTrace
import MatedCRT.FirstPass.S5c.EntranceLevel

/-!
# FIRST PASS, 5.1 stopped clause: null-measurable rational containment events (Gap 2 decoder, G1 reduction)

Operator ruling 21:25 UTC: Gap 2 follows the compact-set decoder repair of CHATGPT-G-hT-G-stopped.md (Borel versions of the closed
sets via eventual rational hitting tests); AE and null-measurable versions are acceptable. The repository lemma
`nullMeasurableSet_lt_infDist_compl_of_trace` (InfDistTrace.lean) is that hitting-test argument: for a random regular-open set `U`
with nonempty complement, the distance tests `{r < infDist x Uᶜ}` are null measurable from the point memberships at a countable
dense family. For an open `U` with nonempty complement, `closedBall z r ⊆ U ↔ r < infDist z Uᶜ`, so the rational containment
events `{ratDisk C ⊆ Λ_q}` are null measurable from the point memberships. This file proves that reduction and the null-measurable
versions of the entrance-level and fixed-time new-mass statements (`hentr` and `hC` in their null-measurable form).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- For an open set `U` with nonempty complement, a closed disk lies in `U` iff its centre is at distance `> r` from `Uᶜ`. -/
theorem closedBall_subset_iff_lt_infDist {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty) (z : ℂ) (r : ℝ) :
    closedBall z r ⊆ U ↔ r < infDist z Uᶜ := by
  constructor
  · intro hsub
    obtain ⟨y, hyU, hyeq⟩ := hU.isClosed_compl.exists_infDist_eq_dist hne z
    have hyn : r < dist z y := by
      by_contra h
      have hyc : y ∈ closedBall z r := mem_closedBall.2 (by rw [dist_comm]; exact not_lt.1 h)
      exact hyU (hsub hyc)
    rw [hyeq]
    exact hyn
  · intro hlt y hy
    by_contra hyU
    have h1 : infDist z Uᶜ ≤ dist z y := infDist_le_dist_of_mem (show y ∈ Uᶜ from hyU)
    have h2 : dist y z ≤ r := mem_closedBall.1 hy
    have h3 := dist_comm z y
    linarith

/-- **Null-measurable rational containment events** (Gap 2 decoder reduction): the events `{ratDisk C ⊆ Λ_q}` at a fixed
positive time are null measurable from the point memberships at the countable dense family (InfDistTrace.lean). -/
theorem nullMeasurableSet_ratDisk_containment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Λ : Ω → ℝ → Set ℂ) (q : ℝ)
    (hreg : ∀ᵐ ω ∂P, interior (closure (Λ ω q)) = Λ ω q)
    (hne : ∀ᵐ ω ∂P, (Λ ω q)ᶜ.Nonempty)
    (hmem : ∀ j : ℕ, NullMeasurableSet {ω | densePoint j ∈ Λ ω q} P)
    (c : ℚ × ℚ) (r : ℚ) : NullMeasurableSet {ω | ratDisk c r ⊆ Λ ω q} P := by
  have hd := nullMeasurableSet_lt_infDist_compl_of_trace P (fun ω => Λ ω q) hreg hne hmem (r : ℝ)
    (⟨(c.1 : ℝ), (c.2 : ℝ)⟩ : ℂ)
  refine hd.congr ?_
  filter_upwards [hreg, hne] with ω hreg' hne'
  apply propext
  have hopen : IsOpen (Λ ω q) := hreg' ▸ isOpen_interior
  exact (closedBall_subset_iff_lt_infDist hopen hne' _ _).symm

/-- **Null-measurable entrance level sets** (`hentr`, null-measurable form): from null-measurable rational containment events
at positive rational times, `{ω | τ_C(Λ ω) = t}` is null measurable for each `t > 0`. -/
theorem nullMeasurableSet_entranceLevel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Λ : Ω → ℝ → Set ℂ}
    {C : Set ℂ} {t : ℝ} (ht : 0 < t) (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0))
    (hC : ∀ q : ℚ, 0 < (q : ℝ) → NullMeasurableSet {ω | C ⊆ Λ ω (q : ℝ)} P) :
    NullMeasurableSet {ω | entranceTime (Λ ω) C = t} P := by
  have hset : {ω | entranceTime (Λ ω) C = t} =
      (⋂ q : ℚ, {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ ω (q : ℝ)}) ∩
        (⋂ s : ℚ, {ω | t < (s : ℝ) → C ⊆ Λ ω (s : ℝ)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact entranceTime_eq_iff ht (hmono ω)
  rw [hset]
  refine NullMeasurableSet.inter (NullMeasurableSet.iInter fun q => ?_)
    (NullMeasurableSet.iInter fun s => ?_)
  · by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) < t
    · have e : {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ ω (q : ℝ)} = {ω | C ⊆ Λ ω (q : ℝ)}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, h.1, h.2, true_implies]
      rw [e]
      exact (hC q h.1).compl
    · have e : {ω | 0 < (q : ℝ) → (q : ℝ) < t → ¬ C ⊆ Λ ω (q : ℝ)} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h1, h2⟩ h
      rw [e]
      exact MeasurableSet.univ.nullMeasurableSet
  · by_cases h : t < (s : ℝ)
    · have e : {ω | t < (s : ℝ) → C ⊆ Λ ω (s : ℝ)} = {ω | C ⊆ Λ ω (s : ℝ)} := by
        ext ω
        simp only [mem_ofPred_eq, h, true_implies]
      rw [e]
      exact hC s (lt_trans ht h)
    · have e : {ω | t < (s : ℝ) → C ⊆ Λ ω (s : ℝ)} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h'
        exact absurd h' h
      rw [e]
      exact MeasurableSet.univ.nullMeasurableSet

/-- Countably many positive atoms of the entrance-time laws, null-measurable version. -/
theorem countable_positive_entrance_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {τ : Ω → ℝ} (hτ : ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | τ ω = t} P) :
    {t : ℝ | 0 < P {ω | 0 < t ∧ τ ω = t}}.Countable := by
  have hmeas : ∀ t : ℝ, NullMeasurableSet {ω | 0 < t ∧ τ ω = t} P := fun t => by
    by_cases ht : 0 < t
    · have e : {ω | 0 < t ∧ τ ω = t} = {ω | τ ω = t} := by
        ext ω
        simp only [mem_ofPred_eq, ht, true_and]
      rw [e]
      exact hτ t ht
    · have e : {ω | 0 < t ∧ τ ω = t} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => ht h.1
      rw [e]
      exact MeasurableSet.empty.nullMeasurableSet
  have hdisj : Pairwise (fun t t' : ℝ =>
      AEDisjoint P {ω | 0 < t ∧ τ ω = t} {ω | 0 < t' ∧ τ ω = t'}) := by
    intro t t' htt'
    refine Disjoint.aedisjoint ?_
    refine Set.disjoint_left.2 ?_
    intro ω h1 h2
    exact htt' (h1.2.symm.trans h2.2)
  exact Measure.countable_meas_pos_of_disjoint_iUnion₀ hmeas hdisj

/-- **Fixed-deterministic-time null event, null-measurable form** (Gap 1 repair with the Gap 2 decoder): the new-mass event at
a fixed time `t > 0` is null, from null-measurable rational containment events and the scaling `hscale`. -/
theorem newMass_null_of_null_containment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Λ : Ω → ℝ → Set ℂ}
    (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0)) (hopen : ∀ ω, ∀ s : ℝ, 0 < s → IsOpen (Λ ω s))
    (hC : ∀ (c : ℚ × ℚ) (r q : ℚ), 0 < (q : ℝ) → NullMeasurableSet {ω | ratDisk c r ⊆ Λ ω (q : ℝ)} P)
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P {ω | NewMassAt (Λ ω) (b * t)} = P {ω | NewMassAt (Λ ω) t})
    (t : ℝ) (ht : 0 < t) : P {ω | NewMassAt (Λ ω) t} = 0 := by
  set E' : ℝ → Set Ω := fun s => {ω | 0 < s ∧ NewMassAt (Λ ω) s} with hE'
  have hscale' : ∀ b s : ℝ, 0 < b → 0 < s → P (E' (b * s)) = P (E' s) := by
    intro b s hb hs
    have e1 : E' (b * s) = {ω | NewMassAt (Λ ω) (b * s)} := by
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨mul_pos hb hs, h⟩⟩
    have e2 : E' s = {ω | NewMassAt (Λ ω) s} := by
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
    rw [e1, e2, hscale b s hb hs]
  have hcount : {s : ℝ | 0 < P (E' s)}.Countable := by
    have hsub : {s : ℝ | 0 < P (E' s)} ⊆
        ⋃ i : (ℚ × ℚ) × ℚ, {s : ℝ | 0 < P {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s}} := by
      intro s hs
      by_contra hno
      have hnull : ∀ i : (ℚ × ℚ) × ℚ, P {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s} = 0 := by
        intro i
        by_contra hi
        exact hno (mem_iUnion.2 ⟨i, pos_iff_ne_zero.2 hi⟩)
      have hcovs : E' s ⊆ ⋃ i : (ℚ × ℚ) × ℚ, {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s} := by
        rintro ω ⟨hs0, hNA⟩
        obtain ⟨c, r, hτ⟩ := exists_entrance_eq_of_newMass hs0 (hmono ω) (hopen ω) hNA
        exact mem_iUnion.2 ⟨(c, r), hs0, hτ⟩
      have hle : P (E' s) ≤
          P (⋃ i : (ℚ × ℚ) × ℚ, {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s}) :=
        measure_mono hcovs
      have h0 : P (⋃ i : (ℚ × ℚ) × ℚ, {ω | 0 < s ∧ entranceTime (Λ ω) (ratDisk i.1 i.2) = s}) = 0 :=
        measure_iUnion_null hnull
      have hs' : 0 < P (E' s) := hs
      exact (not_le.2 hs') (hle.trans_eq h0)
    exact Set.Countable.mono hsub (Set.countable_iUnion fun i =>
      countable_positive_entrance_null P (fun t' ht' =>
        nullMeasurableSet_entranceLevel P ht' hmono (fun q hq => hC i.1 i.2 q hq)))
  have heq : E' t = {ω | NewMassAt (Λ ω) t} := by
    ext ω
    exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
  rw [← heq]
  exact null_of_scale_invariant P E' hscale' hcount t ht

/-- **Fixed-deterministic-time null event from point memberships** (Gap 1 repair, Gap 2 decoder input): the new-mass event at a
fixed time is null from the a.s. regularity and nonemptiness of the complements of `Λ_q` at positive rational times, the
null measurability of point memberships at the countable dense family (the decoder), and the scaling `hscale`. -/
theorem newMass_null_of_point_memberships {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Λ : Ω → ℝ → Set ℂ}
    (hmono : ∀ ω, MonotoneOn (Λ ω) (Ioi 0)) (hopen : ∀ ω, ∀ s : ℝ, 0 < s → IsOpen (Λ ω s))
    (hreg : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ ω ∂P, interior (closure (Λ ω (q : ℝ))) = Λ ω (q : ℝ))
    (hne : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ ω ∂P, (Λ ω (q : ℝ))ᶜ.Nonempty)
    (hmem : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ j : ℕ, NullMeasurableSet {ω | densePoint j ∈ Λ ω (q : ℝ)} P)
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P {ω | NewMassAt (Λ ω) (b * t)} = P {ω | NewMassAt (Λ ω) t})
    (t : ℝ) (ht : 0 < t) : P {ω | NewMassAt (Λ ω) t} = 0 :=
  newMass_null_of_null_containment P hmono hopen
    (fun c r q hq => nullMeasurableSet_ratDisk_containment P Λ (q : ℝ) (hreg q hq) (hne q hq)
      (fun j => hmem q hq j) c r)
    hscale t ht

end MatedCRT.S5c
