import MatedCRT.FirstPass.S6e.Admissible
import MatedCRT.FirstPass.S6e.Universal

/-!
# FIRST PASS: the measurable universal event over the radii (LEMMA68 §6 Steps 1-3, D3)

The critical set (16) (§5.3) and steps 1-3 (§6: the stronger interface at a
measurable radius; the rational and critical checks).

Statement proved: for a measurable upper cutoff `β` and the guarded predicate `PhiG` (write-up (17)), the event
`{ω | ∀ x ∈ [α, β ω], Phi x}` is measurable. Proof: per `ω`, the universal assertion on `[α, β ω]` is equivalent to the
rational-radius checks together with the checks at the finite critical set (16) (`Universal.forall_Icc_of_rat_and_crit`,
with the constancy `Admissible.PhiG_iff_of_avoid`); each check is measurable by `Admissible.measurableSet_Phi` at a
measurable radius. No assumption beyond those of `measurableSet_Phi` and the measurability of `β`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT

namespace Lemma68UniversalEvent

open Lemma68Admissible Lemma68Universal Lemma68Geometry Lemma68Walk

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The finite critical set (16) as a finite list of coordinates: a predicate holds at every point of `critSet` iff it
holds at `α`, `β`, `d_v` for `v ∈ F0 ∪ A`, `2 d_a`, `2 M_a`, and `c_B`, `t_B` for `B ⊆ A`. -/
theorem forall_mem_critSet_iff (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm α β : ℝ) (G : ℝ → Prop) :
    (∀ c ∈ critSet ε η Θ F0 A a s1 βm α β, G c) ↔
      (G α ∧ G β) ∧ (∀ v ∈ F0 ∪ A, G (dd ε η Θ v)) ∧ (G (2 * dd ε η Θ a) ∧ G (2 * ddMax ε η Θ a)) ∧
        (∀ B ∈ A.powerset, G (cRad ε η B) ∧ G (tRad ε s1 βm B)) := by
  unfold critSet
  constructor
  · intro h
    refine ⟨⟨h α (Or.inl (Or.inl (Or.inl (Or.inl rfl)))), h β (Or.inl (Or.inl (Or.inl (Or.inr rfl))))⟩,
      fun v hv => h (dd ε η Θ v) (Or.inl (Or.inl (Or.inr ⟨v, Finset.mem_coe.2 hv, rfl⟩))),
      ⟨h (2 * dd ε η Θ a) (Or.inl (Or.inr (Or.inl rfl))), h (2 * ddMax ε η Θ a) (Or.inl (Or.inr (Or.inr rfl)))⟩,
      fun B hB => ⟨h (cRad ε η B) (Or.inr (Set.mem_iUnion₂.2 ⟨B, hB, Or.inl rfl⟩)),
        h (tRad ε s1 βm B) (Or.inr (Set.mem_iUnion₂.2 ⟨B, hB, Or.inr rfl⟩))⟩⟩
  · rintro ⟨⟨hα, hβ⟩, hv, ⟨h2, h2'⟩, hB⟩ c hc
    rcases hc with ((((rfl | rfl) | ⟨v, hv', rfl⟩) | (rfl | rfl)) | hc')
    · exact hα
    · exact hβ
    · exact hv v (Finset.mem_coe.1 hv')
    · exact h2
    · exact h2'
    · obtain ⟨B, hB', hc⟩ := Set.mem_iUnion₂.1 hc'
      rcases hc with rfl | rfl
      · exact (hB B hB').1
      · exact (hB B hB').2

/-- Measurability of a predicate over a finite family: `{ω | ∀ i ∈ s, Q i ω}` for a finset `s`. -/
lemma measurableSet_forall_mem_finset {ι : Type*} (s : Finset ι) {Q : ι → Ω → Prop}
    (h : ∀ i, MeasurableSet {ω | Q i ω}) : MeasurableSet {ω | ∀ i ∈ s, Q i ω} := by
  have e : {ω | ∀ i ∈ s, Q i ω} = ⋂ i ∈ s, {ω | Q i ω} := by
    ext ω
    simp
  rw [e]
  exact Finset.measurableSet_biInter s fun i _ => h i

/-- (B2, Step 3 of write-up §6) The guarded predicate `PhiG` (write-up (17)) at a measurable radius `R`, with a
measurable upper cutoff `β`, is measurable in `ω`. -/
lemma measurableSet_PhiG_radius {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ))
    {p : Ω → ℤ → ℤ → ℝ≥0∞} (hp : ∀ u v : ℤ, Measurable fun ω => p ω u v)
    {P : Ω → Measure (ℕ → ℤ)} {a : ℤ} (hP : ∀ ω, IsQuenchedWalk (p ω) a (P ω))
    (ε : ℝ) (Θ F0 A : Finset ℤ) (s1 βm α : ℝ) {β R : Ω → ℝ} (hβ : Measurable β) (hR : Measurable R) :
    MeasurableSet {ω | PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (R ω)} := by
  unfold PhiG
  have h1 : MeasurableSet {ω | α ≤ R ω ∧ R ω ≤ β ω} :=
    (measurableSet_le measurable_const hR).inter (measurableSet_le hR hβ)
  have h2 : MeasurableSet {ω | Phi ε (η ω) Θ F0 A a s1 βm (P ω) (R ω)} :=
    measurableSet_Phi hη hp hP ε Θ F0 A s1 βm hR
  exact MeasurableSet.imp h1 h2

/-- (B2, Step 3) The critical-radius checks: the event that the guarded predicate holds at every point of the finite
critical set (16) is measurable. -/
lemma measurableSet_critChecks {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ))
    {p : Ω → ℤ → ℤ → ℝ≥0∞} (hp : ∀ u v : ℤ, Measurable fun ω => p ω u v)
    {P : Ω → Measure (ℕ → ℤ)} {a : ℤ} (hP : ∀ ω, IsQuenchedWalk (p ω) a (P ω))
    (ε : ℝ) (Θ F0 A : Finset ℤ) (s1 βm α : ℝ) {β : Ω → ℝ} (hβ : Measurable β) :
    MeasurableSet {ω | ∀ c ∈ critSet ε (η ω) Θ F0 A a s1 βm α (β ω),
      PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) c} := by
  have hG : ∀ R : Ω → ℝ, Measurable R → MeasurableSet {ω | PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (R ω)} :=
    fun R hR => measurableSet_PhiG_radius hη hp hP ε Θ F0 A s1 βm α hβ hR
  have e : {ω | ∀ c ∈ critSet ε (η ω) Θ F0 A a s1 βm α (β ω),
      PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) c} =
      {ω | (PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) α ∧ PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (β ω)) ∧
        (∀ v ∈ F0 ∪ A, PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (dd ε (η ω) Θ v)) ∧
        (PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (2 * dd ε (η ω) Θ a) ∧
          PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (2 * ddMax ε (η ω) Θ a)) ∧
        (∀ B ∈ A.powerset, PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (cRad ε (η ω) B) ∧
          PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (tRad ε s1 βm B))} := by
    ext ω
    exact forall_mem_critSet_iff ε (η ω) Θ F0 A a s1 βm α (β ω)
      (fun c => PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) c)
  rw [e]
  have h1 := (hG (fun _ => α) measurable_const).inter (hG β hβ)
  have h2 := measurableSet_forall_mem_finset (F0 ∪ A)
    (Q := fun v ω => PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (dd ε (η ω) Θ v))
    fun v => hG (fun ω => dd ε (η ω) Θ v) (measurable_dd hη ε Θ v)
  have h3 := (hG (fun ω => 2 * dd ε (η ω) Θ a) ((measurable_dd hη ε Θ a).const_mul 2)).inter
    (hG (fun ω => 2 * ddMax ε (η ω) Θ a) ((measurable_ddMax hη ε Θ a).const_mul 2))
  have h4 := measurableSet_forall_mem_finset A.powerset
    (Q := fun B ω => PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (cRad ε (η ω) B) ∧
      PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (tRad ε s1 βm B))
    fun B => (hG (fun ω => cRad ε (η ω) B) (measurable_cRad hη ε B)).inter
      (hG (fun _ => tRad ε s1 βm B) measurable_const)
  exact h1.inter (h2.inter (h3.inter h4))

/-- (B2, §6 Steps 1-3, D3) The literal universal event: for a measurable upper cutoff `β`, the event that the
admissibility implication `Phi` holds at every radius `x ∈ [α, β ω]` is measurable in `ω`. -/
theorem measurableSet_universal {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ))
    {p : Ω → ℤ → ℤ → ℝ≥0∞} (hp : ∀ u v : ℤ, Measurable fun ω => p ω u v)
    {P : Ω → Measure (ℕ → ℤ)} {a : ℤ} (hP : ∀ ω, IsQuenchedWalk (p ω) a (P ω))
    (ε : ℝ) (Θ F0 A : Finset ℤ) (s1 βm α : ℝ) {β : Ω → ℝ} (hβ : Measurable β) :
    MeasurableSet {ω | ∀ x : ℝ, α ≤ x → x ≤ β ω → Phi ε (η ω) Θ F0 A a s1 βm (P ω) x} := by
  have e : {ω | ∀ x : ℝ, α ≤ x → x ≤ β ω → Phi ε (η ω) Θ F0 A a s1 βm (P ω) x} =
      {ω | ∀ q : ℚ, PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) (q : ℝ)} ∩
        {ω | ∀ c ∈ critSet ε (η ω) Θ F0 A a s1 βm α (β ω),
          PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω) c} := by
    ext ω
    constructor
    · intro h
      exact ⟨fun q hq => h q hq.1 hq.2, fun c _ hc => h c hc.1 hc.2⟩
    · rintro ⟨hq, hc⟩ x hαx hxβ
      have key := forall_Icc_of_rat_and_crit (Φ := PhiG ε (η ω) Θ F0 A a s1 βm (P ω) α (β ω))
        (critSet_finite ε (η ω) Θ F0 A a s1 βm α (β ω))
        (Or.inr (mem_critSet_alpha ε (η ω) Θ F0 A a s1 βm α (β ω)))
        (fun r s hrs hC => PhiG_iff_of_avoid hrs hC)
        (fun q _ _ => hq q) (fun c hcC _ _ => hc c hcC) x hαx hxβ
      exact key ⟨hαx, hxβ⟩
  rw [e, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun q : ℚ => measurableSet_PhiG_radius hη hp hP ε Θ F0 A s1 βm α hβ
    (measurable_const : Measurable fun _ : Ω => (q : ℝ))).inter
    (measurableSet_critChecks hη hp hP ε Θ F0 A s1 βm α hβ)

end Lemma68UniversalEvent

end MatedCRT
