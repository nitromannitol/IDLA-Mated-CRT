import Mathlib
import MatedCRT.FirstPass.S6e.Geometry
import MatedCRT.FirstPass.S6e.Walk
import MatedCRT.FirstPass.S6e.Universal

/-!
# FIRST PASS: admissibility, the critical radii and `hconst` (LEMMA68 B2)

For a configuration `(Θ, F0, A, a)` (finite
vertex sets `Θ` (the filled set), `F0 = F` (the branch), `A` (the target set), a vertex `a`) and constants `s1, βm`
of (14)-(15), the radius-dependent predicate is
`Φ x := Admissible x → P(exit event of U_x, A) ≤ 1/2` (B1 probability), with `U_x = killed x = {v ∈ F0 : d_v < x} \ Θ`
(write-up (10)) and `Admissible x` the conjunction of (12) for `a`, `A ⊆ U_x`, and the sparsity (15).
The guard `α ≤ x ≤ β` of (17) is included in `PhiG`, so that `hconst` of `Universal.forall_Icc_of_rat_and_crit` holds
for the exact type. The critical set (16) is finite; `d_v, M_a, c_B` are the real parts of the countable formulas
of `Geometry.lean`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT

namespace Lemma68Admissible

open Lemma68Geometry Lemma68Walk

/-- `d_v` as a real number (write-up (3)). -/
noncomputable def dd (ε : ℝ) (η : ℝ → ℂ) (Θ : Finset ℤ) (v : ℤ) : ℝ := (cellDist ε η Θ v).toReal

/-- `M_a` as a real number (write-up (4)). -/
noncomputable def ddMax (ε : ℝ) (η : ℝ → ℂ) (Θ : Finset ℤ) (a : ℤ) : ℝ := (cellDistMax ε η Θ a).toReal

/-- `c_B` as a real number (write-up (5)). -/
noncomputable def cRad (ε : ℝ) (η : ℝ → ℂ) (B : Finset ℤ) : ℝ := (capRadius ε η B).toReal

/-- `t_B = (|B| ε / s₁)^{1/(2β⁻)}` (write-up (14)-(15)). -/
noncomputable def tRad (ε s1 βm : ℝ) (B : Finset ℤ) : ℝ := ((B.card : ℝ) * ε / s1) ^ (1 / (2 * βm))

/-- The killed set `U_x = {v ∈ F0 : d_v < x} \ Θ` (write-up (10)). -/
def killed (ε : ℝ) (η : ℝ → ℂ) (Θ F0 : Finset ℤ) (x : ℝ) : Set ℤ :=
  {v | v ∈ F0 ∧ dd ε η Θ v < x ∧ v ∉ Θ}

/-- The admissibility of the configuration at radius `x`: (12) for the vertex `a`, the inclusion `A ⊆ U_x`, and the
sparsity clause (15) for every nonempty `B ⊆ A`. -/
def Admissible (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm : ℝ) (x : ℝ) : Prop :=
  (2 * dd ε η Θ a ≤ x ∧ x ≤ 2 * ddMax ε η Θ a) ∧ (↑A ⊆ killed ε η Θ F0 x) ∧
    ∀ B ⊆ A, B.Nonempty → x ≤ cRad ε η B ∨ tRad ε s1 βm B < x

/-- The admissibility implication with the quenched exit probability `P` of B1 (write-up §6, Step 2). -/
noncomputable def Phi (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm : ℝ) (P : Measure (ℕ → ℤ))
    (x : ℝ) : Prop :=
  Admissible ε η Θ F0 A a s1 βm x → P (exitEvent (killed ε η Θ F0 x) ↑A) ≤ 1 / 2

/-- The guarded predicate `x ↦ (α ≤ x ≤ β) → Φ x` of write-up (17). -/
noncomputable def PhiG (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm : ℝ) (P : Measure (ℕ → ℤ))
    (α β x : ℝ) : Prop :=
  (α ≤ x ∧ x ≤ β) → Phi ε η Θ F0 A a s1 βm P x

/-- The finite critical set (write-up (16)): `α`, `β`, the values `d_v` for `v ∈ F0 ∪ A`, the boundary values
`2 d_a`, `2 M_a`, and `c_B`, `t_B` for the subsets `B ⊆ A`. -/
noncomputable def critSet (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm α β : ℝ) : Set ℝ :=
  {α, β} ∪ (fun v => dd ε η Θ v) '' ↑(F0 ∪ A) ∪ {2 * dd ε η Θ a, 2 * ddMax ε η Θ a} ∪
    ⋃ B ∈ A.powerset, {cRad ε η B, tRad ε s1 βm B}

lemma critSet_finite (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm α β : ℝ) :
    (critSet ε η Θ F0 A a s1 βm α β).Finite := by
  unfold critSet
  refine Set.Finite.union (Set.Finite.union (Set.Finite.union (Set.toFinite _) ?_) (Set.toFinite _))
    (Set.Finite.biUnion (Finset.finite_toSet _) fun B _ => Set.toFinite _)
  exact (Finset.finite_toSet _).image _

/-- Comparison of a fixed real `c ∉ [r, s]` with two radii `r ≤ s` (write-up §5.4: the four comparison forms). -/
lemma cmp_const {c r s : ℝ} (hrs : r ≤ s) (hc : c ∉ Icc r s) :
    (c < r ↔ c < s) ∧ (r < c ↔ s < c) ∧ (c ≤ r ↔ c ≤ s) ∧ (r ≤ c ↔ s ≤ c) := by
  rcases lt_or_ge c r with h1 | h1
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro h <;> linarith
  rcases lt_or_ge s c with h2 | h2
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro h <;> linarith
  exact absurd ⟨h1, h2⟩ hc

lemma mem_critSet_alpha (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm α β : ℝ) :
    α ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))

lemma mem_critSet_beta (ε : ℝ) (η : ℝ → ℂ) (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm α β : ℝ) :
    β ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))

lemma mem_critSet_dd {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm α β : ℝ} {v : ℤ}
    (hv : v ∈ F0 ∪ A) : dd ε η Θ v ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inl (Or.inl (Or.inr ⟨v, Finset.mem_coe.2 hv, rfl⟩))

lemma mem_critSet_twice_dd {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm α β : ℝ} :
    2 * dd ε η Θ a ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inl (Or.inr (Or.inl rfl))

lemma mem_critSet_twice_max {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm α β : ℝ} :
    2 * ddMax ε η Θ a ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inl (Or.inr (Or.inr rfl))

lemma mem_critSet_cRad {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm α β : ℝ} {B : Finset ℤ}
    (hB : B ⊆ A) : cRad ε η B ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inr (Set.mem_iUnion₂.2 ⟨B, Finset.mem_powerset.2 hB, Or.inl rfl⟩)

lemma mem_critSet_tRad {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm α β : ℝ} {B : Finset ℤ}
    (hB : B ⊆ A) : tRad ε s1 βm B ∈ critSet ε η Θ F0 A a s1 βm α β := by
  unfold critSet
  exact Or.inr (Set.mem_iUnion₂.2 ⟨B, Finset.mem_powerset.2 hB, Or.inr rfl⟩)

/-- (B2, `hconst` of `forall_Icc_of_rat_and_crit`, exact type) If `r ≤ s` and `[r, s]` avoids the critical set, then
the guarded predicate takes the same truth value at `r` and `s` (write-up §5.4-5.5). -/
theorem PhiG_iff_of_avoid {ε : ℝ} {η : ℝ → ℂ} {Θ F0 A : Finset ℤ} {a : ℤ} {s1 βm α β : ℝ}
    {P : Measure (ℕ → ℤ)} {r s : ℝ} (hrs : r ≤ s)
    (hC : ∀ c ∈ critSet ε η Θ F0 A a s1 βm α β, c ∉ Icc r s) :
    PhiG ε η Θ F0 A a s1 βm P α β r ↔ PhiG ε η Θ F0 A a s1 βm P α β s := by
  have hkilled : killed ε η Θ F0 r = killed ε η Θ F0 s := by
    ext v
    by_cases hv : v ∈ F0
    · have hc := cmp_const (c := dd ε η Θ v) hrs
        (hC _ (mem_critSet_dd (η := η) (a := a) (s1 := s1) (α := α) (β := β) (Finset.mem_union_left _ hv)))
      simp only [killed, Set.mem_ofPred_eq, hv, true_and]
      rw [hc.1]
    · simp [killed, hv]
  have hAdm : Admissible ε η Θ F0 A a s1 βm r ↔ Admissible ε η Θ F0 A a s1 βm s := by
    have e1 := (cmp_const (c := 2 * dd ε η Θ a) hrs (hC _ mem_critSet_twice_dd)).2.2.1
    have e2 := (cmp_const (c := 2 * ddMax ε η Θ a) hrs (hC _ mem_critSet_twice_max)).2.2.2
    have e3 : ∀ B ⊆ A, B.Nonempty →
        (r ≤ cRad ε η B ∨ tRad ε s1 βm B < r ↔ s ≤ cRad ε η B ∨ tRad ε s1 βm B < s) := by
      intro B hB _
      have hc1 := (cmp_const (c := cRad ε η B) hrs (hC _ (mem_critSet_cRad (a := a) (s1 := s1) (α := α)
        (β := β) (Θ := Θ) (F0 := F0) (η := η) (ε := ε) hB))).2.2.2
      have hc2 := (cmp_const (c := tRad ε s1 βm B) hrs (hC _ (mem_critSet_tRad (a := a) (α := α) (β := β)
        (Θ := Θ) (F0 := F0) (η := η) (ε := ε) hB))).1
      exact or_congr hc1 hc2
    unfold Admissible
    rw [hkilled]
    exact and_congr (and_congr e1 e2) (and_congr Iff.rfl
      ⟨fun h B hB hne => (e3 B hB hne).1 (h B hB hne), fun h B hB hne => (e3 B hB hne).2 (h B hB hne)⟩)
  unfold PhiG Phi
  rw [hkilled]
  have hα := cmp_const (c := α) hrs (hC _ (mem_critSet_alpha (ε := ε) (η := η) (Θ := Θ) (F0 := F0) (A := A)
    (a := a) (s1 := s1) (βm := βm) (α := α) (β := β)))
  have hβ := cmp_const (c := β) hrs (hC _ (mem_critSet_beta (ε := ε) (η := η) (Θ := Θ) (F0 := F0) (A := A)
    (a := a) (s1 := s1) (βm := βm) (α := α) (β := β)))
  exact imp_congr (and_congr hα.2.2.1 hβ.2.2.2) (imp_congr hAdm Iff.rfl)

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_dd {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (Θ : Finset ℤ)
    (v : ℤ) : Measurable fun ω => dd ε (η ω) Θ v :=
  (measurable_cellDist hη ε Θ v).ennreal_toReal

lemma measurable_ddMax {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (Θ : Finset ℤ)
    (a : ℤ) : Measurable fun ω => ddMax ε (η ω) Θ a :=
  (measurable_cellDistMax hη ε Θ a).ennreal_toReal

lemma measurable_cRad {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ) (B : Finset ℤ) :
    Measurable fun ω => cRad ε (η ω) B :=
  (measurable_capRadius hη ε B).ennreal_toReal

lemma measurableSet_killed_mem {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ)
    (Θ F0 : Finset ℤ) {R : Ω → ℝ} (hR : Measurable R) (v : ℤ) :
    MeasurableSet {ω | v ∈ killed ε (η ω) Θ F0 (R ω)} := by
  show MeasurableSet {ω | v ∈ F0 ∧ dd ε (η ω) Θ v < R ω ∧ v ∉ Θ}
  exact (MeasurableSet.const _).inter ((measurableSet_lt (measurable_dd hη ε Θ v) hR).inter
    (MeasurableSet.const _))

lemma measurableSet_admissible {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ)) (ε : ℝ)
    (Θ F0 A : Finset ℤ) (a : ℤ) (s1 βm : ℝ) {R : Ω → ℝ} (hR : Measurable R) :
    MeasurableSet {ω | Admissible ε (η ω) Θ F0 A a s1 βm (R ω)} := by
  have h1 : MeasurableSet {ω | 2 * dd ε (η ω) Θ a ≤ R ω} :=
    measurableSet_le ((measurable_dd hη ε Θ a).const_mul 2) hR
  have h2 : MeasurableSet {ω | R ω ≤ 2 * ddMax ε (η ω) Θ a} :=
    measurableSet_le hR ((measurable_ddMax hη ε Θ a).const_mul 2)
  have h3 : MeasurableSet {ω | ↑A ⊆ killed ε (η ω) Θ F0 (R ω)} := by
    have e : {ω | ↑A ⊆ killed ε (η ω) Θ F0 (R ω)} =
        ⋂ v ∈ A, {ω | v ∈ killed ε (η ω) Θ F0 (R ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h v hv => h (Finset.mem_coe.2 hv), fun h x hx => h x (Finset.mem_coe.1 hx)⟩
    rw [e]
    exact Finset.measurableSet_biInter A fun v _ => measurableSet_killed_mem hη ε Θ F0 hR v
  have h4 : MeasurableSet {ω | ∀ B ⊆ A, B.Nonempty → R ω ≤ cRad ε (η ω) B ∨ tRad ε s1 βm B < R ω} := by
    have e : {ω | ∀ B ⊆ A, B.Nonempty → R ω ≤ cRad ε (η ω) B ∨ tRad ε s1 βm B < R ω} =
        ⋂ B : Finset ℤ, {ω | B ⊆ A → B.Nonempty → R ω ≤ cRad ε (η ω) B ∨ tRad ε s1 βm B < R ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [e]
    refine MeasurableSet.iInter fun B => MeasurableSet.imp (MeasurableSet.const _)
      (MeasurableSet.imp (MeasurableSet.const _) ?_)
    exact MeasurableSet.union (measurableSet_le hR (measurable_cRad hη ε B))
      (measurableSet_lt measurable_const hR)
  exact (h1.inter h2).inter (h3.inter h4)

/-- (B2, the stronger interface of write-up §6, Steps 1-3) For a measurable radius `R`, the predicate `ω ↦ Φ ω (R ω)`
is measurable: the admissibility is a Boolean combination of threshold events, and the exit probability at `R(ω)` is
measurable by the cylinder argument of B1 (`Walk.measurableSet_quenchedExit_le`) applied to the variable killed set. -/
theorem measurableSet_Phi {η : Ω → ℝ → ℂ} (hη : ∀ q : ℚ, Measurable fun ω => η ω (q : ℝ))
    {p : Ω → ℤ → ℤ → ℝ≥0∞} (hp : ∀ u v : ℤ, Measurable fun ω => p ω u v)
    {P : Ω → Measure (ℕ → ℤ)} {a : ℤ} (hP : ∀ ω, IsQuenchedWalk (p ω) a (P ω))
    (ε : ℝ) (Θ F0 A : Finset ℤ) (s1 βm : ℝ) {R : Ω → ℝ} (hR : Measurable R) :
    MeasurableSet {ω | Phi ε (η ω) Θ F0 A a s1 βm (P ω) (R ω)} := by
  unfold Phi
  exact MeasurableSet.imp (measurableSet_admissible hη ε Θ F0 A a s1 βm hR)
    (measurableSet_quenchedExit_le hp (U := fun ω => killed ε (η ω) Θ F0 (R ω))
      (A := fun _ => (↑A : Set ℤ)) (fun v => measurableSet_killed_mem hη ε Θ F0 hR v)
      (fun v => MeasurableSet.const _) hP (1 / 2))

end Measurability


end Lemma68Admissible

end MatedCRT
