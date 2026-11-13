import MatedCRT.FirstPass.Derived.ExitDecomposition
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath
import MatedCRT.FirstPass.Derived.ExitCouplingPath

/-!
# Good walks for the exit coupling of the interpolated walk

Events and elementary facts used to compare the interpolated simple random walks from two nearby
vertices after coupling them at the exit time from a smaller vertex set `A'`
(Berestycki–Gwynne (2020), Proposition 6.12, Step 2).  `walkGood v m A' A ρ ε z` is the set of walks
from `z` that exit `A` in finite time, leave `A'` within the rescaled time `ρ`, and whose
interpolation of speed `m` has oscillation at most `ε` over windows of length at most `ρ` before the
exit time from `A`.  The complement has probability at most the sum of the probabilities of the
three failures (`srwLaw_walkGood_compl_le`).
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingEvents

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingPath

/-- The good walks from `z`: they start at `z`, exit `A` in finite time, leave `A'` within the
rescaled time `ρ`, and have oscillation at most `ε` over windows of length at most `ρ` before their
exit time from `A`. -/
def walkGood (v : ℤ → ℂ) (m : ℝ≥0) (A' A : Set ℤ) (ρ : ℝ≥0) (ε : ℝ) (z : ℤ) : Set (ℕ → ℤ) :=
  {X | X 0 = z ∧ vExitTime A X ≠ ⊤ ∧ ((vExitTime A' X).toNat : ℝ≥0) / m ≤ ρ ∧
    ∀ s t : ℝ≥0, s ≤ ((vExitTime A X).toNat : ℝ≥0) / m → t ≤ ((vExitTime A X).toNat : ℝ≥0) / m →
      dist s t ≤ ρ → dist (interpPathFn v m X s) (interpPathFn v m X t) ≤ ε}

lemma interpPathFn_zero (v : ℤ → ℂ) (m : ℝ) (X : ℕ → ℤ) : interpPathFn v m X 0 = v (X 0) := by
  simp [interpPathFn, linInterp]

lemma measurable_exitTimeScaled (A : Set ℤ) (m : ℝ≥0) :
    Measurable fun X : ℕ → ℤ => ((vExitTime A X).toNat : ℝ≥0) / m :=
  (measurable_of_countable (fun n : ℕ => ((n : ℝ≥0) / m))).comp
    ((measurable_of_countable ENat.toNat).comp (measurable_vExitTime A))

/-- The exit time from `A` of the post-`A'`-exit walk is finite if that of the walk is. -/
lemma vExitTime_postExit_ne_top {A' A : Set ℤ} (hAA : A' ⊆ A) {X : ℕ → ℤ}
    (h : vExitTime A X ≠ ⊤) : vExitTime A (postExit A' X) ≠ ⊤ := by
  have hX := vExitTime_eq_add_pathShift (A := A) (x := X) (T := (vExitTime A' X).toNat)
    (fun n hn => hAA (mem_of_lt_toNat hn))
  intro htop
  apply h
  rw [hX]
  have : vExitTime A (WalkPotential.pathShift (vExitTime A' X).toNat X) = ⊤ := htop
  rw [this]
  simp

/-- The walks from `z` that are not good have probability at most the sum of the probabilities of
a slow exit from `A'` and of a large oscillation, provided the exit time from `A` is a.s. finite. -/
lemma srwLaw_walkGood_compl_le (mult : ℤ → ℤ → ℕ) (z : ℤ) (v : ℤ → ℂ) (m : ℝ≥0)
    (A' A : Set ℤ) (ρ : ℝ≥0) (ε : ℝ) {p₁ p₂ : ℝ≥0∞}
    (hfin : srwLaw mult z {X | vExitTime A X = ⊤} = 0)
    (hT : srwLaw mult z {X | ρ < ((vExitTime A' X).toNat : ℝ≥0) / m} ≤ p₁)
    (hosc : srwLaw mult z {X | ∃ s t : ℝ≥0, s ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧
      t ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧ dist s t ≤ ρ ∧
      ε < dist (interpPathFn v m X s) (interpPathFn v m X t)} ≤ p₂) :
    srwLaw mult z (walkGood v m A' A ρ ε z)ᶜ ≤ p₁ + p₂ := by
  have h0 : srwLaw mult z {X | X 0 ≠ z} = 0 := ae_iff.1 (srwLaw_ae_start mult z)
  have hsub : (walkGood v m A' A ρ ε z)ᶜ ⊆ {X | X 0 ≠ z} ∪ {X | vExitTime A X = ⊤} ∪
      {X | ρ < ((vExitTime A' X).toNat : ℝ≥0) / m} ∪
      {X | ∃ s t : ℝ≥0, s ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧
        t ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧ dist s t ≤ ρ ∧
        ε < dist (interpPathFn v m X s) (interpPathFn v m X t)} := by
    intro X hX
    by_contra hX'
    apply hX
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hX'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hX'
    refine ⟨h1, h2, not_lt.1 h3, ?_⟩
    intro s t hs ht hst
    by_contra hlt
    exact h4 ⟨s, t, hs, ht, hst, not_le.1 hlt⟩
  calc srwLaw mult z (walkGood v m A' A ρ ε z)ᶜ ≤ _ := measure_mono hsub
    _ ≤ srwLaw mult z {X | X 0 ≠ z} + srwLaw mult z {X | vExitTime A X = ⊤} +
        srwLaw mult z {X | ρ < ((vExitTime A' X).toNat : ℝ≥0) / m} +
        srwLaw mult z {X | ∃ s t : ℝ≥0, s ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧
          t ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧ dist s t ≤ ρ ∧
          ε < dist (interpPathFn v m X s) (interpPathFn v m X t)} :=
      (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ p₁ + p₂ := by
      rw [h0, hfin, zero_add, zero_add]
      exact add_le_add hT hosc

end ExitCouplingEvents
end MatedCRT
