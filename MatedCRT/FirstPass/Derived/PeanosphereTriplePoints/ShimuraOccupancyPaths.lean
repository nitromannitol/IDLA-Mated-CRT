import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSummationProof

/-!
# The first occupied cell in terms of truncated right tests

Shimura's event `A^n_k` for the cell `[(k - 1)/n, k/n]` is the conjunction of a left test
(`ShimuraCellLeft`: the minimum of `X` on the cell is at most its minimum on the window
`[k/n - 2, (k - 1)/n]`) and a right test (`ShimuraCellRightUpTo`: the minimum of `Y` on the cell
is at most its minimum on `[k/n, c]`, with `c = (k - 1)/n + 2` for the event itself).

For `k ≤ 2 n`, the path lies in `firstCellEvent n k` if and only if the right test at `k` holds,
the left test at `k` holds, and for every earlier cell `i` the left test at `i` together with the
right test at `i` truncated at `k/n` fails (`mem_firstCellEvent_iff`). All these tests are closed
conditions on the path, hence measurable.
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (Path2)

namespace MatedCRT.PeanosphereTriplePoints

/-- The left test of Shimura's event at the cell `[(i - 1)/n, i/n]`. -/
def ShimuraCellLeft (n i : ℕ) (X : ℝ → ℝ) : Prop :=
  ∃ s ∈ Icc (((i : ℝ) - 1) / n) ((i : ℝ) / n),
    ∀ u ∈ Icc ((i : ℝ) / n - 2) (((i : ℝ) - 1) / n), X s ≤ X u

/-- The right test of Shimura's event at the cell `[(i - 1)/n, i/n]`, truncated at `c`. -/
def ShimuraCellRightUpTo (n i : ℕ) (c : ℝ) (Y : ℝ → ℝ) : Prop :=
  ∃ s ∈ Icc (((i : ℝ) - 1) / n) ((i : ℝ) / n), ∀ u ∈ Icc ((i : ℝ) / n) c, Y s ≤ Y u

theorem shimuraCell_iff {n i : ℕ} {X Y : ℝ → ℝ} :
    ShimuraCell n i X Y ↔
      ShimuraCellLeft n i X ∧ ShimuraCellRightUpTo n i (((i : ℝ) - 1) / n + 2) Y :=
  Iff.rfl

/-- The left test holds at `k` and every earlier cell fails its left test or its right test
truncated at `k/n`. -/
def priorCellsFail (n k : ℕ) (X Y : ℝ → ℝ) : Prop :=
  ShimuraCellLeft n k X ∧
    ∀ i ∈ Finset.Ico 1 k, ¬ (ShimuraCellLeft n i X ∧ ShimuraCellRightUpTo n i ((k : ℝ) / n) Y)

theorem cell_iff_trunc {n i k : ℕ} {X Y : ℝ → ℝ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hik : i < k)
    (hk : k ≤ 2 * n) (hRk : ShimuraCellRightUpTo n k (((k : ℝ) - 1) / n + 2) Y) :
    (ShimuraCellLeft n i X ∧ ShimuraCellRightUpTo n i (((i : ℝ) - 1) / n + 2) Y) ↔
      (ShimuraCellLeft n i X ∧ ShimuraCellRightUpTo n i ((k : ℝ) / n) Y) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hik' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
  have hkb : (k : ℝ) / n ≤ ((i : ℝ) - 1) / n + 2 := by
    have : ((i : ℝ) - 1) / n + 2 = ((i : ℝ) - 1 + 2 * n) / n := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) hnR.le
  constructor
  · rintro ⟨hL, s, hs, hR⟩
    exact ⟨hL, s, hs, fun u hu => hR u ⟨hu.1, hu.2.trans hkb⟩⟩
  · rintro ⟨hL, s, hs, hR⟩
    obtain ⟨s', hs', hR'⟩ := hRk
    refine ⟨hL, s, hs, fun u hu => ?_⟩
    by_cases hu2 : u ≤ (k : ℝ) / n
    · exact hR u ⟨hu.1, hu2⟩
    · have hu3 : (k : ℝ) / n ≤ u := (not_le.1 hu2).le
      have hbi : (i : ℝ) / n ≤ ((k : ℝ) - 1) / n :=
        div_le_div_of_nonneg_right (by linarith) hnR.le
      have hai : ((i : ℝ) - 1) / n ≤ ((k : ℝ) - 1) / n :=
        div_le_div_of_nonneg_right (by linarith) hnR.le
      exact (hR s' ⟨hbi.trans hs'.1, hs'.2⟩).trans (hR' u ⟨hu3, by linarith [hu.2]⟩)

/-- For `k ≤ 2 n`, a path lies in `firstCellEvent n k` if and only if the cells `i < k` fail their
truncated tests and the cell `k` carries its full right test. -/
theorem mem_firstCellEvent_iff {n k : ℕ} (hn : 1 ≤ n) (hk2 : k ≤ 2 * n) (p : Path2) :
    p ∈ firstCellEvent n k ↔
      priorCellsFail n k (fun t => (p t).1) (fun t => (p t).2) ∧
        ShimuraCellRightUpTo n k (((k : ℝ) - 1) / n + 2) (fun t => (p t).2) := by
  constructor
  · rintro ⟨⟨hL, hR⟩, hnot⟩
    refine ⟨⟨hL, fun i hi h => ?_⟩, hR⟩
    have hi' := Finset.mem_Ico.1 hi
    exact hnot (mem_iUnion₂.2 ⟨i, hi, (cell_iff_trunc (X := fun t => (p t).1)
      (Y := fun t => (p t).2) hn hi'.1 hi'.2 hk2 hR).2 h⟩)
  · rintro ⟨⟨hL, hprior⟩, hR⟩
    refine ⟨⟨hL, hR⟩, fun hmem => ?_⟩
    obtain ⟨i, hi, hcell⟩ := mem_iUnion₂.1 hmem
    have hi' := Finset.mem_Ico.1 hi
    exact hprior i hi ((cell_iff_trunc (X := fun t => (p t).1)
      (Y := fun t => (p t).2) hn hi'.1 hi'.2 hk2 hR).1 hcell)

theorem measurableSet_cellLeft (n i : ℕ) :
    MeasurableSet {p : Path2 | ShimuraCellLeft n i (fun t => (p t).1)} :=
  (isClosed_exists_min (f := fun x : ℝ × ℝ => x.1) continuous_fst _ _ _ _).measurableSet

theorem measurableSet_cellRightUpTo (n i : ℕ) (c : ℝ) :
    MeasurableSet {p : Path2 | ShimuraCellRightUpTo n i c (fun t => (p t).2)} :=
  (isClosed_exists_min (f := fun x : ℝ × ℝ => x.2) continuous_snd _ _ _ _).measurableSet

theorem measurableSet_priorCellsFail (n k : ℕ) :
    MeasurableSet {p : Path2 | priorCellsFail n k (fun t => (p t).1) (fun t => (p t).2)} := by
  have : {p : Path2 | priorCellsFail n k (fun t => (p t).1) (fun t => (p t).2)} =
      {p : Path2 | ShimuraCellLeft n k (fun t => (p t).1)} ∩
        ⋂ i ∈ Finset.Ico 1 k, ({p : Path2 | ShimuraCellLeft n i (fun t => (p t).1)} ∩
          {p : Path2 | ShimuraCellRightUpTo n i ((k : ℝ) / n) (fun t => (p t).2)})ᶜ := by
    ext p
    simp only [priorCellsFail, mem_inter_iff, mem_iInter, mem_compl_iff, mem_ofPred_eq]
  rw [this]
  exact (measurableSet_cellLeft n k).inter (Finset.measurableSet_biInter _ fun i _ =>
    ((measurableSet_cellLeft n i).inter (measurableSet_cellRightUpTo n i _)).compl)

end MatedCRT.PeanosphereTriplePoints
