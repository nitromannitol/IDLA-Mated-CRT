import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BrownianMinimum

/-!
# Unique minimizing times of a correlated Brownian coordinate

Uses Leonardo Bonanno's Brownian infrastructure through the project-local `BrownianLocalMin` port (source `MatedCRTHarmonic.MatedCRT.BrownianG0`, commit `31e7483`) and `BrownianMinimum`; the port headers retain their source credits.

Source: `notes/wpn-steps2/steps2-r3.tex`, Section 3, Lemma `lem:bm-minimum-unique`
(r3:534-599), the uniqueness argument at r3:585-599. The separated-interval theorem
`ae_separated_minima_ne` of `BrownianMinimum.lean` (commit 944485f) is used unchanged.

For either coordinate `X` of `IsCorrelatedBM2` and each deterministic `a < b`, the minimum of
`X` over `[a, b]` is attained at exactly one time, almost surely (`ae_unique_minimizer`).

* Existence holds on every path: a continuous path attains its minimum on a compact interval.
* Uniqueness: if `t < t'` were two minimizing times, rationals `p < q` with `t < p < q < t'`
  give closed subintervals `[a, p]` and `[q, b]`, with `a < p` and `q < b`, whose minima both
  equal the minimum over `[a, b]`. This contradicts `ae_separated_minima_ne`. The exceptional
  events are indexed by the countably many rational pairs `(p, q)` (`ae_pairs_separated`).

At one fixed positive mesh `ε`, the middle intervals `[ε j, ε (k - 1)]` with `j, k ∈ ℤ` and
`1 < k - j` satisfy uniqueness for both coordinates simultaneously, almost surely
(`ae_unique_minimizer_grid`). This is one countable intersection at that mesh. No event common
to all real meshes is claimed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MatedCRT.SeparatedMinimum

/-! ### Deterministic facts about minima over intervals -/

/-- A continuous function attains its minimum on a compact interval `[a, b]` with `a ≤ b`. -/
lemma exists_min_Icc_of_continuous {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    ∃ t ∈ Icc a b, ∀ s ∈ Icc a b, g t ≤ g s := by
  obtain ⟨t, ht, hmin⟩ :=
    (isCompact_Icc : IsCompact (Icc a b)).exists_isMinOn (nonempty_Icc.2 hab) hg.continuousOn
  exact ⟨t, ht, fun s hs => isMinOn_iff.1 hmin s hs⟩

/-- If `Icc c d ⊆ Icc a b`, `t ∈ Icc c d`, and `g` is minimal at `t` over `Icc a b`, then the
infimum of `g` over `Icc c d` equals `g t`. -/
lemma iInf_Icc_eq_of_isMin {g : ℝ → ℝ} {a b c d t : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (htmem : t ∈ Icc c d) (hmin : ∀ s ∈ Icc a b, g t ≤ g s) :
    (⨅ s : Icc c d, g s) = g t := by
  have : Nonempty (Icc c d) := ⟨⟨t, htmem⟩⟩
  have hbdd : BddBelow (range fun s : Icc c d => g s) := by
    refine ⟨g t, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hmin s (hsub s.2)
  exact le_antisymm (ciInf_le hbdd ⟨t, htmem⟩) (le_ciInf fun s => hmin s (hsub s.2))

/-- Two distinct minimizing times `t < t'` of `g` over `[a, b]` produce a rational pair
`p < q` with `t < p < q < t'`. The minima over `[a, p]` and `[q, b]` both equal the minimum
over `[a, b]`, so they coincide. This contradicts the separated-interval hypothesis `hsep`. -/
lemma false_of_two_minimizers {g : ℝ → ℝ} {a b t t' : ℝ} (ht : t ∈ Icc a b)
    (ht' : t' ∈ Icc a b) (hmin : ∀ s ∈ Icc a b, g t ≤ g s) (hmin' : ∀ s ∈ Icc a b, g t' ≤ g s)
    (hlt : t < t')
    (hsep : ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < b →
      (⨅ s : Icc a (p : ℝ), g s) ≠ ⨅ s : Icc (q : ℝ) b, g s) :
    False := by
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hlt
  obtain ⟨q, hpq, hq2⟩ := exists_rat_btwn hp2
  have hap : a < (p : ℝ) := lt_of_le_of_lt ht.1 hp1
  have hqb : (q : ℝ) < b := lt_of_lt_of_le hq2 ht'.2
  have hsub₁ : Icc a (p : ℝ) ⊆ Icc a b := Icc_subset_Icc le_rfl (hp2.trans_le ht'.2).le
  have hsub₂ : Icc (q : ℝ) b ⊆ Icc a b := Icc_subset_Icc (hap.trans hpq).le le_rfl
  have h₁ : (⨅ s : Icc a (p : ℝ), g s) = g t :=
    iInf_Icc_eq_of_isMin hsub₁ ⟨ht.1, hp1.le⟩ hmin
  have h₂ : (⨅ s : Icc (q : ℝ) b, g s) = g t' :=
    iInf_Icc_eq_of_isMin hsub₂ ⟨hq2.le, ht'.2⟩ hmin'
  have heq : g t = g t' := le_antisymm (hmin t' ht') (hmin' t ht)
  exact hsep p q hap hpq hqb (h₁.trans (heq.trans h₂.symm))

/-! ### Countably many separated-interval events -/

/-- Almost surely, for every rational pair `p < q` with `a < p` and `q < b`, the minima of the
coordinate `i` over `[a, p]` and over `[q, b]` are distinct. There are countably many pairs, each
event is null by `ae_separated_minima_ne`, and pairs outside the range are vacuous. -/
lemma ae_pairs_separated {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) (a b : ℝ) :
    ∀ᵐ ω ∂μ, ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < b →
      (⨅ s : Icc a (p : ℝ), lrCoord i (s : ℝ) ω) ≠ ⨅ s : Icc (q : ℝ) b, lrCoord i (s : ℝ) ω := by
  refine ae_all_iff.2 fun p => ae_all_iff.2 fun q => ?_
  by_cases h : a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b
  · filter_upwards [ae_separated_minima_ne hμ i h.1 h.2.1 h.2.2] with ω hω
    exact fun _ _ _ => hω
  · exact ae_of_all _ fun ω h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ h

/-! ### Unique minimizers on one deterministic interval -/

/-- **Unique minimizing time on a deterministic interval.** For `a < b` and either coordinate of
`IsCorrelatedBM2`, almost surely the minimum over `[a, b]` is attained at exactly one time. -/
theorem ae_unique_minimizer {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂μ, ∃! t : ℝ, t ∈ Icc a b ∧ ∀ s ∈ Icc a b, lrCoord i t ω ≤ lrCoord i s ω := by
  filter_upwards [ae_pairs_separated hμ i a b] with ω hω
  obtain ⟨t, ht, hmin⟩ := exists_min_Icc_of_continuous (lrCoord_continuous i ω) hab.le
  refine ⟨t, ⟨ht, hmin⟩, fun t' ht'' => ?_⟩
  obtain ⟨ht', hmin'⟩ := ht''
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact (false_of_two_minimizers (g := fun s => lrCoord i s ω) ht ht' hmin hmin' hlt hω).elim
  · exact heq.symm
  · exact (false_of_two_minimizers (g := fun s => lrCoord i s ω) ht' ht hmin' hmin hgt hω).elim

/-! ### Simultaneous uniqueness on the middle intervals of one mesh -/

/-- **Unique minimizers on the middle intervals of a fixed mesh.** Fix `ε > 0`. Almost surely, for
both coordinates and every pair `j, k ∈ ℤ` with `1 < k - j`, the minimum of the coordinate over
`[ε j, ε (k - 1)]` is attained at exactly one time. This is one countable intersection at the mesh
`ε`; no event common to all real meshes is claimed. -/
theorem ae_unique_minimizer_grid {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ j k : ℤ, 1 < k - j →
      ∃! t : ℝ, t ∈ Icc (ε * (j : ℝ)) (ε * ((k : ℝ) - 1)) ∧
        ∀ s ∈ Icc (ε * (j : ℝ)) (ε * ((k : ℝ) - 1)), lrCoord i t ω ≤ lrCoord i s ω := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
  by_cases h : 1 < k - j
  · have hjk : (j : ℝ) < (k : ℝ) - 1 := by
      have h' : (1 : ℝ) < (k : ℝ) - (j : ℝ) := by exact_mod_cast h
      linarith
    filter_upwards [ae_unique_minimizer hμ i (mul_lt_mul_of_pos_left hjk hε)] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ fun ω h' => absurd h' h

end MatedCRTHarmonic.MatedCRT.SeparatedMinimum
