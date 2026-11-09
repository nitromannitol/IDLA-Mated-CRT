import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel
import MatedCRT.Defs.Map
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BrownianMinimumUnique

/-!
# Strict excursions between the endpoint cells and the middle minimum

Deterministic component of the adjacent-cell step (steps2-r3:602-630, audited; sha256 88dfb1f9).
Let `X` be continuous and let `bmAdjacent ε X j k` hold (Definition 1.1, eq:edge-map). Let `τ` be the
unique time at which `X` attains its minimum `c` over the middle interval `[ε j, ε k - ε]`. Then the
last level-`c` time `u` in the left endpoint cell `[ε j - ε, ε j]` and the first level-`c` time `v` in
the right endpoint cell `[ε k - ε, ε k]` satisfy

* `u = τ ∨ DirectRel X u τ` and `τ = v ∨ DirectRel X τ v`.

The strict inequality of `DirectRel` is proved, not assumed: the path stays strictly above `c` strictly
between each witness and `τ`. Coincident times are the equality branch.

`DirectRel` is Leonardo Bonanno's frozen definition (`MatedCRTHarmonic.MatedCRT.DirectRel`, module
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel`, adapted from his lean-formalizations at
commit 31e7483), used unchanged.

Distinct local-minimum values are not needed here. The fixed-mesh almost-sure corollary
`MatedCRTHarmonic.MatedCRT.SeparatedMinimum.ae_bmAdjacent_strict_excursions` uses
`ae_unique_minimizer_grid` (steps2-r3:534-599) only at its end.
-/

namespace MatedCRT.StrictAdjacencyExcursions

open Set

/-- **Last level time of an endpoint cell.** Let `X` be continuous, `s₀ ∈ [p, a]` with `X s₀ ≤ c`, and
`c ≤ X a`. Then `u` is the last time in `[p, a]` with `X u = c`, and `c ≤ X w` for all `w ∈ (u, a]`.
The second half is the step "after a last level-`c` time the path cannot fall below `c` and then return
to level at least `c` without another contact". -/
theorem exists_last_level {X : ℝ → ℝ} (hX : Continuous X) {p a c s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc p a) (hXs₀ : X s₀ ≤ c) (hXa : c ≤ X a) :
    ∃ u ∈ Icc p a, X u = c ∧ (∀ t ∈ Icc p a, X t = c → t ≤ u) ∧ ∀ w ∈ Ioc u a, c ≤ X w := by
  have hne : (Icc p a ∩ {s | X s = c}).Nonempty := by
    obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc hs₀.2 hX.continuousOn ⟨hXs₀, hXa⟩
    exact ⟨s, ⟨hs₀.1.trans hs.1, hs.2⟩, hXs⟩
  have hclosed : IsClosed (Icc p a ∩ {s | X s = c}) :=
    isClosed_Icc.inter (isClosed_eq hX continuous_const)
  have hbdd : BddAbove (Icc p a ∩ {s | X s = c}) := ⟨a, fun _ hs => hs.1.2⟩
  obtain ⟨u, hu, hu_max⟩ : ∃ u ∈ Icc p a ∩ {s | X s = c},
      ∀ t ∈ Icc p a ∩ {s | X s = c}, t ≤ u :=
    ⟨sSup (Icc p a ∩ {s | X s = c}), hclosed.csSup_mem hne hbdd, fun t ht => le_csSup hbdd ht⟩
  refine ⟨u, hu.1, hu.2, fun t ht hXt => hu_max t ⟨ht, hXt⟩, fun w hw => ?_⟩
  by_contra hlt
  have hXw : X w < c := not_le.mp hlt
  obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc hw.2 hX.continuousOn ⟨hXw.le, hXa⟩
  have hsA : s ∈ Icc p a ∩ {s | X s = c} :=
    ⟨⟨hu.1.1.trans (hw.1.le.trans hs.1), hs.2⟩, hXs⟩
  have hsu := hu_max s hsA
  linarith [hw.1, hs.1]

/-- **First level time of an endpoint cell** (mirror image of `exists_last_level`). Let `X` be continuous,
`s₁ ∈ [b, q]` with `X s₁ ≤ c`, and `c ≤ X b`. Then `v` is the first time in `[b, q]` with `X v = c`, and
`c ≤ X w` for all `w ∈ [b, v)`. -/
theorem exists_first_level {X : ℝ → ℝ} (hX : Continuous X) {b q c s₁ : ℝ}
    (hs₁ : s₁ ∈ Icc b q) (hXs₁ : X s₁ ≤ c) (hXb : c ≤ X b) :
    ∃ v ∈ Icc b q, X v = c ∧ (∀ t ∈ Icc b q, X t = c → v ≤ t) ∧ ∀ w ∈ Ico b v, c ≤ X w := by
  have hne : (Icc b q ∩ {s | X s = c}).Nonempty := by
    obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc' hs₁.1 hX.continuousOn ⟨hXs₁, hXb⟩
    exact ⟨s, ⟨hs.1, hs.2.trans hs₁.2⟩, hXs⟩
  have hclosed : IsClosed (Icc b q ∩ {s | X s = c}) :=
    isClosed_Icc.inter (isClosed_eq hX continuous_const)
  have hbdd : BddBelow (Icc b q ∩ {s | X s = c}) := ⟨b, fun _ hs => hs.1.1⟩
  obtain ⟨v, hv, hv_min⟩ : ∃ v ∈ Icc b q ∩ {s | X s = c},
      ∀ t ∈ Icc b q ∩ {s | X s = c}, v ≤ t :=
    ⟨sInf (Icc b q ∩ {s | X s = c}), hclosed.csInf_mem hne hbdd, fun t ht => csInf_le hbdd ht⟩
  refine ⟨v, hv.1, hv.2, fun t ht hXt => hv_min t ⟨ht, hXt⟩, fun w hw => ?_⟩
  by_contra hlt
  have hXw : X w < c := not_le.mp hlt
  obtain ⟨s, hs, hXs⟩ := intermediate_value_Icc' hw.1 hX.continuousOn ⟨hXw.le, hXb⟩
  have hsB : s ∈ Icc b q ∩ {s | X s = c} :=
    ⟨⟨hs.1, hs.2.trans (hw.2.le.trans hv.1.2)⟩, hXs⟩
  have hvs := hv_min s hsB
  linarith [hw.2, hs.2]

/-- **Strict excursion witnesses (deterministic component).** Let `X` be continuous and `a ≤ b`. Let
`τ ∈ [a, b]` with `X τ = c`, `c ≤ X t` on `[a, b]`, and `X t = c → t = τ` on `[a, b]` (so `τ` is the
unique minimizer, with value `c`). Let the endpoint cells `[p, a]` and `[b, q]` each contain a time where
`X ≤ c`. Then there are the last level-`c` time `u ∈ [p, a]` and the first level-`c` time `v ∈ [b, q]`
with `u = τ ∨ DirectRel X u τ` and `τ = v ∨ DirectRel X τ v`. -/
theorem exists_strict_excursions {X : ℝ → ℝ} (hX : Continuous X) {p a b q τ c : ℝ}
    (hab : a ≤ b) (hτ : τ ∈ Icc a b) (hXτ : X τ = c)
    (hmin : ∀ t ∈ Icc a b, c ≤ X t) (huniq : ∀ t ∈ Icc a b, X t = c → t = τ)
    (hL : ∃ s ∈ Icc p a, X s ≤ c) (hR : ∃ s ∈ Icc b q, X s ≤ c) :
    ∃ u ∈ Icc p a, ∃ v ∈ Icc b q,
      X u = c ∧ X v = c ∧
      (∀ t ∈ Icc p a, X t = c → t ≤ u) ∧ (∀ t ∈ Icc b q, X t = c → v ≤ t) ∧
      (u = τ ∨ MatedCRTHarmonic.MatedCRT.DirectRel X u τ) ∧
      (τ = v ∨ MatedCRTHarmonic.MatedCRT.DirectRel X τ v) := by
  obtain ⟨s₀, hs₀, hXs₀⟩ := hL
  obtain ⟨s₁, hs₁, hXs₁⟩ := hR
  obtain ⟨u, hu, hXu, hu_max, hLabove⟩ :=
    exists_last_level hX hs₀ hXs₀ (hmin a ⟨le_rfl, hab⟩)
  obtain ⟨v, hv, hXv, hv_min, hRbelow⟩ :=
    exists_first_level hX hs₁ hXs₁ (hmin b ⟨hab, le_rfl⟩)
  -- strictly above c on (u, a]: a level time there would contradict the lastness of u
  have hLgt : ∀ w ∈ Ioc u a, c < X w := fun w hw =>
    lt_of_le_of_ne (hLabove w hw) fun h => by
      have hwu := hu_max w ⟨hu.1.trans hw.1.le, hw.2⟩ h.symm
      linarith [hw.1]
  -- strictly above c on [b, v): a level time there would contradict the firstness of v
  have hRgt : ∀ w ∈ Ico b v, c < X w := fun w hw =>
    lt_of_le_of_ne (hRbelow w hw) fun h => by
      have hvw := hv_min w ⟨hw.1, hw.2.le.trans hv.2⟩ h.symm
      linarith [hw.2]
  -- strictly above c on (u, τ): either in (u, a] or in the middle interval off the unique minimizer
  have hLdir : ∀ w ∈ Ioo u τ, c < X w := by
    intro w hw
    rcases le_total w a with hwa | hwa
    · exact hLgt w ⟨hw.1, hwa⟩
    · refine lt_of_le_of_ne (hmin w ⟨hwa, hw.2.le.trans hτ.2⟩) fun h => ?_
      have hwτ := huniq w ⟨hwa, hw.2.le.trans hτ.2⟩ h.symm
      linarith [hw.2]
  -- strictly above c on (τ, v): either in [b, v) or in the middle interval off the unique minimizer
  have hRdir : ∀ w ∈ Ioo τ v, c < X w := by
    intro w hw
    rcases le_total b w with hbw | hbw
    · exact hRgt w ⟨hbw, hw.2⟩
    · refine lt_of_le_of_ne (hmin w ⟨hτ.1.trans hw.1.le, hbw⟩) fun h => ?_
      have hwτ := huniq w ⟨hτ.1.trans hw.1.le, hbw⟩ h.symm
      linarith [hw.1]
  refine ⟨u, hu, v, hv, hXu, hXv, hu_max, hv_min, ?_, ?_⟩
  · by_cases hut : u = τ
    · exact Or.inl hut
    · have hult : u < τ := lt_of_le_of_ne (hu.2.trans hτ.1) hut
      refine Or.inr ⟨hult, ?_, fun w hw => ?_⟩
      · rw [hXu, hXτ]
      · rw [hXu]
        exact hLdir w hw
  · by_cases htv : τ = v
    · exact Or.inl htv
    · have htv' : τ < v := lt_of_le_of_ne (hτ.2.trans hv.1) htv
      refine Or.inr ⟨htv', ?_, fun w hw => ?_⟩
      · rw [hXτ, hXv]
      · rw [hXτ]
        exact hRdir w hw

/-- **Strict excursion witnesses for an adjacency edge.** Let `ε ≥ 0`, `j < k`, and let
`bmAdjacent ε X j k` hold (the edge of Definition 1.1). Suppose the minimum of `X` over the middle
interval `[ε j, ε k - ε]` is attained at exactly one time `τ`. Then there are `u ∈ [ε j - ε, ε j]`
and `v ∈ [ε k - ε, ε k]`, both at the level `X τ`, with `u = τ ∨ DirectRel X u τ` and
`τ = v ∨ DirectRel X τ v`. -/
theorem bmAdjacent_strict_excursions {ε : ℝ} (hε : 0 ≤ ε) {X : ℝ → ℝ} (hX : Continuous X)
    {j k : ℤ} (hjk : j < k) (hadj : bmAdjacent ε X j k)
    (hU : ∃! t : ℝ, t ∈ Icc (ε * j) (ε * k - ε) ∧ ∀ s ∈ Icc (ε * j) (ε * k - ε), X t ≤ X s) :
    ∃ u ∈ Icc (ε * j - ε) (ε * j), ∃ τ ∈ Icc (ε * j) (ε * k - ε),
      ∃ v ∈ Icc (ε * k - ε) (ε * k),
      X u = X τ ∧ X v = X τ ∧
      (u = τ ∨ MatedCRTHarmonic.MatedCRT.DirectRel X u τ) ∧
      (τ = v ∨ MatedCRTHarmonic.MatedCRT.DirectRel X τ v) := by
  obtain ⟨τ, ⟨hτ, hτmin⟩, hτuniq⟩ := hU
  have hadj' : max (sInf (X '' Icc (ε * j - ε) (ε * j))) (sInf (X '' Icc (ε * k - ε) (ε * k)))
      ≤ sInf (X '' Icc (ε * j) (ε * k - ε)) := hadj
  have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show j + 1 ≤ k by omega)
  have hab : ε * j ≤ ε * k - ε := by nlinarith [mul_nonneg hε (sub_nonneg.mpr hjk')]
  have hpa : ε * j - ε ≤ ε * j := by linarith
  have hcd : ε * k - ε ≤ ε * k := by linarith
  have hK₀ : IsCompact (X '' Icc (ε * j - ε) (ε * j)) := isCompact_Icc.image hX
  have hK₁ : IsCompact (X '' Icc (ε * k - ε) (ε * k)) := isCompact_Icc.image hX
  have hKm : IsCompact (X '' Icc (ε * j) (ε * k - ε)) := isCompact_Icc.image hX
  have hτle : sInf (X '' Icc (ε * j) (ε * k - ε)) ≤ X τ :=
    csInf_le hKm.bddBelow ⟨τ, hτ, rfl⟩
  -- the endpoint-cell minima are attained, and each is at most the middle minimum
  obtain ⟨s₀, hs₀, hXs₀⟩ := hK₀.sInf_mem ((nonempty_Icc.mpr hpa).image X)
  obtain ⟨s₁, hs₁, hXs₁⟩ := hK₁.sInf_mem ((nonempty_Icc.mpr hcd).image X)
  have hL : ∃ s ∈ Icc (ε * j - ε) (ε * j), X s ≤ X τ :=
    ⟨s₀, hs₀, hXs₀.le.trans (le_trans (le_max_left _ _) (hadj'.trans hτle))⟩
  have hR : ∃ s ∈ Icc (ε * k - ε) (ε * k), X s ≤ X τ :=
    ⟨s₁, hs₁, hXs₁.le.trans (le_trans (le_max_right _ _) (hadj'.trans hτle))⟩
  have hmin : ∀ t ∈ Icc (ε * j) (ε * k - ε), X τ ≤ X t := fun t ht => hτmin t ht
  have huniq : ∀ t ∈ Icc (ε * j) (ε * k - ε), X t = X τ → t = τ := fun t ht heq =>
    hτuniq t ⟨ht, fun s hs => by rw [heq]; exact hτmin s hs⟩
  obtain ⟨u, hu, v, hv, hXu, hXv, -, -, hu_dir, hv_dir⟩ :=
    exists_strict_excursions (p := ε * j - ε) (a := ε * j) (b := ε * k - ε) (q := ε * k)
      (τ := τ) (c := X τ) hX hab hτ rfl hmin huniq hL hR
  exact ⟨u, hu, τ, hτ, v, hv, hXu, hXv, hu_dir, hv_dir⟩

/-- **Consumer check: the strict witnesses meet the cells.** Given witnesses `u`, `τ`, `v` as above and the
merge rule for `DirectRel` (the coupling's `merge`), the cells of the vertices `j` and `k` intersect. -/
theorem cell_meet_of_strict_witnesses {ε : ℝ} {η : ℝ → ℂ} {X : ℝ → ℝ} {j k : ℤ}
    (hmerge : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel X s t → η s = η t)
    {u τ v : ℝ} (hu : u ∈ Icc (ε * j - ε) (ε * j)) (hv : v ∈ Icc (ε * k - ε) (ε * k))
    (h1 : u = τ ∨ MatedCRTHarmonic.MatedCRT.DirectRel X u τ)
    (h2 : τ = v ∨ MatedCRTHarmonic.MatedCRT.DirectRel X τ v) :
    (cell ε η j ∩ cell ε η k).Nonempty := by
  have e1 : η u = η τ := by
    rcases h1 with h | h
    · rw [h]
    · exact hmerge u τ h
  have e2 : η τ = η v := by
    rcases h2 with h | h
    · rw [h]
    · exact hmerge τ v h
  refine ⟨η u, ⟨u, ?_, rfl⟩, ⟨v, ?_, (e1.trans e2).symm⟩⟩
  · rw [show ε * ((j : ℝ) - 1) = ε * j - ε by ring]
    exact hu
  · rw [show ε * ((k : ℝ) - 1) = ε * k - ε by ring]
    exact hv

end MatedCRT.StrictAdjacencyExcursions

namespace MatedCRTHarmonic.MatedCRT.SeparatedMinimum

open MeasureTheory Set

/-- **Fixed-mesh almost-sure corollary.** Fix a correlated Brownian pair `μ` and a mesh `ε > 0`. Almost
surely, for both coordinates, every `j, k` with `1 < k - j` and every adjacency edge
`bmAdjacent ε (lrCoord i · ω) j k` carry the strict excursion witnesses. The event is one countable
intersection at the mesh `ε` (`ae_unique_minimizer_grid`); no event common to all real meshes is claimed. -/
theorem ae_bmAdjacent_strict_excursions {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ j k : ℤ, 1 < k - j →
      MatedCRT.bmAdjacent ε (fun t => lrCoord i t ω) j k →
      ∃ u ∈ Icc (ε * j - ε) (ε * j), ∃ τ ∈ Icc (ε * j) (ε * k - ε),
        ∃ v ∈ Icc (ε * k - ε) (ε * k),
        lrCoord i u ω = lrCoord i τ ω ∧ lrCoord i v ω = lrCoord i τ ω ∧
        (u = τ ∨ MatedCRTHarmonic.MatedCRT.DirectRel (fun t => lrCoord i t ω) u τ) ∧
        (τ = v ∨ MatedCRTHarmonic.MatedCRT.DirectRel (fun t => lrCoord i t ω) τ v) := by
  filter_upwards [ae_unique_minimizer_grid hμ hε] with ω hω i j k hjk hadj
  have hU := hω i j k hjk
  rw [show ε * ((k : ℝ) - 1) = ε * k - ε by ring] at hU
  exact MatedCRT.StrictAdjacencyExcursions.bmAdjacent_strict_excursions hε.le (lrCoord_continuous i ω)
    (by omega) hadj hU

end MatedCRTHarmonic.MatedCRT.SeparatedMinimum
