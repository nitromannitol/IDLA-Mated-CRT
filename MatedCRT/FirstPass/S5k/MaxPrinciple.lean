import MatedCRT.Defs.Setting
import HarmonicBalls.Steps.Sec11.SubharmonicMaximum

/-!
# First pass: maximum principle on a bounded open set

The maximum principle proves uniqueness of the obstacle solution by the maximum
principle for `u = w₁ - w₂` on `D = {w₁ > w₂}`, a bounded open set on whose frontier `u ≤ 0`. Harmonic-Balls gives the
strong maximum principle only on a connected open set (`IsSubharmonicOn.eqOn_of_attains_upper_bound`,
`HarmonicBalls/Steps/Sec11/SubharmonicMaximum.lean:74`). This file derives the frontier form by passing to the connected
component of a maximiser.
-/

namespace MatedCRT

open Set Filter Topology Metric

/-- **Maximum principle on a bounded open set** (Armitage–Gardiner, the weak maximum principle for subharmonic functions,
here in the strong form on each component). If `u` is subharmonic on a bounded open `D`, continuous on `closure D`, and
`u ≤ 0` on `frontier D`, then `u ≤ 0` on `D`. -/
theorem maximum_principle_of_frontier {D : Set ℂ} {u : ℂ → ℝ} (hD : IsOpen D) (hbdd : Bornology.IsBounded D)
    (hsub : _root_.HarmonicBalls.IsSubharmonicOn D u) (hcont : ContinuousOn u (closure D))
    (hfr : ∀ p ∈ frontier D, u p ≤ 0) : ∀ x ∈ D, u x ≤ 0 := by
  intro x0 hx0
  by_contra hneg
  have hneg' : 0 < u x0 := not_le.mp hneg
  have hcpt : IsCompact (closure D) := hbdd.isCompact_closure
  obtain ⟨x1, hx1, hmax⟩ := hcpt.exists_isMaxOn ⟨x0, subset_closure hx0⟩ hcont
  have hmax' : ∀ y ∈ closure D, u y ≤ u x1 := fun y hy => isMaxOn_iff.mp hmax y hy
  have hx1pos : 0 < u x1 := lt_of_lt_of_le hneg' (hmax' x0 (subset_closure hx0))
  have hx1D : x1 ∈ D := by
    by_contra h
    have hfr1 : x1 ∈ frontier D := ⟨hx1, by rwa [hD.interior_eq]⟩
    linarith [hfr x1 hfr1]
  -- the connected component of the maximiser
  have hC_open : IsOpen (connectedComponentIn D x1) := hD.connectedComponentIn
  have hC_sub : connectedComponentIn D x1 ⊆ D := connectedComponentIn_subset D x1
  have hC_pre : IsPreconnected (connectedComponentIn D x1) := isPreconnected_connectedComponentIn
  have hx1C : x1 ∈ connectedComponentIn D x1 := mem_connectedComponentIn hx1D
  have hsubC : _root_.HarmonicBalls.IsSubharmonicOn (connectedComponentIn D x1) u := by
    unfold _root_.HarmonicBalls.IsSubharmonicOn _root_.HarmonicBalls.IsSuperharmonicOn at hsub ⊢
    exact ⟨hsub.1.mono hC_sub, fun x hx r hr hball => hsub.2 x (hC_sub hx) r hr (hball.trans hC_sub)⟩
  have hcontC : ContinuousOn u (connectedComponentIn D x1) :=
    hcont.mono ((hC_sub.trans subset_closure))
  have hmaxC : ∀ y ∈ connectedComponentIn D x1, u y ≤ u x1 := fun y hy =>
    hmax' y (subset_closure (hC_sub hy))
  have hconst : EqOn u (fun _ => u x1) (connectedComponentIn D x1) :=
    _root_.HarmonicBalls.IsSubharmonicOn.eqOn_of_attains_upper_bound hsubC hcontC hC_open hC_pre hx1C hmaxC
  -- the frontier of the component is nonempty (it is bounded and nonempty, and ℂ is connected)
  have hfrC : (frontier (connectedComponentIn D x1)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hclopen : IsClopen (connectedComponentIn D x1) := isClopen_iff_frontier_eq_empty.mpr hempty
    have huniv : connectedComponentIn D x1 = univ := hclopen.eq_univ ⟨x1, hx1C⟩
    exact NormedSpace.unbounded_univ ℝ ℂ (hbdd.subset (huniv ▸ hC_sub))
  obtain ⟨p, hpfr⟩ := hfrC
  have hpC_cl : p ∈ closure (connectedComponentIn D x1) := hpfr.1
  have hpnC : p ∉ connectedComponentIn D x1 := by
    intro hp
    have := hpfr.2
    rw [hC_open.interior_eq] at this
    exact this hp
  -- u is constant on the closure of the component
  have hup : u p = u x1 := by
    have hEq : EqOn u (fun _ => u x1) (closure (connectedComponentIn D x1)) :=
      EqOn.of_subset_closure hconst (hcont.mono (closure_mono hC_sub)) continuousOn_const subset_closure
        (subset_refl _)
    exact hEq hpC_cl
  -- p is not in D: otherwise its component meets the component of x1
  have hpnD : p ∉ D := by
    intro hpD
    have hpK : p ∈ connectedComponentIn D p := mem_connectedComponentIn hpD
    obtain ⟨q, hqK, hqC⟩ := mem_closure_iff.mp hpC_cl (connectedComponentIn D p)
      (hD.connectedComponentIn) hpK
    have e1 : connectedComponentIn D p = connectedComponentIn D q := connectedComponentIn_eq hqK
    have e2 : connectedComponentIn D x1 = connectedComponentIn D q := connectedComponentIn_eq hqC
    have hpC : p ∈ connectedComponentIn D x1 := by
      rw [e2, ← e1]
      exact hpK
    exact hpnC hpC
  have hpfrD : p ∈ frontier D :=
    ⟨closure_mono hC_sub hpC_cl, by rw [hD.interior_eq]; exact hpnD⟩
  have hpnonpos : u p ≤ 0 := hfr p hpfrD
  linarith

end MatedCRT
