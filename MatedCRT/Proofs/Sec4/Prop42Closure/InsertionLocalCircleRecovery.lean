import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionCoordinate

/-!
# Simultaneous circle recovery from countably many circles (steps3:603-625)

Internal module; it cites no literature input of its own. It formalizes the countable-to-continuous passage written in
`notes/wpn-steps3/steps3.tex` (lines 603-625): Gaussian covariances identify the joint circle law, and continuity
extends countably many circle identities to every circle contained in the disk. The result is the circle-identity
clause of `LocalDirichletHarmonicDecompositionStep` (`InsertionCoordinate.lean:663-674`; the clause is at line 671),
derived from identities that hold almost surely on each fixed admissible circle.

* `admissibleCircles D = {(r, z) | 0 < r ∧ closedBall z r ⊆ D}` is the parameter set on which the circle-average
  continuity clauses are stated (`IsDirichletGFF.continuous_circle`, `IsWholePlaneGFF.ae_continuousOn_circle`).
* `exists_countable_dense_admissibleCircles`: a countable dense family of admissible circles, from separability of
  `ℝ × ℂ` (Mathlib `TopologicalSpace.exists_countable_dense_subset`). No hypothesis on `D` is used.
* `circle_identity_of_countable_subset` is the deterministic passage, by `Set.EqOn.of_subset_closure`: continuity on
  the admissible set and density of the countable family in it extend the identity to every admissible circle.
* `ae_circle_identity_of_coordinatewise` builds the single full-measure event as the intersection, over the countable
  family, of the coordinatewise almost sure identities (`MeasureTheory.ae_ball_iff`).
* `ae_localDirichlet_circle_clause` is the almost sure conclusion of the Step for `D = Metric.ball c ρ`. Its continuity
  fields come from the imported Gaussian/field infrastructure: the whole-plane GFF interface `IsWholePlaneGFF` and the
  Dirichlet GFF interface `IsDirichletGFF`. Leonardo Bonanno's counterpart of the circle-average field is
  `LQGDimension.IsGFFCircleAverage` (REUSE-LEO.md, section 2).
* `localDirichletHarmonicDecompositionStep_iff_coordinatewise` shows that the Step is equivalent to the coordinatewise
  premise `LocalDirichletCoordinatewiseStep`.

Not proved here: the Gaussian Dirichlet projection, the existence of `h0`, `hcirc0`, `H`, and the almost sure
harmonicity of `H`. These stay explicit producer premises (`hD`, `hHarm`, and the existential in
`LocalDirichletCoordinatewiseStep`). The simultaneous identity is derived, not assumed.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory HarmonicBalls

namespace MatedCRT

/-- The admissible circle parameters of `D ⊆ ℂ`: positive radius and closed ball contained in `D`. This is the index
set of the circle-average continuity clause of `IsDirichletGFF` and of the circle clause of
`LocalDirichletHarmonicDecompositionStep` (`InsertionCoordinate.lean:663-674`). -/
abbrev admissibleCircles (D : Set ℂ) : Set (ℝ × ℂ) :=
  {p | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D}

/-- A countable dense family of admissible circles, from separability of `ℝ × ℂ` (steps3:603-625). No hypothesis on
`D` is needed. -/
theorem exists_countable_dense_admissibleCircles (D : Set ℂ) :
    ∃ S : Set (ℝ × ℂ), S.Countable ∧ S ⊆ admissibleCircles D ∧ admissibleCircles D ⊆ closure S := by
  obtain ⟨S, hSc, hSA, hdense⟩ := TopologicalSpace.exists_countable_dense_subset (admissibleCircles D)
  exact ⟨S, hSc, hSA, hdense⟩

/-- **Deterministic simultaneous-circle recovery** (steps3:603-625: continuity extends countably many circle identities
to every circle contained in `D`). Let `hc` and `hc0` be continuous on the admissible circles of `D`, and `H` continuous
on `D`. If `hc r z = hc0 r z + H z` holds on a subset `S` of the admissible circles that is dense in them, then it holds
on every circle `closedBall z r ⊆ D` with `0 < r`. -/
theorem circle_identity_of_countable_subset {D : Set ℂ} {hc hc0 : ℝ → ℂ → ℝ} {H : ℂ → ℝ}
    (hc_cont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (admissibleCircles D))
    (hc0_cont : ContinuousOn (fun p : ℝ × ℂ => hc0 p.1 p.2) (admissibleCircles D))
    (H_cont : ContinuousOn H D) {S : Set (ℝ × ℂ)} (hSA : S ⊆ admissibleCircles D)
    (hdense : admissibleCircles D ⊆ closure S)
    (hS : ∀ p ∈ S, hc p.1 p.2 = hc0 p.1 p.2 + H p.2) :
    ∀ r z, 0 < r → Metric.closedBall z r ⊆ D → hc r z = hc0 r z + H z := by
  have hH : ContinuousOn (fun p : ℝ × ℂ => H p.2) (admissibleCircles D) :=
    H_cont.comp continuous_snd.continuousOn fun p hp => hp.2 (Metric.mem_closedBall_self hp.1.le)
  have hEq : Set.EqOn (fun p : ℝ × ℂ => hc p.1 p.2) (fun p : ℝ × ℂ => hc0 p.1 p.2 + H p.2)
      (admissibleCircles D) :=
    Set.EqOn.of_subset_closure (fun p hp => hS p hp) hc_cont (hc0_cont.add hH) hSA hdense
  intro r z hr hball
  exact hEq (show (r, z) ∈ admissibleCircles D from ⟨hr, hball⟩)

/-- **Almost sure simultaneous-circle recovery** (steps3:603-625). Suppose that almost surely `hc` and `hc0` are
continuous on the admissible circles of `D` and `H` is continuous on `D`, and that for each admissible circle the
identity holds almost surely (a coordinatewise statement). Then almost surely the identity holds on every admissible
circle simultaneously. The full-measure event is the intersection over a countable dense family of admissible circles;
the simultaneous identity on it comes from `circle_identity_of_countable_subset`. -/
theorem ae_circle_identity_of_coordinatewise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} {hc hc0 : Ω → ℝ → ℂ → ℝ} {H : Ω → ℂ → ℝ}
    (hc_cont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hc ω p.1 p.2) (admissibleCircles D))
    (hc0_cont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hc0 ω p.1 p.2) (admissibleCircles D))
    (H_cont : ∀ᵐ ω ∂P, ContinuousOn (H ω) D)
    (hcoord : ∀ p ∈ admissibleCircles D, ∀ᵐ ω ∂P, hc ω p.1 p.2 = hc0 ω p.1 p.2 + H ω p.2) :
    ∀ᵐ ω ∂P, ∀ r z, 0 < r → Metric.closedBall z r ⊆ D → hc ω r z = hc0 ω r z + H ω z := by
  obtain ⟨S, hSc, hSA, hdense⟩ := exists_countable_dense_admissibleCircles D
  have hS : ∀ᵐ ω ∂P, ∀ p ∈ S, hc ω p.1 p.2 = hc0 ω p.1 p.2 + H ω p.2 :=
    (ae_ball_iff hSc).2 fun p hp => hcoord p (hSA hp)
  filter_upwards [hc_cont, hc0_cont, H_cont, hS] with ω h1 h2 h3 h4
  exact circle_identity_of_countable_subset h1 h2 h3 hSA hdense h4

/-- **Circle clause of `LocalDirichletHarmonicDecompositionStep` from coordinatewise identities**
(`InsertionCoordinate.lean:663-674`, clause at line 671). Let `(hC, hcirc)` be a whole-plane GFF, `(h0, hcirc0)` a
Dirichlet GFF on `D = Metric.ball c ρ`, and `H` an almost surely harmonic remainder. If the identity
`hcirc ω r z = hcirc0 ω r z + H ω z` holds almost surely on each fixed admissible circle, then almost surely `H ω` is
harmonic on the disk and the identity holds on every admissible circle at once. The continuity of `hcirc` on the
admissible circles is the restriction of `IsWholePlaneGFF.ae_continuousOn_circle` (stated on `Ioi 0 ×ˢ univ`); that of
`hcirc0` is `IsDirichletGFF.continuous_circle`. -/
theorem ae_localDirichlet_circle_clause {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {c : ℂ} {ρ : ℝ} {h0 : Ω → (ℂ → ℝ) → ℝ} {hcirc0 : Ω → ℝ → ℂ → ℝ}
    (hD : IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0) {H : Ω → ℂ → ℝ}
    (hHarm : ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω))
    (hcoord : ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ →
      ∀ᵐ ω ∂P, hcirc ω r z = hcirc0 ω r z + H ω z) :
    ∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z := by
  have hcirc_cont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
      (admissibleCircles (Metric.ball c ρ)) :=
    hGFF.ae_continuousOn_circle.mono fun ω h => h.mono fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hsim := ae_circle_identity_of_coordinatewise (D := Metric.ball c ρ) (hc := hcirc) (hc0 := hcirc0)
    (H := H) hcirc_cont hD.continuous_circle (hHarm.mono fun ω h => h.1)
    fun p hp => hcoord p.1 p.2 hp.1 hp.2
  filter_upwards [hHarm, hsim] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Coordinatewise producer premise** for `LocalDirichletHarmonicDecompositionStep` (steps3:609-625). It is the same
existence statement, except that the circle identity is required only on each fixed admissible circle, almost surely.
The Gaussian Dirichlet projection that would produce `(h0, hcirc0, H)` is not formalized and enters as this premise. -/
def LocalDirichletCoordinatewiseStep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ) →
    ∃ (h0 : Ω → (ℂ → ℝ) → ℝ) (hcirc0 : Ω → ℝ → ℂ → ℝ) (H : Ω → ℂ → ℝ),
      IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0 ∧
      (∀ ω r z, ¬ Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc0 ω r z = 0) ∧
      (∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω)) ∧
      ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ →
        ∀ᵐ ω ∂P, hcirc ω r z = hcirc0 ω r z + H ω z

/-- The Step `LocalDirichletHarmonicDecompositionStep` is equivalent to its coordinatewise premise. The forward
direction is immediate, since a simultaneous almost sure identity gives each coordinatewise one. The backward direction
is `ae_localDirichlet_circle_clause`, which derives the simultaneous identity from the coordinatewise ones. -/
theorem localDirichletHarmonicDecompositionStep_iff_coordinatewise :
    LocalDirichletHarmonicDecompositionStep ↔ LocalDirichletCoordinatewiseStep := by
  constructor
  · intro h Ω _ P _ hC hcirc hGFF c ρ hρ hsub
    obtain ⟨h0, hcirc0, H, hD, hz, hsim⟩ := h Ω P hC hcirc hGFF c ρ hρ hsub
    exact ⟨h0, hcirc0, H, hD, hz, hsim.mono fun ω hω => hω.1,
      fun r z hr hball => hsim.mono fun ω hω => hω.2 r z hr hball⟩
  · intro h Ω _ P _ hC hcirc hGFF c ρ hρ hsub
    obtain ⟨h0, hcirc0, H, hD, hz, hHarm, hcoord⟩ := h Ω P hC hcirc hGFF c ρ hρ hsub
    exact ⟨h0, hcirc0, H, hD, hz, ae_localDirichlet_circle_clause hGFF hD hHarm hcoord⟩

end MatedCRT
