import MatedCRT.FirstPass.Derived.GMS21Lemma33Cone
import MatedCRT.FirstPass.Derived.CellSideMult
import LatticeProb.LQG.MassReparamBorel

/-!
# The reconstruction map of the local configurations of a quantum cone

For the proof of `ConeConfigReconstruction` (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Lemma 3.3, and the
answer to MQ-sbl-18, section "Recovering the formal configuration"), this file defines the Borel map `coneRecon` that
reads a local configuration off the outer data `(e, μ|{δ < |z| < M})` and the residues `(r₋, r₊)` of the two offsets.

Fix time cutoffs `0 < a < L` and an outer radius `M`. On the two time blocks `[-L, -a]` and `[a, L]` of the curve `e`
the relative quantum clock is the mass clock of the measure along `e(±a + ·)` (`LatticeProb.LQG.massClock`), and the
Lebesgue times of the cell endpoints are its inverse (`negBlockTime`, `posBlockTime`) at the relative quantum times
`(j - 1 - r)/n` and `(j - r)/n`. The synthetic label `ℓ ≤ 0` stands for the cell `j = ℓ` of the negative block, the label
`ℓ ≥ 1` for the cell `j = ℓ - 2` of the positive block, so that labels of different blocks are never consecutive.
A label is valid (`reconValid`) when its cell lies in its block; the synthetic data (`reconData`) put the terminal
point `e(t)` of each valid cell and, between valid cells, the multiplicity `0` on the diagonal, `1` for consecutive
labels and otherwise the frontier-side count `cellSideCount` of `e` at the Lebesgue times of the two cells. Invalid
labels get the point `0` and no edges. The map `coneRecon` is the local configuration near the annulus of these data.

The measure is first capped (`cappedMeasure`): restricted to `closedBall 0 M` when finite there, `0` otherwise, so that
it is finite on compact sets for every input; on outer data it is the measure itself.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT

open LatticeProb (CountablePhaseSpace)
open LatticeProb.LQG (massClock massClockInv)

/-- The measure restricted to `closedBall 0 M` if it is finite there, and `0` otherwise. -/
def cappedMeasure (M : ℝ) (μ : Measure ℂ) : Measure ℂ :=
  if μ (closedBall (0 : ℂ) M) < ⊤ then μ.restrict (closedBall (0 : ℂ) M) else 0

instance isFiniteMeasure_cappedMeasure (M : ℝ) (μ : Measure ℂ) : IsFiniteMeasure (cappedMeasure M μ) := by
  unfold cappedMeasure
  split_ifs with h
  · exact ⟨by rw [Measure.restrict_apply_univ]; exact h⟩
  · infer_instance

/-- The Lebesgue time of the relative quantum time `s` on the positive block: `a + massClockInv` along `e(a + ·)`. -/
def posBlockTime (a M : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (s : ℝ) : ℝ :=
  a + massClockInv (cappedMeasure M μ) (fun t => e (a + t)) s

/-- The Lebesgue time of the relative quantum time `s ≤ 0` on the negative block: `-a + massClockInv` along
`e(-a + ·)`. -/
def negBlockTime (a M : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (s : ℝ) : ℝ :=
  -a + massClockInv (cappedMeasure M μ) (fun t => e (-a + t)) s

/-- The quantum mass of the positive block `e([a, L])`. -/
def posBlockMass (a L M : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) : ℝ :=
  (cappedMeasure M μ (e '' Icc a L)).toReal

/-- The quantum mass of the negative block `e([-L, -a])`. -/
def negBlockMass (a L M : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) : ℝ :=
  (cappedMeasure M μ (e '' Icc (-L) (-a))).toReal

/-- The relative quantum times of the two endpoints of the synthetic cell `ℓ` at mesh `1/n` (`ℓ ≤ 0`: cell `ℓ` of the
negative block; `ℓ ≥ 1`: cell `ℓ - 2` of the positive block). -/
def reconRelLeft (n : ℕ) (r : Fin 2 → ℝ) (ℓ : ℤ) : ℝ :=
  if ℓ ≤ 0 then ((ℓ : ℝ) - 1 - r 0) / n else ((ℓ : ℝ) - 3 - r 1) / n

def reconRelRight (n : ℕ) (r : Fin 2 → ℝ) (ℓ : ℤ) : ℝ :=
  if ℓ ≤ 0 then ((ℓ : ℝ) - r 0) / n else ((ℓ : ℝ) - 2 - r 1) / n

/-- The Lebesgue time of a relative quantum time on the block of the label `ℓ`. -/
def reconTime (a M : ℝ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (ℓ : ℤ) (s : ℝ) : ℝ :=
  if ℓ ≤ 0 then negBlockTime a M e μ s else posBlockTime a M e μ s

/-- The synthetic cell `ℓ` lies in its block. -/
def ReconValid (a L M : ℝ) (n : ℕ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (r : Fin 2 → ℝ) (ℓ : ℤ) : Prop :=
  if ℓ ≤ 0 then -negBlockMass a L M e μ < reconRelLeft n r ℓ ∧ reconRelRight n r ℓ ≤ 0
  else 0 ≤ reconRelLeft n r ℓ ∧ reconRelRight n r ℓ < posBlockMass a L M e μ

/-- The frontier-side count of the cells `[t₁, t₂]` and `[t₃, t₄]` of `e`, on increasing quadruples (`0` otherwise). -/
def cellSideCountInc (t₁ t₂ t₃ t₄ : ℝ) (e : C(ℝ, ℂ)) : ℕ :=
  if t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ then cellSideCount t₁ t₂ t₃ t₄ ⇑e else 0

open Classical in
/-- **The synthetic data**: points and multiplicities of the synthetic cells. -/
def reconData (a L M : ℝ) (n : ℕ) (e : C(ℝ, ℂ)) (μ : Measure ℂ) (r : Fin 2 → ℝ) :
    (ℤ → ℂ) × (ℤ → ℤ → ℕ) :=
  (fun ℓ => if ReconValid a L M n e μ r ℓ then e (reconTime a M e μ ℓ (reconRelRight n r ℓ)) else 0,
    fun ℓ ℓ' => if ReconValid a L M n e μ r ℓ ∧ ReconValid a L M n e μ r ℓ' then
      (if ℓ = ℓ' then 0 else if |ℓ - ℓ'| = 1 then 1 else
        cellSideCountInc (reconTime a M e μ (min ℓ ℓ') (reconRelLeft n r (min ℓ ℓ')))
          (reconTime a M e μ (min ℓ ℓ') (reconRelRight n r (min ℓ ℓ')))
          (reconTime a M e μ (max ℓ ℓ') (reconRelLeft n r (max ℓ ℓ')))
          (reconTime a M e μ (max ℓ ℓ') (reconRelRight n r (max ℓ ℓ'))) e)
    else 0)

/-- The residue vector of a marked phase vector, padded with `0`. -/
def residuePair {E : Type*} (x : CountablePhaseSpace E) : Fin 2 → ℝ :=
  fun i => if h : (i : ℕ) < x.1 then x.2.2 ⟨i, h⟩ else 0

/-- **The reconstruction map**: the local configuration near `B_R(0) \ closedBall 0 α` of the synthetic data of the
outer data and the residues. -/
def coneRecon (α R a L M : ℝ) (n : ℕ) (x : CountablePhaseSpace (C(ℝ, ℂ) × Measure ℂ)) : LocalConfig :=
  localConfig (ball (0 : ℂ) R \ closedBall (0 : ℂ) α) (reconData a L M n x.2.1.1 x.2.1.2 (residuePair x))

/-- **The curve event**: the curve maps `[-2a, 2a]` into `B_{α/4}(0)`, every compact interval of times `t` with
`|t| ≥ L/2` outside `closedBall 0 (2R + 2)`, and the two blocks `a ≤ |t| ≤ L` into the annulus `{2δ < |z| < M/2}`. -/
def ReconCurveEvent (α R a L δ M : ℝ) : Set C(ℝ, ℂ) :=
  {e | MapsTo e (Icc (-(2 * a)) (2 * a)) (ball (0 : ℂ) (α / 4)) ∧
    (∀ m : ℕ, MapsTo e (Icc (L / 2) (L / 2 + m) ∪ Icc (-(L / 2) - m) (-(L / 2)))
      (closedBall (0 : ℂ) (2 * R + 2))ᶜ) ∧
    MapsTo e (Icc (-L) (-a) ∪ Icc a L) (offsetOuterAnnulus (2 * δ) (M / 2))}

theorem measurableSet_reconCurveEvent (α R a L δ M : ℝ) : MeasurableSet (ReconCurveEvent α R a L δ M) := by
  have hann : IsOpen (offsetOuterAnnulus (2 * δ) (M / 2)) := isOpen_ball.sdiff isClosed_closedBall
  have h1 : MeasurableSet {e : C(ℝ, ℂ) | MapsTo e (Icc (-(2 * a)) (2 * a)) (ball (0 : ℂ) (α / 4))} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc isOpen_ball).measurableSet
  have h2 : MeasurableSet {e : C(ℝ, ℂ) | ∀ m : ℕ,
      MapsTo e (Icc (L / 2) (L / 2 + m) ∪ Icc (-(L / 2) - m) (-(L / 2))) (closedBall (0 : ℂ) (2 * R + 2))ᶜ} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter fun m => (ContinuousMap.isOpen_setOfPred_mapsTo
      (isCompact_Icc.union isCompact_Icc) isClosed_closedBall.isOpen_compl).measurableSet
  have h3 : MeasurableSet
      {e : C(ℝ, ℂ) | MapsTo e (Icc (-L) (-a) ∪ Icc a L) (offsetOuterAnnulus (2 * δ) (M / 2))} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_Icc.union isCompact_Icc) hann).measurableSet
  exact h1.inter (h2.inter h3)

end MatedCRT
