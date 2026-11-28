import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceSteps
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath
import LatticeProb.Prob.IndepFunCountableCoordinates
import LatticeProb.Prob.BrownianRestartPath
import LatticeProb.Topology.PolishContinuousMap

/-!
# The outer window of a cone as a measurable functional of the path

For a path `x : ℝ≥0 → ℝ` let `outerWindowOfPath S x` be the path `s ↦ c (ℓ + min s S)` with
`c u = x u.toNNReal` and `ℓ` the last zero of `c` (`lastZeroR`). The outer window of the cone
`coneOuterWindow v S b'` is `outerWindowOfPath S` of the drifted path `t ↦ b'_t + v t`
(`coneOuterWindow_eq`).

On the space `C(ℝ≥0, ℝ)` of continuous paths with its Borel σ-algebra the last zero is measurable
(`measurable_pathLastZero`, via the countable description of the last zero of a continuous path of
`QuantumZipper.WedgeMeas.measurable_lastZero`), hence so is the window
(`measurable_outerWindowOfPath`). A measurable map out of `C(ℝ≥0, ℝ)` extends to a measurable map out
of `ℝ≥0 → ℝ` with the product σ-algebra, because the restriction of continuous paths to a countable
dense set of times is a measurable embedding (Lusin–Souslin; `exists_measurable_extension`). This
gives `coneOuterWindowMeasurable` (`ConeAnnulusAreaLawEquivalenceOuter.lean`).

Source: Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating of trees*
(arXiv:1409.7055), Definition 4.10 for the cone; Kechris, *Classical Descriptive Set Theory*,
Theorem 15.1 (Lusin–Souslin) for the measurable embedding.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-- The last zero `sup {s ≥ 0 : x s = 0}` of a path `x : ℝ≥0 → ℝ`, read through the real-indexed path
`u ↦ x u.toNNReal`. -/
noncomputable def pathLastZero (x : ℝ≥0 → ℝ) : ℝ :=
  lastZeroR fun u : ℝ => x u.toNNReal

/-- The window of a path after its last zero: `s ↦ x (ℓ + min s S)` with `ℓ` the last zero. -/
noncomputable def outerWindowOfPath (S : ℝ) (x : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun s => x ((pathLastZero x + min (s : ℝ) S).toNNReal)

theorem pathLastZero_nonneg (x : ℝ≥0 → ℝ) : 0 ≤ pathLastZero x :=
  Real.sSup_nonneg fun _ hs => hs.1

/-- The outer window of the cone is the window of the drifted path. -/
theorem coneOuterWindow_eq {v S : ℝ} (hS : 0 ≤ S) (b' : ℝ≥0 → ℝ) :
    coneOuterWindow v S b' = outerWindowOfPath S (fun t => b' t + v * t) := by
  have hz : lastZeroR (fun u : ℝ => b' u.toNNReal + v * u) =
      pathLastZero (fun t => b' t + v * t) := by
    unfold lastZeroR pathLastZero
    congr 1
    ext s
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hs => ?_
    rw [Real.coe_toNNReal _ hs]
  funext s
  have hnn : 0 ≤ pathLastZero (fun t => b' t + v * t) + min (s : ℝ) S :=
    add_nonneg (pathLastZero_nonneg _) (le_min (NNReal.coe_nonneg s) hS)
  simp only [coneOuterWindow, outerWindowOfPath]
  rw [hz, Real.coe_toNNReal _ hnn]

theorem measurable_pathLastZero :
    Measurable fun x : C(ℝ≥0, ℝ) => pathLastZero fun t => x t :=
  QuantumZipper.WedgeMeas.measurable_lastZero
    (f := fun (x : C(ℝ≥0, ℝ)) (u : ℝ) => x u.toNNReal)
    (fun x => x.continuous.comp continuous_real_toNNReal)
    (fun u => (continuous_eval_const u.toNNReal).measurable)

theorem measurable_outerWindowOfPath (S : ℝ) :
    Measurable fun x : C(ℝ≥0, ℝ) => outerWindowOfPath S fun t => x t := by
  refine measurable_pi_iff.2 fun s => ?_
  have hev : Measurable fun q : C(ℝ≥0, ℝ) × ℝ≥0 => q.1 q.2 := continuous_eval.measurable
  have hτ : Measurable fun x : C(ℝ≥0, ℝ) =>
      (pathLastZero (fun t => x t) + min (s : ℝ) S).toNNReal :=
    measurable_real_toNNReal.comp (measurable_pathLastZero.add_const _)
  exact hev.comp (measurable_id.prodMk hτ)

/-- A measurable map out of the continuous paths extends to a measurable map out of all paths with
the product σ-algebra. -/
theorem exists_measurable_extension {Y : Type*} [MeasurableSpace Y] [Nonempty Y]
    {G : C(ℝ≥0, ℝ) → Y} (hG : Measurable G) :
    ∃ Φ : (ℝ≥0 → ℝ) → Y, Measurable Φ ∧ ∀ x : C(ℝ≥0, ℝ), Φ (fun t => x t) = G x := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have : PolishSpace C(ℝ≥0, ℝ) := LatticeProb.polishSpace_continuousMap ℝ≥0 ℝ
  have he : MeasurableEmbedding (fun f : C(ℝ≥0, ℝ) => fun i : D => f i) :=
    LatticeProb.Prob.measurableEmbedding_restrict_denseRange
      (D := fun i : D => (i : ℝ≥0)) hDd.denseRange_val
  obtain ⟨g, hg, hgf⟩ := he.exists_measurable_extend hG (fun _ => inferInstance)
  exact ⟨fun y => g fun i : D => y i,
    hg.comp (measurable_pi_iff.2 fun i => measurable_pi_apply _), fun x => congrFun hgf x⟩

end MatedCRT
