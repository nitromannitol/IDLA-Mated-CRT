import LatticeProb.Bonanno.ReflectedGMS.Limit.GaussianLimitInputAtTarget
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Isotropy of the limiting covariance (GMS21, Proposition 3.1, last assertion)

Gwynne–Miller–Sheffield, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity* (arXiv 1705.11161), Proposition 3.1: "the covariance matrix `Σ` of the limiting Brownian
motion is a positive scalar multiple of the identity matrix", with the proof "The covariance matrix
`Σ` is a scalar multiple of the identity since the law of `(h, η)` is invariant under rotations
about the origin."

This file proves the path-law half of that argument for the anisotropic Brownian targets of the
Lean statement `ReflectedGMS.GMS.Theorem1_16`:

* `covariance_eq_smul_one_of_map_quarterTurnPath`: if the target path law is invariant under the
  quarter turn `(x, y) ↦ (-y, x)` of the plane, its covariance is `c • 1` with `c > 0`;
* `pathLaw_eq_of_convergesWeaklyInC`: a family of path laws has at most one weak limit;
* `covariance_eq_smul_one_of_convergesWeaklyInC_quarterTurn`: if a family of paths and its quarter
  turn both converge weakly to the same target, the covariance of the target is `c • 1`, `c > 0`.

The last statement is the form in which rotation invariance of the law of the cell configuration
enters: the walk on the rotated configuration is the rotated walk.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Filter
open scoped NNReal Topology InnerProductSpace Matrix

open ReflectedGMS.StatementIngredients ReflectedGMS.GaussianLimitIdentification
  ReflectedGMS.TargetPathLawMoments ReflectedGMS.GaussianLimitInputAtTarget

/-- The quarter turn `(x, y) ↦ (-y, x)` of the plane, as a matrix. -/
def quarterTurnMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The quarter turn of the plane applied to every value of a planar path. -/
def quarterTurnPath (f : BouRabeeGwynne.BrownianPath 2) : BouRabeeGwynne.BrownianPath 2 :=
  linearImageBrownianPath quarterTurnMatrix f

theorem measurable_quarterTurnPath : Measurable quarterTurnPath :=
  measurable_linearImageBrownianPath _

/-- A linear map applied to every value of a path is continuous for the topology of uniform
convergence on compact sets. -/
theorem continuous_linearImageBrownianPath (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous (linearImageBrownianPath A) := by
  have hφ : Continuous (fun x : BouRabeeGwynne.Euc 2 =>
      (WithLp.toLp 2 (A *ᵥ fun j => x j) : BouRabeeGwynne.Euc 2)) := by fun_prop
  refine (ContinuousMap.continuous_postcomp (⟨_, hφ⟩ : C(BouRabeeGwynne.Euc 2,
    BouRabeeGwynne.Euc 2))).congr ?_
  intro f
  exact ContinuousMap.ext fun _ => rfl

theorem continuous_quarterTurnPath : Continuous quarterTurnPath :=
  continuous_linearImageBrownianPath _

/-- **Invariance of the target path law under a linear map transports its second moments.** If
the target path law is invariant under `f ↦ A f`, then `(Aᵀθ)ᵀ Σ (Aᵀη) = θᵀ Σ η`. -/
theorem bilinForm_transposeDir_eq_of_map_eq (target : AnisotropicBrownianTarget)
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (h : (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map
        (linearImageBrownianPath A) = target.pathLaw)
    (θ η : EuclideanSpace ℝ (Fin 2)) :
    bilinForm target.covariance (transposeDir A θ) (transposeDir A η) =
      bilinForm target.covariance θ η := by
  have hm : Measurable (fun f : BouRabeeGwynne.BrownianPath 2 => ⟪θ, f 1⟫_ℝ * ⟪η, f 1⟫_ℝ) :=
    (measurable_inner_eval θ 1).mul (measurable_inner_eval η 1)
  have h1 := integral_inner_mul_inner_pathLaw target θ η 1 1
  have h2 := integral_inner_mul_inner_pathLaw target (transposeDir A θ) (transposeDir A η) 1 1
  rw [← h, integral_map (measurable_linearImageBrownianPath A).aemeasurable
    hm.aestronglyMeasurable] at h1
  simp only [inner_linearImage] at h1
  have h3 := h2.symm.trans h1
  have hmin : ((min (1 : ℝ≥0) 1 : ℝ≥0) : ℝ) = 1 := by simp
  rw [hmin, mul_one, mul_one] at h3
  exact h3

/-- **A quarter-turn invariant target law has isotropic covariance.** If the path law of an
anisotropic Brownian target is invariant under the quarter turn of the plane, then its covariance is
`c • 1` for some `c > 0` (GMS21, Proposition 3.1, last assertion, path-law half). -/
theorem covariance_eq_smul_one_of_map_quarterTurnPath (target : AnisotropicBrownianTarget)
    (h : (target.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map quarterTurnPath =
      target.pathLaw) :
    ∃ c : ℝ≥0, 0 < c ∧ target.covariance = (c : ℝ) • 1 := by
  obtain ⟨hsym, hpos⟩ := target.positiveDefinite
  have key := bilinForm_transposeDir_eq_of_map_eq target quarterTurnMatrix h
  set C := target.covariance with hC
  have hform : ∀ θ η : EuclideanSpace ℝ (Fin 2),
      bilinForm C (transposeDir quarterTurnMatrix θ) (transposeDir quarterTurnMatrix η) =
        θ 1 * η 1 * C 0 0 - θ 1 * η 0 * C 0 1 - θ 0 * η 1 * C 1 0 + θ 0 * η 0 * C 1 1 := by
    intro θ η
    simp [bilinForm, transposeDir, quarterTurnMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring
  have hbil : ∀ θ η : EuclideanSpace ℝ (Fin 2),
      bilinForm C θ η =
        θ 0 * η 0 * C 0 0 + θ 0 * η 1 * C 0 1 + θ 1 * η 0 * C 1 0 + θ 1 * η 1 * C 1 1 := by
    intro θ η
    simp [bilinForm, Fin.sum_univ_two]
    ring
  have e00 := key (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  have e01 := key (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  rw [hform, hbil] at e00 e01
  simp at e00 e01
  have h10 := hsym 1 0
  have hpos0 := hpos (Pi.single 0 1) (by simp)
  simp [Fin.sum_univ_two] at hpos0
  refine ⟨(C 0 0).toNNReal, Real.toNNReal_pos.mpr hpos0, ?_⟩
  rw [Real.coe_toNNReal _ hpos0.le]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- **Uniqueness of the weak limit.** If a family of path laws converges weakly in
`C([0,∞), ℂ)` to the path laws of two targets, the two path laws agree. -/
theorem pathLaw_eq_of_convergesWeaklyInC {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2} {T T' : AnisotropicBrownianTarget}
    (h : ReflectedGMS.GMS.ConvergesWeaklyInC Q Y T)
    (h' : ReflectedGMS.GMS.ConvergesWeaklyInC Q Y T') :
    (T.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)) = T'.pathLaw := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have hb : ∃ C, ∀ f, |g f| ≤ C :=
    ⟨‖g‖, fun f => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm f⟩
  exact tendsto_nhds_unique (h g g.continuous hb) (h' g g.continuous hb)

/-- **A weak limit invariant in law under the rotated family is quarter-turn invariant.** If a
family of paths `Y` and its quarter turn `quarterTurnPath ∘ Y` both converge weakly to the path law
of `T`, then that path law is invariant under the quarter turn. -/
theorem map_quarterTurnPath_pathLaw_eq_of_convergesWeaklyInC {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2} {T : AnisotropicBrownianTarget}
    (h : ReflectedGMS.GMS.ConvergesWeaklyInC Q Y T)
    (hq : ReflectedGMS.GMS.ConvergesWeaklyInC Q (fun ε ω => quarterTurnPath (Y ε ω)) T) :
    (T.pathLaw : Measure (BouRabeeGwynne.BrownianPath 2)).map quarterTurnPath = T.pathLaw := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map measurable_quarterTurnPath.aemeasurable
    g.continuous.measurable.aestronglyMeasurable]
  have hb : ∃ C, ∀ f, |g f| ≤ C :=
    ⟨‖g‖, fun f => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm f⟩
  have hbq : ∃ C, ∀ f, |g (quarterTurnPath f)| ≤ C :=
    ⟨‖g‖, fun f => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm (quarterTurnPath f)⟩
  exact tendsto_nhds_unique (h (fun f => g (quarterTurnPath f))
    (g.continuous.comp continuous_quarterTurnPath) hbq) (hq g g.continuous hb)

/-- **Isotropy of the limiting covariance from rotation equivariance of the walk.** If a family of
paths and its quarter turn both converge weakly to the path law of `T`, the covariance of `T` is
`c • 1` with `c > 0`. -/
theorem covariance_eq_smul_one_of_convergesWeaklyInC_quarterTurn {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {Y : ℝ≥0 → Ω → BouRabeeGwynne.BrownianPath 2} {T : AnisotropicBrownianTarget}
    (h : ReflectedGMS.GMS.ConvergesWeaklyInC Q Y T)
    (hq : ReflectedGMS.GMS.ConvergesWeaklyInC Q (fun ε ω => quarterTurnPath (Y ε ω)) T) :
    ∃ c : ℝ≥0, 0 < c ∧ T.covariance = (c : ℝ) • 1 :=
  covariance_eq_smul_one_of_map_quarterTurnPath T
    (map_quarterTurnPath_pathLaw_eq_of_convergesWeaklyInC h hq)

end MatedCRT
