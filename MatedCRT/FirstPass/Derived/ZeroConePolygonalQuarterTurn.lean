import MatedCRT.FirstPass.Derived.ZeroConePolygonalCovariance
import MatedCRT.FirstPass.Derived.ZeroConePolygonalQuarterTurnBase

/-!
# The polygonal configuration of the rotated curve

The law of the polygonal cell configuration used in the proof of Lemma 3.5 of Gwynne–Miller–Sheffield
(arXiv:1705.11161v5, p. 26) is invariant under the quarter turn of the plane, because the law of the decorated
curve is invariant under rotations about the origin (proof of Proposition 3.1, p. 24) and the construction commutes
with rotations. This file records the deterministic part, in terms of the image `isometryGMS T H` of a point of the
GMS space under a linear isometry `T` of the plane.

* `polygonalConfig_mapDatum`: the polygonal configuration of the datum carried by `T` is the image under `T` of the
  polygonal configuration of the datum, the default point being carried along.
* `polygonalConfig_quarterTurnCurve`: the same for the quarter turn and the rotated curve `t ↦ i η(t)` with the same
  edge counts.
* `cellSideMult_quarterTurnCurve`, `polygonalConfig_curveCode_quarterTurn`: the frontier-side multiplicities of
  the cells (arXiv:1705.11161v5, §2.5 and Proposition 2.2, pp. 20-21) are unchanged by the rotation, so the polygonal
  configuration of a curve with the multiplicities read off the curve is carried by the quarter turn.
-/

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS ReflectedGMS.GMS

/-- **The polygonal configuration of the datum carried by a linear isometry `T` is the image under `T`** of the
polygonal configuration of the datum (with the default point carried along). -/
theorem polygonalConfig_mapDatum (T : Plane ≃ₗᵢ[ℝ] Plane) (H₀ : GMSSpace) (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :
    polygonalConfig (isometryGMS T H₀) (mapDatum T w) = isometryGMS T (polygonalConfig H₀ w) := by
  by_cases h : UnitMeshValid w
  · apply Subtype.ext
    exact cellConfig_eq_of (polygonalConfig_mapDatum_cells h H₀ (isometryGMS T H₀))
      (funext fun K => funext fun K' => polygonalConfig_mapDatum_c h H₀ (isometryGMS T H₀) K K')
  · rw [polygonalConfig_of_not_valid (mt unitMeshValid_mapDatum_iff.1 h), polygonalConfig_of_not_valid h]

/-- The quarter turn of a datum is the rotated curve `t ↦ i η(t)` with the same edge counts. -/
theorem mapDatum_quarterTurn (w : C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :
    mapDatum quarterTurn w = (quarterTurnCurve w.1, w.2) := by
  refine Prod.ext (ContinuousMap.ext fun t => ?_) rfl
  show Complex.orthonormalBasisOneI.repr.symm (quarterTurn (Complex.orthonormalBasisOneI.repr (w.1 t))) =
    Complex.I * w.1 t
  rw [quarterTurn_repr, LinearIsometryEquiv.symm_apply_apply]

/-- **The polygonal configuration of the rotated curve is the quarter turn of the polygonal configuration**, for
the same edge counts and the rotated default point. -/
theorem polygonalConfig_quarterTurnCurve (H₀ : GMSSpace) (q : C(ℝ, ℂ)) (m : ℤ → ℤ → ℕ) :
    polygonalConfig (isometryGMS quarterTurn H₀) (quarterTurnCurve q, m) =
      isometryGMS quarterTurn (polygonalConfig H₀ (q, m)) := by
  have h := polygonalConfig_mapDatum quarterTurn H₀ (q, m)
  rwa [mapDatum_quarterTurn] at h

/-- **The frontier-side multiplicities of the rotated curve are those of the curve.** -/
theorem cellSideMult_quarterTurnCurve (q : C(ℝ, ℂ)) (ε : ℝ) (j k : ℤ) :
    cellSideMult ε ⇑(quarterTurnCurve q) j k = cellSideMult ε ⇑q j k :=
  cellSideMult_mul_left Complex.I_ne_zero ε q j k

/-- **The polygonal configuration of a curve with the multiplicities read off the curve is carried by the quarter
turn**: rotating the curve rotates the configuration. -/
theorem polygonalConfig_curveCode_quarterTurn (H₀ : GMSSpace) (q : C(ℝ, ℂ)) :
    polygonalConfig (isometryGMS quarterTurn H₀)
        (quarterTurnCurve q, fun j k => cellSideMult 1 ⇑(quarterTurnCurve q) j k) =
      isometryGMS quarterTurn (polygonalConfig H₀ (q, fun j k => cellSideMult 1 ⇑q j k)) := by
  simp only [cellSideMult_quarterTurnCurve]
  exact polygonalConfig_quarterTurnCurve H₀ q _

end MatedCRT.ZeroConePolygonal
