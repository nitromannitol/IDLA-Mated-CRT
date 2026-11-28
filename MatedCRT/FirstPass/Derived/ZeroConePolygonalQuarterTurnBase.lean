import MatedCRT.FirstPass.Derived.GMS21CellConfigRotation

/-!
# Plane-rotation helpers for the polygonal configuration

These are the plane-rotation helpers used by the polygonal configuration of the proof of Lemma 3.5 of
Gwynne–Miller–Sheffield (arXiv:1705.11161v5, p. 26), whose law is invariant under rotations about the origin
(proof of Proposition 3.1, p. 24).

* `quarterTurnCurve`, `continuous_quarterTurnCurve`: the quarter turn `t ↦ i η(t)` of a planar curve.
* `quarterTurn_repr`: the quarter turn `quarterTurn` of the Euclidean plane is multiplication by `i` in the complex
  coordinate.
* `cellConfig_eq_of`: two cell configurations with the same cells and the same conductances are equal.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS.GMS

/-- The quarter turn `t ↦ i η(t)` of a planar curve. -/
def quarterTurnCurve (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  (⟨fun z => Complex.I * z, continuous_const.mul continuous_id⟩ : C(ℂ, ℂ)).comp c

theorem continuous_quarterTurnCurve : Continuous quarterTurnCurve :=
  ContinuousMap.continuous_postcomp _

/-- The quarter turn of the plane is multiplication by `i` in the complex coordinate. -/
theorem quarterTurn_repr (z : ℂ) :
    quarterTurn (Complex.orthonormalBasisOneI.repr z) =
      Complex.orthonormalBasisOneI.repr (Complex.I * z) := by
  ext i
  fin_cases i <;> simp

/-- Two cell configurations with the same cells and the same conductances are equal. -/
theorem cellConfig_eq_of {H H' : CellConfig} (h1 : H.cells = H'.cells) (h2 : H.c = H'.c) : H = H' := by
  cases H
  cases H'
  cases h1
  cases h2
  rfl

end MatedCRT.ZeroConePolygonal
