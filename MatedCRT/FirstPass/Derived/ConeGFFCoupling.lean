import MatedCRT.Defs.QuantumCone

/-!
# Coupling the quantum cone with a whole-plane field: the pathwise algebra

Let `(hC, hcirc)` be the pairings and circle averages of a sample of the `γ`-quantum cone (circle average embedding,
Definition 2.1; Duplantier-Miller-Sheffield, Definition 4.10) and let `w` be a path indexed by `ℝ≥0` (later an
independent standard Brownian motion). We replace the radial part `x ↦ h_{|x|}(0)` of the cone by the radial profile

* `h_{|x|}(0) + γ log |x|` for `|x| ≤ 1` (the cone's radial part with the logarithmic singularity removed), and
* `h_1(0) + w(log |x|) - w(0)` for `|x| > 1` (the independent path),

keeping the lateral part `h - h_{|·|}(0)`. The resulting field `h^ℂ` has the cone's lateral part
(`lateralEval_coneCoupling`), its radial process is the cone's radial process minus the drift `γ t` on one side and the
path `w` on the other (`radialProcess_coneCouplingCircle`), and the cone is `h^ℂ - γ log |·|` plus the circle average of
an explicit remainder vanishing on the closed unit disk (`circle_eq_fieldCircleAverage_coneCoupling_add`). These are
deterministic identities; the law of `h^ℂ` (a whole-plane GFF when `w` is an independent Brownian motion) is a
separate statement.
-/

open MeasureTheory Set HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- The radial profile of the coupled field: `h_{|x|}(0) + γ log |x|` on the closed unit disk and
`h_1(0) + w(log |x|) - w(0)` outside it. -/
noncomputable def coneCouplingRadial (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (x : ℂ) : ℝ :=
  if ‖x‖ ≤ 1 then hcirc ‖x‖ 0 + γ * Real.log ‖x‖
  else hcirc 1 0 + (w (Real.toNNReal (Real.log ‖x‖)) - w 0)

/-- The circle averages of the coupled field: the cone's lateral circle average plus the circle average of the radial
profile `coneCouplingRadial`. -/
noncomputable def coneCouplingCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  hcirc r z - Real.circleAverage (fun x => hcirc ‖x‖ 0) z r +
    Real.circleAverage (coneCouplingRadial γ hcirc w) z r

/-- The pairings of the coupled field: the cone's lateral pairing plus the pairing with the radial profile
`coneCouplingRadial`. -/
noncomputable def coneCouplingPairing (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ)
    (φ : ℂ → ℝ) : ℝ :=
  hC φ - (∫ x, φ x * hcirc ‖x‖ 0) + ∫ x, φ x * coneCouplingRadial γ hcirc w x

/-- The remainder `h_{|x|}(0) - h^ℂ_{|x|}(0) + γ log |x|` of the coupling, written so that it vanishes on the closed
unit disk. -/
noncomputable def coneCouplingRemainder (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (x : ℂ) : ℝ :=
  if ‖x‖ ≤ 1 then 0
  else hcirc ‖x‖ 0 - hcirc 1 0 - (w (Real.toNNReal (Real.log ‖x‖)) - w 0) + γ * Real.log ‖x‖

theorem coneCouplingRadial_congr_norm (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) {x y : ℂ}
    (h : ‖y‖ = ‖x‖) : coneCouplingRadial γ hcirc w y = coneCouplingRadial γ hcirc w x := by
  simp only [coneCouplingRadial, h]

/-- Pointwise decomposition of the radial profile: `h_{|x|}(0) + γ log |x| - remainder`. -/
theorem coneCouplingRadial_eq (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (x : ℂ) :
    coneCouplingRadial γ hcirc w x =
      hcirc ‖x‖ 0 + γ * Real.log ‖x‖ - coneCouplingRemainder γ hcirc w x := by
  unfold coneCouplingRadial coneCouplingRemainder
  split_ifs <;> ring

/-- The circle average of the coupled field over `∂B_{|x|}(0)` is the radial profile at `x` (also at `x = 0`, where
the circle is a point). -/
theorem coneCouplingCircle_norm (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (x : ℂ) :
    coneCouplingCircle γ hcirc w ‖x‖ 0 = coneCouplingRadial γ hcirc w x := by
  have hsph : ∀ y ∈ Metric.sphere (0 : ℂ) |‖x‖|, ‖y‖ = ‖x‖ := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, abs_norm] at hy
    exact hy
  have h1 : Real.circleAverage (fun y => hcirc ‖y‖ 0) 0 ‖x‖ = hcirc ‖x‖ 0 :=
    Real.circleAverage_const_on_circle fun y hy => by rw [hsph y hy]
  have h2 : Real.circleAverage (coneCouplingRadial γ hcirc w) 0 ‖x‖ = coneCouplingRadial γ hcirc w x :=
    Real.circleAverage_const_on_circle fun y hy => coneCouplingRadial_congr_norm γ hcirc w (hsph y hy)
  rw [coneCouplingCircle, h1, h2]
  ring

/-- The radial part `x ↦ h^ℂ_{|x|}(0)` of the coupled field is the radial profile. -/
theorem coneCouplingCircle_radialPart (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    (fun x : ℂ => coneCouplingCircle γ hcirc w ‖x‖ 0) = coneCouplingRadial γ hcirc w :=
  funext (coneCouplingCircle_norm γ hcirc w)

/-- The coupled field has the lateral part of the cone. -/
theorem lateralEval_coneCoupling (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    lateralEval (coneCouplingPairing γ hC hcirc w) (coneCouplingCircle γ hcirc w) = lateralEval hC hcirc := by
  funext o
  cases o with
  | pairing φ =>
    simp only [lateralEval, coneCouplingPairing, coneCouplingCircle_norm]
    ring
  | circle r z =>
    simp only [lateralEval, coneCouplingCircle_radialPart]
    rw [coneCouplingCircle]
    ring

/-- The lateral process of the coupled field is that of the cone. -/
theorem lateralProcess_coneCoupling (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    lateralProcess (coneCouplingPairing γ hC hcirc w) (coneCouplingCircle γ hcirc w) =
      lateralProcess hC hcirc := by
  funext o
  simp only [lateralProcess, lateralEval_coneCoupling]

/-- The radial process of the coupled field: `t ↦ h_{e^{-t}}(0) - γ t` (the cone's radial process without its drift)
and `s ↦ h_1(0) + w(s) - w(0)`. -/
theorem radialProcess_coneCouplingCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    radialProcess (coneCouplingCircle γ hcirc w) =
      (fun t : ℝ≥0 => hcirc (Real.exp (-(t : ℝ))) 0 - γ * t, fun s : ℝ≥0 => hcirc 1 0 + (w s - w 0)) := by
  have hnorm : ∀ ρ : ℝ, 0 < ρ → coneCouplingCircle γ hcirc w ρ 0 = coneCouplingRadial γ hcirc w (ρ : ℂ) := by
    intro ρ hρ
    have h := coneCouplingCircle_norm γ hcirc w (ρ : ℂ)
    rwa [Complex.norm_of_nonneg hρ.le] at h
  simp only [radialProcess, Prod.mk.injEq]
  constructor
  · funext t
    have hle : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.2)
    rw [hnorm _ (Real.exp_pos _), coneCouplingRadial, Complex.norm_of_nonneg (Real.exp_pos _).le]
    simp only [hle, ↓reduceIte, Real.log_exp]
    ring
  · funext s
    rw [hnorm _ (Real.exp_pos _), coneCouplingRadial, Complex.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_exp]
    rcases eq_or_lt_of_le s.2 with hs | hs
    · have hs0 : s = 0 := NNReal.coe_eq_zero.mp hs.symm
      subst hs0
      simp
    · have hlt : ¬Real.exp (s : ℝ) ≤ 1 := not_le.mpr (Real.one_lt_exp_iff.mpr hs)
      simp only [hlt, ↓reduceIte, Real.toNNReal_coe]

/-- **The cone is the coupled field minus `γ log |·|`, plus the circle average of the remainder**, on every circle on
which the three radial terms are integrable (in particular on every circle of positive radius avoiding the origin,
when `ρ ↦ h_ρ(0)` and `w` are continuous). -/
theorem circle_eq_fieldCircleAverage_coneCoupling_add (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ)
    {r : ℝ} {z : ℂ} (h₁ : CircleIntegrable (fun x => hcirc ‖x‖ 0) z r)
    (h₂ : CircleIntegrable (fun x : ℂ => Real.log ‖x‖) z r)
    (h₃ : CircleIntegrable (coneCouplingRemainder γ hcirc w) z r) :
    hcirc r z = fieldCircleAverage γ (coneCouplingCircle γ hcirc w) r z +
      Real.circleAverage (coneCouplingRemainder γ hcirc w) z r := by
  have hR : Real.circleAverage (coneCouplingRadial γ hcirc w) z r =
      Real.circleAverage (fun x => hcirc ‖x‖ 0) z r + γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r -
        Real.circleAverage (coneCouplingRemainder γ hcirc w) z r := by
    have hfun : coneCouplingRadial γ hcirc w =
        fun x => (hcirc ‖x‖ 0 + γ * Real.log ‖x‖) - coneCouplingRemainder γ hcirc w x :=
      funext (coneCouplingRadial_eq γ hcirc w)
    have h₂' : CircleIntegrable (fun x : ℂ => γ * Real.log ‖x‖) z r := IntervalIntegrable.const_mul h₂ γ
    have h₁₂ : CircleIntegrable (fun x => hcirc ‖x‖ 0 + γ * Real.log ‖x‖) z r := h₁.add h₂'
    have hsm : Real.circleAverage (fun x : ℂ => γ * Real.log ‖x‖) z r =
        γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := γ) (f := fun x : ℂ => Real.log ‖x‖) (c := z) (R := r))
    rw [hfun, Real.circleAverage_fun_sub h₁₂ h₃, Real.circleAverage_fun_add h₁ h₂', hsm]
  rw [fieldCircleAverage, coneCouplingCircle, hR]
  ring

end MatedCRT.FirstPass.Derived
