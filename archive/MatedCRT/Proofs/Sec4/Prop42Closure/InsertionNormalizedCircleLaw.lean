import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionAffineCircleLaw
import MatedCRT.Proofs.Field.WholePlaneAffineCov
import MatedCRT.Proofs.Field.WholePlaneAffine
import MatedCRT.Proofs.Field.GaussianLaw

/-!
# Normalized complex-affine circle law, circle-only proof

Internal module; it cites no literature input. It formalizes the circle-law calculation (measurable limits, absence of an atom), including the assertion for complex rotations, not just positive real dilations. For `a ≠ 0`, `R = |a|` and `u = a / R`
(so `‖u‖ = 1`), the normalized circle process is
`h^a(r, z) = h(R r, a z) - h(R, 0) = h(R r, R u z) - h(R, 0)`, i.e. `normalizedCircleProc a`.

The smeared observables are the whole-plane circle averages `circle s w` (the `GFFObservable.circle` of
`IsWholePlaneGFF`), whose covariance is `wholePlaneGFFCov`, the iterated circle average of the kernel `wholePlaneCov`.

* `circleAverage_comp_unit_mul`: rotation invariance of circle averages, `avg_{∂B(c,s)} f(u ·) = avg_{∂B(u c,s)} f`.
* `wholePlaneCov_unit_mul`, `wGC_circle_unit_mul`: the kernel and the circle covariance are invariant under a common
  rotation of both arguments.
* `normalized_wGC_affine_cc`: the cross-term and variance cancellation of , read off from
  `Field.affine_cc` (real dilation `R`, complex centres).
* `cov_normalized_circle`: covariance of two normalized circle observables, by bilinearity of the Gaussian observables
  (`Field.cov_comb_four`) and `IsWholePlaneGFF.covariance_eq`.
* `normalized_circle_law_complex`: the laws of the normalized circle process and of the circle process agree on the
  product σ-algebra, by `Field.map_eq_of_covariance` (centred Gaussian families with equal covariances).

No rotated whole-plane GFF is used: the only hypothesis is `IsWholePlaneGFF` of the original field.
-/

open MeasureTheory ProbabilityTheory Filter Set HarmonicBalls

namespace MatedCRT

/-- Rotation invariance of circle averages (complex rotations). For `‖u‖ = 1`,
`avg_{x ∈ ∂B(c,s)} f(u x) = avg_{x ∈ ∂B(u c, s)} f(x)`. -/
theorem circleAverage_comp_unit_mul (f : ℂ → ℝ) {u : ℂ} (hu : ‖u‖ = 1) (c : ℂ) (s : ℝ) :
    Real.circleAverage (fun x => f (u * x)) c s = Real.circleAverage f (u * c) s := by
  have hexp : Complex.exp ((Complex.arg u : ℝ) * Complex.I) = u := by
    have h := Complex.norm_mul_exp_arg_mul_I u
    rw [hu, Complex.ofReal_one, one_mul] at h
    exact h
  set φ : ℝ := Complex.arg u with hφ
  have key : ∀ θ : ℝ, u * circleMap c s θ = circleMap (u * c) s (θ + φ) := by
    intro θ
    have hθ : Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((θ : ℂ) * Complex.I) * u := by
      rw [← hexp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [circleMap]
    rw [hθ]
    ring
  have hper : Function.Periodic (fun t : ℝ => f (circleMap (u * c) s t)) (2 * Real.pi) :=
    fun t => congrArg f (periodic_circleMap (u * c) s t)
  have h1 := intervalIntegral.integral_comp_add_right (f := fun t : ℝ => f (circleMap (u * c) s t))
    (a := (0 : ℝ)) (b := 2 * Real.pi) φ
  have h2 := hper.intervalIntegral_add_eq φ 0
  simp only [zero_add] at h1 h2
  unfold Real.circleAverage
  congr 1
  simp only [key]
  rw [h1, add_comm (2 * Real.pi) φ, h2]

/-- The logarithmic whole-plane kernel is invariant under a common rotation. -/
theorem wholePlaneCov_unit_mul {u : ℂ} (hu : ‖u‖ = 1) (x y : ℂ) :
    wholePlaneCov (u * x) (u * y) = wholePlaneCov x y := by
  unfold wholePlaneCov
  rw [← mul_sub]
  simp only [norm_mul, hu, one_mul]

/-- The smeared circle covariance is invariant under a common rotation of both circle centres. -/
theorem wGC_circle_unit_mul {u : ℂ} (hu : ‖u‖ = 1) (s t : ℝ) (w v : ℂ) :
    wholePlaneGFFCov (.circle s (u * w)) (.circle t (u * v))
      = wholePlaneGFFCov (.circle s w) (.circle t v) := by
  rw [Field.wGC_cc, Field.wGC_cc, ← circleAverage_comp_unit_mul
    (fun x => Real.circleAverage (fun y => wholePlaneCov x y) (u * v) t) hu w s]
  congr 1
  funext x
  rw [← circleAverage_comp_unit_mul (fun y => wholePlaneCov (u * x) y) hu v t]
  simp only [wholePlaneCov_unit_mul hu]

/-- The cross-term and variance cancellation of  for the smeared circle covariances: with `R > 0`,
`Γ(A,C) - Γ(A,B) - Γ(C,B) + Γ(B,B) = Γ(circle s w, circle t v)`, where `A = circle (R s) (R w + z)`,
`C = circle (R t) (R v + z)` and `B = circle R z`. Read off from `Field.affine_cc`. -/
theorem normalized_wGC_affine_cc {R : ℝ} (hR : 0 < R) (z : ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (w v : ℂ) :
    wholePlaneGFFCov (.circle (R * s) ((R : ℂ) * w + z)) (.circle (R * t) ((R : ℂ) * v + z))
      - wholePlaneGFFCov (.circle (R * s) ((R : ℂ) * w + z)) (.circle R z)
      - wholePlaneGFFCov (.circle (R * t) ((R : ℂ) * v + z)) (.circle R z)
      + wholePlaneGFFCov (.circle R z) (.circle R z)
      = wholePlaneGFFCov (.circle s w) (.circle t v) := by
  rw [Field.wGC_circle_N R s z w, Field.wGC_circle_N R t z v, Field.wGC_NN R z,
    Field.wGC_cc (R * s) (R * t), Field.wGC_cc s t w v]
  exact Field.affine_cc hR z hs ht w v

/-- Covariance of two normalized circle observables `h(R s, R u w) - h(R, 0)` and `h(R t, R u v) - h(R, 0)` of a
whole-plane GFF, for `R > 0` and `‖u‖ = 1`: it is the circle covariance `Γ(circle s w, circle t v)` of the original
field. -/
theorem cov_normalized_circle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {R : ℝ} (hR : 0 < R) {u : ℂ} (hu : ‖u‖ = 1) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w v : ℂ) :
    cov[fun ω => hcirc ω (R * s) ((R : ℂ) * (u * w)) - hcirc ω R 0,
        fun ω => hcirc ω (R * t) ((R : ℂ) * (u * v)) - hcirc ω R 0; P]
      = wholePlaneGFFCov (.circle s w) (.circle t v) := by
  have hpos1 : 0 < R * s := mul_pos hR hs
  have hpos2 : 0 < R * t := mul_pos hR ht
  have hX1 : MemLp (fun ω => hcirc ω (R * s) ((R : ℂ) * (u * w))) 2 P :=
    Field.memLp_obs hh ⟨.circle (R * s) ((R : ℂ) * (u * w)), hpos1⟩
  have hX2 : MemLp (fun ω => hcirc ω R 0) 2 P := Field.memLp_obs hh ⟨.circle R 0, hR⟩
  have hY1 : MemLp (fun ω => hcirc ω (R * t) ((R : ℂ) * (u * v))) 2 P :=
    Field.memLp_obs hh ⟨.circle (R * t) ((R : ℂ) * (u * v)), hpos2⟩
  have c11 : cov[fun ω => hcirc ω (R * s) ((R : ℂ) * (u * w)),
      fun ω => hcirc ω (R * t) ((R : ℂ) * (u * v)); P]
      = wholePlaneGFFCov (.circle (R * s) ((R : ℂ) * (u * w))) (.circle (R * t) ((R : ℂ) * (u * v))) :=
    hh.covariance_eq (.circle (R * s) ((R : ℂ) * (u * w))) (.circle (R * t) ((R : ℂ) * (u * v))) hpos1 hpos2
  have c12 : cov[fun ω => hcirc ω (R * s) ((R : ℂ) * (u * w)), fun ω => hcirc ω R 0; P]
      = wholePlaneGFFCov (.circle (R * s) ((R : ℂ) * (u * w))) (.circle R 0) :=
    hh.covariance_eq (.circle (R * s) ((R : ℂ) * (u * w))) (.circle R 0) hpos1 hR
  have c21 : cov[fun ω => hcirc ω R 0, fun ω => hcirc ω (R * t) ((R : ℂ) * (u * v)); P]
      = wholePlaneGFFCov (.circle (R * t) ((R : ℂ) * (u * v))) (.circle R 0) := by
    rw [covariance_comm]
    exact hh.covariance_eq (.circle (R * t) ((R : ℂ) * (u * v))) (.circle R 0) hpos2 hR
  have c22 : cov[fun ω => hcirc ω R 0, fun ω => hcirc ω R 0; P]
      = wholePlaneGFFCov (.circle R 0) (.circle R 0) :=
    hh.covariance_eq (.circle R 0) (.circle R 0) hR hR
  have e1 : (fun ω => hcirc ω (R * s) ((R : ℂ) * (u * w)) - hcirc ω R 0)
      = fun ω => (1 : ℝ) * hcirc ω (R * s) ((R : ℂ) * (u * w)) + (-1 : ℝ) * hcirc ω R 0 := by
    funext ω
    ring
  have e2 : (fun ω => hcirc ω (R * t) ((R : ℂ) * (u * v)) - hcirc ω R 0)
      = fun ω => (1 : ℝ) * hcirc ω (R * t) ((R : ℂ) * (u * v)) + (-1 : ℝ) * hcirc ω R 0 := by
    funext ω
    ring
  rw [e1, e2, Field.cov_comb_four hX1 hX2 hY1 hX2 1 (-1) 1 (-1), c11, c12, c21, c22]
  have key := normalized_wGC_affine_cc hR 0 hs ht (u * w) (u * v)
  simp only [add_zero] at key
  have rot := wGC_circle_unit_mul hu s t w v
  linear_combination key + rot

/-- The law of the normalized circle process for a unit rotation `u` and dilation `R > 0`: with
`h^{R u}(r, z) = h(R r, R u z) - h(R, 0)`, the circle process has the same law as the original one. -/
theorem normalized_circle_law_of_unit {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {R : ℝ} (hR : 0 < R) {u : ℂ} (hu : ‖u‖ = 1) :
    P.map (fun ω => circleProc (normalizedCircleProc ((R : ℂ) * u) (hcirc ω)))
      = P.map (fun ω => circleProc (hcirc ω)) := by
  have hnorm : ‖(R : ℂ) * u‖ = R := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hpos : ∀ p : Set.Ioi (0 : ℝ) × ℂ, 0 < R * (p.1 : ℝ) :=
    fun p => mul_pos hR (Set.mem_Ioi.mp p.1.2)
  let X : Set.Ioi (0 : ℝ) × ℂ → Ω → ℝ :=
    fun p ω => hcirc ω (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2)) - hcirc ω R 0
  let Y : Set.Ioi (0 : ℝ) × ℂ → Ω → ℝ := fun p ω => hcirc ω (p.1 : ℝ) p.2
  let aI : Set.Ioi (0 : ℝ) × ℂ → GFFObservable.Admissible :=
    fun p => ⟨.circle (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2)), hpos p⟩
  let bI : GFFObservable.Admissible := ⟨.circle R 0, hR⟩
  have hX : IsGaussianProcess X P := by
    have h := Field.isGaussianProcess_comb (V := Field.obsFam hC hcirc) hGFF.isGaussianProcess
      aI (fun _ => bI) (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ))
    have e : X = fun p ω =>
        (1 : ℝ) * Field.obsFam hC hcirc (aI p) ω + (-1 : ℝ) * Field.obsFam hC hcirc bI ω := by
      funext p ω
      simp only [X, aI, bI, Field.obsFam, GFFObservable.eval]
      ring
    rw [e]
    exact h
  have hXm : ∀ p, Measurable (X p) := fun p =>
    (hGFF.measurable_circle _ _ (hpos p)).sub (hGFF.measurable_circle _ _ hR)
  have hX0 : ∀ p, ∫ ω, X p ω ∂P = 0 := by
    intro p
    have i1 : Integrable (fun ω => hcirc ω (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2))) P :=
      (Field.memLp_obs hGFF ⟨.circle (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2)), hpos p⟩).integrable one_le_two
    have i2 : Integrable (fun ω => hcirc ω R 0) P :=
      (Field.memLp_obs hGFF ⟨.circle R 0, hR⟩).integrable one_le_two
    have z1 : ∫ ω, hcirc ω (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2)) ∂P = 0 :=
      hGFF.integral_eq_zero (.circle (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2))) (hpos p)
    have z2 : ∫ ω, hcirc ω R 0 ∂P = 0 := hGFF.integral_eq_zero (.circle R 0) hR
    show ∫ ω, (hcirc ω (R * (p.1 : ℝ)) ((R : ℂ) * (u * p.2)) - hcirc ω R 0) ∂P = 0
    rw [integral_sub i1 i2, z1, z2, sub_zero]
  have hY : IsGaussianProcess Y P :=
    hGFF.isGaussianProcess.comp_right
      (fun p : Set.Ioi (0 : ℝ) × ℂ => (⟨.circle (p.1 : ℝ) p.2, Set.mem_Ioi.mp p.1.2⟩ : GFFObservable.Admissible))
  have hYm : ∀ p, Measurable (Y p) := fun p => hGFF.measurable_circle _ _ (Set.mem_Ioi.mp p.1.2)
  have hY0 : ∀ p, ∫ ω, Y p ω ∂P = 0 := fun p =>
    hGFF.integral_eq_zero (.circle (p.1 : ℝ) p.2) (Set.mem_Ioi.mp p.1.2)
  have hcov : ∀ p q, covariance (X p) (X q) P = covariance (Y p) (Y q) P := by
    intro p q
    exact (cov_normalized_circle hGFF hR hu (Set.mem_Ioi.mp p.1.2) (Set.mem_Ioi.mp q.1.2) p.2 q.2).trans
      (hGFF.covariance_eq (.circle (p.1 : ℝ) p.2) (.circle (q.1 : ℝ) q.2)
        (Set.mem_Ioi.mp p.1.2) (Set.mem_Ioi.mp q.1.2)).symm
  have hmain := Field.map_eq_of_covariance hX hY hXm hYm hX0 hY0 hcov
  have hfun : (fun ω => circleProc (normalizedCircleProc ((R : ℂ) * u) (hcirc ω)))
      = fun ω t => X t ω := by
    funext ω t
    simp only [circleProc, normalizedCircleProc, hnorm, X, mul_assoc]
  rw [hfun]
  exact hmain

/-- **Normalized complex-affine circle law** (complex rotations included). For a whole-plane GFF
`h` and `a ≠ 0`, the normalized circle process `(r, z) ↦ h(|a| r, a z) - h(|a|, 0)` has the same law as the circle
process `(r, z) ↦ h(r, z)`, on the product σ-algebra of `(0, ∞) × ℂ → ℝ`. Only `IsWholePlaneGFF` of `h` is used. -/
theorem normalized_circle_law_complex {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) :
    P.map (fun ω => circleProc (normalizedCircleProc a (hcirc ω)))
      = P.map (fun ω => circleProc (hcirc ω)) := by
  have hR : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hRc : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hu : ‖a / (‖a‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hR.ne']
  have hau : (‖a‖ : ℂ) * (a / (‖a‖ : ℂ)) = a := by
    field_simp
  have h := normalized_circle_law_of_unit hGFF hR hu
  rw [hau] at h
  exact h

end MatedCRT
