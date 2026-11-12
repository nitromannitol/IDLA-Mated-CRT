import MatedCRT.FirstPass.Derived.ConeGFFFiniteLaw

/-!
# The coupled cone field is a whole-plane Gaussian free field

Let `(hC, hcirc)` be the circle average embedding of a `γ`-quantum cone under `P` and let `w` be an independent
standard Brownian motion. The coupled field of `ConeGFFCoupling2.lean`, with pairings `coneCouplingPairing` and circle
averages `coneGFFCircle`, replaces the radial part of the cone outside the unit disk by `h_1(0) + w(log |x|) - w(0)`
and removes the drift `-γ log |x|` inside it. Its finite-dimensional laws are those of a whole-plane GFF
(`map_finset_coneGFF_eq`). This file upgrades that to the full structure `IsWholePlaneGFF`:

* `isWholePlaneGFF_of_map_finset_eq`: a family of pairings and circle averages whose admissible observables are
  random variables, whose circle averages are a.s. continuous in `(r, z)`, and whose finite-dimensional laws are those
  of a whole-plane GFF, is a whole-plane GFF (Gaussianity, centring and covariance are properties of the
  finite-dimensional laws);
* `circleOff N hcirc`: the circle averages with a measurable null set `N` of samples set to zero. When `N` contains the
  samples whose circle averages are not continuous, `(ρ, ω) ↦ h_ρ(0)` is jointly measurable (continuous in `ρ > 0`,
  measurable in `ω`), so the radial integrals defining the coupled field are random variables;
* `isWholePlaneGFF_coneGFF`: for such an `N`, the coupled field built from `(hC, circleOff N hcirc)` and `w` is a
  whole-plane GFF under `P ⊗ BM`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}

/-- Each admissible observable is a random variable when the pairings with test functions and the circle averages of
positive radius are. -/
theorem measurable_eval_admissible (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (o : GFFObservable.Admissible) :
    Measurable fun ω => o.1.eval (hC ω) (hcirc ω) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact hmp φ ho
  | circle r z => exact hmc r z ho

/-- **Whole-plane GFF from its finite-dimensional laws.** If the admissible observables of `(hC, hcirc)` are random
variables, the circle averages are a.s. continuous on `(0, ∞) × ℂ`, and every finite family of admissible observables
has the joint law of the same family for a whole-plane GFF `(hC', hcirc')`, then `(hC, hcirc)` is a whole-plane GFF. -/
theorem isWholePlaneGFF_of_map_finset_eq (hh : IsWholePlaneGFF P' hC' hcirc')
    (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hlaw : ∀ S : Finset GFFObservable.Admissible,
      P.map (fun ω (i : S) => i.1.1.eval (hC ω) (hcirc ω)) =
        P'.map (fun ω (i : S) => i.1.1.eval (hC' ω) (hcirc' ω))) :
    IsWholePlaneGFF P hC hcirc := by
  let _ : DecidableEq GFFObservable.Admissible := Classical.decEq _
  have hX : ∀ S : Finset GFFObservable.Admissible,
      Measurable fun ω (i : S) => i.1.1.eval (hC ω) (hcirc ω) :=
    fun S => Measurable.of_eval fun i : S => measurable_eval_admissible hmp hmc i.1
  have hY : ∀ S : Finset GFFObservable.Admissible,
      Measurable fun ω (i : S) => i.1.1.eval (hC' ω) (hcirc' ω) :=
    fun S => Measurable.of_eval fun i : S =>
      measurable_eval_admissible hh.measurable_pairing hh.measurable_circle i.1
  have hint : ∀ (S : Finset GFFObservable.Admissible) (F : (S → ℝ) → ℝ), Measurable F →
      ∫ ω, F (fun i : S => i.1.1.eval (hC ω) (hcirc ω)) ∂P =
        ∫ ω, F (fun i : S => i.1.1.eval (hC' ω) (hcirc' ω)) ∂P' := by
    intro S F hF
    rw [← integral_map (hX S).aemeasurable hF.aestronglyMeasurable, hlaw S,
      integral_map (hY S).aemeasurable hF.aestronglyMeasurable]
  have hmean : ∀ o : GFFObservable, o.IsAdmissible →
      ∫ ω, o.eval (hC ω) (hcirc ω) ∂P = ∫ ω, o.eval (hC' ω) (hcirc' ω) ∂P' := by
    intro o ho
    exact hint {⟨o, ho⟩} (fun v => v ⟨⟨o, ho⟩, Finset.mem_singleton_self _⟩) (measurable_pi_apply _)
  refine
    { measurable_pairing := hmp
      measurable_circle := hmc
      isGaussianProcess := ⟨fun S => ⟨(hX S).aemeasurable, by
        show IsGaussian (P.map fun ω (i : S) => i.1.1.eval (hC ω) (hcirc ω))
        rw [hlaw S]; exact (hh.isGaussianProcess.hasGaussianLaw S).isGaussian_map⟩⟩
      integral_eq_zero := fun o ho => (hmean o ho).trans (hh.integral_eq_zero o ho)
      covariance_eq := ?_
      ae_continuousOn_circle := hcont }
  intro o o' ho ho'
  rw [← hh.covariance_eq o o' ho ho']
  have h1 : (⟨o, ho⟩ : GFFObservable.Admissible) ∈
      ({(⟨o, ho⟩ : GFFObservable.Admissible), (⟨o', ho'⟩ : GFFObservable.Admissible)} : Finset GFFObservable.Admissible) :=
    Finset.mem_insert_self (α := GFFObservable.Admissible) _ _
  have h2 : (⟨o', ho'⟩ : GFFObservable.Admissible) ∈
      ({(⟨o, ho⟩ : GFFObservable.Admissible), (⟨o', ho'⟩ : GFFObservable.Admissible)} : Finset GFFObservable.Admissible) :=
    Finset.mem_insert_of_mem (α := GFFObservable.Admissible) (Finset.mem_singleton_self _)
  have key := hint ({(⟨o, ho⟩ : GFFObservable.Admissible), (⟨o', ho'⟩ : GFFObservable.Admissible)} : Finset GFFObservable.Admissible)
    (fun v => (v ⟨_, h1⟩ - ∫ ω, o.eval (hC' ω) (hcirc' ω) ∂P') *
      (v ⟨_, h2⟩ - ∫ ω, o'.eval (hC' ω) (hcirc' ω) ∂P'))
    (((measurable_pi_apply _).sub_const _).mul ((measurable_pi_apply _).sub_const _))
  simp only [covariance]
  rw [hmean o ho, hmean o' ho']
  exact key

end Transfer

section ConeVersion

variable {Ω : Type*} {N : Set Ω} {hcirc : Ω → ℝ → ℂ → ℝ}

open Classical in
/-- The circle averages with the samples in `N` set to zero. -/
noncomputable def circleOff (N : Set Ω) (hcirc : Ω → ℝ → ℂ → ℝ) : Ω → ℝ → ℂ → ℝ :=
  fun ω r z => if ω ∈ N then 0 else hcirc ω r z

theorem circleOff_of_notMem {ω : Ω} (hω : ω ∉ N) : circleOff N hcirc ω = hcirc ω := by
  funext r z
  simp only [circleOff, hω, ↓reduceIte]

theorem measurable_circleOff [MeasurableSpace Ω] (hNm : MeasurableSet N) {r : ℝ} {z : ℂ} (hm : Measurable fun ω => hcirc ω r z) :
    Measurable fun ω => circleOff N hcirc ω r z := by
  classical
  exact Measurable.ite hNm measurable_const hm

theorem continuousOn_circleOff
    (hcN : ∀ ω ∉ N, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) (ω : Ω) :
    ContinuousOn (fun p : ℝ × ℂ => circleOff N hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
  by_cases hω : ω ∈ N
  · simp only [circleOff, hω, ↓reduceIte]
    exact continuousOn_const
  · simpa only [circleOff, hω, ↓reduceIte] using hcN ω hω

/-- **Joint measurability of the radial circle averages** `(ρ, ω) ↦ h_ρ(0)`, `ρ > 0`, once the samples with
discontinuous circle averages are removed (Carathéodory: continuous in `ρ`, measurable in `ω`). -/
theorem measurable_circleOff_radial [MeasurableSpace Ω] (hNm : MeasurableSet N)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcN : ∀ ω ∉ N, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Measurable fun q : Ioi (0 : ℝ) × Ω => circleOff N hcirc q.2 q.1 0 := by
  refine measurable_uncurry_of_continuous_of_measurable (u := fun (ρ : Ioi (0 : ℝ)) ω => circleOff N hcirc ω ρ 0)
    (fun ω => ?_) (fun ρ => measurable_circleOff hNm (hmc ρ 0 ρ.2))
  exact (continuousOn_circleOff hcN ω).comp_continuous (continuous_subtype_val.prodMk continuous_const)
    fun ρ => ⟨ρ.2, mem_univ _⟩

open Classical in
/-- `‖x‖` off the origin and `1` at the origin, as a positive real. -/
noncomputable def posNorm (x : ℂ) : Ioi (0 : ℝ) :=
  ⟨if x = 0 then (1 : ℝ) else ‖x‖, by
    split_ifs with h
    · exact Set.mem_Ioi.2 one_pos
    · exact Set.mem_Ioi.2 (norm_pos_iff.2 h)⟩

theorem measurable_posNorm : Measurable posNorm := by
  classical
  exact (Measurable.ite (measurableSet_singleton 0) measurable_const measurable_norm).subtype_mk

theorem posNorm_of_ne {x : ℂ} (hx : x ≠ 0) : (posNorm x : ℝ) = ‖x‖ := by
  simp only [posNorm, hx, ↓reduceIte]

/-- The radial function `x ↦ h_{|x|}(0)` of a sample with `N` removed, read at radius `1` at the origin. -/
noncomputable def radialOff (N : Set Ω) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (x : ℂ) : ℝ :=
  circleOff N hcirc ω (posNorm x) 0

theorem radialOff_of_ne {ω : Ω} {x : ℂ} (hx : x ≠ 0) : radialOff N hcirc ω x = circleOff N hcirc ω ‖x‖ 0 := by
  simp only [radialOff, posNorm_of_ne hx]

theorem measurable_radialOff [MeasurableSpace Ω]
    (hrad : Measurable fun q : Ioi (0 : ℝ) × Ω => circleOff N hcirc q.2 q.1 0) :
    Measurable fun q : Ω × ℂ => radialOff N hcirc q.1 q.2 :=
  hrad.comp ((measurable_posNorm.comp measurable_snd).prodMk measurable_fst)

theorem ae_ne_zero_complex : ∀ᵐ x : ℂ, x ≠ 0 :=
  (show ∀ᵐ x : ℂ, x ∈ ({0} : Set ℂ)ᶜ from compl_mem_ae_iff.2 (measure_singleton 0)).mono fun _ hx => hx

end ConeVersion

section CoupledField

variable {Ω : Type*} [MeasurableSpace Ω] {K : Ω → ℝ → ℂ → ℝ} {Rad : Ω → ℂ → ℝ}

/-- Evaluation of a continuous path at a time is jointly measurable in the time and the path. -/
theorem measurable_continuousPath_eval : Measurable fun q : ℝ≥0 × ContinuousPath ℝ => q.2 q.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ≥0) (w : ContinuousPath ℝ) => w s)
    (fun w => w.continuous) (fun s => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s)

/-- The remainder of the coupling is jointly measurable in the sample, the Brownian path and the point, given a jointly
measurable radial function `Rad` with `Rad ω x = K ω |x| 0` off the origin. -/
theorem measurable_coneCouplingRemainder (γ : ℝ) (hrad : Measurable fun q : Ω × ℂ => Rad q.1 q.2)
    (hR : ∀ ω x, x ≠ 0 → Rad ω x = K ω ‖x‖ 0) (h1 : Measurable fun ω => K ω 1 0) :
    Measurable fun q : (Ω × ContinuousPath ℝ) × ℂ =>
      coneCouplingRemainder γ (K q.1.1) (fun t => q.1.2 t) q.2 := by
  have heq : (fun q : (Ω × ContinuousPath ℝ) × ℂ =>
      coneCouplingRemainder γ (K q.1.1) (fun t => q.1.2 t) q.2) = fun q =>
        if ‖q.2‖ ≤ 1 then 0 else Rad q.1.1 q.2 - K q.1.1 1 0 -
          (q.1.2 (Real.toNNReal (Real.log ‖q.2‖)) - q.1.2 0) + γ * Real.log ‖q.2‖ := by
    funext q
    unfold coneCouplingRemainder
    split_ifs with h
    · rfl
    · rw [hR _ _ fun h0 => h (by rw [h0, norm_zero]; exact zero_le_one)]
  rw [heq]
  have hlog : Measurable fun q : (Ω × ContinuousPath ℝ) × ℂ => Real.log ‖q.2‖ :=
    Real.measurable_log.comp (measurable_norm.comp measurable_snd)
  have hev := measurable_continuousPath_eval
  exact Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const) measurable_const
    ((((hrad.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (h1.comp (measurable_fst.comp measurable_fst))).sub
      ((hev.comp ((measurable_real_toNNReal.comp hlog).prodMk (measurable_snd.comp measurable_fst))).sub
        (hev.comp (measurable_const.prodMk (measurable_snd.comp measurable_fst))))).add
      (measurable_const.mul hlog))

/-- Each circle average of the coupled field is a random variable on `Ω × (paths)`. -/
theorem measurable_coneGFFCircle (γ : ℝ) (hrad : Measurable fun q : Ω × ℂ => Rad q.1 q.2)
    (hR : ∀ ω x, x ≠ 0 → Rad ω x = K ω ‖x‖ 0) (h1 : Measurable fun ω => K ω 1 0) {r : ℝ} {z : ℂ}
    (hK : Measurable fun ω => K ω r z) :
    Measurable fun p : Ω × ContinuousPath ℝ => coneGFFCircle γ (K p.1) (fun t => p.2 t) r z := by
  have hF : Measurable fun q : (Ω × ContinuousPath ℝ) × ℝ =>
      coneCouplingRemainder γ (K q.1.1) (fun t => q.1.2 t) (circleMap z r q.2) :=
    (measurable_coneCouplingRemainder γ hrad hR h1).comp
      (measurable_fst.prodMk ((continuous_circleMap z r).measurable.comp measurable_snd))
  have hI : Measurable fun p : Ω × ContinuousPath ℝ =>
      ∫ θ in Ioc 0 (2 * Real.pi), coneCouplingRemainder γ (K p.1) (fun t => p.2 t) (circleMap z r θ) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).measurable
  have heq : (fun p : Ω × ContinuousPath ℝ => coneGFFCircle γ (K p.1) (fun t => p.2 t) r z) = fun p =>
      K p.1 r z + γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r -
        (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), coneCouplingRemainder γ (K p.1) (fun t => p.2 t) (circleMap z r θ) := by
    funext p
    show _ - Real.circleAverage _ z r = _
    congr 1
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
  rw [heq]
  exact ((hK.comp measurable_fst).add_const _).sub (hI.const_mul _)

/-- Each pairing of the coupled field with a measurable `φ` is a random variable on `Ω × (paths)`. -/
theorem measurable_coneCouplingPairing (γ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ}
    (hrad : Measurable fun q : Ω × ℂ => Rad q.1 q.2) (hR : ∀ ω x, x ≠ 0 → Rad ω x = K ω ‖x‖ 0)
    (h1 : Measurable fun ω => K ω 1 0) {φ : ℂ → ℝ} (hφ : Measurable φ) (hCφ : Measurable fun ω => hC ω φ) :
    Measurable fun p : Ω × ContinuousPath ℝ => coneCouplingPairing γ (hC p.1) (K p.1) (fun t => p.2 t) φ := by
  have h2 : ∀ p : Ω × ContinuousPath ℝ, ∫ x, φ x * K p.1 ‖x‖ 0 = ∫ x, φ x * Rad p.1 x := fun p =>
    integral_congr_ae (ae_ne_zero_complex.mono fun x hx => by simp only [hR p.1 x hx])
  have h3 : ∀ p : Ω × ContinuousPath ℝ, ∫ x, φ x * coneCouplingRadial γ (K p.1) (fun t => p.2 t) x =
      ∫ x, φ x * (if ‖x‖ ≤ 1 then Rad p.1 x + γ * Real.log ‖x‖
        else K p.1 1 0 + (p.2 (Real.toNNReal (Real.log ‖x‖)) - p.2 0)) := fun p =>
    integral_congr_ae (ae_ne_zero_complex.mono fun x hx => by simp only [coneCouplingRadial, hR p.1 x hx])
  have heq : (fun p : Ω × ContinuousPath ℝ => coneCouplingPairing γ (hC p.1) (K p.1) (fun t => p.2 t) φ) =
      fun p => hC p.1 φ - (∫ x, φ x * Rad p.1 x) + ∫ x, φ x * (if ‖x‖ ≤ 1 then Rad p.1 x + γ * Real.log ‖x‖
        else K p.1 1 0 + (p.2 (Real.toNNReal (Real.log ‖x‖)) - p.2 0)) := by
    funext p
    rw [coneCouplingPairing, h2 p, h3 p]
  rw [heq]
  have hlog : Measurable fun q : (Ω × ContinuousPath ℝ) × ℂ => Real.log ‖q.2‖ :=
    Real.measurable_log.comp (measurable_norm.comp measurable_snd)
  have hev := measurable_continuousPath_eval
  have hRq : Measurable fun q : (Ω × ContinuousPath ℝ) × ℂ => Rad q.1.1 q.2 :=
    hrad.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hA : Measurable fun q : (Ω × ContinuousPath ℝ) × ℂ => φ q.2 * Rad q.1.1 q.2 :=
    (hφ.comp measurable_snd).mul hRq
  have hB : Measurable fun q : (Ω × ContinuousPath ℝ) × ℂ => φ q.2 *
      (if ‖q.2‖ ≤ 1 then Rad q.1.1 q.2 + γ * Real.log ‖q.2‖
        else K q.1.1 1 0 + (q.1.2 (Real.toNNReal (Real.log ‖q.2‖)) - q.1.2 0)) :=
    (hφ.comp measurable_snd).mul
      (Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const)
        (hRq.add (measurable_const.mul hlog))
        ((h1.comp (measurable_fst.comp measurable_fst)).add
          ((hev.comp ((measurable_real_toNNReal.comp hlog).prodMk (measurable_snd.comp measurable_fst))).sub
            (hev.comp (measurable_const.prodMk (measurable_snd.comp measurable_fst))))))
  exact ((hCφ.comp measurable_fst).sub (hA.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable).add
    (hB.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end CoupledField

/-- **The coupled cone field is a whole-plane GFF** (step C4). Let `(hC, hcirc)` be the circle average embedding of a
`γ`-quantum cone under `P`. There is a measurable `P`-null set `N` of samples (containing those whose circle averages
are not continuous) such that the coupled field built from the cone with `N` removed and an independent standard
Brownian motion `w`, with pairings `coneCouplingPairing` and circle averages `coneGFFCircle`, is a whole-plane GFF
under `P ⊗ BM`. -/
theorem isWholePlaneGFF_coneGFF {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc) :
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ IsWholePlaneGFF (P.prod (brownianMotion 0))
      (fun p => coneCouplingPairing γ (hC p.1) (circleOff N hcirc p.1) (fun t => p.2 t))
      (fun p => coneGFFCircle γ (circleOff N hcirc p.1) (fun t => p.2 t)) := by
  have hbad : P {ω | ¬ ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi 0 ×ˢ univ)} = 0 :=
    ae_iff.1 hQ.ae_continuousOn_circle
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  have hcN : ∀ ω ∉ N, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi 0 ×ˢ univ) :=
    fun ω hω => by_contra fun h => hω (hNsub h)
  have hrad := measurable_radialOff (measurable_circleOff_radial hNm hQ.measurable_circle hcN)
  have hR : ∀ ω x, x ≠ 0 → radialOff N hcirc ω x = circleOff N hcirc ω ‖x‖ 0 :=
    fun _ _ hx => radialOff_of_ne hx
  have h1 := measurable_circleOff hNm (hQ.measurable_circle 1 0 one_pos)
  obtain ⟨Ω'', _, P'', hC'', hcirc'', hP'', hgff'', -⟩ := hQ.lateral_law
  have := hP''
  refine ⟨N, hNm, hN0, isWholePlaneGFF_of_map_finset_eq hgff'' (fun φ hφ => ?_) (fun r z hr => ?_)
    (Eventually.of_forall fun p => continuousOn_coneGFFCircle γ (continuousOn_circleOff hcN p.1) p.2.continuous)
    (fun S => ?_)⟩
  · exact measurable_coneCouplingPairing γ hrad hR h1 hφ.1.continuous.measurable
      (hQ.measurable_pairing φ hφ)
  · exact measurable_coneGFFCircle γ hrad hR h1 (measurable_circleOff hNm (hQ.measurable_circle r z hr))
  · have hae : ∀ᵐ p ∂(P.prod (brownianMotion 0)), p.1 ∉ N :=
      Measure.quasiMeasurePreserving_fst.ae (measure_eq_zero_iff_ae_notMem.1 hN0)
    rw [← map_finset_coneGFF_eq hQ hgff'' S]
    exact Measure.map_congr (hae.mono fun p hp => by simp only [circleOff_of_notMem hp])

end MatedCRT.FirstPass.Derived
