import MatedCRT.FirstPass.Derived.ExitReparamLevels
import MatedCRT.FirstPass.Derived.ExitReparamSetup
import MatedCRT.FirstPass.Derived.MarkovTimeChange
import LatticeProb.Topology.CurveExactReparam
import LatticeProb.Prob.MapEqOfEqOnFibers
import LatticeProb.Prob.CouplingOfEqualObservationLaws
import LatticeProb.Topology.CurveStartPoint

/-!
# Equal stopped curve classes give exact reparametrizations of continuous planar paths

Deterministic part of the time-change coupling of a path law with planar Brownian motion.
For continuous paths without interval of constancy:

* `exists_exactReparam_of_stoppedExitCurve_eq`: equal curve classes of the paths stopped at their
  first exit time from an open set give an exact increasing reparametrization of the two stopped
  pieces (pause-free curves at Fréchet distance zero, `exists_orderIso_of_frechetEDist_eq_zero`);
* `stoppedExitCurve_ball_eq_of_le`: equal stopped classes at exit from the ball of radius `r'`
  give equal stopped classes at exit from every smaller ball.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric HarmonicBalls MarkovProcess LatticeProb
open scoped ENNReal NNReal unitInterval

namespace MatedCRT.ExitReparamAssembly

open MatedCRT.ExitReparamPatch MatedCRT.ExitReparamLevels MatedCRT.ExitReparamClass
  MatedCRT.ExitReparamSetup

/-- A function on `ℝ≥0` is not constant on any nondegenerate interval. -/
def NoFlat {α : Type*} (f : ℝ≥0 → α) : Prop :=
  ∀ s t : ℝ≥0, s < t → ∃ u, s ≤ u ∧ u ≤ t ∧ f u ≠ f s

theorem noPause_normalizedPathPrefix {α : Type*} [TopologicalSpace α] {w : C(ℝ≥0, α)}
    {a : ℝ≥0} (ha : 0 < a) (hw : NoFlat w) : NoPause (normalizedPathPrefix w a) := by
  intro s t hst
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  set s' : ℝ≥0 := ⟨(s : ℝ) * a, mul_nonneg s.property.1 a.property⟩ with hs'
  set t' : ℝ≥0 := ⟨(t : ℝ) * a, mul_nonneg t.property.1 a.property⟩ with ht'
  have hlt : s' < t' := by
    show (s : ℝ) * a < (t : ℝ) * a
    exact mul_lt_mul_of_pos_right hst ha'
  obtain ⟨u', hsu, hut, hne⟩ := hw s' t' hlt
  have hsu' : (s : ℝ) * a ≤ u' := hsu
  have hut' : (u' : ℝ) ≤ t * a := hut
  have hu'nn : (0 : ℝ) ≤ (u' : ℝ) / a := div_nonneg u'.property ha'.le
  have hu1 : (u' : ℝ) / a ≤ 1 := by
    rw [div_le_one ha']
    have ht1 : (t : ℝ) * a ≤ a := mul_le_of_le_one_left a.property t.property.2
    linarith
  refine ⟨⟨(u' : ℝ) / a, hu'nn, hu1⟩, ⟨?_, ?_⟩, ?_⟩
  · show (s : ℝ) ≤ (u' : ℝ) / a
    rw [le_div_iff₀ ha']
    exact hsu'
  · show (u' : ℝ) / a ≤ t
    rw [div_le_iff₀ ha']
    exact hut'
  · have hu : (⟨((u' : ℝ) / a) * (a : ℝ), mul_nonneg hu'nn a.property⟩ : ℝ≥0) = u' :=
      NNReal.eq (by
        show ((u' : ℝ) / a) * (a : ℝ) = (u' : ℝ)
        exact div_mul_cancel₀ _ ha'.ne')
    simp only [normalizedPathPrefix_apply]
    rw [hu]
    exact hne

/-- **Equal finite-prefix curve classes of pause-free paths give an exact reparametrization.** -/
theorem exists_exactReparam_of_normalizedPrefixCurve_eq {d : ℕ}
    {w v : C(ℝ≥0, EuclideanSpace ℝ (Fin d))} {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b)
    (hw : NoFlat w) (hv : NoFlat v) (h : normalizedPrefixCurve w a = normalizedPrefixCurve v b) :
    ∃ φ : ℝ≥0 → ℝ≥0, ExactReparam (⇑w) (⇑v) a b φ := by
  have h0 := (CurveSpace.mk_eq_mk_iff _ _).1 h
  obtain ⟨e, he⟩ := NormalizedCurve.exists_orderIso_of_frechetEDist_eq_zero _ _
    (noPause_normalizedPathPrefix ha hw) (noPause_normalizedPathPrefix hb hv) h0
  exact exactReparam_of_orderIso ha hb e he

theorem noFlat_complexToEuclideanPath {f : C(ℝ≥0, ℂ)} (hf : NoFlat f) :
    NoFlat (LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath f) := by
  intro s t hst
  obtain ⟨u, hsu, hut, hne⟩ := hf s t hst
  refine ⟨u, hsu, hut, fun h => hne ?_⟩
  exact Complex.orthonormalBasisOneI.repr.injective h

/-- **Equal stopped curve classes give an exact reparametrization of the stopped pieces.** If the
planar continuous paths `f`, `g` have no interval of constancy, both start in the open set `U`
and leave it, and their curve classes stopped at the first exit time from `U` agree, then `g` is
an exact increasing reparametrization of `f` between the exit times. -/
theorem exists_exactReparam_of_stoppedExitCurve_eq {f g : ContinuousPath ℂ} {U : Set ℂ}
    (hf : NoFlat f) (hg : NoFlat g) (ha : 0 < (pathExitTime U ⇑f).toNNReal)
    (hb : 0 < (pathExitTime U ⇑g).toNNReal)
    (h : MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve U f =
      MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve U g) :
    ∃ φ : ℝ≥0 → ℝ≥0, ExactReparam (⇑f) (⇑g) (pathExitTime U ⇑f).toNNReal
      (pathExitTime U ⇑g).toNNReal φ := by
  unfold MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve at h
  have h' := (LatticeProb.CurveSpaceComparison.isometryEquiv 2).injective h
  obtain ⟨φ, hφ⟩ := exists_exactReparam_of_normalizedPrefixCurve_eq ha hb
    (noFlat_complexToEuclideanPath hf) (noFlat_complexToEuclideanPath hg) h'
  exact ⟨φ, hφ.strictMonoOn, hφ.mapsTo, hφ.surjOn, fun t ht =>
    Complex.orthonormalBasisOneI.repr.injective (hφ.eq t ht)⟩

/-- **Equal stopped classes at exit from a ball give equal stopped classes at exit from every
smaller ball.** -/
theorem stoppedExitCurve_ball_eq_of_le {f g : ContinuousPath ℂ} {r r' : ℝ} (hrr : r ≤ r')
    (hf : NoFlat f) (hg : NoFlat g) (hf0 : ‖f 0‖ < r') (hg0 : ‖g 0‖ < r')
    (hfl : pathExitTime (ball (0 : ℂ) r') ⇑f < ⊤) (hgl : pathExitTime (ball (0 : ℂ) r') ⇑g < ⊤)
    (h : MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r') f =
      MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r') g) :
    MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r) f =
      MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r) g := by
  have ha := toNNReal_pathExitTime_pos isOpen_ball (mem_ball_zero_iff.2 hf0) hfl
  have hb := toNNReal_pathExitTime_pos isOpen_ball (mem_ball_zero_iff.2 hg0) hgl
  obtain ⟨φ, hφ⟩ := exists_exactReparam_of_stoppedExitCurve_eq hf hg ha hb h
  refine stoppedExitCurve_eq_of_exactReparam hφ isOpen_ball ?_
  intro hmem
  have h1 := norm_exit_point_eq hf0 hfl
  rw [mem_ball_zero_iff] at hmem
  linarith

/-- The curve classes of a planar path stopped at its exit from the balls of radii `r k`. -/
noncomputable def levelClasses (r : ℕ → ℝ) (f : ContinuousPath ℂ) :
    ℕ → BouRabeeGwynne.CurveSpace 2 := fun k =>
  MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (r k)) f

theorem measurable_levelClasses (r : ℕ → ℝ) : Measurable (levelClasses r) :=
  measurable_pi_iff.2 fun _ =>
    MatedCRT.StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ isOpen_ball

/-- A path without interval of constancy that starts inside the first ball and leaves every ball. -/
def LevelGood (r : ℕ → ℝ) (f : ContinuousPath ℂ) : Prop :=
  NoFlat f ∧ ‖f 0‖ < r 0 ∧ ∀ k, pathExitTime (ball (0 : ℂ) (r k)) ⇑f < ⊤

/-- **Joint laws of the stopped classes from the laws at each level.** For two probability
measures carried by good paths, equality of the laws of the stopped class at each ball radius
`r k` (`r` monotone) gives equality of the joint laws of all the stopped classes. -/
theorem map_levelClasses_eq {μ ν : Measure (ContinuousPath ℂ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {r : ℕ → ℝ} (hr : Monotone r) (hμ : ∀ᵐ f ∂μ, LevelGood r f)
    (hν : ∀ᵐ f ∂ν, LevelGood r f)
    (hlaw : ∀ k, μ.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (r k))) =
      ν.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (r k)))) :
    μ.map (levelClasses r) = ν.map (levelClasses r) := by
  have hLv := measurable_levelClasses r
  refine MeasureTheory.IsProjectiveLimit.unique
    (P := fun (J : Finset ℕ) => (ν.map (levelClasses r)).map
      (Finset.restrict (π := fun _ : ℕ => BouRabeeGwynne.CurveSpace 2) J)) ?_ (fun _ => rfl)
  intro (J : Finset ℕ)
  have hres : Measurable (Finset.restrict J : (ℕ → BouRabeeGwynne.CurveSpace 2) →
      ((i : J) → BouRabeeGwynne.CurveSpace 2)) := Finset.measurable_restrict J
  beta_reduce
  rw [Measure.map_map hres hLv, Measure.map_map hres hLv]
  set n := J.sup id with hn
  refine map_eq_map_of_eqOn_fibers
    (p := MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (r n)))
    (N := {f | LevelGood r f})
    (MatedCRT.StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ isOpen_ball)
    (hres.comp hLv) ?_ (ae_iff.1 hμ) (ae_iff.1 hν) (hlaw n)
  rintro a ⟨ha1, ha2, ha3⟩ a' ⟨hb1, hb2, hb3⟩ hcls
  funext ⟨k, hk⟩
  have hkn : k ≤ n := Finset.le_sup (f := id) hk
  exact stoppedExitCurve_ball_eq_of_le (hr hkn) ha1 hb1 (ha2.trans_le (hr n.zero_le))
    (hb2.trans_le (hr n.zero_le)) (ha3 n) (hb3 n) hcls

/-- If the stopped curve class has the law it has under planar Brownian motion from `z`, then
`P`-almost every path starts at `z` (the initial point of a curve class is `1`-Lipschitz). -/
theorem ae_eval_zero_of_map_eq {z : ℂ} {r : ℝ} {P : Measure (ContinuousPath ℂ)}
    (hb : P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
      (planarBrownianMotion z).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r))) :
    ∀ᵐ f ∂P, f 0 = z := by
  set c := MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r) with hc
  have hcm : Measurable c :=
    MatedCRT.StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ isOpen_ball
  let g : BouRabeeGwynne.CurveSpace 2 → EuclideanSpace ℝ (Fin 2) := fun q =>
    LatticeProb.CurveSpace.startPoint ((LatticeProb.CurveSpaceComparison.isometryEquiv 2).symm q)
  have hg : Continuous g := LatticeProb.CurveSpace.continuous_startPoint.comp
    (LatticeProb.CurveSpaceComparison.isometryEquiv 2).symm.continuous
  have hgc : ∀ f, g (c f) = Complex.orthonormalBasisOneI.repr (f 0) := by
    intro f
    simp only [g, hc, MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve,
      IsometryEquiv.symm_apply_apply, normalizedPrefixCurve,
      LatticeProb.CurveSpace.startPoint_project]
    simp [normalizedPathPrefix_apply, LatticeProb.ReparamDistanceIsometry.complexToEuclideanPath]
    rfl
  set E : Set (BouRabeeGwynne.CurveSpace 2) := {q | g q = Complex.orthonormalBasisOneI.repr z}
    with hE
  have hEm : MeasurableSet E := (isClosed_eq hg continuous_const).measurableSet
  have hW : ∀ᵐ f ∂(planarBrownianMotion z), c f ∈ E := by
    filter_upwards [ae_planarBrownianMotion_eval_zero z] with f hf
    show g (c f) = _
    rw [hgc, hf]
  have h1 : (P.map c) Eᶜ = 0 := by
    rw [hb, Measure.map_apply hcm hEm.compl]
    exact ae_iff.1 hW
  rw [Measure.map_apply hcm hEm.compl] at h1
  have hP : ∀ᵐ f ∂P, c f ∈ E := ae_iff.2 h1
  filter_upwards [hP] with f hf
  have hf' : g (c f) = Complex.orthonormalBasisOneI.repr z := hf
  rw [hgc] at hf'
  exact Complex.orthonormalBasisOneI.repr.injective hf'

/-- Almost every path is good when its stopped classes have the Brownian laws. -/
theorem ae_levelGood_of_map_eq {z : ℂ} {r : ℕ → ℝ} (hr0 : ‖z‖ < r 0) (hrm : Monotone r)
    {P : Measure (ContinuousPath ℂ)}
    (hflat : P {f : ContinuousPath ℂ | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0)
    (hb : ∀ k, P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (r k))) =
      (planarBrownianMotion z).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (r k)))) :
    ∀ᵐ f ∂P, LevelGood r f := by
  have hz0 := ae_eval_zero_of_map_eq (hb 0)
  have hex : ∀ᵐ f : ContinuousPath ℂ ∂P, ∀ k, pathExitTime (ball (0 : ℂ) (r k)) ⇑f < ⊤ :=
    ae_all_iff.2 fun k =>
      ae_pathExitTime_lt_top_of_map_eq (hr0.trans_le (hrm k.zero_le)) (hb k)
  filter_upwards [hz0, hex, measure_eq_zero_iff_ae_notMem.1 hflat] with f h0 hf hnf
  refine ⟨fun s t hst => ?_, by rw [h0]; exact hr0, hf⟩
  by_contra hn
  refine hnf ⟨s, t, hst, fun u h1 h2 => ?_⟩
  by_contra hne
  exact hn ⟨u, h1, h2, hne⟩

/-- **Coupling of a path law with planar Brownian motion through a continuous nondecreasing time
change** (the exact-reparametrization step of the proof of BG20, Lemma 7.4). If `P` is a law on
planar continuous paths with almost surely no interval of constancy whose stopped curve class at
exit from the ball of radius `r` has the Brownian law from `z` for almost every `r > ‖z‖`, then
there is a coupling `(B, X)` of planar Brownian motion from `z` and `P` with `X = B ∘ τ`
for a continuous (indeed strictly increasing) time change `τ` with `τ 0 = 0`. -/
theorem exists_timeChange_coupling {z : ℂ} {P : Measure (ContinuousPath ℂ)}
    [IsProbabilityMeasure P]
    (hflat : P {f : ContinuousPath ℂ | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0)
    (hb : ∀ᵐ r ∂(volume : Measure ℝ), ‖z‖ < r →
      P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r))) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (B X : Ω → ContinuousPath ℂ) (τ : Ω → ℝ≥0 → ℝ≥0),
      AEMeasurable B Q ∧ AEMeasurable X Q ∧ Q.map B = planarBrownianMotion z ∧
      (∀ᵐ ω ∂Q, Continuous (τ ω) ∧ StrictMono (τ ω) ∧ τ ω 0 = 0 ∧ ∀ u, X ω u = B ω (τ ω u)) ∧
      P = Q.map X := by
  obtain ⟨r, hrs, hr0, hrt, hrb⟩ := exists_radii_seq (c := ‖z‖)
    (p := fun r => P.map (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
      (planarBrownianMotion z).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r))) hb
  have hrm : Monotone r := hrs.monotone
  have hgP := ae_levelGood_of_map_eq hr0 hrm hflat hrb
  have hgW := ae_levelGood_of_map_eq hr0 hrm (planarBrownianMotion_noFlat z) (fun k => rfl)
  have hjoint := map_levelClasses_eq hrm hgP hgW hrb
  have : StandardBorelSpace (ContinuousPath ℂ) := ContinuousPath.standardBorelSpace_borel
  have : Nonempty (ContinuousPath ℂ) := ⟨ContinuousMap.const _ 0⟩
  obtain ⟨Q, hQ, hfst, hsnd, hae⟩ := LatticeProb.exists_coupling_of_map_eq
    (measurable_levelClasses r) P (planarBrownianMotion z) hjoint
  have h1 : ∀ᵐ ω ∂Q, LevelGood r ω.1 := by
    have h := hgP
    rw [← hfst] at h
    exact ae_of_ae_map (f := Prod.fst) measurable_fst.aemeasurable h
  have h2 : ∀ᵐ ω ∂Q, LevelGood r ω.2 := by
    have h := hgW
    rw [← hsnd] at h
    exact ae_of_ae_map (f := Prod.snd) measurable_snd.aemeasurable h
  have hex : ∀ᵐ ω ∂Q, ∃ τ : ℝ≥0 → ℝ≥0,
      Continuous τ ∧ StrictMono τ ∧ τ 0 = 0 ∧ ∀ u, ω.1 u = ω.2 (τ u) := by
    filter_upwards [h1, h2, hae] with ω hf hg hcls
    have hφ : ∀ k, ∃ φ : ℝ≥0 → ℝ≥0, ExactReparam (⇑ω.1) (⇑ω.2)
        (pathExitTime (ball (0 : ℂ) (r k)) ⇑ω.1).toNNReal
        (pathExitTime (ball (0 : ℂ) (r k)) ⇑ω.2).toNNReal φ := fun k => by
      have ha := toNNReal_pathExitTime_pos isOpen_ball
        (mem_ball_zero_iff.2 (hf.2.1.trans_le (hrm k.zero_le))) (hf.2.2 k)
      have hb := toNNReal_pathExitTime_pos isOpen_ball
        (mem_ball_zero_iff.2 (hg.2.1.trans_le (hrm k.zero_le))) (hg.2.2 k)
      exact exists_exactReparam_of_stoppedExitCurve_eq hf.1 hg.1 ha hb (congrFun hcls k)
    obtain ⟨τ, hτ1, hτ2, hτ3, hτ4⟩ := exists_strictMono_of_levels hrm hrt hf.2.2 hg.2.2 hφ
    exact ⟨τ, hτ2, hτ1, hτ3, hτ4⟩
  refine ⟨ContinuousPath ℂ × ContinuousPath ℂ, inferInstance, Q, hQ, Prod.snd, Prod.fst,
    fun ω => Classical.epsilon (fun τ : ℝ≥0 → ℝ≥0 =>
      Continuous τ ∧ StrictMono τ ∧ τ 0 = 0 ∧ ∀ u, ω.1 u = ω.2 (τ u)),
    measurable_snd.aemeasurable, measurable_fst.aemeasurable, hsnd, ?_, hfst.symm⟩
  filter_upwards [hex] with ω hω
  exact Classical.epsilon_spec hω

/-- **Definition 7.2 from the stopped curve classes** (BG20, Lemma 7.4, second half of the proof):
a family of path laws without interval of constancy whose stopped curve classes at exit from the
ball of radius `r` have the planar Brownian laws for almost every `r > ‖z‖` is a time-changed
Brownian motion with a continuous strictly increasing time change. -/
theorem definesTimeChangedBM_of_exitClassLaws (P : PathLawFamily)
    (hflat : ∀ z : ℂ, ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
      {f : ContinuousPath ℂ | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0)
    (hb : ∀ z : ℂ, ∀ᵐ r ∂(volume : Measure ℝ), ‖z‖ < r →
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
        (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r))) :
    DefinesTimeChangedBM P := fun z => exists_timeChange_coupling (hflat z) (hb z)

end MatedCRT.ExitReparamAssembly
