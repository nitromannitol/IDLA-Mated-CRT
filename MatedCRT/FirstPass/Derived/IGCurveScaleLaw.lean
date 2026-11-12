import MatedCRT.Proofs.Sec1.EnvironmentScaling.IGCurveScaling
import LatticeProb.Prob.UniformModShift
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Scale invariance in law of whole-plane space-filling SLE

Let `(hIG₀, U, ηL)` be the imaginary-geometry part of a mating-of-trees coupling: `hIG₀` is a
whole-plane GFF normalized by `hIG₀_1(0) = 0`, `U` is uniform on `[0, 2πχ)` and independent of
`hIG₀`, and the whole-plane space-filling SLE_{κ'} curve `ηL` (parametrized by Lebesgue measure,
`ηL 0 = 0`) is a fixed measurable function `Φ` of the circle-average array of the whole-plane GFF
modulo `2πχ`, `hIG = hIG₀ + U`.

**Theorem.** For each `s > 0`, the dilated curve `affineReroot 0 s 0 ηL = s⁻¹ ηL(s² ·)` has the
law of `ηL`.

Proof (the scaling step of the main law lemma). By the coordinate change of imaginary geometry
(`igMap_scale_normalized_identity`), almost surely `s⁻¹ ηL(s² ·) = Φ(A − a + V)`, where
`A(r, w) = hIG₀_{sr}(sw)`, `a = hIG₀_s(0)` and `V = (U + a) mod 2πχ`. The circle-average array of
the normalized dilated field `I = hIG₀(s ·) − a` is `A − a` at every fixed positive radius and
center almost surely, so the array `A − a + V` is a modification (at positive radii, the only ones
`Φ` reads) of the array of `(I, V)`. The pair `(I, V)` has the law of `(hIG₀, U)`: `I` has the law
of `hIG₀` (scale invariance of the normalized whole-plane GFF) and `V` is uniform and independent
of `hIG₀`, hence of `I`. Since the law of a process on the product σ-algebra is that of any of
its modifications, `Φ(A − a + V)` has the law of `Φ(array of (hIG₀, U)) = ηL`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace MatedCRT.Sec1

open MatedCRTHarmonic.MatedCRT (affineReroot igChi)

/-- `χ = 2/γ − γ/2 > 0` for `γ ∈ (0, 2)`. -/
theorem igChi_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < igChi γ := by
  have h1 : γ / 2 < 1 := by linarith
  have h2 : 1 < 2 / γ := by rw [lt_div_iff₀ hγ]; linarith
  unfold igChi
  linarith

/-- **Scale invariance in law of whole-plane space-filling SLE.** For a mating-of-trees
coupling with `γ ∈ (0, 2)` and each `s > 0`, the curve `affineReroot 0 s 0 ηL` (that is,
`s⁻¹ ηL(s² ·)`, re-rooted at its hitting time of `0`) has the law of `ηL`. -/
theorem map_affineReroot_igCurve {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) (s : ℝ) (hs : 0 < s) :
    P.map (fun ω => affineReroot 0 s 0 (ηL ω)) = P.map ηL := by
  have := h.isProbabilityMeasure
  have hp : 0 < 2 * Real.pi * igChi γ := by
    have := igChi_pos hγ hγ2
    positivity
  obtain ⟨hh, hUlaw, hindIU⟩ := h.igField
  have hUlaw' : P.map U = LatticeProb.uniformIco (2 * Real.pi * igChi γ) := hUlaw
  -- a measurable version `U'` of the uniform variable
  have hUae : AEMeasurable U P := by
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x : ℝ, P.map U = Measure.dirac x :=
      ⟨_, Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)⟩
    have h1 : LatticeProb.uniformIco (2 * Real.pi * igChi γ) {x} = 0 :=
      ProbabilityTheory.cond_absolutelyContinuous (Real.volume_singleton)
    rw [← hUlaw', hx, Measure.dirac_apply_of_mem (Set.mem_singleton x)] at h1
    exact one_ne_zero h1
  set U' : Ω → ℝ := hUae.mk U with hU'_def
  have hU'm : Measurable U' := hUae.measurable_mk
  have hUU' : U =ᵐ[P] U' := hUae.ae_eq_mk
  have hU'law : P.map U' = LatticeProb.uniformIco (2 * Real.pi * igChi γ) := by
    rw [← Measure.map_congr hUU']
    exact hUlaw'
  have hIm : Measurable hIG₀ := hh.1.measurable
  have hind' : IndepFun U' hIG₀ P := (hindIU.congr (ae_eq_refl _) hUU').symm
  -- the normalizing constant `a`, the normalized dilated field `G`, the reduced uniform `V`
  set a : MatedCRTHarmonic.MatedCRT.Field → ℝ := fun g => LQGMetric.circleAvg g s 0 with ha_def
  have ham : Measurable a := LQGMetric.measurable_circleAvg_left s 0
  set G : MatedCRTHarmonic.MatedCRT.Field → MatedCRTHarmonic.MatedCRT.Field :=
    fun g => LQGMetric.addConst (LQGMetric.affineComp s 0 g) (-LQGMetric.circleAvg g s 0)
    with hG_def
  have hGm : Measurable G := by
    refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
    simp only [hG_def, LQGMetric.GFFInv.addConst_apply]
    exact ((LQGMetric.measurable_distOn_apply φ).comp (LQGMetric.measurable_affineComp s 0)).add
      ((LQGMetric.measurable_circleAvg_left s 0).neg.const_mul _)
  set V : Ω → ℝ := fun ω => toIcoMod hp 0 (U' ω + a (hIG₀ ω)) with hV_def
  have hVm : Measurable V :=
    (LatticeProb.measurable_toIcoMod_zero hp).comp (hU'm.add (ham.comp hIm))
  -- the pair `(G hIG₀, V)` has the law of `(hIG₀, U')`
  have hpair : P.map (fun ω => (G (hIG₀ ω), V ω)) = P.map (fun ω => (hIG₀ ω, U' ω)) := by
    have hVI := LatticeProb.indepFun_toIcoMod_add_uniformIco hp hU'm hIm hU'law hind' ham
    have hVG := LatticeProb.indepFun_toIcoMod_add_uniformIco_comp hp hU'm hIm hU'law hind' ham hGm
    have hGI : Measurable fun ω => G (hIG₀ ω) := hGm.comp hIm
    rw [(indepFun_iff_map_prod_eq_prod_map_map hGI.aemeasurable hVm.aemeasurable).1 hVG.symm,
      (indepFun_iff_map_prod_eq_prod_map_map hIm.aemeasurable hU'm.aemeasurable).1 hind'.symm]
    congr 1
    · exact LQGMetric.CircleAvg.map_affine_sub_circleAvg hh hs 0
    · rw [hVI.1, hU'law]
  -- the circle-average array at positive radii, as a function of (field, constant)
  set H : MatedCRTHarmonic.MatedCRT.Field × ℝ → (ℝ × ℂ → ℝ) :=
    fun q x => if 0 < x.1 then LQGMetric.circleAvg q.1 x.1 x.2 + q.2 else 0 with hH_def
  have hHm : Measurable H := by
    refine measurable_pi_iff.2 fun x => ?_
    by_cases hx : 0 < x.1
    · simp only [hH_def, hx, ↓reduceIte]
      exact ((LQGMetric.measurable_circleAvg_left x.1 x.2).comp measurable_fst).add measurable_snd
    · simp only [hH_def, hx, ↓reduceIte]
      exact measurable_const
  -- the dilated array `A − a + V` at positive radii
  set W : Ω → ℝ × ℂ → ℝ := fun ω x => if 0 < x.1 then
      LQGMetric.circleAvg (hIG₀ ω) (s * x.1) (s * x.2) - a (hIG₀ ω) + V ω else 0 with hW_def
  have hWm : Measurable W := by
    refine measurable_pi_iff.2 fun x => ?_
    by_cases hx : 0 < x.1
    · simp only [hW_def, hx, ↓reduceIte]
      exact (((LQGMetric.measurable_circleAvg_left _ _).comp hIm).sub (ham.comp hIm)).add hVm
    · simp only [hW_def, hx, ↓reduceIte]
      exact measurable_const
  -- `W` is a modification of the array of `(G hIG₀, V)`
  have hlaw1 : P.map W = P.map (fun ω => H (G (hIG₀ ω), V ω)) := by
    refine map_eq_of_forall_ae_eq (X := fun x ω => W ω x)
      (Y := fun x ω => H (G (hIG₀ ω), V ω) x) hWm.aemeasurable
      (hHm.comp ((hGm.comp hIm).prodMk hVm)).aemeasurable fun x => ?_
    by_cases hx : 0 < x.1
    · have hA := LQGMetric.CircleAvg.ae_circleAvg_addConst (hh.1.affineComp hs 0) x.2 hx
      have hB := LQGMetric.CircleAvg.ae_circleAvg_affineComp (hh.1.affineComp hs 0) hx x.2
      have hC := LQGMetric.CircleAvg.ae_circleAvg_affineComp hh.1 (mul_pos hs hx) ((s : ℂ) * x.2)
      filter_upwards [hA, hB, hC] with ω hAω hBω hCω
      simp only [hW_def, hH_def, hG_def, ha_def, hx, ↓reduceIte]
      rw [hAω, ← hBω, LQGMetric.GM.affineComp_comp hx.ne' hs.ne', add_zero, hCω]
      ring
    · filter_upwards with ω
      simp only [hW_def, hH_def, hx, ↓reduceIte]
  have hlaw2 : P.map (fun ω => H (G (hIG₀ ω), V ω)) = P.map (fun ω => H (hIG₀ ω, U' ω)) :=
    calc P.map (fun ω => H (G (hIG₀ ω), V ω))
        = (P.map (fun ω => (G (hIG₀ ω), V ω))).map H :=
          (Measure.map_map hHm ((hGm.comp hIm).prodMk hVm)).symm
      _ = (P.map (fun ω => (hIG₀ ω, U' ω))).map H := by rw [hpair]
      _ = P.map (fun ω => H (hIG₀ ω, U' ω)) := Measure.map_map hHm (hIm.prodMk hU'm)
  -- the coordinate change of imaginary geometry
  obtain ⟨Φ, hΦm, hign, hrep, hcov, -⟩ := h.igMap
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) :=
    h.spaceFilling.mono fun ω hω => hω.2.1
  have hwit := igMap_scale_normalized_identity P γ
    (fun ω ρ w => LQGMetric.circleAvg (hIG₀ ω) ρ w + U ω) ηL Φ hrep hcov htr s hs
    (fun ω (r : ℝ) (w : ℂ) => LQGMetric.circleAvg (hIG₀ ω) (s * r) (s * w))
    (fun ω => LQGMetric.circleAvg (hIG₀ ω) s 0) U (fun ω r w => rfl)
  have hcurry : Measurable (Function.curry : (ℝ × ℂ → ℝ) → ℝ → ℂ → ℝ) :=
    measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun w => measurable_pi_apply (r, w)
  have hΨm : Measurable fun f : ℝ × ℂ → ℝ => Φ (Function.curry f) := hΦm.comp hcurry
  have hleft : ∀ᵐ ω ∂P, affineReroot 0 s 0 (ηL ω) = Φ (Function.curry (W ω)) := by
    filter_upwards [hwit, hUU'] with ω hω hUω
    rw [← hω]
    refine hign _ _ fun ρ hρ => ?_
    funext w
    simp only [Function.curry, hW_def, hV_def, ha_def, hρ, ↓reduceIte, hUω, toIcoMod,
      toIcoDiv_eq_floor, sub_zero, zsmul_eq_mul]
  have hright : ∀ᵐ ω ∂P, Φ (Function.curry (H (hIG₀ ω, U' ω))) = ηL ω := by
    filter_upwards [hrep, hUU'] with ω hω hUω
    rw [hω]
    refine hign _ _ fun ρ hρ => ?_
    funext w
    simp only [Function.curry, hH_def, hρ, ↓reduceIte, hUω]
  calc P.map (fun ω => affineReroot 0 s 0 (ηL ω))
      = P.map (fun ω => Φ (Function.curry (W ω))) := Measure.map_congr hleft
    _ = (P.map W).map (fun f => Φ (Function.curry f)) := (Measure.map_map hΨm hWm).symm
    _ = (P.map (fun ω => H (hIG₀ ω, U' ω))).map (fun f => Φ (Function.curry f)) := by
      rw [hlaw1, hlaw2]
    _ = P.map (fun ω => Φ (Function.curry (H (hIG₀ ω, U' ω)))) :=
      Measure.map_map hΨm (hHm.comp (hIm.prodMk hU'm))
    _ = P.map ηL := Measure.map_congr hright

end MatedCRT.Sec1
