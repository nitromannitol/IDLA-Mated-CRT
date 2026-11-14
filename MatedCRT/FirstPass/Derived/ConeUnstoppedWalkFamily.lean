import MatedCRT.FirstPass.Derived.StoppedWalkCarrier
import MatedCRT.FirstPass.Derived.ConeEnvironmentJointLaw

/-! # Joint cone scaling of embedded walks from all vertices -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set LatticeProb
open scoped NNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- The embedded interpolated walk depends measurably on the embedding and walk. -/
theorem measurable_interpPathCM_random (v : Ω → ℤ → ℂ) (hv : Measurable v) (m : ℝ≥0) :
    Measurable fun p : Ω × (ℕ → ℤ) => interpPathCM (v p.1) m.coe_nonneg p.2 := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have h1 : ∀ n : ℕ, Measurable fun p : Ω × (ℕ → ℤ) => v p.1 (p.2 n) := fun n =>
    (measurable_from_prod_countable_left (f := fun q : (ℤ → ℂ) × ℤ => q.1 q.2)
      fun y => measurable_pi_apply y).comp
      ((hv.comp measurable_fst).prodMk ((measurable_pi_apply n).comp measurable_snd))
  simp only [interpPathCM_apply, interpPathFn, linInterp]
  exact (measurable_const.mul (h1 _)).add (measurable_const.mul (h1 _))

/-- The quenched law of the embedded walk depends measurably on its environment. -/
theorem measurable_interpPathCM_srwLaw (v : Ω → ℤ → ℂ) (hv : Measurable v)
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (m : ℝ≥0) (a : ℤ) :
    Measurable fun ω => (srwLaw (M ω) a).map (interpPathCM (v ω) m.coe_nonneg) := by
  let κ : Kernel Ω (ℕ → ℤ) := ⟨fun ω => srwLaw (M ω) a,
    GreenEnvironment.measurable_srwLaw M hM a⟩
  have : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_srwLaw (M ω) a⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hset : MeasurableSet {p : Ω × (ℕ → ℤ) | interpPathCM (v p.1) m.coe_nonneg p.2 ∈ s} :=
    measurable_interpPathCM_random v hv m hs
  have h := κ.measurable_kernel_prodMk_left hset
  convert h using 1
  funext ω
  exact Measure.map_apply (measurable_interpPathCM (v ω) m.coe_nonneg) hs

/-- Starting positions and quenched laws of the whole walks at all vertices. -/
noncomputable def walkVertexFamily (ε : ℝ) (η : ℝ → ℂ) (bm : ℝ → ℝ × ℝ)
    (m : ℝ≥0) : ℤ → ℂ × Measure C(ℝ≥0, ℂ) := fun a =>
  (vertexPoint ε η a,
    (srwLaw (bmEdgeCount ε (fun t => (bm t).1) (fun t => (bm t).2)) a).map
      (interpPathCM (vertexPoint ε η) m.coe_nonneg))

/-- The whole vertex-indexed family is measurable on the continuous data carrier. -/
theorem measurable_walkVertexFamily (ε : ℝ) (m : ℝ≥0) :
    Measurable fun p : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) => walkVertexFamily ε p.1 p.2 m := by
  have hv : Measurable (fun p : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) => vertexPoint ε p.1) := by
    apply measurable_pi_iff.2
    intro k
    exact (ContinuousMap.measurable_eval _).comp measurable_fst
  have hM : ∀ j k, Measurable (fun p : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) =>
      bmEdgeCount ε (fun t => (p.2 t).1) (fun t => (p.2 t).2) j k) := by
    intro j k
    exact (measurable_bmEdgeCount_path ε j k).comp measurable_snd
  apply measurable_pi_iff.2
  intro a
  exact ((ContinuousMap.measurable_eval _).comp measurable_fst).prodMk
    (measurable_interpPathCM_srwLaw _ hv _ hM m a)

/-- The family of embedded walks has the same joint law after cone rescaling. -/
theorem MatedCRTEnv.IsValid.map_walkVertexFamily_rescaled
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    (ε : ℝ) (m : ℝ≥0) :
    S.P.map (fun ω => walkVertexFamily ε
      (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
      (rescaledPair b (S.bm ω)) m) =
    S.P.map (fun ω => walkVertexFamily ε (S.η ω) (S.bm ω) m) := by
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  let G : MatedCRTHarmonic.MatedCRT.CouplingData → ℤ → ℂ × Measure C(ℝ≥0, ℂ) :=
    fun v => walkVertexFamily ε v.η v.bm m
  have hG : Measurable G := (measurable_walkVertexFamily ε m).comp
    (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.prodMk
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm)
  have hmap := congrArg (fun μ => Measure.map G μ) hlaw
  rw [Measure.map_map hG hV', Measure.map_map hG hV] at hmap
  refine (Measure.map_congr ?_).trans (hmap.trans (Measure.map_congr ?_))
  · filter_upwards [hid] with ω hω
    dsimp [G, walkVertexFamily]
    rw [hω.1, hω.2.1]
  · filter_upwards [htie] with ω hω
    dsimp [G, walkVertexFamily]
    rw [hω.1, hbm ω]

end MatedCRT
