import MatedCRT.FirstPass.Derived.ZeroConeConnectedAlongLines
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-!
# Translation invariance and ergodicity modulo scaling of the shifted zero-cone cell configuration

Gwynne–Miller–Sheffield (arXiv:1705.11161, Section 3.1, (3.1)) consider a `0`-quantum cone `(ℂ, h, 0, ∞)` with the
circle-average embedding, an independent whole-plane space-filling SLE `η` parametrized by `γ`-LQG mass with
`η(0) = 0`, an independent phase `θ` uniform on `[0, 1]`, and the cell configuration `H = {η([x - 1, x]) : x ∈ ℤ + θ}`,
two cells being adjacent when they share a non-trivial boundary arc, with conductance `2` when they share both a left
and a right boundary arc and `1` otherwise. Proposition 3.1 there verifies the hypotheses of the invariance principle
for random cell configurations (Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16). Two of these hypotheses
rest on properties of the zero-quantum cone and of space-filling SLE that are not part of the mating-of-trees
coupling; this file states them as named hypotheses on the configuration of the coupling, in the form verified in
the proof of Proposition 3.1:

* `ZeroConeSpatialAverageInvariance` (paragraph "Translation invariance modulo scaling" of the proof): condition 2 of
  Definition 1.2 of arXiv:1807.07515 (attainability as a spatial average of the sample instance) with
  `U_j = B_{R_j}(0)`: if `z_j` is sampled uniformly from Lebesgue measure on `B_{R_j}(0)`, then for some random
  `C_j > 0` the configurations `C_j (H - z_j)` converge in law to `H` (from the proof of
  Duplantier–Miller–Sheffield, arXiv:1409.7055, Proposition 4.13(ii), and the translation and scale invariance of the
  law of whole-plane space-filling SLE modulo time parametrization);
* `ZeroConeTailTriviality` (paragraph "Ergodicity modulo scaling" of the proof, from Lemma A.1 and Remark A.2
  there): every bounded measurable function `Φ` of `H` with `Φ(C (H - z)) = Φ(H)` for all `C > 0`, `z ∈ ℂ` is almost
  surely constant.

In the coupling, the configuration (3.1) is the configuration of
`exists_zeroCone_clocked_shiftedCellConfig_connectedAlongLines` with `ε = 1` and `θ` uniform on `[0, 1]`: the cells
`η₀([x - 1 + θ, x + θ])`, `x ∈ ℤ`, of the zero-cone curve, with the contour edge counts of the transported
boundary-length pair `G = bm ∘ ψ` (`ψ` the clock of the zero cone). `IsZeroConeConfigRealization` records that a
random element `F` of the GMS space realizes it.

From the second hypothesis, `ergodicModuloScaling_map_of_zeroConeTailTriviality` proves `ErgodicModuloScaling` for the
law of every realization, and `exists_zeroCone_config_ergodicModuloScaling_connectedAlongLines` assembles it with
connectedness along lines.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal BoundedContinuousFunction

/-- The law of the phase `θ` in (3.1) of arXiv:1705.11161: uniform on `[0, 1]`. -/
def zeroConePhase : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure zeroConePhase :=
  ⟨by simp [zeroConePhase]⟩

/-- `C (H - z)` as a point of the GMS space, for the scale factor `C = exp c > 0`. -/
def similarityConfig (c : ℝ) (z : ReflectedGMS.Plane) (H : GMSSpace) : GMSSpace :=
  ⟨H.1.similarity (Real.exp c) z (Real.exp_pos c),
    CellConfig.isCellConfiguration_similarity (Real.exp c) z (Real.exp_pos c) H.2⟩

section Hypotheses

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **`F` realizes the shifted zero-cone cell configuration (3.1) of arXiv:1705.11161 in the GMS space.** `G` is the
boundary-length pair of the zero-cone curve, `G ω t = bm ω (ψ t)` almost surely with `ψ` the clock of the zero cone,
and `F : Ω × ℝ → GMSSpace` is almost measurable for `P ⊗ Unif[0, 1]` with `F (ω, θ)` almost surely equal to the
configuration of the cells `η₀([x - 1 + θ, x + θ])`, `x ∈ ℤ`, with the contour edge counts of the time-translated
pair `t ↦ G ω (t + θ)`. -/
def IsZeroConeConfigRealization (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (G : Ω → Path2) (F : Ω × ℝ → GMSSpace) : Prop :=
  Measurable G ∧
    (∀ᵐ ω ∂P, ∀ t, G ω t = bm ω (CellScaling.JointScalingO.clock γ
      (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) (η₀ ω) t)) ∧
    AEMeasurable F (P.prod zeroConePhase) ∧
    ∀ᵐ p ∂P.prod zeroConePhase, ∃ h : IsAreaParametrized
        ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
      (F p).1 = shiftedAreaCellConfig h one_pos p.2
        (bmEdgeCount 1 (fun t => (G p.1 (t + 1 * p.2)).1) (fun t => (G p.1 (t + 1 * p.2)).2))

/-- **Translation invariance modulo scaling of the shifted zero-cone cell configuration, in the spatial-average
form** (condition 2 of Definition 1.2 of Gwynne–Miller–Sheffield, arXiv:1807.07515), as verified in the proof of
Proposition 3.1 of arXiv:1705.11161 (paragraph "Translation invariance modulo scaling", from the proof of
Duplantier–Miller–Sheffield, arXiv:1409.7055, Proposition 4.13(ii)). For every realization `F` of the configuration
there are random radii `R_j → ∞` (there: `R_j` the largest `r` with `h_r(0) + Q log r = γ⁻¹ log j`) and random scale
factors `C_j = exp (c_j) > 0`, depending on everything and on the sampled point, such that, with `z_j` sampled
uniformly from Lebesgue measure on `B_{R_j}(0)` given everything, `C_j (H - z_j)` converges in law to `H`: the
integral of every bounded continuous function on the GMS space (topology of the metric `d^CC`) converges. -/
def ZeroConeSpatialAverageInvariance
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
    ∃ R : ℕ → Ω → ℝ, (∀ j, Measurable (R j)) ∧ (∀ j ω, 0 < R j ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => R j ω) atTop atTop) ∧
      ∃ c : ℕ → (Ω × ℝ) × ReflectedGMS.Plane → ℝ,
        (∀ j, AEMeasurable (fun q => similarityConfig (c j q) q.2 (F q.1))
          ((P.prod zeroConePhase).prod volume)) ∧
        ∀ φ : GMSSpace →ᵇ ℝ, Tendsto
          (fun j => ∫ p, (⨍ z in Metric.ball (0 : ReflectedGMS.Plane) (R j p.1),
            φ (similarityConfig (c j (p, z)) z (F p))) ∂(P.prod zeroConePhase))
          atTop (𝓝 (∫ p, φ (F p) ∂(P.prod zeroConePhase)))

/-- **Tail triviality modulo scaling of the shifted zero-cone cell configuration**, as verified in the proof of
Proposition 3.1 of Gwynne–Miller–Sheffield, arXiv:1705.11161 (paragraph "Ergodicity modulo scaling", from Lemma A.1
and Remark A.2 there): for every realization `F` of the configuration, every bounded Borel function `Φ` on the GMS
space with `Φ(C (H - z)) = Φ(H)` for all `C > 0` and `z` is almost surely constant along `F`. -/
def ZeroConeTailTriviality
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  ∀ (G : Ω → Path2) (F : Ω × ℝ → GMSSpace), IsZeroConeConfigRealization D hγ G F →
    ∀ Φ : GMSSpace → ℝ, Measurable Φ → (∃ M : ℝ, ∀ H, |Φ H| ≤ M) →
      (∀ (s : ℝ) (u) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' → Φ H' = Φ H) →
      ∃ c : ℝ, ∀ᵐ p ∂P.prod zeroConePhase, Φ (F p) = c

/-- **Ergodicity modulo scaling of the shifted zero-cone cell configuration** (hypothesis 2 of
Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16, Definition 1.3): under the tail triviality of the zero cone,
the law of every realization of the configuration (3.1) of arXiv:1705.11161 gives every Borel event invariant under
`H ↦ C (H - z)` probability `0` or `1`. -/
theorem ergodicModuloScaling_map_of_zeroConeTailTriviality
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hT : ZeroConeTailTriviality D hγ) {G : Ω → Path2} {F : Ω × ℝ → GMSSpace}
    (hF : IsZeroConeConfigRealization D hγ G F) :
    ErgodicModuloScaling ((P.prod zeroConePhase).map F) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hFm : AEMeasurable F (P.prod zeroConePhase) := hF.2.2.1
  have hν : IsProbabilityMeasure ((P.prod zeroConePhase).map F) :=
    (Measure.isProbabilityMeasure_map_iff hFm).2 inferInstance
  intro A hA hinv
  have hbd : ∃ M : ℝ, ∀ H, |A.indicator (fun _ => (1 : ℝ)) H| ≤ M := by
    refine ⟨1, fun H => ?_⟩
    by_cases h : H ∈ A <;> simp [h]
  have hinv' : ∀ (s : ℝ) (u : ReflectedGMS.Plane) (hs : 0 < s) (H H' : GMSSpace),
      IsSimilar s u hs H H' →
        A.indicator (fun _ => (1 : ℝ)) H' = A.indicator (fun _ => (1 : ℝ)) H := by
    intro s u hs H H' hHH'
    have hiff := hinv s u hs H H' hHH'
    by_cases h : H ∈ A
    · simp [h, hiff.1 h]
    · have h' : H' ∉ A := fun h' => h (hiff.2 h')
      simp [h, h']
  obtain ⟨c, hc⟩ := hT G F hF _ (measurable_const.indicator hA) hbd hinv'
  by_cases hc1 : c = 1
  · right
    have hae : ∀ᵐ H ∂((P.prod zeroConePhase).map F), H ∈ A := by
      refine (ae_map_iff (p := fun H => H ∈ A) hFm hA).2 ?_
      filter_upwards [hc] with p hp
      show F p ∈ A
      by_contra hn
      have h0 : A.indicator (fun _ => (1 : ℝ)) (F p) = 0 := by simp [hn]
      rw [h0] at hp
      exact zero_ne_one (hp.trans hc1)
    have h0 : (P.prod zeroConePhase).map F Aᶜ = 0 := by
      rw [Set.compl_def]
      exact ae_iff.mp hae
    exact (prob_compl_eq_zero_iff hA).1 h0
  · left
    have hae : ∀ᵐ H ∂((P.prod zeroConePhase).map F), H ∉ A := by
      refine (ae_map_iff (p := fun H => H ∉ A) hFm hA.compl).2 ?_
      filter_upwards [hc] with p hp
      show F p ∉ A
      intro hmem
      have h1 : A.indicator (fun _ => (1 : ℝ)) (F p) = 1 := by simp [hmem]
      exact hc1 (hp.symm.trans h1)
    have h0 := ae_iff.mp hae
    simp only [not_not, Set.ofPred_mem_eq] at h0
    exact h0

/-- **Hypotheses 2 and 3 of the invariance principle for the shifted zero-cone cell configuration**
(Gwynne–Miller–Sheffield, arXiv:1807.07515, Theorem 1.16, as verified in arXiv:1705.11161, Proposition 3.1). For the
configuration (3.1) of arXiv:1705.11161 in the coupling (unit-area cells `η₀([x - 1 + θ, x + θ])` of the zero-cone
curve, contour edge counts of the transported boundary-length pair `G = bm ∘ ψ`, phase `θ` uniform on `[0, 1]`), every
realization `F` in the GMS space, measurable for the Borel σ-algebra of `d^CC`, has a law connected along lines, and,
under the tail triviality of the zero cone, ergodic modulo scaling. -/
theorem exists_zeroCone_config_ergodicModuloScaling_connectedAlongLines
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P) :
    ∃ G : Ω → Path2, ∃ H : Ω × ℝ → CellConfig,
      (∀ᵐ p ∂P.prod zeroConePhase, ∃ h : IsAreaParametrized
          ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
        H p = shiftedAreaCellConfig h one_pos p.2
          (bmEdgeCount 1 (fun t => (G p.1 (t + 1 * p.2)).1) (fun t => (G p.1 (t + 1 * p.2)).2)) ∧
          (H p).IsCellConfiguration) ∧
      AEMeasurable (fun p => (H p).code) (P.prod zeroConePhase) ∧
      ∀ F : Ω × ℝ → GMSSpace, AEMeasurable F (P.prod zeroConePhase) →
        (∀ᵐ p ∂P.prod zeroConePhase, (F p).1 = H p) →
        IsZeroConeConfigRealization D hγ G F ∧
          ConnectedAlongLines ((P.prod zeroConePhase).map F) ∧
          (ZeroConeTailTriviality D hγ → ErgodicModuloScaling ((P.prod zeroConePhase).map F)) := by
  have hQ : zeroConePhase ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hphase : ∀ᵐ θ ∂zeroConePhase, θ ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  obtain ⟨G, hG, hclock, H, hH, hcode, hcal⟩ :=
    exists_zeroCone_clocked_shiftedCellConfig_connectedAlongLines D hγ hf one_pos zeroConePhase hQ hphase
  refine ⟨G, H, hH, hcode, fun F hF hF_eq => ?_⟩
  have hreal : IsZeroConeConfigRealization D hγ G F := by
    refine ⟨hG, ?_, hF, ?_⟩
    · filter_upwards [hclock] with ω hω
      obtain ⟨ψ, _, _, hGψ, hψ, _⟩ := hω
      intro t
      rw [hGψ t, hψ t]
    · filter_upwards [hH, hF_eq] with p hp hpF
      obtain ⟨h, hEq, -⟩ := hp
      exact ⟨h, hpF.trans hEq⟩
  exact ⟨hreal, hcal F hF hF_eq, fun hT => ergodicModuloScaling_map_of_zeroConeTailTriviality D hγ hT hreal⟩

end Hypotheses

end MatedCRT
