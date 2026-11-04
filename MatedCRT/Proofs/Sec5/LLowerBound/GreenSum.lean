import MatedCRT.Proofs.Sec5.LLowerBound.GreenEstimates
import MatedCRT.Proofs.Sec5.MeanValueInequality.GreenReversibility

/-!
# Green sums over a finite subdomain

A lower bound on the normalized Green kernel in a smaller domain yields a
lower bound on the incoming Green-function sum over a larger domain. The
Green-function first-step and reversibility infrastructure includes work by
Leonardo Bonanno.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Sum the local kernel lower bound over a finite set, using domain
monotonicity and reversibility to orient the Green function toward `a`. -/
theorem greenSum_lower_of_kernel {m : ℤ → ℤ → ℕ} {D C A : Set ℤ} {a : ℤ} {q : ℝ}
    (hsymm : ∀ x y, m x y = m y x) (hlf : ∀ x, {y | m x y ≠ 0}.Finite)
    (hcons : ∀ x, m x (x + 1) ≠ 0) (hA : A.Finite) (hC : C.Finite)
    (hDC : D ⊆ C) (hCA : C ⊆ A)
    (hkernel : ∀ b ∈ D, q ≤ greenKernel m C a b) :
    q * (D.ncard : ℝ) ≤ ∑' b : A, greenFn m A b a := by
  classical
  have := hA.fintype
  have := (hC.subset hDC).fintype
  have hdeg : ∀ x, mdeg m x ≠ 0 := fun x => (mdeg_pos_of_ne_zero hlf (hcons x)).ne'
  have hdeg1 : (1 : ℝ) ≤ mdeg m a := by
    exact_mod_cast mdeg_pos_of_ne_zero hlf (hcons a)
  have hfirstC := greenFn_laplacian_fst hlf hcons hC
  have hfirstA := greenFn_laplacian_fst hlf hcons hA
  have hpoint : ∀ b ∈ D, q ≤ greenFn m A b a := by
    intro b hb
    have h := hkernel b hb
    rw [greenKernel_symm_of_firstStep hsymm hlf hC hdeg hfirstC a b] at h
    change q ≤ greenFn m C b a / (mdeg m a : ℝ) at h
    exact h.trans ((div_le_self (greenFn_nonnegative m C b a) hdeg1).trans
      (greenFn_mono_of_firstStep hlf hcons hC hCA hfirstC hfirstA b a))
  let f : D → A := fun b => ⟨b, hCA (hDC b.property)⟩
  have hf : Function.Injective f := fun x y h => Subtype.ext (congrArg (fun z : A => (z : ℤ)) h)
  have hsum : (∑' _ : D, q) ≤ ∑' b : A, greenFn m A b a :=
    Summable.tsum_le_tsum_of_inj f hf (fun b _ => greenFn_nonnegative m A b a)
      (fun b => hpoint b b.property) ((hasSum_fintype _).summable) ((hasSum_fintype _).summable)
  have hcard : (∑' _ : D, q) = q * (D.ncard : ℝ) := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Set.ncard_eq_toFinset_card' D, Set.toFinset_card]
    ring
  rwa [hcard] at hsum

/-- A positive mass and the counting-measure error give the power-law Green
sum required in Lemma 5.4 once the scale is sufficiently small. -/
theorem greenSum_lower_of_count {m : ℤ → ℤ → ℕ} {D C A : Set ℤ} {a : ℤ}
    (hsymm : ∀ x y, m x y = m y x) (hlf : ∀ x, {y | m x y ≠ 0}.Finite)
    (hcons : ∀ x, m x (x + 1) ≠ 0) (hA : A.Finite) (hC : C.Finite)
    (hDC : D ⊆ C) (hCA : C ⊆ A) {ε α M : ℝ} (hε : 0 < ε)
    (hkernel : ∀ b ∈ D, (1 / 2 : ℝ) ≤ greenKernel m C a b)
    (hcount : ε⁻¹ * M - ε ^ (-1 + α) ≤ (D.ncard : ℝ))
    (herr : ε ^ α ≤ M / 2) (hsmall : ε ^ (1 / 4 : ℝ) ≤ M / 4) :
    ε ^ (-(3 / 4 : ℝ)) ≤ ∑' b : A, greenFn m A b a := by
  have hsum := greenSum_lower_of_kernel hsymm hlf hcons hA hC hDC hCA hkernel
  have herr' : ε⁻¹ * ε ^ α ≤ ε⁻¹ * (M / 2) :=
    mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hε.le)
  have hsmall' : ε⁻¹ * ε ^ (1 / 4 : ℝ) ≤ ε⁻¹ * (M / 4) :=
    mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hε.le)
  have hpow (x : ℝ) : ε ^ (-1 + x) = ε⁻¹ * ε ^ x := by
    rw [Real.rpow_add hε, Real.rpow_neg_one]
  rw [hpow] at hcount
  have hpow' : ε ^ (-(3 / 4 : ℝ)) = ε⁻¹ * ε ^ (1 / 4 : ℝ) := by
    convert hpow (1 / 4) using 1
    norm_num
  rw [hpow']
  linarith

/-- The logarithmic kernel estimate is at least `1/2` inside a sufficiently
small ball. -/
theorem half_le_greenKernel_of_log {C x g : ℝ} (hC : 0 < C)
    (hx : Real.exp (3 / 2 * C) ≤ x) (hg : C⁻¹ * Real.log x - 1 ≤ g) :
    (1 / 2 : ℝ) ≤ g := by
  have hlog : 3 / 2 * C ≤ Real.log x := by
    rw [← Real.log_exp (3 / 2 * C)]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hscaled : 3 / 2 ≤ C⁻¹ * Real.log x := by
    rw [le_inv_mul_iff₀ hC]
    linarith
  linarith

/-- Lemma 2.9 with the constant test function gives a lower bound on the
number of cells meeting `D`. The choice of representatives follows the
counting argument in the Lemma 6.8 development. -/
theorem count_cells_of_counting_measure {ε ρ α β : ℝ} {η : ℝ → ℂ} {μ : Measure ℂ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) {D : Set ℂ}
    (hD : D ⊆ ball 0 ρ) (hfin : (cellVertices ε η D).Finite)
    (h29 : ∀ (E : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), E ⊆ ball 0 ρ →
      (∀ x ∈ thickening (ε ^ α) E, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β)) →
      (∀ x ∈ thickening (ε ^ α) E, ∀ y ∈ thickening (ε ^ α) E,
        |f x - f y| ≤ ε ^ (-β) * ‖x - y‖) →
      (∀ k ∈ cellVertices ε η E, w k ∈ cell ε η k ∩ closure E) →
      ε⁻¹ * ∫ x in E, f x ∂μ - ε ^ (-1 + α) ≤ ∑' k : cellVertices ε η E, f (w k)) :
    ε⁻¹ * (μ D).toReal - ε ^ (-1 + α) ≤ ((cellVertices ε η D).ncard : ℝ) := by
  classical
  have h := h29 D (fun _ => 1)
    (fun k => if hk : (cell ε η k ∩ D).Nonempty then hk.some else 0) hD
    (fun _ _ => ⟨zero_le_one, by
      rw [abs_one]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)⟩)
    (fun _ _ _ _ => by simp only [sub_self, abs_zero]; positivity)
    (fun k hk => by
      have hk' : (cell ε η k ∩ D).Nonempty := hk
      rw [dite_eq_left hk']
      exact ⟨hk'.some_mem.1, subset_closure hk'.some_mem.2⟩)
  have := hfin.fintype
  have hcard : (∑' _ : cellVertices ε η D, (1 : ℝ)) = (cellVertices ε η D).ncard := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Set.ncard_eq_toFinset_card' _, Set.toFinset_card]
  simpa only [hcard, setIntegral_const, smul_eq_mul, mul_one, measureReal_def] using h

/-- The local kernel and counting estimates needed to bound the incoming
Green sum. The mass may depend on the vertex; the two scale inequalities
ensure that the counting error and the power loss can be absorbed. -/
def LLowerBoundLocalStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  GreenKernelLowerBoundStmt 𝒮 → CountingMeasureConvergenceStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      let m := S.mult ε ω
      let A := matedDiscreteCluster m ε (S.η ω) ρ t
      let B := ballInterior ε (S.η ω) ρ
      (∀ a, {b | m a b ≠ 0}.Finite) ∧ (∀ a, m a (a + 1) ≠ 0) ∧
      A.Finite ∧ B.Finite ∧ A ⊆ B ∧ A ⊆ cellVertices ε (S.η ω) (ball 0 ρ) ∧
      ∀ a ∈ A, δ < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) A)) →
        ∃ (D C : Set ℤ) (α M : ℝ), C.Finite ∧ D ⊆ C ∧ C ⊆ A ∧
          (∀ b ∈ D, (1 / 2 : ℝ) ≤ greenKernel m C a b) ∧
          ε⁻¹ * M - ε ^ (-1 + α) ≤ (D.ncard : ℝ) ∧
          ε ^ α ≤ M / 2 ∧ ε ^ (1 / 4 : ℝ) ≤ M / 4}

/-- The local kernel and counting estimates imply the Green-sum event. -/
theorem lLowerBoundSumStep_of_local (𝒮 : SpaceFillingSLEModel)
    (hlocal : LLowerBoundLocalStep 𝒮) : LLowerBoundSumStep 𝒮 := by
  intro h216 h29 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have h := hlocal h216 h29 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro hgood
  apply hω.2
  dsimp only at hgood
  obtain ⟨hlf, hcons, hA, hB, hAB, hAcell, hlocal'⟩ := hgood
  refine ⟨hlf, hcons, hA, hAB, hAcell, greenFn_laplacian_fst hlf hcons hA,
    greenFn_laplacian_fst hlf hcons hB, ?_⟩
  intro a ha hdist
  obtain ⟨D, C, α, M, hC, hDC, hCA, hkernel, hcount, herr, hsmall⟩ := hlocal' a ha hdist
  exact greenSum_lower_of_count (S.mult_symm ε ω) hlf hcons hA hC hDC hCA hε hkernel hcount herr hsmall

end MatedCRT
