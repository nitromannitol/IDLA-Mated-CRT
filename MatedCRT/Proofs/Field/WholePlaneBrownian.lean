import MatedCRT.Proofs.Field.WholePlaneRadial
import MatedCRT.Proofs.Field.GaussianLaw
import MarkovProcess.Examples.BrownianMotion
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The radial process of a whole-plane GFF has the law of Brownian motion

For a whole-plane GFF `h^ℂ` the radial process `t ↦ h^ℂ_{e^{-t}}(0)`, `t ≥ 0`, is a centred Gaussian process with
covariance `min(s, t)` (`cov_radial`, `isGaussianProcess_radial`). The coordinate process of `brownianMotion 0`
(MarkovProcess, heat semigroup) is a centred Gaussian process with the same covariance: its one-time marginals are
`gaussianReal 0 t`, its increments over disjoint intervals are independent and Gaussian
(`isBrownianReal_brownianMotion`). This file proves

* `brownian_isGaussianProcess`: the coordinate process of `brownianMotion 0` is a Gaussian process;
* `brownian_covariance`: its covariance is `min s t`;
* `map_radial_eq_brownian`: the radial process of a whole-plane GFF has the law of `brownianMotion 0` on
  `ℝ≥0 → ℝ` (product σ-algebra), by `map_eq_of_covariance` (`GaussianLaw.lean`).

No input beyond the MarkovProcess Brownian motion and Mathlib is used.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory MarkovProcess HarmonicBalls
open scoped NNReal

/-- Covariance is unchanged by almost-everywhere modifications of its two arguments. -/
lemma covariance_congr_ae' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') : covariance X Y μ = covariance X' Y' μ := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω h1 h2
  simp only [h1, h2]

/-- The coordinate at time `0` of `brownianMotion 0` vanishes almost surely. -/
lemma brownian_coord_zero_ae : ∀ᵐ w ∂(brownianMotion 0), w 0 = 0 := by
  have h : HasLaw (fun w : ContinuousPath ℝ => w 0 - 0) (gaussianReal 0 0) (brownianMotion 0) :=
    (isBrownianReal_brownianMotion 0).hasLaw_eval 0
  rw [gaussianReal_zero_var] at h
  have hm : Measurable (fun w : ContinuousPath ℝ => w 0 - 0) :=
    (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) (0 : ℝ≥0)).sub measurable_const
  have hae : ∀ᵐ y ∂((brownianMotion 0).map (fun w : ContinuousPath ℝ => w 0 - 0)), y = 0 := by
    rw [h.map_eq]
    simp
  have hset : MeasurableSet {x : ℝ | x = 0} := measurableSet_singleton 0
  filter_upwards [(ae_map_iff (p := fun y : ℝ => y = 0) hm.aemeasurable hset).1 hae] with w hw
  simpa using hw

/-- The increment of `brownianMotion 0` over `[a, b]` is a centred Gaussian variable. -/
lemma brownian_increment_hasGaussianLaw {a b : ℝ≥0} (hab : a ≤ b) :
    HasGaussianLaw (fun w : ContinuousPath ℝ => w b - w a) (brownianMotion 0) := by
  have hm : Measurable (fun w : ContinuousPath ℝ => w b - w a) :=
    (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) b).sub
      (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) a)
  have hl : HasLaw (fun w : ContinuousPath ℝ => w b - w a) (gaussianReal 0 (b - a))
      (brownianMotion 0) :=
    ⟨hm.aemeasurable, brownianMotion_map_increment 0 a b hab⟩
  exact hl.hasGaussianLaw

/-- The increments of `brownianMotion 0` over consecutive times of a monotone family are independent. -/
lemma brownian_increments_iIndepFun {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    iIndepFun (fun (i : Fin n) (w : ContinuousPath ℝ) => w (t i.succ) - w (t i.castSucc))
      (brownianMotion 0) := by
  have h := (isBrownianReal_brownianMotion 0).hasIndepIncrements n t ht
  simpa only [sub_zero] using h

/-- The variance of the Brownian coordinate `w s` is `s`. -/
lemma brownian_variance (s : ℝ≥0) :
    variance (fun w : ContinuousPath ℝ => w s) (brownianMotion 0) = (s : ℝ) := by
  have h : HasLaw (fun w : ContinuousPath ℝ => w s - 0) (gaussianReal 0 s) (brownianMotion 0) :=
    (isBrownianReal_brownianMotion 0).hasLaw_eval s
  have h2 := h.variance_eq
  simpa [variance_id_gaussianReal] using h2

/-- For `s ≤ t`, the covariance of the Brownian coordinates `w s` and `w t` is `s`. -/
lemma brownian_covariance_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    covariance (fun w : ContinuousPath ℝ => w s) (fun w => w t) (brownianMotion 0) = (s : ℝ) := by
  have hae0 := brownian_coord_zero_ae
  have hA : (fun w : ContinuousPath ℝ => w s) =ᵐ[brownianMotion 0] (fun w => w s - w 0) := by
    filter_upwards [hae0] with w hw
    rw [hw]
    ring
  have hB : (fun w : ContinuousPath ℝ => w t) =ᵐ[brownianMotion 0]
      (fun w => (w s - w 0) + (w t - w s)) := by
    filter_upwards [hae0] with w hw
    rw [hw]
    ring
  have hX : MemLp (fun w : ContinuousPath ℝ => w s - w 0) 2 (brownianMotion 0) :=
    (brownian_increment_hasGaussianLaw (show (0 : ℝ≥0) ≤ s from zero_le)).memLp_two
  have hD : MemLp (fun w : ContinuousPath ℝ => w t - w s) 2 (brownianMotion 0) :=
    (brownian_increment_hasGaussianLaw hst).memLp_two
  have hmon : Monotone (![(0 : ℝ≥0), s, t]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hind : IndepFun (fun w : ContinuousPath ℝ => w s - w 0)
      (fun w : ContinuousPath ℝ => w t - w s) (brownianMotion 0) := by
    have h := (brownian_increments_iIndepFun ![(0 : ℝ≥0), s, t] hmon).indepFun
      (show (0 : Fin 2) ≠ 1 by decide)
    simpa using h
  have hsplit : covariance (fun w : ContinuousPath ℝ => w s - w 0)
      (fun w => (w s - w 0) + (w t - w s)) (brownianMotion 0)
      = covariance (fun w : ContinuousPath ℝ => w s - w 0) (fun w => w s - w 0) (brownianMotion 0)
        + covariance (fun w : ContinuousPath ℝ => w s - w 0) (fun w => w t - w s)
          (brownianMotion 0) :=
    covariance_add_right hX hX hD
  have hmeas : AEMeasurable (fun w : ContinuousPath ℝ => w s) (brownianMotion 0) :=
    (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).aemeasurable
  rw [covariance_congr_ae' hA hB, hsplit, hind.covariance_eq_zero hX hD, add_zero,
    ← covariance_congr_ae' hA hA, covariance_self hmeas, brownian_variance]

/-- The covariance of the Brownian coordinates is `min s t`. -/
lemma brownian_covariance (s t : ℝ≥0) :
    covariance (fun w : ContinuousPath ℝ => w s) (fun w => w t) (brownianMotion 0)
      = min (s : ℝ) (t : ℝ) := by
  rcases le_total s t with hst | hst
  · rw [brownian_covariance_of_le hst, min_eq_left (NNReal.coe_le_coe.2 hst)]
  · rw [covariance_comm, brownian_covariance_of_le hst, min_eq_right (NNReal.coe_le_coe.2 hst)]

/-- Telescoping for the increments of a family `f : Fin (n+1) → ℝ`: for `m ≤ n`, the increments with index `< m`
sum to `f m - f 0`. -/
lemma sum_increments_ite_aux {n : ℕ} (f : Fin (n + 1) → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ i : Fin n, (if (i : ℕ) < m then f i.succ - f i.castSucc else 0)
      = f ⟨m, Nat.lt_succ_of_le hm⟩ - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmn : m < n := hm
    have hterm : ∀ i : Fin n, (if (i : ℕ) < m + 1 then f i.succ - f i.castSucc else 0)
        = (if (i : ℕ) < m then f i.succ - f i.castSucc else 0)
          + (if (i : ℕ) = m then f i.succ - f i.castSucc else 0) := by
      intro i
      by_cases h1 : (i : ℕ) < m
      · have h2 : (i : ℕ) ≠ m := by omega
        simp [h1, h2, show (i : ℕ) < m + 1 by omega]
      · by_cases h2 : (i : ℕ) = m
        · simp [h2]
        · have h3 : ¬ (i : ℕ) < m + 1 := by omega
          simp [h1, h2, h3]
    have hsingle : ∑ i : Fin n, (if (i : ℕ) = m then f i.succ - f i.castSucc else 0)
        = f (⟨m, hmn⟩ : Fin n).succ - f (⟨m, hmn⟩ : Fin n).castSucc := by
      rw [Finset.sum_eq_single (⟨m, hmn⟩ : Fin n)]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ m := fun h => hb (Fin.ext h)
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have e1 : (⟨m, hmn⟩ : Fin n).succ = ⟨m + 1, by omega⟩ := Fin.ext rfl
    have e2 : (⟨m, hmn⟩ : Fin n).castSucc = ⟨m, by omega⟩ := Fin.ext rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ih (by omega), hsingle, e1, e2]
    ring

/-- Telescoping of the increments of `f : Fin (n+1) → ℝ` below `k`. -/
lemma sum_increments_ite {n : ℕ} (f : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    ∑ i : Fin n, (if (i : ℕ) < (k : ℕ) then f i.succ - f i.castSucc else 0) = f k - f 0 := by
  have h := sum_increments_ite_aux f k (Nat.lt_succ_iff.mp k.isLt)
  simpa using h

/-- Finite-dimensional vectors of `brownianMotion 0` along a monotone family starting at `0` are Gaussian: they are
linear images of the independent Gaussian increments (lower-triangular summation matrix). -/
lemma brownian_vector_hasGaussianLaw {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (h0 : t 0 = 0) :
    HasGaussianLaw (fun (w : ContinuousPath ℝ) (k : Fin (n + 1)) => w (t k)) (brownianMotion 0) := by
  let A : Matrix (Fin (n + 1)) (Fin n) ℝ := Matrix.of fun k i => if (i : ℕ) < (k : ℕ) then 1 else 0
  let M : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  have hinc : HasGaussianLaw (fun (w : ContinuousPath ℝ) (i : Fin n) => w (t i.succ) - w (t i.castSucc))
      (brownianMotion 0) :=
    iIndepFun.hasGaussianLaw
      (fun i => brownian_increment_hasGaussianLaw
        (ht (show Fin.castSucc i < Fin.succ i from Fin.castSucc_lt_succ).le))
      (brownian_increments_iIndepFun t ht)
  have hM := hinc.map M
  refine hM.congr ?_
  filter_upwards [brownian_coord_zero_ae] with w hw
  funext k
  have hsum := sum_increments_ite (fun j => w (t j)) k
  simp only [Function.comp_apply, M, A, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  beta_reduce at hsum
  rw [hsum, h0, hw, sub_zero]

/-- Finite-dimensional laws of `brownianMotion 0`: the vector of coordinates at a finite set of times is Gaussian.
The set is enumerated increasingly together with the base time `0`. -/
lemma brownian_finset_hasGaussianLaw (I : Finset ℝ≥0) :
    HasGaussianLaw (fun (w : ContinuousPath ℝ) (i : I) => w i) (brownianMotion 0) := by
  set J : Finset ℝ≥0 := insert 0 I with hJ
  have h0J : (0 : ℝ≥0) ∈ J := Finset.mem_insert_self _ _
  have hcard : 0 < J.card := Finset.card_pos.2 ⟨0, h0J⟩
  obtain ⟨n, hn⟩ : ∃ n, J.card = n + 1 := ⟨J.card - 1, by omega⟩
  let e : Fin (n + 1) → ℝ≥0 := J.orderEmbOfFin hn
  have he_mono : Monotone e := (J.orderEmbOfFin hn).monotone
  have he0 : e 0 = 0 := by
    have h1 : e 0 = J.min' (Finset.card_pos.mp (hn ▸ Nat.succ_pos n)) :=
      Finset.orderEmbOfFin_zero hn (Nat.succ_pos n)
    rw [h1]
    exact le_antisymm (Finset.min'_le _ _ h0J) zero_le
  let f : I → Fin (n + 1) := fun i => (J.orderIsoOfFin hn).symm ⟨i.1, Finset.mem_insert_of_mem i.2⟩
  have hfe : ∀ i : I, e (f i) = i.1 := by
    intro i
    show (J.orderEmbOfFin hn) ((J.orderIsoOfFin hn).symm _) = i.1
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  let L : (Fin (n + 1) → ℝ) →L[ℝ] (I → ℝ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℝ ℝ f)
  have hV := brownian_vector_hasGaussianLaw e he_mono he0
  have hL := hV.map L
  refine hL.congr (Filter.Eventually.of_forall fun w => ?_)
  funext i
  simp only [Function.comp_apply, L, LinearMap.coe_toContinuousLinearMap', LinearMap.funLeft_apply]
  rw [hfe i]

/-- The coordinate process of `brownianMotion 0` is a Gaussian process. -/
lemma brownian_isGaussianProcess :
    IsGaussianProcess (fun (t : ℝ≥0) (w : ContinuousPath ℝ) => w t) (brownianMotion 0) where
  hasGaussianLaw I := brownian_finset_hasGaussianLaw I

/-- **The radial process of a whole-plane GFF has the law of Brownian motion.** On `ℝ≥0 → ℝ` with the product
σ-algebra, the radial process `t ↦ h^ℂ_{e^{-t}}(0)` of a whole-plane GFF has the law of the coordinate process of
`brownianMotion 0`: both are centred Gaussian processes with covariance `min(s, t)`. -/
theorem map_radial_eq_brownian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) :
    P.map (fun ω (t : ℝ≥0) => hcirc ω (Real.exp (-(t : ℝ))) 0) =
      (brownianMotion 0).map (fun w (t : ℝ≥0) => w t) := by
  have hmean : ∀ t : ℝ≥0, ∫ w : ContinuousPath ℝ, w t ∂(brownianMotion 0) = 0 := by
    intro t
    have hmap : ∫ x : ℝ, x ∂((brownianMotion 0).map (fun w : ContinuousPath ℝ => w t))
        = ∫ w : ContinuousPath ℝ, w t ∂(brownianMotion 0) :=
      integral_map (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).aemeasurable
        aestronglyMeasurable_id
    rw [← hmap, brownianMotion_map_eval, integral_id_gaussianReal]
  refine map_eq_of_covariance (isGaussianProcess_radial hh) brownian_isGaussianProcess
    (fun t => hh.measurable_circle _ _ (Real.exp_pos _))
    (fun t => ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t)
    (fun t => ?_) (fun t => hmean t) (fun s t => ?_)
  · exact hh.integral_eq_zero (GFFObservable.circle (Real.exp (-(t : ℝ))) 0) (Real.exp_pos _)
  · exact (cov_radial hh s t).trans (brownian_covariance s t).symm

end MatedCRT.Field
