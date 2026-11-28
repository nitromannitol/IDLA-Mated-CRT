import Mathlib
import LatticeProb.Analysis.CorrelatedBMHolder
import LatticeProb.Bonanno.BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsov

/-!
# A locally Hölder version of a Gaussian field on the plane

A real random field `X : ℂ → Ω → ℝ` whose increments `X x - X y` are centred Gaussian with variance
at most `C ‖x - y‖ ^ (2 θ)` has a modification `Y` all of whose sample paths are `β`-Hölder on every
compact set, for every `β < θ`.

The proof is the Kolmogorov-Chentsov theorem as printed in Duplantier-Sheffield, *Liouville quantum
gravity and KPZ*, arXiv:0808.1560v2, proof of Proposition 3.1, p. 18: the even Gaussian moments
give `E |X x - X y| ^ (2 m) ≤ M_m ‖x - y‖ ^ (2 m θ)`, and the Kolmogorov-Chentsov criterion with
exponents `p = 2 m` and `q = 2 m θ` in dimension `d = 2` gives Hölder exponents below
`(q - d) / p = θ - 1 / m`, hence below `θ`.  The Lean proof of the criterion is the one of the
brownian-motion project of R. Degenne (`exists_modification_holder_iSup`, vendored in
`LatticeProb.Bonanno.BouRabeeGwynne.Upstream.BrownianMotion.Continuity`).

* `hasBoundedCoveringNumber_ball`: the open ball of radius `r` of `ℂ` has covering numbers at most
  `(6 r / ε) ^ 2` at every scale `ε` up to its diameter (Vershynin, *High-Dimensional Probability*,
  section 4.2, via `coveringNumber_closedBall_le_three_mul`);
* `isCoverWithBoundedCoveringNumber_ball`: the balls of radius `n + 1` form the cover with bounded
  covering numbers of exponent `2` required by the Kolmogorov-Chentsov theorem;
* `exists_holderOnWith_of_locally`: a function that is `β`-Hölder near every point of a compact set
  is `β`-Hölder on it;
* `exists_holder_version_of_gaussian`: the statement above.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.GFFLocalRegularity

/-! ### Covering numbers of the plane, exponent two -/

/-- Two points of the open ball of radius `r` about `0` in `ℂ` are at distance at most `2 r`. -/
lemma ediam_ball_le (r : ℝ≥0) :
    Metric.ediam (Metric.ball (0 : ℂ) r) ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := by
  refine Metric.ediam_le fun x hx y hy => ?_
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := mem_ball_zero_iff.1 hx
  have h2 := mem_ball_zero_iff.1 hy
  have h3 := dist_le_norm_add_norm x y
  push_cast
  linarith

/-- The open ball of radius `r` of `ℂ` has covering numbers at most `(6 r / ε) ^ 2` at every scale
`ε` up to its diameter. -/
lemma hasBoundedCoveringNumber_ball (r : ℝ≥0) (hr : r ≠ 0) :
    HasBoundedCoveringNumber (Metric.ball (0 : ℂ) r) (((6 * r : ℝ≥0) : ℝ≥0∞) ^ 2) 2 := by
  have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.closedEBall (0 : ℂ) r := by
    intro x hx
    rw [Metric.mem_closedEBall, edist_dist, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (mem_ball.1 hx).le
  refine ⟨(ediam_ball_le r).trans_lt ENNReal.coe_lt_top, fun ε hε => ?_⟩
  have hε2 : ε / 2 ≤ r := by
    have h : ε ≤ 2 * r := ENNReal.coe_le_coe.1 (hε.trans (ediam_ball_le r))
    rw [div_le_iff₀ two_pos, mul_comm]
    exact h
  calc (coveringNumber ε (Metric.ball (0 : ℂ) r) : ℝ≥0∞)
      ≤ coveringNumber (ε / 2) (Metric.closedEBall (0 : ℂ) r) :=
        mod_cast coveringNumber_subset_le hsub
    _ ≤ (3 * r / ((ε / 2 : ℝ≥0) : ℝ≥0∞)) ^ (Module.finrank ℝ ℂ) :=
        coveringNumber_closedBall_le_three_mul hr hε2
    _ = ((6 * r : ℝ≥0) : ℝ≥0∞) ^ 2 * (ε : ℝ≥0∞)⁻¹ ^ (2 : ℝ) := by
        rw [Complex.finrank_real_complex, ENNReal.rpow_two, ENNReal.coe_div two_ne_zero,
          div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv,
          ENNReal.coe_ofNat, ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring

/-- The balls of radius `n + 1` about `0` in `ℂ` form a cover of `ℂ` with bounded covering numbers
of exponent `2`. -/
lemma isCoverWithBoundedCoveringNumber_ball :
    IsCoverWithBoundedCoveringNumber
      (fun n : ℕ => Metric.ball (0 : ℂ) (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ)) Set.univ
      (fun n : ℕ => ((6 * ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) ^ 2) (fun _ => 2) where
  c_ne_top n := by finiteness
  d_pos _ := two_pos
  isOpen _ := Metric.isOpen_ball
  totallyBounded _ :=
    (isCompact_closedBall (0 : ℂ) _).totallyBounded.subset Metric.ball_subset_closedBall
  hasBoundedCoveringNumber n := hasBoundedCoveringNumber_ball _ (by positivity)
  mono n m hnm := Metric.ball_subset_ball (by exact_mod_cast (by gcongr : (n : ℝ≥0) + 1 ≤ m + 1))
  subset_iUnion x _ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.2 ⟨n, mem_ball_zero_iff.2 (by push_cast; linarith)⟩

/-! ### From local to compact Hölder continuity -/

/-- A function that is `β`-Hölder on a neighbourhood of every point of a compact set of `ℂ`, with
`0 < β`, is `β`-Hölder on that set. -/
lemma exists_holderOnWith_of_locally {f : ℂ → ℝ} {β : ℝ≥0} (hβ : 0 < β) {K : Set ℂ}
    (hK : IsCompact K) (h : ∀ t ∈ K, ∃ U ∈ 𝓝 t, ∃ C : ℝ≥0, HolderOnWith C β f U) :
    ∃ C : ℝ≥0, HolderOnWith C β f K := by
  choose! U hU C hC using h
  have hcont : ContinuousOn f K := fun t ht =>
    ((hC t ht).continuousOn hβ).continuousAt (hU t ht) |>.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  obtain ⟨s, hsK, hcov⟩ := hK.elim_nhds_subcover (fun t => interior (U t))
    fun t ht => interior_mem_nhds.2 (hU t ht)
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric (ι := s) (c := fun i => interior (U i)) hK
    (fun _ => isOpen_interior) (fun x hx => by simpa using hcov hx)
  set B' : ℝ := max B 0 with hB'
  have hδβ : 0 < δ ^ (β : ℝ) := Real.rpow_pos_of_pos hδ _
  refine ⟨s.sup C ⊔ (2 * B' / δ ^ (β : ℝ)).toNNReal, fun x hx y hy => ?_⟩
  by_cases hxy : dist x y < δ
  · obtain ⟨i, hi⟩ := hδK x hx
    have hyi : y ∈ U i := interior_subset (hi (mem_ball.2 (by rwa [dist_comm])))
    have hxi : x ∈ U i := interior_subset (hi (mem_ball_self hδ))
    calc edist (f x) (f y) ≤ C i * edist x y ^ (β : ℝ) := hC i (hsK i i.2) x hxi y hyi
      _ ≤ ((s.sup C ⊔ (2 * B' / δ ^ (β : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) * edist x y ^ (β : ℝ) := by
        gcongr
        exact le_sup_of_le_left (Finset.le_sup (f := C) i.2)
  · have hxy' : δ ≤ dist x y := not_lt.1 hxy
    have h1 : edist (f x) (f y) ≤ ENNReal.ofReal (2 * B') := by
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hB x hx
      have := hB y hy
      rw [Real.dist_eq]
      have := le_max_left B 0
      have := (abs_sub (f x) (f y))
      rw [Real.norm_eq_abs] at *
      linarith [abs_nonneg (f x), abs_nonneg (f y)]
    have h2 : ENNReal.ofReal δ ^ (β : ℝ) ≤ edist x y ^ (β : ℝ) := by
      refine ENNReal.rpow_le_rpow ?_ β.coe_nonneg
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hxy'
    have h3 : ((2 * B' / δ ^ (β : ℝ)).toNNReal : ℝ≥0∞) * ENNReal.ofReal δ ^ (β : ℝ)
        = ENNReal.ofReal (2 * B') := by
      rw [ENNReal.ofReal_rpow_of_pos hδ]
      change ENNReal.ofReal _ * _ = _
      rw [← ENNReal.ofReal_mul (div_nonneg (by positivity) hδβ.le), div_mul_cancel₀ _ hδβ.ne']
    calc edist (f x) (f y) ≤ ENNReal.ofReal (2 * B') := h1
      _ = ((2 * B' / δ ^ (β : ℝ)).toNNReal : ℝ≥0∞) * ENNReal.ofReal δ ^ (β : ℝ) := h3.symm
      _ ≤ ((2 * B' / δ ^ (β : ℝ)).toNNReal : ℝ≥0∞) * edist x y ^ (β : ℝ) := by gcongr
      _ ≤ ((s.sup C ⊔ (2 * B' / δ ^ (β : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) * edist x y ^ (β : ℝ) := by
        gcongr
        exact le_sup_right

/-! ### Gaussian increments -/

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The second moment of a centred Gaussian variable is its variance. -/
lemma integral_sq_eq_of_hasLaw_gaussianReal {U : Ω → ℝ} {v : ℝ≥0}
    (hU : HasLaw U (gaussianReal 0 v) P) : ∫ ω, U ω ^ 2 ∂P = v := by
  have h0 : ∫ ω, U ω ^ 2 ∂P = ∫ z, z ^ 2 ∂(gaussianReal 0 v) :=
    hU.integral_comp (f := fun z : ℝ => z ^ 2) (by fun_prop)
  rw [h0]
  have h := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := id) aemeasurable_id
    (by simp)
  rw [variance_id_gaussianReal] at h
  exact h.symm

/-- If `a - b` is centred Gaussian of variance `v`, then `E |a - b| ^ (2 k) = v ^ k c_k`, where `c_k`
is the `2 k`-th absolute moment of the standard Gaussian law. -/
lemma lintegral_edist_rpow_eq {a b : Ω → ℝ} {v : ℝ≥0}
    (h : HasLaw (fun ω => a ω - b ω) (gaussianReal 0 v) P) (k : ℕ) :
    ∫⁻ ω, edist (a ω) (b ω) ^ (2 * (k : ℝ)) ∂P
      = (v : ℝ≥0∞) ^ (k : ℝ) * ∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (k : ℝ)) ∂(gaussianReal 0 1) := by
  rw [← LatticeProb.CorrelatedBM.lintegral_enorm_rpow_gaussianReal_eq_mul, ← h.map_eq,
    lintegral_map' (f := fun x : ℝ => ‖x‖ₑ ^ (2 * (k : ℝ))) (by fun_prop) h.aemeasurable]
  exact lintegral_congr fun ω => by rw [edist_eq_enorm_sub]

end Gaussian

/-! ### The Hölder version -/

/-- **Hölder version of a Gaussian field on the plane** (Kolmogorov-Chentsov theorem, Duplantier-
Sheffield, *Liouville quantum gravity and KPZ*, proof of Proposition 3.1, p. 18).  If the increments
`X x - X y` of a real field on `ℂ` are centred Gaussian with variance at most `C ‖x - y‖ ^ (2 θ)`,
then `X` has a modification `Y` all of whose sample paths are `β`-Hölder on every compact set, for
every `β < θ`. -/
theorem exists_holder_version_of_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℂ → Ω → ℝ} (hmeas : ∀ x, Measurable (X x))
    (hgauss : ∀ x y, ∃ v : ℝ≥0, HasLaw (fun ω => X x ω - X y ω) (gaussianReal 0 v) P)
    {θ : ℝ} (hθ0 : 0 < θ) {C : ℝ}
    (hvar : ∀ x y, ∫ ω, (X x ω - X y ω) ^ 2 ∂P ≤ C * ‖x - y‖ ^ (2 * θ)) :
    ∃ Y : ℂ → Ω → ℝ, (∀ x, Measurable (Y x)) ∧ (∀ x, Y x =ᵐ[P] X x) ∧
      ∀ ω, ∀ β : ℝ≥0, (β : ℝ) < θ → ∀ K : Set ℂ, IsCompact K →
        ∃ C' : ℝ≥0, HolderOnWith C' β (fun x => Y x ω) K := by
  choose v hv using hgauss
  set C' : ℝ≥0 := C.toNNReal with hC'
  set G : ℕ → ℝ≥0∞ := fun k => ∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (k : ℝ)) ∂(gaussianReal 0 1) with hG
  have hvle : ∀ x y, (v x y : ℝ≥0∞) ≤ C' * edist x y ^ (2 * θ) := by
    intro x y
    have h1 : (v x y : ℝ) ≤ C' * ‖x - y‖ ^ (2 * θ) := by
      rw [← integral_sq_eq_of_hasLaw_gaussianReal (hv x y)]
      exact (hvar x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C)
        (by positivity))
    calc (v x y : ℝ≥0∞) = ENNReal.ofReal (v x y) := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal (C' * ‖x - y‖ ^ (2 * θ)) := ENNReal.ofReal_le_ofReal h1
      _ = C' * edist x y ^ (2 * θ) := by
        rw [ENNReal.ofReal_mul C'.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity), ofReal_norm,
          edist_eq_enorm_sub]
  set M : ℕ → ℝ≥0 := fun k => ((C' : ℝ≥0∞) ^ k * G k).toNNReal with hM
  have hkol : ∀ k : ℕ, k ≠ 0 → ∀ x y : ℂ,
      ∫⁻ ω, edist (X x ω) (X y ω) ^ (2 * (k : ℝ)) ∂P ≤ M k * edist x y ^ (2 * (k : ℝ) * θ) := by
    intro k hk x y
    have hne : (C' : ℝ≥0∞) ^ k * G k ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
        (LatticeProb.CorrelatedBM.lintegral_enorm_rpow_gaussianReal_ne_top k hk)
    rw [lintegral_edist_rpow_eq (hv x y) k, hM, ENNReal.coe_toNNReal hne]
    calc (v x y : ℝ≥0∞) ^ (k : ℝ) * G k ≤ (C' * edist x y ^ (2 * θ)) ^ (k : ℝ) * G k := by
          gcongr
          exact hvle x y
      _ = (C' : ℝ≥0∞) ^ k * G k * edist x y ^ (2 * (k : ℝ) * θ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ k.cast_nonneg, ← ENNReal.rpow_mul,
            ENNReal.rpow_natCast, show 2 * θ * (k : ℝ) = 2 * (k : ℝ) * θ by ring]
          ring
  obtain ⟨n0, hn0⟩ := exists_nat_gt (1 / θ)
  set m : ℕ → ℕ := fun n => n + n0 + 1 with hm
  have hm0 : ∀ n, m n ≠ 0 := fun n => by simp [hm]
  have hm1 : ∀ n, 1 < (m n : ℝ) * θ := by
    intro n
    have h1 : 1 < (n0 : ℝ) * θ := by rwa [div_lt_iff₀ hθ0] at hn0
    have h2 : (n0 : ℝ) ≤ m n := by
      simp only [hm]
      push_cast
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have hK : ∀ n, IsKolmogorovProcess X P (2 * (m n : ℝ)) (2 * (m n : ℝ) * θ) (M (m n)) :=
    fun n => IsKolmogorovProcess.mk_of_secondCountableTopology hmeas (hkol (m n) (hm0 n))
      (by have := hm1 n; positivity) (by have := hm1 n; positivity)
  obtain ⟨Y, hYm, hYe, hYh⟩ := exists_modification_holder_iSup (d := 2)
    (p := fun n => 2 * (m n : ℝ)) (q := fun n => 2 * (m n : ℝ) * θ) (M := fun n => M (m n))
    isCoverWithBoundedCoveringNumber_ball (fun n => (hK n).IsAEKolmogorovProcess)
    (fun n => by finiteness) two_pos (fun n => by linarith [hm1 n])
  refine ⟨Y, hYm, hYe, fun ω β hβ K hKc => ?_⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : ℝ≥0, (β' : ℝ) = (β + θ) / 2 :=
    ⟨⟨(β + θ) / 2, by have := β.coe_nonneg; positivity⟩, rfl⟩
  have hβ'pos : 0 < β' := by
    rw [← NNReal.coe_pos, hβ']
    have := β.coe_nonneg
    positivity
  have hββ' : β ≤ β' := by
    rw [← NNReal.coe_le_coe, hβ']
    linarith
  have hβ'θ : (β' : ℝ) < θ := by
    rw [hβ']
    linarith
  have hsup : (β' : ℝ) < ⨆ n, ((2 * (m n : ℝ) * θ) - 2) / (2 * (m n : ℝ)) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (θ - β'))
    have hpos : 0 < θ - (β' : ℝ) := by linarith
    have h1 : 1 < (n : ℝ) * (θ - β') := by rwa [div_lt_iff₀ hpos] at hn
    have h2 : (n : ℝ) ≤ m n := by
      simp only [hm]
      push_cast
      linarith [(Nat.cast_nonneg n0 : (0 : ℝ) ≤ n0)]
    have hmpos : (0 : ℝ) < m n := by exact_mod_cast Nat.pos_of_ne_zero (hm0 n)
    have hbdd : BddAbove (Set.range fun n => ((2 * (m n : ℝ) * θ) - 2) / (2 * (m n : ℝ))) := by
      refine ⟨θ, ?_⟩
      rintro _ ⟨k, rfl⟩
      have hk : (0 : ℝ) < m k := by exact_mod_cast Nat.pos_of_ne_zero (hm0 k)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd n)
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hloc : ∀ t ∈ K, ∃ U ∈ 𝓝 t, ∃ C : ℝ≥0, HolderOnWith C β' (fun x => Y x ω) U :=
    fun t _ => hYh ω t β' hβ'pos hsup
  obtain ⟨C₁, hC₁⟩ := exists_holderOnWith_of_locally hβ'pos hKc hloc
  exact hC₁.mono_right hββ' hKc.isBounded

end MatedCRT.GFFLocalRegularity
