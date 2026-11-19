import MatedCRT.FirstPass.SLERef.CanonicalModel

/-!
# Normalized law of the canonical space-filling SLE model

For the canonical model `ProbeMi.canonicalSLEModel ν` (curve modulo increasing reparametrization, with a free
Lebesgue-area representative), this module identifies the law of the rational-time code of every anchored
Lebesgue-area representative with `ν κ`, i.e. it proves `HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν`, under
one hypothesis on the family `ν`: for `κ > 4`, `ν κ`-almost every code is the code of a path that visits the spatial
point `0` only at time `0` (`SLECodeZeroOnlyAtOrigin ν`).

* `ZeroOnlyAtOriginCode`: codes whose path stays away from `0` on every rational interval avoiding time `0`. It is a
  measurable subset of the product space `SLEPathCode` (`measurableSet_zeroOnlyAtOriginCode`), and the code of a
  continuous path lies in it exactly when the path visits `0` only at time `0`
  (`slePathCode_mem_zeroOnlyAtOriginCode_iff`).
* `eq_of_isLebesgueRepresentativeFree_of_isLebesgueRepresentative`: two Lebesgue-area representatives of the same
  curve, both starting at `0`, differ by a time shift `θ` with `c θ = 0`; when the free one visits `0` only at time
  `0`, they are equal.
* `hasNormalizedSLELaw_canonicalSLEModel`: the normalized law of the canonical model.
* `ae_mem_zeroOnlyAtOriginCode_of_map_eq`: the hypothesis on `ν κ` follows from the path-level statement for any
  measurable representative whose code has law `ν κ`.

The hypothesis `SLECodeZeroOnlyAtOrigin ν` is the statement that the fixed point `0` is hit only once. For the law of
whole-plane space-filling SLE parametrized by Lebesgue measure with `η 0 = 0`, this is what one expects from
Duplantier-Miller-Sheffield (arXiv:1409.7055, p. 24: Lebesgue-a.e. time is the only visit of its point) together with
the translation invariance of the Lebesgue parametrization (Holden-Sun, Lemma 2.3). Nothing in this module proves it
for any family `ν`: it is the explicit hypothesis `hν`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Codes whose path stays away from `0` on every rational interval `[a, b]` that avoids `0`: for each such interval
there is `n` with `1 / (n + 1) ≤ ‖x q‖` for all rational `q ∈ [a, b]`. -/
def ZeroOnlyAtOriginCode : Set SLEPathCode :=
  {x | ∀ a b : ℚ, (0 < a ∨ b < 0) → ∃ n : ℕ, ∀ q : ℚ, a ≤ q → q ≤ b → (1 : ℝ) / (n + 1) ≤ ‖x q‖}

/-- For `κ > 4`, `ν κ`-almost every code is the code of a path that visits `0` only at time `0`
(see `slePathCode_mem_zeroOnlyAtOriginCode_iff`). -/
def SLECodeZeroOnlyAtOrigin (ν : ℝ → Measure SLEPathCode) : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ᵐ x ∂(ν κ), x ∈ ZeroOnlyAtOriginCode

/-- `ZeroOnlyAtOriginCode` is measurable for the product σ-algebra on `SLEPathCode` (countable operations over
rationals and naturals of the coordinate sets `{x | c ≤ ‖x q‖}`). -/
theorem measurableSet_zeroOnlyAtOriginCode : MeasurableSet ZeroOnlyAtOriginCode := by
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.forall fun a => Measurable.forall fun b => Measurable.imp measurable_const ?_
  refine Measurable.exists fun n => Measurable.forall fun q => Measurable.imp measurable_const
    (Measurable.imp measurable_const ?_)
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_pi_apply q).norm)

/-- If the code of a continuous path lies in `ZeroOnlyAtOriginCode`, the path visits `0` only at time `0`. -/
theorem eq_zero_of_slePathCode_mem_zeroOnlyAtOriginCode {c : C(ℝ, ℂ)}
    (hx : slePathCode c ∈ ZeroOnlyAtOriginCode) : ∀ t, c t = 0 → t = 0 := by
  intro t ht
  by_contra hne
  obtain ⟨a, b, hab, hat, htb⟩ : ∃ a b : ℚ, (0 < a ∨ b < 0) ∧ (a : ℝ) < t ∧ t < b := by
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn h
      obtain ⟨a, ha⟩ := exists_rat_lt t
      exact ⟨a, b, Or.inr (by exact_mod_cast hb2), ha, hb1⟩
    · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn h
      obtain ⟨b, hb⟩ := exists_rat_gt t
      exact ⟨a, b, Or.inl (by exact_mod_cast ha1), ha2, hb⟩
  obtain ⟨n, hn⟩ := hx a b hab
  have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 c.continuous t _ hpos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (a:ℝ) (t - δ) < min (b:ℝ) (t + δ) by
    simp only [max_lt_iff, lt_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  have hqa : (a:ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hqb : (q:ℝ) < b := lt_of_lt_of_le hq2 (min_le_left _ _)
  have hdist : dist (q:ℝ) t < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right (a:ℝ) (t - δ), min_le_right (b:ℝ) (t + δ)]
  have h1 := hδc q hdist
  rw [ht, dist_zero_right] at h1
  have h2 := hn q (by exact_mod_cast hqa.le) (by exact_mod_cast hqb.le)
  simp only [slePathCode] at h2
  linarith

/-- If a continuous path visits `0` only at time `0`, its code lies in `ZeroOnlyAtOriginCode`: on a compact interval
avoiding time `0`, `‖c‖` attains a positive minimum. -/
theorem slePathCode_mem_zeroOnlyAtOriginCode_of_forall {c : C(ℝ, ℂ)} (h0 : ∀ t, c t = 0 → t = 0) :
    slePathCode c ∈ ZeroOnlyAtOriginCode := by
  simp only [ZeroOnlyAtOriginCode, Set.mem_ofPred_eq]
  intro a b hab
  by_cases hba : a ≤ b
  · have hab' : (a : ℝ) ≤ b := by exact_mod_cast hba
    obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := (a : ℝ)) (b := (b : ℝ))).exists_isMinOn
      (Set.nonempty_Icc.2 hab') c.continuous.norm.continuousOn
    have hne : c t ≠ 0 := by
      intro hct
      have h := h0 t hct
      rw [h] at ht
      rcases hab with ha | hb
      · have : (0 : ℝ) < a := by exact_mod_cast ha
        linarith [ht.1]
      · have : (b : ℝ) < 0 := by exact_mod_cast hb
        linarith [ht.2]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hne)
    refine ⟨n, fun q haq hqb => ?_⟩
    have hq : (q : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨by exact_mod_cast haq, by exact_mod_cast hqb⟩
    have hle : ‖c t‖ ≤ ‖c q‖ := isMinOn_iff.1 hmin q hq
    simp only [slePathCode]
    linarith
  · exact ⟨0, fun q haq hqb => absurd (haq.trans hqb) hba⟩

/-- The code of a continuous path lies in `ZeroOnlyAtOriginCode` iff the path visits `0` only at time `0`. -/
theorem slePathCode_mem_zeroOnlyAtOriginCode_iff (c : C(ℝ, ℂ)) :
    slePathCode c ∈ ZeroOnlyAtOriginCode ↔ ∀ t, c t = 0 → t = 0 :=
  ⟨eq_zero_of_slePathCode_mem_zeroOnlyAtOriginCode, slePathCode_mem_zeroOnlyAtOriginCode_of_forall⟩

/-- Deterministic step. Let `c` be a free Lebesgue-area representative of `η` and `c'` an anchored one. With
`ψ := φ'⁻¹ ∘ φ` one has `c' = c ∘ ψ`, and the area parametrization forces `ψ` to be the time shift by `ψ 0`, a zero of
`c`. If `c` visits `0` only at time `0`, then `ψ 0 = 0` and `c' = c`. -/
theorem eq_of_isLebesgueRepresentativeFree_of_isLebesgueRepresentative {η : ℝ → ℂ} {c c' : C(ℝ, ℂ)}
    (hc : ProbeMi.IsLebesgueRepresentativeFree η c) (hc' : IsLebesgueRepresentative η c')
    (h0 : ∀ t, c t = 0 → t = 0) : c' = c := by
  obtain ⟨-, -, -, hvol, φ, hφ⟩ := hc
  obtain ⟨hc'0, -, -, hvol', φ', -, hφ'⟩ := hc'
  let ψ : ℝ ≃o ℝ := φ'.symm.trans φ
  have hcomp : ∀ u, c' u = c (ψ u) := by
    intro u
    have := hφ' (φ'.symm u)
    rw [OrderIso.apply_symm_apply] at this
    rw [← this, hφ]
    rfl
  have hψ0 : ψ 0 = 0 := h0 _ (by rw [← hcomp, hc'0])
  have himg : ∀ s t, c' '' Icc s t = c '' Icc (ψ s) (ψ t) := by
    intro s t
    rw [← OrderIso.image_Icc, ← Set.image_comp]
    congr 1
    funext u
    exact hcomp u
  have hψt : ∀ t, ψ t = t := by
    intro t
    rcases le_total 0 t with ht | ht
    · have h1 := hvol' 0 t ht
      have hle : ψ 0 ≤ ψ t := ψ.monotone ht
      rw [himg, hvol (ψ 0) (ψ t) hle, hψ0] at h1
      rw [hψ0] at hle
      have := (ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)).1 h1
      linarith
    · have h1 := hvol' t 0 ht
      have hle : ψ t ≤ ψ 0 := ψ.monotone ht
      rw [himg, hvol (ψ t) (ψ 0) hle, hψ0] at h1
      rw [hψ0] at hle
      have := (ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)).1 h1
      linarith
  ext u
  rw [hcomp, hψt]

/-- **Normalized law of the canonical model.** If, for `κ > 4`, `ν κ`-almost every code is the code of a path visiting
`0` only at time `0`, then the canonical model `ProbeMi.canonicalSLEModel ν` has normalized law `ν`: every anchored
Lebesgue-area representative `ηL` has the code law `ν κ`, since it agrees almost surely with the free representative
of the model. -/
theorem hasNormalizedSLELaw_canonicalSLEModel {ν : ℝ → Measure SLEPathCode}
    (hν : SLECodeZeroOnlyAtOrigin ν) : HasNormalizedSLELaw (ProbeMi.canonicalSLEModel ν) ν := by
  intro Ω mΩ P 𝓕 κ η ηL hP hκ hSLE _ hrep
  obtain ⟨-, -, ηL', hm', hrep', hlaw', -⟩ := hSLE
  have hZ : ∀ᵐ ω ∂P, slePathCode (ηL' ω) ∈ ZeroOnlyAtOriginCode := by
    have h := hν κ hκ
    rw [← hlaw'] at h
    exact (ae_map_iff hm'.aemeasurable measurableSet_zeroOnlyAtOriginCode).1 h
  have hEq : (fun ω => slePathCode (ηL ω)) =ᵐ[P] (fun ω => slePathCode (ηL' ω)) := by
    filter_upwards [hrep, hrep', hZ] with ω h1 h2 h3
    rw [eq_of_isLebesgueRepresentativeFree_of_isLebesgueRepresentative h2 h1
      (eq_zero_of_slePathCode_mem_zeroOnlyAtOriginCode h3)]
  exact (Measure.map_congr hEq).trans hlaw'

/-- **Transfer from a representative.** If `ηL` is a family of continuous paths whose code map is measurable with law
`ν κ`, and almost surely `ηL ω` visits `0` only at time `0`, then `ν κ`-almost every code lies in
`ZeroOnlyAtOriginCode`. -/
theorem ae_mem_zeroOnlyAtOriginCode_of_map_eq {Ω : Type*} (mΩ : MeasurableSpace Ω) (P : Measure Ω)
    (ηL : Ω → C(ℝ, ℂ)) {ν : ℝ → Measure SLEPathCode} {κ : ℝ}
    (hm : Measurable (fun ω => slePathCode (ηL ω)))
    (hlaw : P.map (fun ω => slePathCode (ηL ω)) = ν κ)
    (h0 : ∀ᵐ ω ∂P, ∀ t, ηL ω t = 0 → t = 0) :
    ∀ᵐ x ∂(ν κ), x ∈ ZeroOnlyAtOriginCode := by
  rw [← hlaw]
  exact (ae_map_iff hm.aemeasurable measurableSet_zeroOnlyAtOriginCode).2
    (h0.mono fun _ hω => slePathCode_mem_zeroOnlyAtOriginCode_of_forall hω)

end MatedCRT.FirstPass.Derived
