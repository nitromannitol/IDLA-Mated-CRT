import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedFunctional
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity

/-!
# Walk-side measurability of the killed occupation functional (E-c2-9)

For a continuous test `g : ℂ → ℝ` and the ball `U = ball z r`, the killed occupation functional
`truncatedOccupationFunctional U g T` of the interpolated walk `interpolatedWalk ε η mε x` is measurable in the
discrete path `x : ℕ → ℤ` (product σ-algebra), for every measure on paths, in particular `srwLaw m a`. This is the
walk-side input `hGW` of `walkFunctional_tendstoInProbability_of_ae_continuousWithin`.

The exit time of a continuous path satisfies `s < pathExitTime U w ↔ ∀ u ∈ [0, s], w u ∈ U`. The interpolated walk is
affine between the nodes, and the ball is convex, so this condition reduces to finitely many node values and the
endpoint `w s`. The integral is a parametric integral of a jointly measurable integrand (the walk is continuous in
time, so Carathéodory's criterion applies). No positivity of `mε` is assumed.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open _root_.HarmonicBalls

/-- The interpolated walk at time `u`, unfolded. -/
theorem interpolatedWalk_apply (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (x : ℕ → ℤ) (u : ℝ≥0) :
    interpolatedWalk ε η m x u =
      ((1 - (m * (u : ℝ) - ⌊m * (u : ℝ)⌋₊) : ℝ) : ℂ) * vertexPoint ε η (x ⌊m * (u : ℝ)⌋₊) +
        ((m * (u : ℝ) - ⌊m * (u : ℝ)⌋₊ : ℝ) : ℂ) * vertexPoint ε η (x (⌊m * (u : ℝ)⌋₊ + 1)) :=
  rfl

/-- The exit time of a continuous path from an open set is `> s` exactly when the path stays in the set on `[0, s]`. -/
theorem coe_lt_pathExitTime_iff {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f) (s : ℝ≥0) :
    (s : ℝ≥0∞) < pathExitTime U f ↔ ∀ u ∈ Icc (0 : ℝ≥0) s, f u ∈ U := by
  have hclosed : IsClosed {t : ℝ≥0 | f t ∉ U} := hU.isClosed_compl.preimage hf
  constructor
  · intro hlt u hu
    by_contra hfu
    have h1 : pathExitTime U f ≤ (u : ℝ≥0∞) := sInf_le ⟨u, rfl, hfu⟩
    have h2 : (u : ℝ≥0∞) ≤ (s : ℝ≥0∞) := ENNReal.coe_le_coe.2 hu.2
    exact lt_irrefl _ (hlt.trans_le (h1.trans h2))
  · intro H
    by_cases hne : ({t : ℝ≥0 | f t ∉ U}).Nonempty
    · have ht0 : sInf {t : ℝ≥0 | f t ∉ U} ∈ {t : ℝ≥0 | f t ∉ U} :=
        hclosed.csInf_mem hne (OrderBot.bddBelow _)
      have ht0' : f (sInf {t : ℝ≥0 | f t ∉ U}) ∉ U := ht0
      have hs_lt : s < sInf {t : ℝ≥0 | f t ∉ U} := by
        by_contra h
        exact ht0' (H _ ⟨zero_le, not_lt.1 h⟩)
      have hsup : pathExitTime U f = ((sInf {t : ℝ≥0 | f t ∉ U} : ℝ≥0) : ℝ≥0∞) := by
        apply le_antisymm
        · exact sInf_le ⟨_, rfl, ht0'⟩
        · apply le_sInf
          rintro c ⟨t, rfl, ht⟩
          exact ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) ht)
      rw [hsup]
      exact ENNReal.coe_lt_coe.2 hs_lt
    · have hempty : {c : ℝ≥0∞ | ∃ t : ℝ≥0, c = (t : ℝ≥0∞) ∧ f t ∉ U} = ∅ := by
        ext c
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨t, -, ht⟩
        exact hne ⟨t, ht⟩
      have htop : pathExitTime U f = ⊤ := by
        unfold pathExitTime
        rw [hempty, sInf_empty]
      rw [htop]
      exact ENNReal.coe_lt_top

/-- A point on the segment between two points of a convex set lies in the set. -/
theorem convex_combo_mem {U : Set ℂ} (hU : Convex ℝ U) {P Q : ℂ} (hP : P ∈ U) (hQ : Q ∈ U) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : ((1 - l : ℝ) : ℂ) * P + (l : ℂ) * Q ∈ U := by
  have h := hU hP hQ (sub_nonneg.2 hl1) hl0 (by ring)
  simpa only [Complex.real_smul] using h

/-- The affine identity behind the segment argument for the interpolated walk. -/
theorem convex_combo_identity (P Q : ℂ) (c d l : ℝ) (h : c = l * d) :
    ((1 - c : ℝ) : ℂ) * P + (c : ℂ) * Q =
      ((1 - l : ℝ) : ℂ) * P + (l : ℂ) * (((1 - d : ℝ) : ℂ) * P + (d : ℂ) * Q) := by
  have h' : (c : ℂ) = (l : ℂ) * (d : ℂ) := by exact_mod_cast h
  push_cast
  linear_combination (Q - P) * h'

/-- Positive rate: the walk stays in a convex set on `[0, s]` iff the nodes `j ≤ ⌊m s⌋₊` and the endpoint do. -/
theorem forall_mem_Icc_interpolatedWalk_iff_pos {U : Set ℂ} (hU : Convex ℝ U) (ε : ℝ) (η : ℝ → ℂ) {m : ℝ}
    (hm : 0 < m) (x : ℕ → ℤ) (s : ℝ≥0) :
    (∀ u ∈ Icc (0 : ℝ≥0) s, interpolatedWalk ε η m x u ∈ U) ↔
      ((∀ j ∈ Finset.range (⌊m * (s : ℝ)⌋₊ + 1), vertexPoint ε η (x j) ∈ U) ∧
        interpolatedWalk ε η m x s ∈ U) := by
  have hms : 0 ≤ m * (s : ℝ) := mul_nonneg hm.le (NNReal.coe_nonneg s)
  constructor
  · intro H
    refine ⟨fun j hj => ?_, H s ⟨zero_le, le_rfl⟩⟩
    have hjN : j ≤ ⌊m * (s : ℝ)⌋₊ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hjm : (0 : ℝ) ≤ (j : ℝ) / m := div_nonneg (Nat.cast_nonneg j) hm.le
    have hvcoe : ((Real.toNNReal ((j : ℝ) / m) : ℝ≥0) : ℝ) = (j : ℝ) / m :=
      Real.coe_toNNReal _ hjm
    have hvs : Real.toNNReal ((j : ℝ) / m) ∈ Icc (0 : ℝ≥0) s := by
      refine ⟨zero_le, ?_⟩
      have hle : ((Real.toNNReal ((j : ℝ) / m) : ℝ≥0) : ℝ) ≤ (s : ℝ) := by
        rw [hvcoe, div_le_iff₀ hm]
        have h1 : (j : ℝ) ≤ (⌊m * (s : ℝ)⌋₊ : ℝ) := Nat.cast_le.2 hjN
        have h2 : (⌊m * (s : ℝ)⌋₊ : ℝ) ≤ m * (s : ℝ) := Nat.floor_le hms
        nlinarith [h1, h2]
      exact_mod_cast hle
    have hmv : m * ((Real.toNNReal ((j : ℝ) / m) : ℝ≥0) : ℝ) = (j : ℝ) := by
      rw [hvcoe]
      field_simp
    have hfloor : ⌊m * ((Real.toNNReal ((j : ℝ) / m) : ℝ≥0) : ℝ)⌋₊ = j := by
      rw [hmv]
      exact Nat.floor_natCast j
    have hval : interpolatedWalk ε η m x (Real.toNNReal ((j : ℝ) / m)) = vertexPoint ε η (x j) := by
      rw [interpolatedWalk_apply, hfloor, hmv]
      simp
    have hmem := H _ hvs
    rwa [hval] at hmem
  · rintro ⟨hp, hs⟩ u hu
    have hus : u ≤ s := hu.2
    have hmu : m * (u : ℝ) ≤ m * (s : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hus) hm.le
    have hnN : ⌊m * (u : ℝ)⌋₊ ≤ ⌊m * (s : ℝ)⌋₊ := Nat.floor_le_floor hmu
    have hθ1 : m * (u : ℝ) - ⌊m * (u : ℝ)⌋₊ < 1 := by
      have := Nat.lt_floor_add_one (m * (u : ℝ))
      linarith
    have hθ0 : 0 ≤ m * (u : ℝ) - ⌊m * (u : ℝ)⌋₊ := by
      have := Nat.floor_le (mul_nonneg hm.le (NNReal.coe_nonneg u))
      linarith
    rw [interpolatedWalk_apply]
    rcases lt_or_eq_of_le hnN with hlt | heq
    · exact convex_combo_mem hU (hp _ (Finset.mem_range.2 (Nat.lt_succ_of_le hnN)))
        (hp _ (Finset.mem_range.2 (Nat.succ_lt_succ hlt))) hθ0 hθ1.le
    · rw [heq] at hθ0 ⊢
      have hpN : vertexPoint ε η (x ⌊m * (s : ℝ)⌋₊) ∈ U :=
        hp _ (Finset.mem_range.2 (Nat.lt_succ_self _))
      have hθs0 : 0 ≤ m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊ := by
        have := Nat.floor_le hms
        linarith
      have hθuS : m * (u : ℝ) - ⌊m * (s : ℝ)⌋₊ ≤ m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊ := by
        linarith
      rcases eq_or_lt_of_le hθs0 with hz | hpos
      · have hθu0 : m * (u : ℝ) - ⌊m * (s : ℝ)⌋₊ = 0 :=
          le_antisymm (by linarith) hθ0
        rw [hθu0]
        simpa using hpN
      · have hl0 : 0 ≤ (m * (u : ℝ) - ⌊m * (s : ℝ)⌋₊) / (m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊) :=
          div_nonneg hθ0 hθs0
        have hl1 : (m * (u : ℝ) - ⌊m * (s : ℝ)⌋₊) / (m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊) ≤ 1 :=
          (div_le_one hpos).2 hθuS
        have hcl : m * (u : ℝ) - ⌊m * (s : ℝ)⌋₊ =
            ((m * (u : ℝ) - ⌊m * (s : ℝ)⌋₊) / (m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊)) *
              (m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊) :=
          (div_mul_cancel₀ _ hpos.ne').symm
        have hWs : interpolatedWalk ε η m x s =
            ((1 - (m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊) : ℝ) : ℂ) * vertexPoint ε η (x ⌊m * (s : ℝ)⌋₊) +
              ((m * (s : ℝ) - ⌊m * (s : ℝ)⌋₊ : ℝ) : ℂ) * vertexPoint ε η (x (⌊m * (s : ℝ)⌋₊ + 1)) :=
          interpolatedWalk_apply ε η m x s
        have hmem := convex_combo_mem hU hpN hs hl0 hl1
        rw [hWs] at hmem
        rw [convex_combo_identity _ _ _ _ _ hcl]
        exact hmem

/-- Nonpositive rate: the walk on `[0, s]` is affine from `p 0` towards the endpoint. -/
theorem forall_mem_Icc_interpolatedWalk_iff_nonpos {U : Set ℂ} (hU : Convex ℝ U) (ε : ℝ) (η : ℝ → ℂ) {m : ℝ}
    (hm : m ≤ 0) (x : ℕ → ℤ) (s : ℝ≥0) :
    (∀ u ∈ Icc (0 : ℝ≥0) s, interpolatedWalk ε η m x u ∈ U) ↔
      ((∀ j ∈ Finset.range (⌊m * (s : ℝ)⌋₊ + 1), vertexPoint ε η (x j) ∈ U) ∧
        interpolatedWalk ε η m x s ∈ U) := by
  have hfl : ∀ u : ℝ≥0, ⌊m * (u : ℝ)⌋₊ = 0 := fun u =>
    Nat.floor_eq_zero.2 (by nlinarith [NNReal.coe_nonneg u])
  have hW : ∀ u : ℝ≥0, interpolatedWalk ε η m x u =
      ((1 - m * (u : ℝ) : ℝ) : ℂ) * vertexPoint ε η (x 0) +
        ((m * (u : ℝ) : ℝ) : ℂ) * vertexPoint ε η (x 1) := by
    intro u
    rw [interpolatedWalk_apply, hfl u]
    simp
  constructor
  · intro H
    refine ⟨fun j hj => ?_, H s ⟨zero_le, le_rfl⟩⟩
    simp only [hfl s, zero_add, Finset.mem_range] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    have h0 := H 0 ⟨le_rfl, zero_le⟩
    rw [hW 0] at h0
    simpa using h0
  · rintro ⟨hp, hs⟩ u hu
    have hp0 : vertexPoint ε η (x 0) ∈ U := hp 0 (by simp only [hfl s, zero_add, Finset.mem_range]; omega)
    rcases eq_or_lt_of_le hu.2 with hus | hus
    · rw [hus]
      exact hs
    · have hs0 : (0 : ℝ) < (s : ℝ) := by
        have : (0 : ℝ≥0) < s := lt_of_le_of_lt zero_le hus
        exact_mod_cast this
      have hsne : (s : ℝ) ≠ 0 := hs0.ne'
      have hl0 : 0 ≤ (u : ℝ) / (s : ℝ) := div_nonneg (NNReal.coe_nonneg u) hs0.le
      have hl1 : (u : ℝ) / (s : ℝ) ≤ 1 := (div_le_one hs0).2 (by exact_mod_cast hus.le)
      have hcl : m * (u : ℝ) = ((u : ℝ) / (s : ℝ)) * (m * (s : ℝ)) := by
        field_simp
      rw [hW u, convex_combo_identity _ _ _ _ _ hcl, ← hW s]
      exact convex_combo_mem hU hp0 hs hl0 hl1

/-- The node criterion for the interpolated walk, for every real rate `m`. -/
theorem forall_mem_Icc_interpolatedWalk_iff {U : Set ℂ} (hU : Convex ℝ U) (ε : ℝ) (η : ℝ → ℂ) (m : ℝ)
    (x : ℕ → ℤ) (s : ℝ≥0) :
    (∀ u ∈ Icc (0 : ℝ≥0) s, interpolatedWalk ε η m x u ∈ U) ↔
      ((∀ j ∈ Finset.range (⌊m * (s : ℝ)⌋₊ + 1), vertexPoint ε η (x j) ∈ U) ∧
        interpolatedWalk ε η m x s ∈ U) := by
  by_cases hm : 0 < m
  · exact forall_mem_Icc_interpolatedWalk_iff_pos hU ε η hm x s
  · exact forall_mem_Icc_interpolatedWalk_iff_nonpos hU ε η (not_lt.1 hm) x s

/-- Measurability of a vertex value in the discrete path. -/
theorem measurable_vertexPoint_comp (ε : ℝ) (η : ℝ → ℂ) (k : ℕ) :
    Measurable (fun x : ℕ → ℤ => vertexPoint ε η (x k)) :=
  (measurable_of_countable (vertexPoint ε η)).comp (measurable_pi_apply k)

/-- The interpolated walk at a fixed time is a measurable function of the discrete path. -/
theorem measurable_interpolatedWalk_apply (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (u : ℝ≥0) :
    Measurable (fun x : ℕ → ℤ => interpolatedWalk ε η m x u) := by
  simp only [interpolatedWalk_apply]
  exact (measurable_const.mul (measurable_vertexPoint_comp ε η _)).add
    (measurable_const.mul (measurable_vertexPoint_comp ε η _))

/-- The exit time of the interpolated walk from a ball is a measurable function of the discrete path. -/
theorem measurable_pathExitTime_interpolatedWalk (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (z : ℂ) (r : ℝ) :
    Measurable (fun x : ℕ → ℤ => pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x)) := by
  refine measurable_of_Ioi fun c => ?_
  induction c using ENNReal.recTopCoe with
  | top => simp
  | coe s =>
    have hset : ((fun x : ℕ → ℤ => pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x)) ⁻¹'
        Ioi (s : ℝ≥0∞)) =
        {x : ℕ → ℤ | ∀ j ∈ Finset.range (⌊m * (s : ℝ)⌋₊ + 1), vertexPoint ε η (x j) ∈ Metric.ball z r} ∩
          {x : ℕ → ℤ | interpolatedWalk ε η m x s ∈ Metric.ball z r} := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_inter_iff, mem_ofPred_eq]
      exact (coe_lt_pathExitTime_iff isOpen_ball (continuous_interpolatedWalk ε m η x) s).trans
        (forall_mem_Icc_interpolatedWalk_iff (convex_ball z r) ε η m x s)
    rw [hset]
    refine MeasurableSet.inter ?_ ?_
    · have hall : {x : ℕ → ℤ | ∀ j ∈ Finset.range (⌊m * (s : ℝ)⌋₊ + 1), vertexPoint ε η (x j) ∈ Metric.ball z r} =
          ⋂ j ∈ Finset.range (⌊m * (s : ℝ)⌋₊ + 1), (fun x : ℕ → ℤ => vertexPoint ε η (x j)) ⁻¹' Metric.ball z r := by
        ext x
        simp
      rw [hall]
      exact Finset.measurableSet_biInter _ fun j _ =>
        (measurable_vertexPoint_comp ε η j) isOpen_ball.measurableSet
    · exact (measurable_interpolatedWalk_apply ε η m s) isOpen_ball.measurableSet



/-- **Walk-side measurability of the killed occupation functional.** For a continuous test `g`, the killed
occupation functional of the interpolated walk is strongly measurable in the discrete path (hence a.e. strongly
measurable), for every measure on paths (in particular `srwLaw m a`). -/
theorem aestronglyMeasurable_truncatedOccupation_interpolatedWalk {μ : Measure (ℕ → ℤ)} (ε : ℝ) (η : ℝ → ℂ)
    (m : ℝ) (z : ℂ) (r T : ℝ) {g : ℂ → ℝ} (hg : Continuous g) :
    AEStronglyMeasurable
      (fun x : ℕ → ℤ => truncatedOccupationFunctional (Metric.ball z r) g T (interpolatedWalk ε η m x)) μ := by
  have hτ : Measurable (fun x : ℕ → ℤ => pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x)) :=
    measurable_pathExitTime_interpolatedWalk ε η m z r
  have ha : Measurable (fun x : ℕ → ℤ =>
      min T (pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x)).toReal) :=
    measurable_const.min (ENNReal.measurable_toReal.comp hτ)
  have hu : Measurable (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
      g (interpolatedWalk ε η m x t.toNNReal)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun x => hg.comp ((continuous_interpolatedWalk ε m η x).comp continuous_real_toNNReal))
      (fun t => hg.measurable.comp (measurable_interpolatedWalk_apply ε η m t.toNNReal))
  set E : Set (ℝ × (ℕ → ℤ)) :=
    {q | 0 < q.1} ∩ {q | q.1 ≤ min T (pathExitTime (Metric.ball z r) (interpolatedWalk ε η m q.2)).toReal} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (ha.comp measurable_snd))
  have hFm := hu.indicator hEm
  have hsm : StronglyMeasurable (fun x : ℕ → ℤ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
        g (interpolatedWalk ε η m x t.toNNReal)) (t, x)) :=
    StronglyMeasurable.integral_prod_left' hFm.stronglyMeasurable
  have heq : (fun x : ℕ → ℤ => truncatedOccupationFunctional (Metric.ball z r) g T (interpolatedWalk ε η m x)) =
      fun x : ℕ → ℤ => ∫ t : ℝ,
        E.indicator (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
          g (interpolatedWalk ε η m x t.toNNReal)) (t, x) := by
    funext x
    unfold truncatedOccupationFunctional
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  rw [heq]
  exact hsm.aestronglyMeasurable

end MatedCRT
