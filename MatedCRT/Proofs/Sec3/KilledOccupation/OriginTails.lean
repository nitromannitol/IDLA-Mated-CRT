import Mathlib
import HarmonicBalls.Defs.GFF

/-!
# Regularized origin tails (Appendix B, `lem:occ-tails`)

Printed statement: `paper/appendix-occupation-C16.tex:296-310`, the same claim in the corrected draft as
`paper/idla_mated_crt-corrected.tex:4815-4826` (`lem:tails`, with `p` and `κ` as printed there).
Printed proof: `paper/appendix-occupation-C16.tex:311-368`.

Field. `hc ω r z` are the circle averages of a whole-plane GFF `h^ℂ` (`HarmonicBalls.IsWholePlaneGFF`). The cone field
is `h = h^ℂ − γ log|·|` (eq:gff, `paper/idla_mated_crt-corrected.tex:443`), with circle averages
`h_ε(x) = HarmonicBalls.fieldCircleAverage γ (hc ω) ε x`.

Proof structure. The printed proof has three steps.
* Annulus estimate for `A_s = {s/2 < |x| ≤ s}` with `ε ≤ s/4` (printed `:335-346`, Gaussian splitting
  eq:occ-regweight, eq:occ-scale, independence and eq:occ-var at `:339`). Here `annulus s` is `{s/2 ≤ |x| < s}`,
  which differs from the printed set by a Lebesgue-null set. It is the hypothesis `h_annulus`.
* Core estimate for `B_c` with `c ≤ 4ε` (printed `:347-358`, with `R = 8ε`). It is the hypothesis `h_core`.
* Dyadic decomposition of `B_a` into annuli down to a core of radius `≤ 4ε` and the summation (printed `:359-368`).
  This part is proved below (`origin_tail_moment`).

Measurability input. `hjoint` is the joint measurability of the circle averages in `(ω, x)`. The structure
`IsWholePlaneGFF` gives measurability in `ω` for fixed `(r, z)` and a.s. continuity in `(r, z)`, not joint
measurability. Without it the expectation of a sum of tails cannot be split.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

noncomputable section

namespace MatedCRT.KilledOccupation

/-- The annulus `A_s = {s/2 ≤ |x| < s}` (printed `A_s = {s/2 < |x| ≤ s}`, up to a Lebesgue-null set). -/
def annulus (s : ℝ) : Set ℂ := {x : ℂ | s / 2 ≤ ‖x‖ ∧ ‖x‖ < s}

/-- The regularized LQG density `μ_ε(dx) = ε^{γ²/2} e^{γ h_ε(x)} dx` at `x` (printed `:296`), with circle averages
`hc` of the whole-plane GFF and `h_ε(x) = HarmonicBalls.fieldCircleAverage γ hc ε x`. -/
def regDensity (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * HarmonicBalls.fieldCircleAverage γ hc ε x))

/-- The weighted mass `∫_S (1 + log(1/|x|)) μ_ε(dx)` of the printed lemma. -/
def weightedMass (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) (S : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ x in S, ENNReal.ofReal (1 + Real.log (1 / ‖x‖)) * regDensity γ ε hc x

lemma measurableSet_annulus (s : ℝ) : MeasurableSet (annulus s) :=
  (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)

lemma ball_eq_union_annulus {r : ℝ} (hr : 0 < r) :
    ball (0 : ℂ) r = ball (0 : ℂ) (r / 2) ∪ annulus r := by
  ext x
  simp only [mem_ball, dist_zero_right, mem_union, annulus, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases h2 : r / 2 ≤ ‖x‖
    · exact Or.inr ⟨h2, h⟩
    · exact Or.inl (not_le.mp h2)
  · rintro (h | h)
    · linarith
    · linarith [h.2]

lemma disjoint_ball_annulus {r : ℝ} : Disjoint (ball (0 : ℂ) (r / 2)) (annulus r) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [mem_ball, dist_zero_right] at hx
  exact absurd hy.1 (not_le.mpr hx)

lemma weightedMass_ball_split (γ ε : ℝ) (hc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    weightedMass γ ε hc (ball 0 r) =
      weightedMass γ ε hc (ball 0 (r / 2)) + weightedMass γ ε hc (annulus r) := by
  unfold weightedMass
  rw [ball_eq_union_annulus hr, lintegral_union (measurableSet_annulus r) disjoint_ball_annulus]

/-- Dyadic decomposition: `B_a` is `B_{a 2^{-J}}` together with the annuli `A_{a 2^{-j}}`, `j < J`. -/
lemma weightedMass_dyadic (γ ε a : ℝ) (hc : ℝ → ℂ → ℝ) (ha : 0 < a) (J : ℕ) :
    weightedMass γ ε hc (ball 0 a) =
      weightedMass γ ε hc (ball 0 (a * (1 / 2) ^ J)) +
        ∑ j ∈ Finset.range J, weightedMass γ ε hc (annulus (a * (1 / 2) ^ j)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hr : 0 < a * (1 / 2) ^ J := by positivity
    have h := weightedMass_ball_split γ ε hc hr
    have e : a * (1 / 2) ^ J / 2 = a * (1 / 2) ^ (J + 1) := by rw [pow_succ]; ring
    rw [e] at h
    rw [ih, h, Finset.sum_range_succ]
    ring

/-- Subadditivity of `x ↦ x^p` for `0 < p ≤ 1` over a finite sum. -/
lemma rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ≥0∞) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, x i) ^ p ≤ ∑ i ∈ s, x i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1).trans (add_le_add le_rfl ih)

/-- Sum of nonnegative bounds over a dyadic partition: the finite sum plus one more term is bounded by the
`tsum`. -/
lemma sum_ofReal_le_ofReal_tsum (J : ℕ) (u : ℕ → ℝ) (hu : ∀ j, 0 ≤ u j) (hs : Summable u) :
    (∑ j ∈ Finset.range J, ENNReal.ofReal (u j)) + ENNReal.ofReal (u J) ≤ ENNReal.ofReal (∑' j, u j) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hu j), ← ENNReal.ofReal_add
    (Finset.sum_nonneg (fun j _ => hu j)) (hu J)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.sum_range_succ]
  exact hs.sum_le_tsum _ (fun j _ => hu j)

lemma measurable_weightedMass {Ω : Type*} [MeasurableSpace Ω] (γ ε : ℝ) (hc : Ω → ℝ → ℂ → ℝ)
    (hjoint : Measurable fun q : Ω × ℂ => HarmonicBalls.fieldCircleAverage γ (hc q.1) ε q.2) (S : Set ℂ) :
    Measurable fun ω => weightedMass γ ε (hc ω) S := by
  have hf : Measurable fun q : Ω × ℂ =>
      ENNReal.ofReal (1 + Real.log (1 / ‖q.2‖)) * regDensity γ ε (hc q.1) q.2 := by
    have h1 : Measurable fun q : Ω × ℂ => ENNReal.ofReal (1 + Real.log (1 / ‖q.2‖)) :=
      Measurable.ennreal_ofReal
        (measurable_const.add ((measurable_const.div (measurable_norm.comp measurable_snd)).log))
    have h2 : Measurable fun q : Ω × ℂ => regDensity γ ε (hc q.1) q.2 := by
      unfold regDensity
      exact Measurable.ennreal_ofReal (measurable_const.mul (Measurable.exp (measurable_const.mul hjoint)))
    exact h1.mul h2
  exact hf.lintegral_prod_right'

/-- **Regularized origin tails** (`lem:occ-tails`, printed `appendix-occupation-C16.tex:296-310`; corrected draft
`idla_mated_crt-corrected.tex:4815-4826`). For `0 < p < min{1, 4/γ² − 1}` and `κ = (2 − γ²/2)p − γ²p²/2`
(positive), there are `C` and `a₀ > 0` such that for all `a, ε ∈ (0, a₀)`,
`E[(∫_{B_a} (1 + log(1/|x|)) μ_ε(dx))^p] ≤ C a^κ (1 + log(1/a))^p`.

The inputs `h_annulus` (printed annulus estimate) and `h_core` (printed core estimate) are the Gaussian steps of the
proof; they are to be closed from the Gaussian splitting. -/
theorem origin_tail_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hc : Ω → ℝ → ℂ → ℝ) (hGFF : HarmonicBalls.IsWholePlaneGFF P hC hc)
    {γ p κ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hp0 : 0 < p) (hp1 : p < min 1 (4 / γ ^ 2 - 1))
    (hκ : κ = (2 - γ ^ 2 / 2) * p - γ ^ 2 * p ^ 2 / 2)
    (hjoint : ∀ ε : ℝ, 0 < ε → Measurable fun q : Ω × ℂ => HarmonicBalls.fieldCircleAverage γ (hc q.1) ε q.2)
    (h_annulus : ∃ C : ℝ, ∀ s ε : ℝ, 0 < s → s ≤ 1 / 8 → 0 < ε → 4 * ε ≤ s →
      ∫⁻ ω, weightedMass γ ε (hc ω) (annulus s) ^ p ∂P ≤
        ENNReal.ofReal (C * s ^ κ * (1 + Real.log (1 / s)) ^ p))
    (h_core : ∃ C : ℝ, ∀ c ε : ℝ, 0 < c → 0 < ε → ε ≤ 1 / 8 → c ≤ 4 * ε →
      ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 c) ^ p ∂P ≤
        ENNReal.ofReal (C * c ^ κ * (1 + Real.log (1 / c)) ^ p)) :
    ∃ C : ℝ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ ε ∈ Ioo 0 a₀,
      ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ∂P ≤
        ENNReal.ofReal (C * a ^ κ * (1 + Real.log (1 / a)) ^ p) := by
  -- `hGFF` and `hγ2` only fix the setting of the statement; the estimates enter through the binders
  have _ := hGFF
  have _ := hγ2
  obtain ⟨C₁, hC₁⟩ := h_annulus
  obtain ⟨C₂, hC₂⟩ := h_core
  have hp1' : p ≤ 1 := le_of_lt (lt_of_lt_of_le hp1 (min_le_left _ _))
  have hp2 : p < 4 / γ ^ 2 - 1 := lt_of_lt_of_le hp1 (min_le_right _ _)
  have hg2 : 0 < γ ^ 2 := by positivity
  have h4 : γ ^ 2 * (1 + p) < 4 := by
    have h' : p < (4 - γ ^ 2) / γ ^ 2 := by
      rw [show (4 : ℝ) / γ ^ 2 - 1 = (4 - γ ^ 2) / γ ^ 2 by field_simp] at hp2
      exact hp2
    rw [lt_div_iff₀ hg2] at h'
    nlinarith
  have hκpos : 0 < κ := by
    have e : κ = p / 2 * (4 - γ ^ 2 * (1 + p)) := by rw [hκ]; ring
    rw [e]
    exact mul_pos (by linarith) (by linarith)
  set M : ℝ := max (max C₁ C₂) 0 with hM
  have hM1 : C₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : C₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  set q : ℝ := (1 / 2 : ℝ) ^ κ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hκpos
  have hK : Summable (fun j : ℕ => q ^ j * (1 + j * Real.log 2)) := by
    have h1 := summable_geometric_of_lt_one hq0 hq1
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg hq0]; exact hq1)
    refine (h1.add (h2.mul_left (Real.log 2))).congr (fun j => ?_)
    simp only [pow_one]
    ring
  refine ⟨M * ∑' j : ℕ, q ^ j * (1 + j * Real.log 2), 1 / 8, by norm_num, ?_⟩
  intro a ha ε hε
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hε0, hε1⟩ := hε
  have ha8 : a ≤ 1 / 8 := ha1.le
  set L : ℝ := Real.log (1 / a) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  -- the dyadic index at which the radius first falls to `4ε`
  have hex : ∃ J : ℕ, a * (1 / 2) ^ J ≤ 4 * ε := by
    obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < 4 * ε / a by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
    exact ⟨J, by rw [mul_comm]; exact ((lt_div_iff₀ ha0).1 hJ).le⟩
  classical
  set J := Nat.find hex with hJdef
  have hJ : a * (1 / 2) ^ J ≤ 4 * ε := Nat.find_spec hex
  have hjlt : ∀ j < J, 4 * ε < a * (1 / 2) ^ j := fun j hj => not_le.mp (Nat.find_min hex hj)
  have hrad : ∀ j : ℕ, 0 < a * (1 / 2) ^ j ∧ a * (1 / 2) ^ j ≤ 1 / 8 := by
    intro j
    refine ⟨by positivity, le_trans ?_ ha8⟩
    exact mul_le_of_le_one_right ha0.le (pow_le_one₀ (by norm_num) (by norm_num))
  -- pointwise bound of one dyadic term by the power of `a`
  have key : ∀ j : ℕ, (a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p ≤
      a ^ κ * (1 + L) ^ p * (q ^ j * (1 + j * Real.log 2)) := by
    intro j
    have h1 : (a * (1 / 2) ^ j) ^ κ = a ^ κ * q ^ j := by
      have hh : ((1 / 2 : ℝ) ^ j) ^ κ = ((1 / 2 : ℝ) ^ κ) ^ j := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [Real.mul_rpow ha0.le (by positivity), hh, hq]
    have h2 : Real.log (1 / (a * (1 / 2) ^ j)) = L + j * Real.log 2 := by
      rw [hL, show 1 / (a * (1 / 2) ^ j) = (1 / a) * 2 ^ j by field_simp; rw [← mul_pow]; norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 : (1 + (L + j * Real.log 2)) ^ p ≤ (1 + L) ^ p * (1 + j * Real.log 2) := by
      have hj0 : 0 ≤ (j : ℝ) * Real.log 2 := by positivity
      have hA : 1 + (L + j * Real.log 2) ≤ (1 + L) * (1 + j * Real.log 2) := by nlinarith
      have hB : (1 + j * Real.log 2) ^ p ≤ 1 + j * Real.log 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + j * Real.log 2 by linarith) hp1'
        simpa using this
      calc (1 + (L + j * Real.log 2)) ^ p ≤ ((1 + L) * (1 + j * Real.log 2)) ^ p :=
            Real.rpow_le_rpow (by linarith) hA hp0.le
        _ = (1 + L) ^ p * (1 + j * Real.log 2) ^ p := Real.mul_rpow (by linarith) (by nlinarith)
        _ ≤ (1 + L) ^ p * (1 + j * Real.log 2) := mul_le_mul_of_nonneg_left hB (by positivity)
    rw [h1, h2]
    have hnn : 0 ≤ a ^ κ := by positivity
    calc a ^ κ * q ^ j * (1 + (L + j * Real.log 2)) ^ p
        ≤ a ^ κ * q ^ j * ((1 + L) ^ p * (1 + j * Real.log 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = a ^ κ * (1 + L) ^ p * (q ^ j * (1 + j * Real.log 2)) := by ring
  have hlog : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ 1 + Real.log (1 / s) := fun s hs hs1 => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / s by rw [le_div_iff₀ hs]; linarith)
    linarith
  -- the core radius `c = a 2^{-J}` and the dyadic terms
  set c : ℝ := a * (1 / 2) ^ J with hcdef
  have hc0 : 0 < c := by positivity
  set u : ℕ → ℝ := fun j => M * (a ^ κ * (1 + L) ^ p) * (q ^ j * (1 + j * Real.log 2)) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => by
    simp only [hu]
    have hX : 0 ≤ 1 + L := by linarith
    positivity
  have hus : Summable u := hK.mul_left _
  -- core bound
  have hF : ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 c) ^ p ∂P ≤ ENNReal.ofReal (u J) := by
    refine (hC₂ c ε hc0 hε0 hε1.le hJ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ c ^ κ * (1 + Real.log (1 / c)) ^ p :=
      mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg (hlog c hc0 (by linarith)) _)
    calc C₂ * c ^ κ * (1 + Real.log (1 / c)) ^ p
        = C₂ * (c ^ κ * (1 + Real.log (1 / c)) ^ p) := by ring
      _ ≤ M * (c ^ κ * (1 + Real.log (1 / c)) ^ p) := mul_le_mul_of_nonneg_right hM2 hX
      _ ≤ M * (a ^ κ * (1 + L) ^ p * (q ^ J * (1 + J * Real.log 2))) :=
          mul_le_mul_of_nonneg_left (key J) hM0
      _ = u J := by simp only [hu]; ring
  -- annulus bounds
  have hG : ∀ j ∈ Finset.range J,
      ∫⁻ ω, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p ∂P ≤ ENNReal.ofReal (u j) := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    obtain ⟨hs0, hs1⟩ := hrad j
    refine (hC₁ (a * (1 / 2) ^ j) ε hs0 hs1 hε0 (le_of_lt (hjlt j hjJ))).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ (a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p :=
      mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg (hlog _ hs0 (by linarith)) _)
    calc C₁ * (a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p
        = C₁ * ((a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p) := by ring
      _ ≤ M * ((a * (1 / 2) ^ j) ^ κ * (1 + Real.log (1 / (a * (1 / 2) ^ j))) ^ p) :=
          mul_le_mul_of_nonneg_right hM1 hX
      _ ≤ M * (a ^ κ * (1 + L) ^ p * (q ^ j * (1 + j * Real.log 2))) :=
          mul_le_mul_of_nonneg_left (key j) hM0
      _ = u j := by simp only [hu]; ring
  -- expectation of the dyadic decomposition
  have hmeasF : Measurable fun ω => weightedMass γ ε (hc ω) (ball 0 c) ^ p :=
    (measurable_weightedMass γ ε hc (hjoint ε hε0) _).pow_const p
  have hmeasG : ∀ j : ℕ, Measurable fun ω => weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p :=
    fun j => (measurable_weightedMass γ ε hc (hjoint ε hε0) _).pow_const p
  have hpt : ∀ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ≤
      weightedMass γ ε (hc ω) (ball 0 c) ^ p +
        ∑ j ∈ Finset.range J, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p := by
    intro ω
    rw [weightedMass_dyadic γ ε a (hc ω) ha0 J]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1').trans
      (add_le_add le_rfl (rpow_sum_le_sum_rpow _ _ hp0 hp1'))
  have htsum : ∑' j, u j = M * (a ^ κ * (1 + L) ^ p) * ∑' j : ℕ, q ^ j * (1 + j * Real.log 2) := by
    rw [← tsum_mul_left]
  calc ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 a) ^ p ∂P
      ≤ ∫⁻ ω, (weightedMass γ ε (hc ω) (ball 0 c) ^ p +
          ∑ j ∈ Finset.range J, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p) ∂P :=
        lintegral_mono hpt
    _ = ∫⁻ ω, weightedMass γ ε (hc ω) (ball 0 c) ^ p ∂P +
          ∑ j ∈ Finset.range J, ∫⁻ ω, weightedMass γ ε (hc ω) (annulus (a * (1 / 2) ^ j)) ^ p ∂P := by
        rw [lintegral_add_left hmeasF, lintegral_finsetSum' _ (fun j _ => (hmeasG j).aemeasurable)]
    _ ≤ (∑ j ∈ Finset.range J, ENNReal.ofReal (u j)) + ENNReal.ofReal (u J) := by
        rw [add_comm]
        exact add_le_add (Finset.sum_le_sum fun j hj => hG j hj) hF
    _ ≤ ENNReal.ofReal (∑' j, u j) := sum_ofReal_le_ofReal_tsum J u hu0 hus
    _ ≤ ENNReal.ofReal ((M * ∑' j : ℕ, q ^ j * (1 + j * Real.log 2)) * a ^ κ * (1 + L) ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        rw [htsum]
        exact le_of_eq (by ring)

end MatedCRT.KilledOccupation
