import MatedCRT.FirstPass.Derived.AnnulusTestEnergyOn
import LatticeProb.Analysis.GridAnnulusTransferSubset

/-!
# The resistance bound (4.15) from the grid energy bound (4.7), at a fixed sample

Berestycki–Gwynne (2020), proof of Lemma 4.3.  Fix a sample of the Brownian pair and cells `H k` of the mated-CRT
map such that

* adjacent vertices have intersecting cells, every cell is preconnected and bounded, and every cell meeting
  `B_{ρ_T}(0)` has diameter at most `d`;
* every annulus `B_{q^a}(c_i) \ B̄_{q^b}(c_i)` of the polynomial grid (mesh `m`, radii between `x` and `1`) with
  `q^b < q^a ≤ 1`, `B_{q^a}(c_i) ⊆ B_{ρ_T}(0)` and the two regularity bounds of (4.7) carries a harmonic extension of
  `log(q^a/|· - c_i|)/log(q^a/q^b)`, and every such extension has energy at most `A · 2π / log(q^a/q^b) + ε^α` on the
  cells meeting the annulus (the event of `LatticeProb.LQG.polyHighProb_grid_annulus_energyOn_le`).

Then, for every vertex `a` whose cell meets `B_ρ(0)`, every `r ≤ dist(η(a), ∂B_ρ)` and every `s ∈ [x, r/4]`, there is
a test function equal to `1` on the vertices whose cells meet `B̄_s(η(a))`, vanishing off the vertices whose cells
meet `B_{3r/4}(η(a))`, whose ordered-pair energy over every finite vertex set is at most `C₂ / log(3r/(4s))`: the
event of the resistance bound (4.15).  The grid annulus is chosen by
`LatticeProb.exists_grid_admissible_energy_le_of_subset`, and the energy comparison is
`ofReal_sum_annulusTestFunction_le_energyOn`.
-/

set_option autoImplicit false

open Metric Set
open scoped ENNReal

namespace MatedCRT

open MatedCRTHarmonic LatticeProb

/-- The inner radii of the grid `gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂` are at least `x₂`. -/
theorem le_zpow_of_mem_gridAnnulusIndex {q η ρ x₁ y₁ x₂ y₂ : ℝ} (hq : 1 < q) (hx₂ : 0 < x₂)
    {i : ℤ × ℤ × ℤ × ℤ} (hi : i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂) : x₂ ≤ q ^ i.2.2.2 := by
  simp only [gridAnnulusIndex, Finset.mem_product, Finset.mem_Icc] at hi
  calc x₂ = q ^ Real.logb q x₂ := (Real.rpow_logb (by linarith) hq.ne' hx₂).symm
    _ ≤ q ^ ((i.2.2.2 : ℤ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le (Int.ceil_le.1 hi.2.2.2.1)
    _ = q ^ i.2.2.2 := Real.rpow_intCast q _

/-- The outer radii of the grid `gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂` are at most `y₁`. -/
theorem zpow_le_of_mem_gridAnnulusIndex {q η ρ x₁ y₁ x₂ y₂ : ℝ} (hq : 1 < q) (hy₁ : 0 < y₁)
    {i : ℤ × ℤ × ℤ × ℤ} (hi : i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂) : q ^ i.2.2.1 ≤ y₁ := by
  simp only [gridAnnulusIndex, Finset.mem_product, Finset.mem_Icc] at hi
  calc q ^ i.2.2.1 = q ^ ((i.2.2.1 : ℤ) : ℝ) := (Real.rpow_intCast q _).symm
    _ ≤ q ^ Real.logb q y₁ := Real.rpow_le_rpow_of_exponent_le hq.le (Int.le_floor.1 hi.2.2.1.2)
    _ = y₁ := Real.rpow_logb (by linarith) hq.ne' hy₁

/-- **Balls inside the distance to the circle `∂B_ρ(0)`.** If `‖x‖ < ρ + d` and `r ≤ dist(x, ∂B_ρ(0))`, then
`r ≤ ρ_T` and `B_r(x) ⊆ B_{ρ_T}(0)` as soon as `ρ + 2d ≤ ρ_T`. -/
theorem ball_subset_ball_of_le_infDist_sphere {x : ℂ} {ρ d r ρT : ℝ} (hρ : 0 < ρ) (hd : 0 ≤ d)
    (hx : ‖x‖ < ρ + d) (hr : r ≤ infDist x (sphere (0 : ℂ) ρ)) (hρT : ρ + 2 * d ≤ ρT) :
    r ≤ ρT ∧ ball x r ⊆ ball (0 : ℂ) ρT := by
  have hr' : r ≤ |‖x‖ - ρ| := by
    by_cases hx0 : x = 0
    · subst hx0
      refine hr.trans ((infDist_le_dist_of_mem (y := ((ρ : ℝ) : ℂ)) ?_).trans ?_)
      · simp [abs_of_pos hρ]
      · simp [abs_of_pos hρ]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      refine hr.trans ((infDist_le_dist_of_mem (y := (ρ / ‖x‖) • x) ?_).trans (le_of_eq ?_))
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hρ, abs_norm,
          div_mul_cancel₀ _ hxn.ne']
      · rw [dist_eq_norm, show x - (ρ / ‖x‖) • x = (1 - ρ / ‖x‖) • x by rw [sub_smul, one_smul],
          norm_smul, Real.norm_eq_abs, show 1 - ρ / ‖x‖ = (‖x‖ - ρ) / ‖x‖ by field_simp, abs_div,
          abs_norm, div_mul_cancel₀ _ hxn.ne']
  have hle : ‖x‖ + |‖x‖ - ρ| ≤ ρT := by
    rcases le_total ‖x‖ ρ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  refine ⟨by linarith [norm_nonneg x], fun z hz => ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  rw [mem_ball_zero_iff]
  have := norm_le_insert' z x
  linarith [norm_sub_rev z x]

/-- **The resistance bound (4.15) at a fixed sample** (Berestycki–Gwynne (2020), proof of Lemma 4.3): from the
grid energy bound (4.7), small cells and the adjacency of intersecting cells, every annulus
`B_{3r/4}(η(a)) \ B̄_s(η(a))` with `x ≤ s ≤ r/4`, `r ≤ dist(η(a), ∂B_ρ)`, carries a test function of ordered-pair
energy at most `max 1 (2 (2π A + 1)) / log(3r/(4s))`. -/
theorem resistanceEvent_of_gridEvent {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} {H : ℤ → Set ℂ} {p : ℤ → ℂ}
    {q m x d ρ ρT A α βT : ℝ} (hε : 0 < ε) (hq : 1 < q) (hq2 : q ^ 2 ≤ 29 / 20) (hm : 0 < m)
    (hx : 0 < x) (hmx : m ≤ x / 100) (hdx : d < x) (hd : 0 ≤ d) (hρ : 0 < ρ) (hρT : ρ + 2 * d ≤ ρT)
    (hρT1 : ρT ≤ 1) (hA : 0 ≤ A)
    (hreg1 : (x * Real.log 2)⁻¹ ≤ ε ^ (-βT)) (hreg2 : (x ^ 2 * Real.log 2)⁻¹ ≤ ε ^ (-βT))
    (henergy : Real.log (1 / x) * ε ^ α ≤ 1)
    (hH : ∀ k, IsPreconnected (H k)) (hHb : ∀ k, Bornology.IsBounded (H k))
    (hdiam : ∀ k, (H k ∩ ball (0 : ℂ) ρT).Nonempty → diam (H k) ≤ d) (hp : ∀ k, p k ∈ H k)
    (hadj : ∀ a b : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) a b ≠ 0 → (H a ∩ H b).Nonempty)
    (hev : ∀ i ∈ gridAnnulusIndex q m 1 x 1 x 1,
      q ^ i.2.2.2 < q ^ i.2.2.1 → q ^ i.2.2.1 ≤ 1 →
      ball (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ ball (0 : ℂ) ρT →
      (q ^ i.2.2.2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-βT) →
      ((q ^ i.2.2.2) ^ 2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-βT) →
      ∃ h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω,
        (∃ g : ℤ → ℝ, (MatedCRTHarmonic.MatedCRT.graph ε ω h).IsHarmonicExtension H
          (ball (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) \
            closedBall (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2))
          (fun w : ℂ => Real.log (q ^ i.2.2.1 /
              ‖w - ((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)‖) /
            Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) g) ∧
        ∀ g : ℤ → ℝ, (MatedCRTHarmonic.MatedCRT.graph ε ω h).IsHarmonicExtension H
          (ball (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) \
            closedBall (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2))
          (fun w : ℂ => Real.log (q ^ i.2.2.1 /
              ‖w - ((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)‖) /
            Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) g →
          (MatedCRTHarmonic.MatedCRT.graph ε ω h).energyOn
              (verticesMeeting H
                (ball (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) \
                  closedBall (((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2))) g ≤
            ENNReal.ofReal A * ENNReal.ofReal (2 * Real.pi / Real.log (q ^ i.2.2.1 / q ^ i.2.2.2)) +
              ENNReal.ofReal (ε ^ α)) :
    ∀ a : ℤ, (H a ∩ ball (0 : ℂ) ρ).Nonempty → ∀ r : ℝ, r ≤ infDist (p a) (sphere (0 : ℂ) ρ) →
      ∀ s : ℝ, x ≤ s → s ≤ r / 4 →
      ∃ h : ℤ → ℝ, (∀ k, (H k ∩ closedBall (p a) s).Nonempty → h k = 1) ∧
        (∀ k, ¬ (H k ∩ ball (p a) (3 * r / 4)).Nonempty → h k = 0) ∧
        ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
          ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T,
            (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k l : ℝ) * (h k - h l) ^ 2) ≤
          max 1 (2 * (A * (2 * Real.pi) + 1)) := by
  classical
  set C : ℝ := A * (2 * Real.pi) + 1 with hCdef
  have hC0 : 0 ≤ C := by positivity
  set K : ℝ := 2 * C / Real.log 3 + 1 with hKdef
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hK : 0 < K := by positivity
  -- the energy functional, truncated at `K` so that it is bounded
  set term : (ℤ → ℝ) → Finset ℤ → ℝ := fun f T => (1 / 2) * ∑ k ∈ T, ∑ l ∈ T,
    (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k l : ℝ) * (f k - f l) ^ 2 with hterm
  have hterm0 : ∀ f T, 0 ≤ term f T := fun f T => by
    simp only [hterm]
    positivity
  set E : (ℤ → ℝ) → ℝ := fun f => ⨆ T : Finset ℤ, min (term f T) K with hE
  have hEbdd : ∀ f, BddAbove (range fun T : Finset ℤ => min (term f T) K) :=
    fun f => ⟨K, by rintro _ ⟨T, rfl⟩; exact min_le_right _ _⟩
  -- the grid test functions
  set c : ℤ × ℤ × ℤ × ℤ → ℂ := fun i => ((m : ℝ) : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I) with hc
  set F : ℤ × ℤ × ℤ × ℤ → ℂ → ℝ := fun i w =>
    Real.log (q ^ i.2.2.1 / ‖w - c i‖) / Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) with hF
  set gsel : ℤ × ℤ × ℤ × ℤ → ℤ → ℝ := fun i => Classical.epsilon fun g : ℤ → ℝ =>
    ∃ h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω,
      (MatedCRTHarmonic.MatedCRT.graph ε ω h).IsHarmonicExtension H
        (ball (c i) (q ^ i.2.2.1) \ closedBall (c i) (q ^ i.2.2.2)) (F i) g with hgsel
  set f : ℤ × ℤ × ℤ × ℤ → ℤ → ℝ := fun i =>
    annulusTestFunction H (c i) (q ^ i.2.2.2) (q ^ i.2.2.1) (gsel i) with hf
  have hV : Monotone fun D : Set ℂ => {k : ℤ | (H k ∩ D).Nonempty} :=
    fun D D' hDD' k ⟨z, hz, hzD⟩ => ⟨z, hz, hDD' hzD⟩
  have hgrid : ∀ i ∈ gridAnnulusIndex q m 1 x 1 x 1, q ^ i.2.2.2 ≤ q ^ i.2.2.1 / 2 →
      ball ((m : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ ball (0 : ℂ) ρT →
      (∀ a ∈ {k : ℤ | (H k ∩ closedBall ((m : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I))
          (q ^ i.2.2.2)).Nonempty}, f i a = 1) ∧
      (∀ a, a ∉ {k : ℤ | (H k ∩ ball ((m : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I))
          (q ^ i.2.2.1)).Nonempty} → f i a = 0) ∧
      0 ≤ E (f i) ∧ Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) * E (f i) ≤ C := by
    intro i hi hba hW
    have hb0 : 0 < q ^ i.2.2.2 := zpow_pos (by linarith) _
    have hlt : q ^ i.2.2.2 < q ^ i.2.2.1 := by linarith
    have ha1 : q ^ i.2.2.1 ≤ 1 := zpow_le_of_mem_gridAnnulusIndex hq one_pos hi
    have hxb : x ≤ q ^ i.2.2.2 := le_zpow_of_mem_gridAnnulusIndex hq hx hi
    have h2 : 2 ≤ q ^ i.2.2.1 / q ^ i.2.2.2 := by rw [le_div_iff₀ hb0]; linarith
    have hL2 : Real.log 2 ≤ Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) := Real.log_le_log (by norm_num) h2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL0 : 0 < Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) := hlog2.trans_le hL2
    have hreg1' : (q ^ i.2.2.2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-βT) :=
      (inv_anti₀ (by positivity) (mul_le_mul hxb hL2 hlog2.le hb0.le)).trans hreg1
    have hreg2' : ((q ^ i.2.2.2) ^ 2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2))⁻¹ ≤ ε ^ (-βT) :=
      (inv_anti₀ (by positivity) (mul_le_mul (pow_le_pow_left₀ hx.le hxb 2) hL2 hlog2.le
        (by positivity))).trans hreg2
    obtain ⟨hlf, ⟨g₀, hg₀⟩, hall⟩ := hev i hi hlt ha1 hW hreg1' hreg2'
    obtain ⟨hlf', hg⟩ := Classical.epsilon_spec (p := fun g : ℤ → ℝ =>
      ∃ h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω,
        (MatedCRTHarmonic.MatedCRT.graph ε ω h).IsHarmonicExtension H
          (ball (c i) (q ^ i.2.2.1) \ closedBall (c i) (q ^ i.2.2.2)) (F i) g) ⟨g₀, hlf, hg₀⟩
    have hf1 : ∀ z ∈ sphere (c i) (q ^ i.2.2.2), F i z = 1 := by
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      simp only [hF, hz]
      exact div_self hL0.ne'
    have hf0 : ∀ z ∈ sphere (c i) (q ^ i.2.2.1), F i z = 0 := by
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      simp only [hF, hz, div_self (hb0.trans hlt).ne', Real.log_one, zero_div]
    have hsep : ∀ k, (H k ∩ sphere (c i) (q ^ i.2.2.2)).Nonempty →
        ¬ (H k ∩ sphere (c i) (q ^ i.2.2.1)).Nonempty := by
      intro k hk
      refine not_meets_both_spheres_of_diam_lt (hHb k) ?_ hk
      obtain ⟨z, hzH, hz⟩ := hk
      have hzW : z ∈ ball (0 : ℂ) ρT := hW (sphere_subset_closedBall.trans
        (closedBall_subset_ball hlt) hz)
      linarith [hdiam k ⟨z, hzH, hzW⟩]
    refine ⟨fun a ha => annulusTestFunction_eq_one _ hH hb0 hlt hf1 hf0 hg ha,
      fun a ha => annulusTestFunction_eq_zero hlt ha, Real.iSup_nonneg fun T => le_min (hterm0 _ _) hK.le, ?_⟩
    set L := Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) with hL
    have hBd : E (f i) ≤ A * (2 * Real.pi / L) + ε ^ α := by
      refine ciSup_le fun T => (min_le_left _ _).trans ?_
      have h1 := ofReal_sum_annulusTestFunction_le_energyOn hlf' hε.le hadj hH hb0 hlt hf1 hf0 hsep hg T
      have h2 := hall (gsel i) hg
      rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h2
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans h2)
    have hLx : L ≤ Real.log (1 / x) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_div_iff₀ hb0 hx]
      nlinarith
    calc L * E (f i) ≤ L * (A * (2 * Real.pi / L) + ε ^ α) := mul_le_mul_of_nonneg_left hBd hL0.le
      _ = A * (2 * Real.pi) + L * ε ^ α := by field_simp
      _ ≤ A * (2 * Real.pi) + Real.log (1 / x) * ε ^ α := by
          gcongr
      _ ≤ C := by rw [hCdef]; linarith
  intro a ha r hr s hxs hsr
  have hs0 : 0 < s := hx.trans_le hxs
  obtain ⟨z, hzH, hz⟩ := ha
  have hda : diam (H a) ≤ d := hdiam a ⟨z, hzH, ball_subset_ball (by linarith) hz⟩
  have hpa : ‖p a‖ < ρ + d := by
    have h1 := dist_le_diam_of_mem (hHb a) (hp a) hzH
    rw [mem_ball_zero_iff] at hz
    have h2 := norm_le_insert' (p a) z
    rw [dist_eq_norm] at h1
    linarith
  obtain ⟨hrT, hball⟩ := ball_subset_ball_of_le_infDist_sphere hρ hd hpa hr hρT
  obtain ⟨i, -, h1, h0, hEi⟩ := exists_grid_admissible_energy_le_of_subset (E := E) (f := f) (C := C)
    (x₁ := x) (y₁ := 1) (x₂ := x) (y₂ := 1) (ρ := 1) hV hq hq2 hm hgrid (z := p a) (s := s) (r := 3 * r / 4)
    (by linarith) ((ball_subset_ball (by linarith)).trans hball) (by linarith) (by linarith) hx
    (by linarith) (by linarith) hx hxs (by linarith)
  refine ⟨f i, h1, h0, fun T => ?_⟩
  set L := Real.log (3 * r / 4 / s) with hL
  have hL3 : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hs0]; linarith)
  have hL0 : 0 < L := hlog3.trans_le hL3
  have hEK : E (f i) < K := by
    have : E (f i) ≤ 2 * C / L := by rw [le_div_iff₀ hL0]; linarith
    have h2 : 2 * C / L ≤ 2 * C / Real.log 3 := div_le_div_of_nonneg_left (by positivity) hlog3 hL3
    linarith
  have hmin : min (term (f i) T) K ≤ E (f i) := le_ciSup (hEbdd (f i)) T
  have hTK : term (f i) T ≤ E (f i) := by
    rcases le_total (term (f i) T) K with h | h
    · rwa [min_eq_left h] at hmin
    · rw [min_eq_right h] at hmin; linarith
  calc L * term (f i) T ≤ L * E (f i) := mul_le_mul_of_nonneg_left hTK hL0.le
    _ ≤ 2 * C := hEi
    _ ≤ max 1 (2 * (A * (2 * Real.pi) + 1)) := le_max_right _ _

end MatedCRT
