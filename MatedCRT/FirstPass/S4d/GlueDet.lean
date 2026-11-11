import MatedCRT.FirstPass.S4d.RescaleGap
import MatedCRT.FirstPass.S4d.RegDecode

/-!
# Glueing stopped families into the global family (FIRST PASS, S4d, deterministic)

Deterministic content of the B2 argument. For a global cone family `Λg` and
stopped families `Λs n` (horizons `b n * Ts n`, rescalings `x ↦ R n x`, `R n > 0`) on the same measure `μ`:
* the stopped family agrees with the global one at every time below its horizon (obstacle characterization; equation
  (4.10));
* the rescaled stopped process at `(t / b n, z / R n)` decides `z ∈ Λg t` once `t < b n * Ts n`, and some `n` has
  `t < b n * Ts n` whenever the horizons are unbounded.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT

/-- The family process unfolds to its time-slice definition. -/
theorem familyProcess_iff {Λ : ℝ → Set ℂ} {T u : ℝ} {x : ℂ} :
    familyProcess Λ T (u, x) ↔ u ∈ Ioo 0 T ∧ x ∈ Λ u :=
  Iff.rfl

/-- Two families satisfying the obstacle characterization agree at a common time, when each is bounded there. -/
theorem obstacle_eq_of_global_stopped {μ : Measure ℂ} {Λg Λs : ℝ → Set ℂ} {H t : ℝ}
    (hg : SatisfiesObstacleCharacterization μ Λg) (hs : SatisfiesObstacleCharacterizationOn μ Λs H)
    (ht : t ∈ Ioo 0 H) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hst : Λs t ⊆ ball 0 r₁) (hgt : Λg t ⊆ ball 0 r₂) : Λs t = Λg t := by
  have h1 : r₁ < max r₁ r₂ + 1 := by linarith [le_max_left r₁ r₂]
  have h2 : r₂ < max r₁ r₂ + 1 := by linarith [le_max_right r₁ r₂]
  rw [(hs t r₁ ht hr₁ hst _ h1).1, (hg t r₂ ht.1 hr₂ hgt _ h2).1]

/-- A bounded set lies in some ball about `0`. -/
theorem exists_pos_subset_ball_of_isBounded {s : Set ℂ} (h : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 < r ∧ s ⊆ ball 0 r := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 h
  refine ⟨|r| + 1, by positivity, fun y hy => ?_⟩
  exact mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 (hr hy)) (by linarith [le_abs_self r]))

/-- Stopped slices lie in a ball of radius `R / 2` (the rescaled half-ball stopping of `IsStoppedAtHalfBall`). -/
theorem stopped_subset_ball {Λs : ℝ → Set ℂ} {b T R : ℝ} (hb : 0 < b) (hR : 0 < R)
    (hstop : IsStoppedAtHalfBall (rescaledFamily Λs R b) T) {s : ℝ} (hs : s ∈ Ioo 0 (b * T)) :
    Λs s ⊆ ball 0 (R / 2) := by
  intro y hy
  have ht : s / b ∈ Ioo 0 T := by
    refine ⟨div_pos hs.1 hb, ?_⟩
    rw [div_lt_iff₀ hb]
    linarith [hs.2, mul_comm b T]
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have e1 : b * (s / b) = s := by field_simp
  have e2 : (R : ℂ) * (y / (R : ℂ)) = y := by field_simp
  have hmem : y / (R : ℂ) ∈ rescaledFamily Λs R b (s / b) := by
    show (R : ℂ) * (y / (R : ℂ)) ∈ Λs (b * (s / b))
    rw [e1, e2]
    exact hy
  have hn : ‖y / (R : ℂ)‖ < 1 / 2 := mem_ball_zero_iff.1 (hstop.1 (s / b) ht hmem)
  rw [mem_ball_zero_iff, ← e2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have := mul_lt_mul_of_pos_left hn hR
  linarith

/-- The rescaled stopped family at time `u` is regular open (its slice is the preimage of `Λs (b u)` under
`x ↦ R x` for `0 < u < T`, and empty otherwise). -/
theorem familyProcess_rescaled_slice_regular {μ : Measure ℂ} {Λs : ℝ → Set ℂ} {b T R : ℝ} (hb : 0 < b)
    (hR : R ≠ 0) (hfam : IsConeHarmonicBallFamilyOn μ Λs (b * T)) (u : ℝ) :
    IsOpen (famOf (familyProcess (rescaledFamily Λs R b) T) u) ∧
      interior (closure (famOf (familyProcess (rescaledFamily Λs R b) T) u)) =
        famOf (familyProcess (rescaledFamily Λs R b) T) u := by
  by_cases hu : u ∈ Ioo 0 T
  · have hbu : b * u ∈ Ioo 0 (b * T) :=
      ⟨mul_pos hb hu.1, mul_lt_mul_of_pos_left hu.2 hb⟩
    have hset : famOf (familyProcess (rescaledFamily Λs R b) T) u =
        (fun x : ℂ => (R : ℂ) * x) ⁻¹' Λs (b * u) := by
      ext x
      exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
    rw [hset]
    exact isRegularOpen_preimage_mul (hfam.1 (b * u) hbu).1 (hfam.2.1.isRegularOpen (b * u) hbu) hR
  · have hset : famOf (familyProcess (rescaledFamily Λs R b) T) u = ∅ := by
      ext x
      exact ⟨fun h => absurd h.1 hu, fun h => by simp at h⟩
    rw [hset]
    exact ⟨isOpen_empty, by simp⟩

/-- **The glue identity (4.10) and its decoder form.** Let `Λg` be a global cone family and, for each `n`, `Λs n` a stopped
family with horizon `b n * Ts n`, rescaled by `R n > 0`, with unbounded horizons. Then for every `t`, `z`: some `n` has
the rescaled stopped process at `(t / b n, z / R n)` true, together with `0 < t`, if and only if `0 < t` and `z ∈ Λg t`. -/
theorem glue_det {μ : Measure ℂ} {Λg : ℝ → Set ℂ} (hg : IsConeHarmonicBallFamily μ Λg)
    {Λs : ℕ → ℝ → Set ℂ} {Ts R b : ℕ → ℝ} (hb : ∀ n, 0 < b n) (hR : ∀ n, 0 < R n)
    (hfam : ∀ n, IsConeHarmonicBallFamilyOn μ (Λs n) (b n * Ts n))
    (hstop : ∀ n, IsStoppedAtHalfBall (rescaledFamily (Λs n) (R n) (b n)) (Ts n))
    (hunb : ∀ M : ℕ, ∃ n, (M : ℝ) < b n * Ts n) (t : ℝ) (z : ℂ) :
    (0 < t ∧ ∃ n, familyProcess (rescaledFamily (Λs n) (R n) (b n)) (Ts n)
        (t / b n, z / (R n : ℂ))) ↔ (0 < t ∧ z ∈ Λg t) := by
  constructor
  · rintro ⟨ht, n, h⟩
    obtain ⟨hu, hw⟩ := familyProcess_iff.1 h
    have hbn : 0 < b n := hb n
    have hbn' : b n ≠ 0 := hbn.ne'
    have hRn : (R n : ℂ) ≠ 0 := by exact_mod_cast (hR n).ne'
    have hlt : t < b n * Ts n := by
      have := (div_lt_iff₀ hbn).1 hu.2
      linarith [mul_comm (Ts n) (b n)]
    have htI : t ∈ Ioo 0 (b n * Ts n) := ⟨ht, hlt⟩
    have e1 : (R n : ℂ) * (z / (R n : ℂ)) = z := by field_simp
    have e2 : b n * (t / b n) = t := by field_simp
    have hzs : z ∈ Λs n t := by
      have hw' : (R n : ℂ) * (z / (R n : ℂ)) ∈ Λs n (b n * (t / b n)) := hw
      rw [e1, e2] at hw'
      exact hw'
    obtain ⟨r₂, hr₂, hgt⟩ := exists_pos_subset_ball_of_isBounded (hg.2.1.isBounded t ht)
    have hst : Λs n t ⊆ ball 0 (R n / 2) := stopped_subset_ball (hb n) (hR n) (hstop n) htI
    have heq : Λs n t = Λg t :=
      obstacle_eq_of_global_stopped hg.2.2 (hfam n).2.2 htI (half_pos (hR n)) hr₂ hst hgt
    exact ⟨ht, by rw [← heq]; exact hzs⟩
  · rintro ⟨ht, hz⟩
    obtain ⟨n, hn⟩ := hunb (⌈t⌉₊)
    have htle : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have hlt : t < b n * Ts n := lt_of_le_of_lt htle hn
    have htI : t ∈ Ioo 0 (b n * Ts n) := ⟨ht, hlt⟩
    obtain ⟨r₂, hr₂, hgt⟩ := exists_pos_subset_ball_of_isBounded (hg.2.1.isBounded t ht)
    have hst : Λs n t ⊆ ball 0 (R n / 2) := stopped_subset_ball (hb n) (hR n) (hstop n) htI
    have heq : Λs n t = Λg t :=
      obstacle_eq_of_global_stopped hg.2.2 (hfam n).2.2 htI (half_pos (hR n)) hr₂ hst hgt
    have hbn : 0 < b n := hb n
    have hbn' : b n ≠ 0 := hbn.ne'
    have hRn : (R n : ℂ) ≠ 0 := by exact_mod_cast (hR n).ne'
    have e1 : (R n : ℂ) * (z / (R n : ℂ)) = z := by field_simp
    have e2 : b n * (t / b n) = t := by field_simp
    refine ⟨ht, n, familyProcess_iff.2 ⟨⟨div_pos ht hbn, ?_⟩, ?_⟩⟩
    · rw [div_lt_iff₀ hbn]
      linarith [mul_comm (Ts n) (b n)]
    · show (R n : ℂ) * (z / (R n : ℂ)) ∈ Λs n (b n * (t / b n))
      rw [e1, e2, heq]
      exact hz

end MatedCRT
