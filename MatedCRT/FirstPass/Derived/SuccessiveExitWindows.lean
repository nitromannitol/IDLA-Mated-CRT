import MatedCRT.FirstPass.Derived.SuccessiveExitGaps
import MatedCRT.FirstPass.S4S6c.FrontierSeparation

/-!
# Travel windows from bounded gaps of the successive exits (BG20 Prop 6.14, (6.49)-(6.51) => (6.47))

Let `A y ⊆ ℤ` be the region attached to the vertex `y` (in Berestycki–Gwynne the vertices of the
mated-CRT map in the Euclidean ball of radius `δ` around `η y`) and `σ_k = succExit A k` the successive
exit times of the walk from these regions (`σ_0 = 0`, `σ_{k+1} = σ_k + τ_{A (X_{σ_k})} ∘ θ_{σ_k}`).

* `exists_window_of_gaps` is the deterministic step from (6.51) to (6.47): if the gaps `σ_{k+1} - σ_k`
  are at most `b` as long as `σ_k < τ` and `τ ≤ σ_K`, every window `[j, j + 2 b)` with `j + b ≤ τ` contains
  a whole interval `[σ_k, σ_{k+1}]`.
* `exists_window_travel` transfers this to the walk: the walk is outside `A (X_{σ_k})` at time `σ_{k+1}`,
  so in every such window the walk leaves the region of one of its own positions (for the balls of
  Berestycki–Gwynne: `η (X)` travels Euclidean distance at least `δ` inside the window).
* `srwLaw_exists_gapEvent_le_delta` is the real-arithmetic form of (6.49): with the exit-time moments
  `N! (ε⁻¹ δ ^ q') ^ N` of (6.48), `b = ⌊ε⁻¹ δ ^ q⌋` and `⌊δ⁻³⌋ + 1` indices, the probability that some gap
  exceeds `b` is at most `2 N! δ ^ (N (q' - q) - 3)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

namespace SuccessiveExitGaps

lemma enat_add_one_le_of_lt {a c : ℕ∞} (h : a < c) : a + 1 ≤ c := by
  induction a using ENat.recTopCoe with
  | top => exact absurd h (not_lt.mpr le_top)
  | coe n =>
    induction c using ENat.recTopCoe with
    | top => simp
    | coe m =>
      have hnm : n < m := by exact_mod_cast h
      exact_mod_cast Nat.succ_le_of_lt hnm

lemma enat_lt_of_add_one_le {a c : ℕ∞} (hc : c ≠ ⊤) (h : a + 1 ≤ c) : a < c := by
  induction a using ENat.recTopCoe with
  | top =>
    rw [top_add, top_le_iff] at h
    exact absurd h hc
  | coe n =>
    induction c using ENat.recTopCoe with
    | top => exact absurd rfl hc
    | coe m =>
      have hnm : n + 1 ≤ m := by exact_mod_cast h
      exact_mod_cast Nat.lt_of_succ_le hnm

/-- Deterministic step (BG20 (6.51) => (6.47)).  If `σ_0 = 0`, the gaps satisfy `σ_{k+1} ≤ σ_k + b` for
`k ≤ K` with `σ_k < τ`, and `τ ≤ σ_K`, then for each `j` with `j + b ≤ τ` there is `k` with
`j ≤ σ_k` and `σ_{k+1} < j + 2 b`. -/
theorem exists_window_of_gaps {σ : ℕ → ℕ∞} {τ : ℕ∞} {b K : ℕ} (hb : 1 ≤ b) (h0 : σ 0 = 0)
    (hgap : ∀ k ≤ K, σ k < τ → σ (k + 1) ≤ σ k + b) (hK : τ ≤ σ K) {j : ℕ}
    (hj : ((j + b : ℕ) : ℕ∞) ≤ τ) :
    ∃ k, (j : ℕ∞) ≤ σ k ∧ σ (k + 1) + 1 ≤ ((j + 2 * b : ℕ) : ℕ∞) := by
  classical
  have hjτ : (j : ℕ∞) ≤ τ := le_trans (by exact_mod_cast Nat.le_add_right j b) hj
  have hex : ∃ k, (j : ℕ∞) ≤ σ k := ⟨K, hjτ.trans hK⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ K := Nat.find_min' hex (hjτ.trans hK)
  have hmin : ∀ k < Nat.find hex, ¬ (j : ℕ∞) ≤ σ k := fun k hk => Nat.find_min hex hk
  generalize Nat.find hex = k0 at hspec hle hmin
  cases k0 with
  | zero =>
    rw [h0] at hspec
    have hj0 : j = 0 := by
      have h00 : (j : ℕ∞) = 0 := le_antisymm hspec (by simp)
      exact_mod_cast h00
    subst hj0
    have hbpos : (0 : ℕ∞) < ((0 + b : ℕ) : ℕ∞) := by exact_mod_cast (show 0 < 0 + b by omega)
    have hτ0 : σ 0 < τ := by
      rw [h0]
      exact lt_of_lt_of_le hbpos hj
    have h1 := hgap 0 (Nat.zero_le K) hτ0
    refine ⟨0, by rw [h0]; exact le_rfl, ?_⟩
    calc σ (0 + 1) + 1 ≤ (σ 0 + b) + 1 := add_le_add h1 le_rfl
      _ = ((b + 1 : ℕ) : ℕ∞) := by rw [h0]; push_cast; ring
      _ ≤ ((0 + 2 * b : ℕ) : ℕ∞) := by exact_mod_cast (show b + 1 ≤ 0 + 2 * b by omega)
  | succ k =>
    have hlt : σ k < j := not_le.mp (hmin k (Nat.lt_succ_self k))
    have hkK : k ≤ K := by omega
    have hτk : σ k < τ := hlt.trans_le hjτ
    have h1 := hgap k hkK hτk
    have hsk : σ k + 1 ≤ j := enat_add_one_le_of_lt hlt
    have h2 : σ (k + 1) + 1 ≤ ((j + b : ℕ) : ℕ∞) := by
      calc σ (k + 1) + 1 ≤ (σ k + b) + 1 := add_le_add h1 le_rfl
        _ = (σ k + 1) + b := add_right_comm _ _ _
        _ ≤ (j : ℕ∞) + b := add_le_add hsk le_rfl
        _ = ((j + b : ℕ) : ℕ∞) := (Nat.cast_add j b).symm
    have hlt2 : σ (k + 1) < τ :=
      (enat_lt_of_add_one_le (ENat.natCast_ne_top _) h2).trans_le hj
    have h3 := hgap (k + 1) hle hlt2
    refine ⟨k + 1, hspec, ?_⟩
    calc σ (k + 1 + 1) + 1 ≤ (σ (k + 1) + b) + 1 := add_le_add h3 le_rfl
      _ = (σ (k + 1) + 1) + b := add_right_comm _ _ _
      _ ≤ ((j + b : ℕ) : ℕ∞) + b := add_le_add h2 le_rfl
      _ = ((j + 2 * b : ℕ) : ℕ∞) := by push_cast; ring

/-- The successive exit times are nondecreasing. -/
lemma succExit_le_succ (A : ℤ → Set ℤ) (x : ℕ → ℤ) (k : ℕ) :
    succExit A k x ≤ succExit A (k + 1) x := by
  by_cases ht : succExit A k x = ⊤
  · have : succExit A (k + 1) x = ⊤ := by
      show SuccessiveExitStop.nextExit A (succExit A k) x = ⊤
      simp [SuccessiveExitStop.nextExit, ht]
    rw [this]
    exact le_top
  · obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.mp ht
    have h := S6j.nextExit_of_eq_coe A (succExit A k) (x := x) (i := i) hi.symm
    have h' : succExit A (k + 1) x =
        (i : ℕ∞) + vExitTime (A (x i)) (WalkPotential.pathShift i x) := h
    rw [h', ← hi]
    exact le_self_add

/-- If the `(k+1)`-st exit time is a finite time `i₂`, then the `k`-th is a finite time `i₁ ≤ i₂` and the
walk is outside `A (X_{i₁})` at time `i₂`. -/
lemma exists_notMem_of_succExit (A : ℤ → Set ℤ) (x : ℕ → ℤ) (k i₂ : ℕ)
    (h : succExit A (k + 1) x = (i₂ : ℕ∞)) :
    ∃ i₁ : ℕ, i₁ ≤ i₂ ∧ succExit A k x = (i₁ : ℕ∞) ∧ x i₂ ∉ A (x i₁) := by
  by_cases ht : succExit A k x = ⊤
  · exfalso
    have : succExit A (k + 1) x = ⊤ := by
      show SuccessiveExitStop.nextExit A (succExit A k) x = ⊤
      simp [SuccessiveExitStop.nextExit, ht]
    rw [this] at h
    exact ENat.natCast_ne_top _ h.symm
  · obtain ⟨i₁, hi⟩ := ENat.ne_top_iff_exists.mp ht
    have h1 := S6j.nextExit_of_eq_coe A (succExit A k) (x := x) (i := i₁) hi.symm
    have h' : succExit A (k + 1) x =
        (i₁ : ℕ∞) + vExitTime (A (x i₁)) (WalkPotential.pathShift i₁ x) := h1
    rw [h'] at h
    have hne : vExitTime (A (x i₁)) (WalkPotential.pathShift i₁ x) ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at h
      exact ENat.natCast_ne_top _ h.symm
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hd] at h
    have hsum : i₁ + d = i₂ := by exact_mod_cast h
    have hnot := FrontierSeparation.notMem_of_vExitTime_eq (hd.symm : vExitTime (A (x i₁)) (WalkPotential.pathShift i₁ x) = d)
    have hx : WalkPotential.pathShift i₁ x d = x i₂ := by
      simp only [WalkPotential.pathShift]
      congr 1
    rw [hx] at hnot
    exact ⟨i₁, by omega, hi.symm, hnot⟩

/-- Walk-level form of BG20 (6.51) => (6.47).  If no gap `σ_{k+1} - σ_k` with `k ≤ K` and `σ_k < τ_Y` exceeds
`b`, and `τ_Y ≤ σ_K`, then every window `[j, j + 2 b)` with `j + b ≤ τ_Y` contains times `i₁ ≤ i₂` with the
walk outside the region `A (X_{i₁})` at time `i₂`. -/
theorem exists_window_travel (A : ℤ → Set ℤ) (Y : Set ℤ) {b K : ℕ} (hb : 1 ≤ b) (x : ℕ → ℤ)
    (hgap : ∀ k < K + 1, x ∉ gapEvent A Y b k) (hK : vExitTime Y x ≤ succExit A K x) {j : ℕ}
    (hj : ((j + b : ℕ) : ℕ∞) ≤ vExitTime Y x) :
    ∃ i₁ i₂ : ℕ, j ≤ i₁ ∧ i₁ ≤ i₂ ∧ i₂ < j + 2 * b ∧ x i₂ ∉ A (x i₁) := by
  have hgap' : ∀ k ≤ K, succExit A k x < vExitTime Y x →
      succExit A (k + 1) x ≤ succExit A k x + b := by
    intro k hk hlt
    have hng : ¬ (succExit A k x < vExitTime Y x ∧
        succExit A k x + ((b + 1 : ℕ) : ℕ∞) ≤ succExit A (k + 1) x) := hgap k (Nat.lt_succ_of_le hk)
    by_contra hcon
    have h1 := enat_add_one_le_of_lt (not_le.mp hcon)
    refine hng ⟨hlt, ?_⟩
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h1
  obtain ⟨k, hjk, hk1⟩ := exists_window_of_gaps (σ := fun k => succExit A k x) hb rfl hgap' hK hj
  have hne : succExit A (k + 1) x ≠ ⊤ := by
    intro h
    rw [h, top_add, top_le_iff] at hk1
    exact ENat.natCast_ne_top _ hk1
  obtain ⟨i₂, hi₂⟩ := ENat.ne_top_iff_exists.mp hne
  obtain ⟨i₁, hi₁le, hi₁, hnot⟩ := exists_notMem_of_succExit A x k i₂ hi₂.symm
  refine ⟨i₁, i₂, ?_, hi₁le, ?_, hnot⟩
  · rw [hi₁] at hjk
    exact_mod_cast hjk
  · rw [← hi₂] at hk1
    have : i₂ + 1 ≤ j + 2 * b := by exact_mod_cast hk1
    omega

/-- Real-number form of the union bound (6.49): with `M = N! c ^ N`, at most `K N! (c / (b + 1)) ^ N`. -/
theorem srwLaw_exists_gapEvent_le_real (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ)
    (N b K : ℕ) {c : ℝ}
    (hM : ∀ y ∈ Y, exitTimeMoment m (A y) y N ≤ ENNReal.ofReal ((N.factorial : ℝ) * c ^ N)) :
    srwLaw m a {x | ∃ k < K, x ∈ gapEvent A Y b k} ≤
      ENNReal.ofReal ((K : ℝ) * ((N.factorial : ℝ) * (c / ((b : ℝ) + 1)) ^ N)) := by
  refine (srwLaw_exists_gapEvent_le m a A Y N b K hM).trans (le_of_eq ?_)
  have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have h1 : ((b + 1 : ℝ≥0∞)) ^ N = ENNReal.ofReal (((b : ℝ) + 1) ^ N) := by
    rw [ENNReal.ofReal_pow hb.le, ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp
  rw [h1, ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_natCast K,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  ring

/-- Real-arithmetic form of BG20 (6.49): with the exit-time moments `N! (ε⁻¹ δ ^ q') ^ N` of (6.48),
`b = ⌊ε⁻¹ δ ^ q⌋` and `⌊δ⁻³⌋ + 1` indices, the probability that some gap exceeds `b` is at most
`2 N! δ ^ (N (q' - q) - 3)` (`0 < δ ≤ 1`). -/
theorem srwLaw_exists_gapEvent_le_delta (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (N : ℕ)
    {ε δ q q' : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : ∀ y ∈ Y, exitTimeMoment m (A y) y N ≤
      ENNReal.ofReal ((N.factorial : ℝ) * (ε⁻¹ * δ ^ q') ^ N)) :
    srwLaw m a {x | ∃ k < ⌊δ ^ (-3 : ℝ)⌋₊ + 1, x ∈ gapEvent A Y ⌊ε⁻¹ * δ ^ q⌋₊ k} ≤
      ENNReal.ofReal (2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * (q' - q) - 3)) := by
  refine (srwLaw_exists_gapEvent_le_real m a A Y N ⌊ε⁻¹ * δ ^ q⌋₊ (⌊δ ^ (-3 : ℝ)⌋₊ + 1) hM).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hpos : 0 < ε⁻¹ * δ ^ q := by positivity
  have hlt : ε⁻¹ * δ ^ q < (⌊ε⁻¹ * δ ^ q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hratio : (ε⁻¹ * δ ^ q') / ((⌊ε⁻¹ * δ ^ q⌋₊ : ℝ) + 1) ≤ δ ^ (q' - q) := by
    calc (ε⁻¹ * δ ^ q') / ((⌊ε⁻¹ * δ ^ q⌋₊ : ℝ) + 1) ≤ (ε⁻¹ * δ ^ q') / (ε⁻¹ * δ ^ q) := by
          have := hlt.le
          gcongr
      _ = δ ^ (q' - q) := by
          rw [Real.rpow_sub hδ]
          field_simp
  have hpow : ((ε⁻¹ * δ ^ q') / ((⌊ε⁻¹ * δ ^ q⌋₊ : ℝ) + 1)) ^ N ≤ δ ^ ((q' - q) * N) := by
    rw [Real.rpow_mul_natCast hδ.le]
    exact pow_le_pow_left₀ (by positivity) hratio N
  have hδ3 : 1 ≤ δ ^ (-3 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by norm_num)
  have hK : ((⌊δ ^ (-3 : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * δ ^ (-3 : ℝ) := by
    push_cast
    have := Nat.floor_le (show 0 ≤ δ ^ (-3 : ℝ) by positivity)
    linarith
  have hfac : (0 : ℝ) ≤ (N.factorial : ℝ) := by positivity
  calc ((⌊δ ^ (-3 : ℝ)⌋₊ + 1 : ℕ) : ℝ) * ((N.factorial : ℝ) *
          ((ε⁻¹ * δ ^ q') / ((⌊ε⁻¹ * δ ^ q⌋₊ : ℝ) + 1)) ^ N)
      ≤ (2 * δ ^ (-3 : ℝ)) * ((N.factorial : ℝ) * δ ^ ((q' - q) * N)) := by
        gcongr
    _ = 2 * (N.factorial : ℝ) * δ ^ ((N : ℝ) * (q' - q) - 3) := by
        rw [show (N : ℝ) * (q' - q) - 3 = -3 + (q' - q) * N by ring, Real.rpow_add hδ]
        ring

#print axioms MatedCRT.SuccessiveExitGaps.exists_window_of_gaps
#print axioms MatedCRT.SuccessiveExitGaps.exists_window_travel
#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_exists_gapEvent_le_delta

end SuccessiveExitGaps

end MatedCRT
