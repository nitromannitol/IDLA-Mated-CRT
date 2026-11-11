import Mathlib

/-!
# Identification of a clock from convergence of its approximants (fibre argument)

Abstract form of the identification `φ = Φ` of the killed-occupation chain (tex:370-425, appendix-occupation-C16.tex):
the approximants `ψ k` (dyadic scales `k`) converge in probability over the product of the environment and the planar
Brownian path to `Φ`, and for each environment the approximants converge in probability over the Brownian path to the
clock `clock ω`. Then the clock equals `Φ` almost surely, on `[0, σ]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Fibre identification of a clock** (Duplantier-Sheffield, Berestycki-Powell convergence in probability, applied
to the product space `Ω × β` of environments and Brownian paths). A subsequence of approximants converges almost
surely on the product (Borel-Cantelli), Fubini gives fibrewise convergence, and uniqueness of the limit in
probability along each fibre identifies the clock with `Φ` on `[0, σ]`. -/
theorem clock_eq_of_approx_convergence {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure β) [IsProbabilityMeasure Q]
    (σ : β → ℝ≥0) (ψ : ℕ → Ω → β → ℝ≥0 → ℝ) (Φ clock : Ω → β → ℝ≥0 → ℝ)
    (hconv : ∀ η : ℝ, 0 < η → Tendsto (fun k : ℕ => (P.prod Q)
      {p : Ω × β | ∃ s ≤ σ p.2, η ≤ |ψ k p.1 p.2 s - Φ p.1 p.2 s|}) atTop (𝓝 0))
    (hlq : ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (η : ℝ), 0 < η → Tendsto (fun k : ℕ => Q
      {b | ∃ t ≤ T, η ≤ |ψ k ω b t - clock ω b t|}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ s ≤ σ b, clock ω b s = Φ ω b s := by
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ, ∀ m, η m = 1 / ((m : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have hηpos : ∀ m, 0 < η m := fun m => by rw [hη]; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℕ → Set (Ω × β), ∀ m k,
      A m k = {p : Ω × β | ∃ s ≤ σ p.2, η m ≤ |ψ k p.1 p.2 s - Φ p.1 p.2 s|} := ⟨_, fun _ _ => rfl⟩
  -- Step 1: along a subsequence the bad sets are summable (Borel-Cantelli)
  have hsub : ∀ m, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∑' j, (P.prod Q) (A m (φ j)) ≠ ⊤ := by
    intro m
    have h0 : Tendsto (fun k => (P.prod Q) (A m k)) atTop (𝓝 0) := by
      simp only [hA]
      exact hconv (η m) (hηpos m)
    have hev : ∀ j : ℕ, ∀ᶠ k in atTop, (P.prod Q) (A m k) ≤ ((2 : ℝ≥0∞)⁻¹) ^ j := by
      intro j
      have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ j :=
        ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) j
      filter_upwards [(tendsto_order.1 h0).2 _ hpos] with k hk
      exact hk.le
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_forall_of_eventually hev
    refine ⟨φ, hφ, ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => hφb j)⟩
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    exact ENNReal.inv_ne_top.2 (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  choose φ hφ hsum using hsub
  -- Step 2: almost surely on the product, the approximants eventually avoid the bad sets
  have hBC : ∀ᵐ p ∂(P.prod Q), ∀ m, ∀ᶠ j in atTop, p ∉ A m (φ m j) := by
    rw [ae_all_iff]
    intro m
    exact ae_eventually_notMem (hsum m)
  have hBC2 : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ m, ∀ᶠ j in atTop, (ω, b) ∉ A m (φ m j) :=
    Measure.ae_ae_of_ae_prod hBC
  filter_upwards [hBC2, hlq] with ω hω1 hω2
  -- Step 3: fibrewise, the clock and `Φ` agree on `[0, σ]`
  have hnull : ∀ T m : ℕ, ∀ᵐ b ∂Q, ¬ ∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧ s ≤ σ b ∧
      η m ≤ |clock ω b s - Φ ω b s| := by
    intro T m
    obtain ⟨m', hm'⟩ := exists_nat_one_div_lt (half_pos (hηpos m))
    have hm'' : η m' < η m / 2 := by rw [hη]; exact hm'
    -- the event that the approximant is far from the clock at a time `≤ T`
    obtain ⟨E, hE⟩ : ∃ E : ℕ → Set β, ∀ j, E j =
        {b | ∃ t ≤ (T : ℝ≥0), η m / 2 ≤ |ψ (φ m' j) ω b t - clock ω b t|} := ⟨_, fun _ => rfl⟩
    have hEt : Tendsto (fun j => Q (E j)) atTop (𝓝 0) := by
      have h := (hω2 (T : ℝ≥0) (η m / 2) (half_pos (hηpos m))).comp (hφ m').tendsto_atTop
      simp only [hE]
      exact h
    -- almost surely in `b`, the approximants are eventually `η m'`-close to `Φ` on `[0, σ b]`
    have hclose : ∀ᵐ b ∂Q, ∀ᶠ j in atTop, ∀ s ≤ σ b, |ψ (φ m' j) ω b s - Φ ω b s| < η m' := by
      filter_upwards [hω1] with b hb
      filter_upwards [hb m'] with j hj
      intro s hs
      by_contra h
      rw [hA] at hj
      exact hj (show ∃ s' ≤ σ b, η m' ≤ |ψ (φ m' j) ω b s' - Φ ω b s'| from
        ⟨s, hs, not_lt.1 h⟩)
    -- the exceptional sets `F N` are null
    obtain ⟨F, hF⟩ : ∃ F : ℕ → Set β, ∀ N, F N = {b | ∀ j, N ≤ j → b ∈ E j} := ⟨_, fun _ => rfl⟩
    have hFnull : ∀ N, Q (F N) = 0 := by
      intro N
      refine le_antisymm (ge_of_tendsto hEt ?_) zero_le
      refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
      exact measure_mono (fun b (hb : b ∈ F N) => by rw [hF] at hb; exact hb j hj)
    have hFae : ∀ᵐ b ∂Q, b ∉ ⋃ N, F N := by
      rw [ae_iff]
      simp only [not_not, Set.ofPred_mem_eq]
      exact measure_iUnion_null hFnull
    have h1 : ∀ᵐ b ∂Q, (∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧ s ≤ σ b ∧ η m ≤ |clock ω b s - Φ ω b s|) →
        ∃ N, ∀ j, N ≤ j → b ∈ E j := by
      filter_upwards [hclose] with b hb hBb
      obtain ⟨s, hsT, hsσ, hs⟩ := hBb
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hb.mono fun j hj => hj s hsσ)
      refine ⟨N, fun j hj => ?_⟩
      have hcl := hN j hj
      rw [hE]
      refine ⟨s, hsT, ?_⟩
      have htri : |clock ω b s - Φ ω b s| ≤ |ψ (φ m' j) ω b s - clock ω b s| +
          |ψ (φ m' j) ω b s - Φ ω b s| := by
        have := abs_sub_le (clock ω b s) (ψ (φ m' j) ω b s) (Φ ω b s)
        rw [abs_sub_comm (clock ω b s) (ψ (φ m' j) ω b s)] at this
        linarith
      linarith
    filter_upwards [h1, hFae] with b hb1 hb2 hBb
    obtain ⟨N, hN⟩ := hb1 hBb
    refine hb2 (mem_iUnion.2 ⟨N, ?_⟩)
    rw [hF]
    exact fun j hj => hN j hj
  have hall : ∀ᵐ b ∂Q, ∀ T m : ℕ, ¬ ∃ s : ℝ≥0, s ≤ (T : ℝ≥0) ∧ s ≤ σ b ∧
      η m ≤ |clock ω b s - Φ ω b s| :=
    ae_all_iff.2 fun T => ae_all_iff.2 fun m => hnull T m
  filter_upwards [hall] with b hb s hs
  by_contra hne
  have hpos : 0 < |clock ω b s - Φ ω b s| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  have hm' : η m ≤ |clock ω b s - Φ ω b s| := by rw [hη]; exact hm.le
  exact hb (⌈s⌉₊) m ⟨s, Nat.le_ceil s, hs, hm'⟩

end MatedCRT.KilledOccupation
