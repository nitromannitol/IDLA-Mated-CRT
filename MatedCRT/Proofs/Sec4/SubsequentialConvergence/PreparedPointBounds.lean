import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedDenseLimit

/-! Pointwise boundedness supplied by prepared compactness. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- A real sequence with a convergent further subsequence along every
subsequence is eventually bounded. -/
theorem eventually_bounded_of_subsequential_compactness (u : ℕ → ℝ)
    (hc : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ l : ℝ,
      Tendsto (fun n => u (ψ (θ n))) atTop (𝓝 l)) :
    ∃ M : ℝ, ∀ᶠ n in atTop, |u n| ≤ M := by
  classical
  by_contra h
  have hf : ∀ M : ℝ, ∀ N : ℕ, ∃ n ≥ N, M < |u n| := by
    intro M N
    by_contra hn
    push Not at hn
    apply h
    refine ⟨M, eventually_atTop.2 ⟨N, ?_⟩⟩
    intro n hnN
    exact hn n hnN
  let pick : ℕ → ℕ → ℕ := fun k N => Classical.choose (hf k N)
  have hpick : ∀ k N, N ≤ pick k N ∧ (k : ℝ) < |u (pick k N)| :=
    fun k N => Classical.choose_spec (hf k N)
  let φ : ℕ → ℕ := fun n => Nat.rec (pick 0 0) (fun k prev => pick (k + 1) (prev + 1)) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := (hpick (n + 1) (φ n + 1)).1
    change φ n < pick (n + 1) (φ n + 1)
    omega
  have hlarge : ∀ n : ℕ, (n : ℝ) < |u (φ n)| := by
    intro n
    cases n with
    | zero => exact (hpick 0 0).2
    | succ n => exact (hpick (n + 1) (φ n + 1)).2
  obtain ⟨θ, hθ, l, hlim⟩ := hc φ hφ
  have hb : ∀ᶠ n in atTop, |u (φ (θ n))| ≤ |l| + 1 := by
    have hm := Metric.tendsto_nhds.1 hlim 1 zero_lt_one
    filter_upwards [hm] with n hn
    rw [Real.dist_eq] at hn
    have ht := abs_sub_le (u (φ (θ n))) l 0
    simp only [sub_zero] at ht
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (|l| + 1)
  obtain ⟨n, hn⟩ := (hb.and (eventually_ge_atTop N)).exists
  have hθn : n ≤ θ n := hθ.id_le n
  have hN' : (|l| + 1) < (θ n : ℝ) := hN.trans_le (by exact_mod_cast le_trans hn.2 hθn)
  linarith [hlarge (θ n), hn.1]

/-- Every prepared odometer sequence is bounded at each point of the closed ball. -/
theorem OdometerPreparedCompactness.eventually_bounded_at
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ t : ℝ} {e : ℕ → ℝ} {ω : Ω}
    (hc : OdometerPreparedCompactness S ρ t e ω)
    {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) ρ) :
    ∃ M : ℝ, ∀ᶠ n in atTop, |rescaledMatedLeastSupersolution S ρ t (e n) ω x| ≤ M := by
  apply eventually_bounded_of_subsequential_compactness
  intro ψ hψ
  obtain ⟨θ, hθ, w, hw, hconv⟩ := hc.1 ψ hψ
  exact ⟨θ, hθ, w x, hconv.tendsto_at hx⟩

end MatedCRT
