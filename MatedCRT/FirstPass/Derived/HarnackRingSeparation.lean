import MatedCRT.FirstPass.Derived.HarnackFromSeparation
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Harnack ratio for the Green kernel from separation inside a ring

Deterministic part of Berestycki–Gwynne (2020), Proposition 3.8, in the form used for the Green kernel `g_B(·, b)`:
if the simple random walk on the mated-CRT map, started at `a`, has probability at least `p` to disconnect the
vertices of the shell `{r₁ < |· - z| < r₂}` from the vertices whose cells meet the two bounding spheres (the event
of Lemma 3.10, with `I₀` the set of those vertices) before it hits `I₀`, then the Green kernel satisfies
`p g_B(y, b) ≤ g_B(a, b)` for every vertex `y` with a cell point in the shell, whenever the pole `b` has a cell point
inside `B_{r₁}(z)` and every vertex outside the killing domain `B` has a cell point outside the shell.

The step from separation of `I₀` to separation of `{b} ∪ Bᶜ` is topological: consecutive cells of a walk meet and
cells are connected, so a walk from the shell to a vertex with a cell point off the shell passes through a cell
meeting one of the two spheres.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov

/-- A cell is connected. -/
theorem isPreconnected_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

/-- A cell is nonempty. -/
theorem cell_nonempty_of_nonneg {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : (cell ε η k).Nonempty :=
  ⟨η (ε * k), ε * k, ⟨by nlinarith, le_rfl⟩, rfl⟩

/-- A connected set which has a point strictly between two radii and meets neither sphere lies in the shell. -/
theorem forall_mem_shell_of_isPreconnected {z : ℂ} {r₁ r₂ : ℝ} {C : Set ℂ} (hC : IsPreconnected C)
    (h₁ : ∀ x ∈ C, dist x z ≠ r₁) (h₂ : ∀ x ∈ C, dist x z ≠ r₂)
    {p : ℂ} (hp : p ∈ C) (hp1 : r₁ < dist p z) (hp2 : dist p z < r₂) :
    ∀ x ∈ C, r₁ < dist x z ∧ dist x z < r₂ := by
  have hD : IsPreconnected ((fun x => dist x z) '' C) :=
    hC.image _ (continuous_id.dist continuous_const).continuousOn
  intro x hx
  constructor
  · by_contra hcon
    have hlt : dist x z < r₁ := lt_of_le_of_ne (not_lt.1 hcon) (h₁ x hx)
    have hm : r₁ ∈ (fun x => dist x z) '' C :=
      hD.Icc_subset ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩ ⟨hlt.le, hp1.le⟩
    obtain ⟨w, hw, hw1⟩ := hm
    exact h₁ w hw hw1
  · by_contra hcon
    have hlt : r₂ < dist x z := lt_of_le_of_ne (not_lt.1 hcon) (h₂ x hx).symm
    have hm : r₂ ∈ (fun x => dist x z) '' C :=
      hD.Icc_subset ⟨p, hp, rfl⟩ ⟨x, hx, rfl⟩ ⟨hp2.le, hlt.le⟩
    obtain ⟨w, hw, hw1⟩ := hm
    exact h₂ w hw hw1

/-- A cell with a point in the shell whose vertex does not belong to `I₀ ⊇ V(∂B_{r₁}) ∪ V(∂B_{r₂})` lies in the
shell. -/
theorem cell_subset_shell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r₁ r₂ : ℝ} {I₀ : Set ℤ}
    (hI₀ : cellVertices ε η (sphere z r₁) ∪ cellVertices ε η (sphere z r₂) ⊆ I₀) {k : ℤ}
    (hk : k ∉ I₀) (hp : ∃ x ∈ cell ε η k, r₁ < dist x z ∧ dist x z < r₂) :
    ∀ x ∈ cell ε η k, r₁ < dist x z ∧ dist x z < r₂ := by
  obtain ⟨p, hpk, hp1, hp2⟩ := hp
  refine forall_mem_shell_of_isPreconnected (isPreconnected_cell hη k) ?_ ?_ hpk hp1 hp2
  · intro x hx hxr
    exact hk (hI₀ (Or.inl ⟨x, hx, hxr⟩))
  · intro x hx hxr
    exact hk (hI₀ (Or.inr ⟨x, hx, hxr⟩))

/-- A path with consecutively meeting cells which starts in the shell and has not visited `I₀` up to time `n` has
its `n`-th cell inside the shell. -/
theorem cell_subset_shell_of_path {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r₁ r₂ : ℝ}
    {I₀ : Set ℤ} (hI₀ : cellVertices ε η (sphere z r₁) ∪ cellVertices ε η (sphere z r₂) ⊆ I₀)
    {ξ : ℕ → ℤ} (hstep : ∀ j, (cell ε η (ξ j) ∩ cell ε η (ξ (j + 1))).Nonempty)
    (h0 : ∃ x ∈ cell ε η (ξ 0), r₁ < dist x z ∧ dist x z < r₂) :
    ∀ n : ℕ, (∀ j ≤ n, ξ j ∉ I₀) → ∀ x ∈ cell ε η (ξ n), r₁ < dist x z ∧ dist x z < r₂ := by
  intro n
  induction n with
  | zero => exact fun h => cell_subset_shell hη hI₀ (h 0 le_rfl) h0
  | succ n ih =>
    intro h
    have hn := ih fun j hj => h j (hj.trans (Nat.le_succ n))
    obtain ⟨x, hx1, hx2⟩ := hstep n
    exact cell_subset_shell hη hI₀ (h (n + 1) le_rfl) ⟨x, hx2, hn x hx1⟩

/-- A walk in a graph whose adjacent vertices have meeting cells, started in the shell and avoiding `I₀`, ends with
a cell inside the shell. -/
theorem cell_subset_shell_of_walk {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r₁ r₂ : ℝ}
    {I₀ : Set ℤ} (hI₀ : cellVertices ε η (sphere z r₁) ∪ cellVertices ε η (sphere z r₂) ⊆ I₀)
    {Γ : SimpleGraph ℤ} (hΓ : ∀ j k, Γ.Adj j k → (cell ε η j ∩ cell ε η k).Nonempty) :
    ∀ {u v : ℤ} (w : Γ.Walk u v), (∃ x ∈ cell ε η u, r₁ < dist x z ∧ dist x z < r₂) →
      (∀ k ∈ w.support, k ∉ I₀) → ∀ x ∈ cell ε η v, r₁ < dist x z ∧ dist x z < r₂ := by
  intro u v w
  induction w with
  | nil =>
    intro h0 hsupp
    exact cell_subset_shell hη hI₀ (hsupp _ (by simp)) h0
  | @cons u v' w' h p ih =>
    intro h0 hsupp
    have hu : u ∉ I₀ := hsupp u (by simp)
    have hall := cell_subset_shell hη hI₀ hu h0
    obtain ⟨x, hx1, hx2⟩ := hΓ _ _ h
    exact ih ⟨x, hx2, hall x hx1⟩ fun k hk => hsupp k (by simp [hk])

/-- If a vertex set `U₀` separates `A` from `I₀`, then a larger set `U` separates `y ∈ A` from every vertex `k` whose
cell has a point off the shell (the vertices of `I`). -/
theorem graphSeparates_of_ring {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r₁ r₂ : ℝ}
    {I₀ : Set ℤ} (hI₀ : cellVertices ε η (sphere z r₁) ∪ cellVertices ε η (sphere z r₂) ⊆ I₀)
    {m : ℤ → ℤ → ℕ} (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {U₀ U A I : Set ℤ} (hU : U₀ ⊆ U) {y : ℤ} (hyA : y ∈ A)
    (hya : ∃ x ∈ cell ε η y, r₁ < dist x z ∧ dist x z < r₂)
    (hI : ∀ k ∈ I, ∃ x ∈ cell ε η k, dist x z < r₁ ∨ r₂ < dist x z)
    (hsep : GraphSeparates (srwGraph m) U₀ A I₀) :
    GraphSeparates (srwGraph m) U {y} I := by
  classical
  intro y' hy' k hk w
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  have hΓ : ∀ j k, (srwGraph m).Adj j k → (cell ε η j ∩ cell ε η k).Nonempty := by
    intro j k hjk
    rcases hjk.2 with h | h
    · exact hedge j k h
    · rw [Set.inter_comm]; exact hedge k j h
  have hex : ∃ u ∈ w.support, u ∈ I₀ := by
    by_contra hno
    push Not at hno
    have hall := cell_subset_shell_of_walk hη hI₀ hΓ w hya hno
    obtain ⟨x, hx, hxo⟩ := hI k hk
    have hxs := hall x hx
    rcases hxo with h | h
    · exact absurd hxs.1 (not_lt.2 h.le)
    · exact absurd hxs.2 (not_lt.2 h.le)
  obtain ⟨u, hu, huI⟩ := hex
  obtain ⟨v, hv, hvU⟩ := hsep _ hyA u huI (w.takeUntil u hu)
  exact ⟨v, SimpleGraph.Walk.support_takeUntil_subset_support w hu hv, hU hvU⟩

/-- Along a path with consecutively meeting cells that starts in the shell, the first visit to `I₀` is not later than
the first visit to a set `I` of vertices having a cell point off the shell. -/
theorem hitTime_le_of_ring {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} {r₁ r₂ : ℝ}
    {I₀ I : Set ℤ} (hI₀ : cellVertices ε η (sphere z r₁) ∪ cellVertices ε η (sphere z r₂) ⊆ I₀)
    (hI : ∀ k ∈ I, ∃ x ∈ cell ε η k, dist x z < r₁ ∨ r₂ < dist x z)
    {ξ : ℕ → ℤ} (hstep : ∀ j, (cell ε η (ξ j) ∩ cell ε η (ξ (j + 1))).Nonempty)
    (h0 : ∃ x ∈ cell ε η (ξ 0), r₁ < dist x z ∧ dist x z < r₂) :
    hitTime I₀ ξ ≤ hitTime I ξ := by
  by_cases htop : hitTime I ξ = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
    rw [← hn]
    obtain ⟨j, hjn, hj⟩ := hitTime_le_coe_iff.1 (le_of_eq hn.symm)
    have hex : ∃ j' ≤ j, ξ j' ∈ I₀ := by
      by_contra hno
      push Not at hno
      have hall := cell_subset_shell_of_path hη hI₀ hstep h0 j fun i hi => hno i hi
      obtain ⟨x, hx, hxo⟩ := hI _ hj
      have hxs := hall x hx
      rcases hxo with h | h
      · exact absurd hxs.1 (not_lt.2 h.le)
      · exact absurd hxs.2 (not_lt.2 h.le)
    obtain ⟨j', hj'j, hj'⟩ := hex
    exact hitTime_le_coe_iff.2 ⟨j', hj'j.trans hjn, hj'⟩

/-- **Harnack ratio for the Green kernel from ring separation.** With `I₀ ⊇ V(∂B_{r₁}(z)) ∪ V(∂B_{r₂}(z))` and
`A ∋ y` such that the walk from `a` disconnects `A` from `I₀` before hitting `I₀` with probability at least `p`:
if `a, y` have cell points in the shell `r₁ < |· - z| < r₂`, the pole `b ∈ B` has a cell point in `B_{r₁}(z)` and
every vertex outside `B` has a cell point off the shell, then `p g_B(y, b) ≤ g_B(a, b)`. -/
theorem mul_greenKernel_le_of_ringSeparation {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hη : Continuous η)
    {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hedge : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {B : Set ℤ} (hB : B.Finite) {b : ℤ} (hbB : b ∈ B) {a y : ℤ} {p : ℝ} (hp : 0 ≤ p)
    {z : ℂ} {r₁ r₂ : ℝ} {I₀ A : Set ℤ}
    (hI₀ : cellVertices ε η (sphere z r₁) ∪ cellVertices ε η (sphere z r₂) ⊆ I₀)
    (hyA : y ∈ A) (hya : ∃ x ∈ cell ε η y, r₁ < dist x z ∧ dist x z < r₂)
    (haa : ∃ x ∈ cell ε η a, r₁ < dist x z ∧ dist x z < r₂)
    (hb : ∃ x ∈ cell ε η b, dist x z < r₁)
    (hBc : ∀ k ∉ B, ∃ x ∈ cell ε η k, dist x z < r₁ ∨ r₂ < dist x z)
    (hsep : ENNReal.ofReal p ≤ srwLaw m a
      {ξ | GraphSeparates (srwGraph m) (traceBefore (id : ℤ → ℤ) I₀ ξ) A I₀}) :
    p * greenKernel m B y b ≤ greenKernel m B a b := by
  have hI : ∀ k ∈ ({b} ∪ Bᶜ : Set ℤ), ∃ x ∈ cell ε η k, dist x z < r₁ ∨ r₂ < dist x z := by
    intro k hk
    rcases hk with hk | hk
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      obtain ⟨x, hx, hxz⟩ := hb
      exact ⟨x, hx, Or.inl hxz⟩
    · exact hBc k hk
  have hae := (srwLaw_ae_start m a).and (srwAeAdjacentStep m a)
  have hmono : srwLaw m a {ξ | GraphSeparates (srwGraph m) (traceBefore (id : ℤ → ℤ) I₀ ξ) A I₀} ≤
      srwLaw m a {ξ | GraphSeparates (srwGraph m)
        (traceBefore (id : ℤ → ℤ) ({b} ∪ Bᶜ) ξ) {y} ({b} ∪ Bᶜ)} := by
    refine measure_mono_ae ?_
    filter_upwards [hae] with ξ hξ hs
    obtain ⟨hξ0, hξs⟩ := hξ
    have hstep : ∀ j, (cell ε η (ξ j) ∩ cell ε η (ξ (j + 1))).Nonempty := by
      intro j
      rcases hξs j with h | h
      · rw [h, Set.inter_self]; exact cell_nonempty_of_nonneg hε η _
      · exact hedge _ _ h
    have h0 : ∃ x ∈ cell ε η (ξ 0), r₁ < dist x z ∧ dist x z < r₂ := by rw [hξ0]; exact haa
    have hle := hitTime_le_of_ring hη hI₀ hI hstep h0
    have hU : traceBefore (id : ℤ → ℤ) I₀ ξ ⊆ traceBefore (id : ℤ → ℤ) ({b} ∪ Bᶜ) ξ := by
      unfold traceBefore
      rintro v ⟨n, hn, hv⟩
      exact ⟨n, lt_of_lt_of_le hn hle, hv⟩
    exact graphSeparates_of_ring hη hI₀ hedge hU hyA hya hI hs
  exact mul_greenKernel_le_of_separation hlf hcons hB hbB hp (hsep.trans hmono)

end MatedCRT
