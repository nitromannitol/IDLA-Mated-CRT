import MatedCRT.FirstPass.Closure.M0CdfMeasurable

/-!
# Exact reparametrizations up to exit times, and their patching

Two paths `f`, `g : ℝ≥0 → α` are related by an exact increasing reparametrization carrying `[0,a]`
onto `[0,b]` when `f = g ∘ φ` on `[0,a]` for a strictly increasing `φ` mapping `[0,a]` onto
`[0,b]`.  If `f` and `g` are continuous paths in the plane and `f` leaves an open set `U` before
time `a`, then the first exit time of `g` from `U` is the image under `φ` of that of `f`
(`exitTime_transport`).  A family of such reparametrizations `φ k` on `[0,s k]`, compatible at the
exit times `s j ≤ s k`, patches to a single strictly increasing continuous surjection `τ` of `ℝ≥0`
with `f = g ∘ τ` (`exists_strictMono_patch`): between consecutive exit times `τ` is the
reparametrization of the first level whose exit time has not been passed.
-/

set_option autoImplicit false

open HarmonicBalls MarkovProcess Set
open scoped ENNReal NNReal

namespace MatedCRT.ExitReparamPatch

/-- `φ` is an exact increasing reparametrization carrying `[0,a]` onto `[0,b]`, with `f = g ∘ φ`
on `[0,a]`. -/
structure ExactReparam {α : Type*} (f g : ℝ≥0 → α) (a b : ℝ≥0) (φ : ℝ≥0 → ℝ≥0) : Prop where
  strictMonoOn : StrictMonoOn φ (Iic a)
  mapsTo : MapsTo φ (Iic a) (Iic b)
  surjOn : SurjOn φ (Iic a) (Iic b)
  eq : ∀ t, t ≤ a → f t = g (φ t)

namespace ExactReparam

variable {α : Type*} {f g : ℝ≥0 → α} {a b : ℝ≥0} {φ : ℝ≥0 → ℝ≥0}

theorem map_zero (h : ExactReparam f g a b φ) : φ 0 = 0 := by
  obtain ⟨t, ht, ht0⟩ := h.surjOn (mem_Iic.2 (bot_le : (0 : ℝ≥0) ≤ b))
  have h1 : φ 0 ≤ φ t :=
    h.strictMonoOn.monotoneOn (mem_Iic.2 (bot_le : (0 : ℝ≥0) ≤ a)) ht (bot_le : (0 : ℝ≥0) ≤ t)
  exact le_antisymm (h1.trans ht0.le) bot_le

theorem map_self (h : ExactReparam f g a b φ) : φ a = b := by
  obtain ⟨t, ht, ht0⟩ := h.surjOn (mem_Iic.2 (le_refl b))
  have h1 : φ t ≤ φ a :=
    h.strictMonoOn.monotoneOn ht (mem_Iic.2 (le_refl a)) ht
  exact le_antisymm (mem_Iic.1 (h.mapsTo (mem_Iic.2 (le_refl a)))) (ht0.symm.le.trans h1)

end ExactReparam

/-- Exit times transport along an exact reparametrization: if the continuous path `f` is outside
the open set `U` at time `a`, its first exit time `m` from `U` is attained, `m ≤ a`, and the first
exit time of `g` is `φ m`. -/
theorem exitTime_transport {f g : ContinuousPath ℂ} {a b : ℝ≥0} {φ : ℝ≥0 → ℝ≥0}
    (h : ExactReparam (⇑f) (⇑g) a b φ) {U : Set ℂ} (hU : IsOpen U) (ha : f a ∉ U) :
    ∃ m : ℝ≥0, m ≤ a ∧ pathExitTime U f = m ∧ f m ∉ U ∧ pathExitTime U g = φ m := by
  have hle : pathExitTime U f ≤ a := MatedCRT.M0Cdf.pathExitTime_le_of_not_mem ha
  have hlt : pathExitTime U f < ⊤ := lt_of_le_of_lt hle ENNReal.coe_lt_top
  obtain ⟨m, hm, hfm⟩ := MatedCRT.M0Cdf.exists_exit_eq hU f hlt
  have hma : m ≤ a := by
    rw [hm] at hle
    exact_mod_cast hle
  have hmI : m ∈ Iic a := hma
  refine ⟨m, hma, hm, hfm, le_antisymm ?_ ?_⟩
  · have hg : g (φ m) ∉ U := by
      rw [← h.eq m hma]
      exact hfm
    exact MatedCRT.M0Cdf.pathExitTime_le_of_not_mem hg
  · refine MatedCRT.M0Cdf.le_pathExitTime fun t' ht' => ?_
    rcases le_total t' b with hb | hb
    · obtain ⟨t, ht, rfl⟩ := h.surjOn (show t' ∈ Iic b from hb)
      have hgt : f t ∉ U := by
        rw [h.eq t ht]
        exact ht'
      have h1 : pathExitTime U f ≤ t := MatedCRT.M0Cdf.pathExitTime_le_of_not_mem hgt
      rw [hm] at h1
      have hmt : m ≤ t := by exact_mod_cast h1
      exact_mod_cast h.strictMonoOn.monotoneOn hmI ht hmt
    · have : φ m ≤ b := h.mapsTo hmI
      exact_mod_cast this.trans hb

/-- Patching of exact reparametrizations along a sequence of exit times.  Let `s k`, `s' k` be the
exit times of `f`, `g` at level `k`, with `φ k` an exact reparametrization of `[0,s k]` onto
`[0,s' k]`, and `φ k (s j) = s' j` for `j ≤ k`.  If `s` is monotone and `s`, `s'` are unbounded,
there is a strictly increasing continuous surjection `τ` of `ℝ≥0` with `τ 0 = 0` and
`f = g ∘ τ`. -/
theorem exists_strictMono_patch {α : Type*} {f g : ℝ≥0 → α} {s s' : ℕ → ℝ≥0}
    {φ : ℕ → ℝ≥0 → ℝ≥0} (hφ : ∀ k, ExactReparam f g (s k) (s' k) (φ k))
    (hcompat : ∀ j k, j ≤ k → φ k (s j) = s' j) (hs : Monotone s)
    (hsu : ∀ T : ℝ≥0, ∃ k, T ≤ s k) (hsu' : ∀ T : ℝ≥0, ∃ k, T ≤ s' k) :
    ∃ τ : ℝ≥0 → ℝ≥0, StrictMono τ ∧ Continuous τ ∧ τ 0 = 0 ∧ Function.Surjective τ ∧
      ∀ u, f u = g (τ u) := by
  classical
  let κ : ℝ≥0 → ℕ := fun u => Nat.find (hsu u)
  have hκ : ∀ u, u ≤ s (κ u) := fun u => Nat.find_spec (hsu u)
  have hκmin : ∀ u k, u ≤ s k → κ u ≤ k := fun u k hk => Nat.find_min' (hsu u) hk
  have hκlt : ∀ u k, k < κ u → s k < u := fun u k hk =>
    lt_of_not_ge fun hle => absurd (hκmin u k hle) (not_le.2 hk)
  let τ : ℝ≥0 → ℝ≥0 := fun u => φ (κ u) u
  have hstrict : StrictMono τ := by
    intro u u' huu
    have hk : κ u ≤ κ u' := hκmin u _ (huu.le.trans (hκ u'))
    rcases hk.eq_or_lt with hk | hk
    · show φ (κ u) u < φ (κ u') u'
      rw [← hk]
      exact (hφ _).strictMonoOn (hκ u) (hk ▸ hκ u' : u' ≤ s (κ u)) huu
    · have h1 : s (κ u) < u' := hκlt u' _ hk
      have hmem : s (κ u) ∈ Iic (s (κ u')) := h1.le.trans (hκ u')
      show φ (κ u) u < φ (κ u') u'
      calc φ (κ u) u ≤ s' (κ u) := (hφ _).mapsTo (hκ u)
        _ = φ (κ u') (s (κ u)) := (hcompat _ _ hk.le).symm
        _ < φ (κ u') u' := (hφ _).strictMonoOn hmem (hκ u') h1
  have hsurj : Function.Surjective τ := by
    intro y
    obtain ⟨k, hk, hkmin⟩ : ∃ k, y ≤ s' k ∧ ∀ j < k, ¬ y ≤ s' j :=
      ⟨Nat.find (hsu' y), Nat.find_spec (hsu' y), fun j hj => Nat.find_min (hsu' y) hj⟩
    obtain ⟨u, hu, hu'⟩ := (hφ k).surjOn (show y ∈ Iic (s' k) from hk)
    have hku : κ u = k := by
      refine le_antisymm (hκmin u k hu) ?_
      by_contra hlt
      have hlt := not_le.1 hlt
      apply hkmin _ hlt
      rw [← hcompat (κ u) k hlt.le, ← hu']
      exact (hφ k).strictMonoOn.monotoneOn hu (show s (κ u) ∈ Iic (s k) from hs hlt.le) (hκ u)
    refine ⟨u, ?_⟩
    show φ (κ u) u = y
    rw [hku]
    exact hu'
  refine ⟨τ, hstrict, hstrict.monotone.continuous_of_surjective hsurj, ?_, hsurj, fun u => ?_⟩
  · exact (hφ (κ 0)).map_zero
  · exact (hφ (κ u)).eq u (hκ u)

end MatedCRT.ExitReparamPatch
