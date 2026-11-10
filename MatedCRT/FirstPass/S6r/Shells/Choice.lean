import MatedCRT.FirstPass.S6r.Shells

/-!
# Lemma 6.8, window S7': total choice of the shell centre and good radius (referee repair of step 5)

At the hitting time `C = firstShellHit ε η X Σ` of a shell `Σ`, the centre is `z = Q_d(η(X_C))` and the good radius
is `R_z(d)` (PRO `shell_center_is_eligible`; referee table, step 5). Here the choice is made total with defaults:
the centre is `0` when `Σ` is never hit, and the radius is `d` at an ineligible centre. On the hitting event the
choice is the one of `shell_hit_choose_center_direct`, with eligibility derived, not assumed.
Step 6 needs the choice to be a measurable function of the path: `measurable_shellCentreAt` and
`measurable_shellRadiusAt`. `ℤ` carries the discrete σ-algebra.
-/

namespace MatedCRT.Lemma68Window

open MeasureTheory Metric Set

open Classical in
/-- Total shell centre (referee step 5): on the event that `S` is hit, `Q_d(η(X_C))` with
`C = firstShellHit ε η X S` (grid rounding of the vertex point of the hit cell); otherwise the default `0`. -/
noncomputable def shellCentreAt (g ε : ℝ) (η : ℝ → ℂ) (S : Set ℂ) (X : ℕ → ℤ) : ℂ :=
  if ∃ n, (cell ε η (X n) ∩ S).Nonempty then
    gridRound g (vertexPoint ε η (X (firstShellHit ε η X S))) else 0

open Classical in
/-- Total good radius (referee step 5): the good radius `R z` when the centre `z` is eligible, and the default `d`
at an ineligible centre. -/
noncomputable def shellRadiusAt (R : ℂ → ℝ) (Elig : ℂ → Prop) (d : ℝ) (z : ℂ) : ℝ :=
  if Elig z then R z else d

theorem shellCentreAt_of_hit {g ε : ℝ} {η : ℝ → ℂ} {S : Set ℂ} {X : ℕ → ℤ}
    (hit : ∃ n, (cell ε η (X n) ∩ S).Nonempty) :
    shellCentreAt g ε η S X = gridRound g (vertexPoint ε η (X (firstShellHit ε η X S))) := by
  unfold shellCentreAt
  simp only [hit, ↓reduceIte]

theorem shellRadiusAt_of_elig {R : ℂ → ℝ} {Elig : ℂ → Prop} {d : ℝ} {z : ℂ} (h : Elig z) :
    shellRadiusAt R Elig d z = R z := by
  unfold shellRadiusAt
  simp only [h, ↓reduceIte]

/-- Step 5 with total choices (referee repair): if `Σ = twoSidedShell K r lam` is hit, the total centre `z` and the
total radius `Rz = shellRadiusAt R Elig d z` satisfy the conclusions of `shell_hit_choose_center_direct` at the first
hitting time, with `Elig z`; the default is never used on the hitting event. -/
theorem shell_choice_total {K : Set ℂ} {ε r h d s g lam ρ s0 : ℝ} {η : ℝ → ℂ}
    (R : ℂ → ℝ) (Elig : ℂ → Prop) (Reg : Set ℂ)
    (hKne : K.Nonempty) (hs0 : ball (0 : ℂ) s0 ⊆ K) (hKb : K ⊆ ball (0 : ℂ) (ρ / 2))
    (hr : 0 < r) (hε : 0 < ε) (X : ℕ → ℤ)
    (hit : ∃ n, (cell ε η (X n) ∩ twoSidedShell K r lam).Nonempty)
    (hdiam : ∀ p ∈ cell ε η (X (firstShellHit ε η X (twoSidedShell K r lam))),
      ∀ q ∈ cell ε η (X (firstShellHit ε η X (twoSidedShell K r lam))), dist p q ≤ h)
    (hlam : lam ≤ r / 20) (hg : g = d / 100) (hd : 0 < d) (hh : h ≤ d / 100)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s)
    (hEligReg : ∀ w : ℂ, closedBall w (3 * s) ⊆ Reg → Elig w)
    (hReg : ∀ x : ℂ, 9 * s0 / 10 ≤ ‖x‖ → ‖x‖ ≤ 3 * ρ / 4 → x ∈ Reg)
    (hcut1 : 2 * g + 3 * s < s0 / 10)
    (hcut2 : ρ / 2 + 11 / 20 * r + 2 * g + 3 * s < 3 * ρ / 4)
    (z : ℂ) (hz : z = shellCentreAt g ε η (twoSidedShell K r lam) X)
    (Rz : ℝ) (hRz : Rz = shellRadiusAt R Elig d z) :
    (∃ y ∈ twoSidedShell K r lam, dist z y ≤ g + h) ∧ g + h ≤ Rz / 50 ∧
      (∀ p ∈ cell ε η (X (firstShellHit ε η X (twoSidedShell K r lam))), dist p z ≤ Rz / 50) ∧
      (∀ p ∈ cell ε η (X (firstShellHit ε η X (twoSidedShell K r lam))), dist p z < 4 * Rz / 3) ∧
      (d ≤ Rz ∧ Rz ≤ s ∧ Elig z) := by
  have hz' : z = gridRound g (vertexPoint ε η (X (firstShellHit ε η X (twoSidedShell K r lam)))) := by
    rw [hz, shellCentreAt_of_hit hit]
  obtain ⟨n, hn⟩ := hit
  have hC := firstShellHit_mem hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := shell_hit_choose_center_direct R Elig Reg hKne hs0 hKb hr hε X
    (firstShellHit ε η X (twoSidedShell K r lam)) hdiam hC hlam hg hd hh hR hEligReg hReg hcut1 hcut2 z hz'
  have hRz' : Rz = R z := by rw [hRz, shellRadiusAt_of_elig h5.2.2]
  rw [hRz']
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Step 6 needs the total centre to be a measurable function of the path: for random variables `X n : Ω → ℤ`,
`ω ↦ shellCentreAt g ε η S (X · ω)` is measurable. The first hitting index is measurable by `measurable_find`
(modified predicate, so that the total `firstShellHit = 0` off the hitting event is recovered). -/
theorem measurable_shellCentreAt {Ω : Type*} [MeasurableSpace Ω] (g ε : ℝ) (η : ℝ → ℂ) (S : Set ℂ)
    (X : ℕ → Ω → ℤ) (hX : ∀ n, Measurable (X n)) :
    Measurable fun ω => shellCentreAt g ε η S (fun n => X n ω) := by
  classical
  have hA : ∀ n, MeasurableSet {ω | (cell ε η (X n ω) ∩ S).Nonempty} := fun n =>
    (hX n) (MeasurableSpace.measurableSet_top (s := {k : ℤ | (cell ε η k ∩ S).Nonempty}))
  have hE : MeasurableSet {ω | ∃ n, (cell ε η (X n ω) ∩ S).Nonempty} := by
    have hEq : {ω | ∃ n, (cell ε η (X n ω) ∩ S).Nonempty} =
        ⋃ n, {ω | (cell ε η (X n ω) ∩ S).Nonempty} := by
      ext ω
      simp
    rw [hEq]
    exact MeasurableSet.iUnion hA
  have hex : ∀ ω, ∃ N, ((cell ε η (X N ω) ∩ S).Nonempty ∨ ¬ ∃ n, (cell ε η (X n ω) ∩ S).Nonempty) := by
    intro ω
    by_cases h : ∃ n, (cell ε η (X n ω) ∩ S).Nonempty
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr h⟩
  have hpm : ∀ N, MeasurableSet {ω | (cell ε η (X N ω) ∩ S).Nonempty ∨
      ¬ ∃ n, (cell ε η (X n ω) ∩ S).Nonempty} := fun N => (hA N).union hE.compl
  have hfind := measurable_find (p := fun ω N => (cell ε η (X N ω) ∩ S).Nonempty ∨
      ¬ ∃ n, (cell ε η (X n ω) ∩ S).Nonempty) hex hpm
  have hI : Measurable fun ω => firstShellHit ε η (fun n => X n ω) S := by
    have heq : (fun ω => firstShellHit ε η (fun n => X n ω) S) = fun ω => Nat.find (hex ω) := by
      funext ω
      by_cases h : ∃ n, (cell ε η (X n ω) ∩ S).Nonempty
      · have hne : {m : ℕ | (cell ε η (X m ω) ∩ S).Nonempty}.Nonempty := h
        show sInf {m : ℕ | (cell ε η (X m ω) ∩ S).Nonempty} = Nat.find (hex ω)
        rw [Nat.sInf_def hne]
        apply le_antisymm
        · exact Nat.find_min' hne (((Nat.find_spec (hex ω)).resolve_right (fun hn => hn h)))
        · exact Nat.find_min' (hex ω) (Or.inl (Nat.find_spec hne))
      · have hem : {m : ℕ | (cell ε η (X m ω) ∩ S).Nonempty} = ∅ :=
          Set.eq_empty_of_forall_notMem fun m hm => h ⟨m, hm⟩
        show sInf {m : ℕ | (cell ε η (X m ω) ∩ S).Nonempty} = Nat.find (hex ω)
        rw [hem, Nat.sInf_empty]
        exact ((Nat.find_eq_zero (hex ω)).mpr (Or.inr h)).symm
    rw [heq]
    exact hfind
  have hG : Measurable fun p : Ω × ℕ => X p.2 p.1 :=
    measurable_from_prod_countable_left (f := fun p : Ω × ℕ => X p.2 p.1) fun n => hX n
  have hF : Measurable fun ω => X (firstShellHit ε η (fun n => X n ω) S) ω :=
    hG.comp (measurable_id.prodMk hI)
  have hcentre : Measurable fun ω =>
      gridRound g (vertexPoint ε η (X (firstShellHit ε η (fun n => X n ω) S) ω)) :=
    (measurable_from_top (f := fun k : ℤ => gridRound g (vertexPoint ε η k))).comp hF
  unfold shellCentreAt
  exact Measurable.ite hE hcentre measurable_const

/-- Step 6: the total good radius is measurable as soon as `R` is measurable and the eligible set is measurable
(both supplied by the good-radius construction of S2). -/
theorem measurable_shellRadiusAt {Ω : Type*} [MeasurableSpace Ω] {R : ℂ → ℝ} {Elig : ℂ → Prop} {d : ℝ}
    (hR : Measurable R) (hEl : MeasurableSet {z : ℂ | Elig z}) {Z : Ω → ℂ} (hZ : Measurable Z) :
    Measurable fun ω => shellRadiusAt R Elig d (Z ω) := by
  unfold shellRadiusAt
  exact Measurable.ite (hEl.preimage hZ) (hR.comp hZ) measurable_const

end MatedCRT.Lemma68Window
