import MatedCRT.Defs.Setting

/-!
# The radial Brownian motion of the quantum cone at a fixed time: Gaussian law and independence

In the mating-of-trees coupling the `γ`-quantum cone is `coneField X (coneRadial γ γ B B')`, with a whole-plane GFF
`X` independent of the pair of Brownian motions `(B, B')`. At a fixed time `t` the value `B t` has law
`gaussianReal 0 t` and is independent of the pair formed by the field `X` and the later increments
`u ↦ B (t + u) - B t` of the radial Brownian motion (the weak Markov property of Brownian motion together with the
independence of `X` and `B`). For `t = log (5/3)` this is the independent log-normal factor of the exit time of
Liouville Brownian motion from `B_{1/2}`.

The Brownian motion is only assumed a.e. measurable at each time, so the path `ω ↦ (u ↦ B u ω)` need not be a.e.
measurable. The proofs use a measurable modification `G'` of the pair `(X, B)` in the weak sense that every
preimage of a measurable set under the pair is a.e. equal to its preimage under `G'`
(`exists_measurable_preimage_ae_eq_prodMk_path`); independence statements transfer along this relation
(`indepFun_of_preimage_ae_eq`).

* `preimage_ae_eq_of_le_generateFrom`, `preimage_ae_eq_pi`, `preimage_ae_eq_prodMk`: the relation is checked on
  generators, on coordinates of a process, and on the factors of a pair.
* `indepFun_prodMk_of_indepFun_of_indepFun_prodMk`: if `E ⊥ C` and `Z ⊥ (E, C)` then `C ⊥ (E, Z)`.
* `indepFun_comp_fst_prodMk_snd`, `indepFun_comp_fst_prodMk_snd_of_preimage_ae_eq`: if `Y ⊥ Z` under `P`, then
  `Y ∘ fst ⊥ (Z ∘ fst, snd)` under `P.prod Q`.
* `indepFun_eval_prodMk_increments`: for a pre-Brownian motion `B` and a measurable `X ⊥ B`, the value `B t` is
  independent of `(X, (B (t + u) - B t)_u)`.
* `isMatingOfTreesCoupling_indepFun_eval_prodMk_increments`, `MatedCRTEnv.IsValid.exists_matingOfTrees_indepFun_radial`
  and `MatedCRTEnv.IsValid.exists_matingOfTrees_indepFun_radial_log`: the mating-of-trees coupling and a valid
  environment.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

section Modification

variable {Ω β γ δ ε : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- If the preimages of the generators of the σ-algebra of `β` under `f` and `g` are a.e. equal, so are the
preimages of every measurable set. -/
theorem preimage_ae_eq_of_le_generateFrom [mβ : MeasurableSpace β] {S : Set (Set β)}
    (hS : mβ ≤ MeasurableSpace.generateFrom S) {f g : Ω → β}
    (h : ∀ Γ ∈ S, f ⁻¹' Γ =ᵐ[P] g ⁻¹' Γ) {Γ : Set β} (hΓ : MeasurableSet Γ) :
    f ⁻¹' Γ =ᵐ[P] g ⁻¹' Γ := by
  have hg : MeasurableSpace.GenerateMeasurable S Γ := hS _ hΓ
  clear hΓ
  induction hg with
  | basic s hs => exact h s hs
  | empty => exact Filter.Eventually.of_forall fun _ => rfl
  | compl s _ ih => exact ih.compl
  | iUnion s _ ih =>
    rw [Set.preimage_iUnion, Set.preimage_iUnion]
    exact Filter.EventuallyEqSet.countable_iUnion ih

/-- Two processes with a.e. equal coordinates have a.e. equal preimages of every measurable set of paths (the
index set may be uncountable). -/
theorem preimage_ae_eq_pi {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {f g : Ω → ∀ i, α i} (h : ∀ i, (fun ω => f ω i) =ᵐ[P] fun ω => g ω i)
    {Γ : Set (∀ i, α i)} (hΓ : MeasurableSet Γ) : f ⁻¹' Γ =ᵐ[P] g ⁻¹' Γ := by
  refine preimage_ae_eq_of_le_generateFrom MeasurableSpace.pi_eq_generateFrom_projections.le ?_ hΓ
  rintro _ ⟨i, A, -, rfl⟩
  filter_upwards [h i] with ω hω
  exact congrArg (· ∈ A) hω

/-- The relation "a.e. equal preimages of measurable sets" passes to pairs. -/
theorem preimage_ae_eq_prodMk [MeasurableSpace β] [MeasurableSpace γ] {f f' : Ω → β} {g g' : Ω → γ}
    (hf : ∀ s, MeasurableSet s → f ⁻¹' s =ᵐ[P] f' ⁻¹' s)
    (hg : ∀ s, MeasurableSet s → g ⁻¹' s =ᵐ[P] g' ⁻¹' s)
    {Γ : Set (β × γ)} (hΓ : MeasurableSet Γ) :
    (fun ω => (f ω, g ω)) ⁻¹' Γ =ᵐ[P] (fun ω => (f' ω, g' ω)) ⁻¹' Γ := by
  refine preimage_ae_eq_of_le_generateFrom generateFrom_prod.ge ?_ hΓ
  rintro _ ⟨A, hA, D, hD, rfl⟩
  rw [Set.mk_preimage_prod, Set.mk_preimage_prod]
  exact (hf A hA).inter (hg D hD)

/-- Independence transfers along a.e. equality of the preimages of measurable sets. No measurability of the
random variables is needed. -/
theorem indepFun_of_preimage_ae_eq [MeasurableSpace β] [MeasurableSpace γ] {f f' : Ω → β} {g g' : Ω → γ}
    (hf : ∀ s, MeasurableSet s → f ⁻¹' s =ᵐ[P] f' ⁻¹' s)
    (hg : ∀ s, MeasurableSet s → g ⁻¹' s =ᵐ[P] g' ⁻¹' s) (h : IndepFun f g P) :
    IndepFun f' g' P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  rw [← measure_congr ((hf s hs).inter (hg t ht)), ← measure_congr (hf s hs),
    ← measure_congr (hg t ht)]
  exact h s t hs ht

/-- Independence of two measurable functions of `G` transfers to the same functions of `G'` when `G` and `G'`
have a.e. equal preimages of measurable sets. -/
theorem indepFun_comp_of_preimage_ae_eq [MeasurableSpace β] [MeasurableSpace δ] [MeasurableSpace ε]
    {G G' : Ω → β} (hG : ∀ Γ, MeasurableSet Γ → G ⁻¹' Γ =ᵐ[P] G' ⁻¹' Γ) {φ : β → δ} {ψ : β → ε}
    (hφ : Measurable φ) (hψ : Measurable ψ) (h : IndepFun (φ ∘ G) (ψ ∘ G) P) :
    IndepFun (φ ∘ G') (ψ ∘ G') P := by
  refine indepFun_of_preimage_ae_eq (f := φ ∘ G) (f' := φ ∘ G') (g := ψ ∘ G) (g' := ψ ∘ G') ?_ ?_ h
  · intro s hs
    exact hG _ (hφ hs)
  · intro s hs
    exact hG _ (hψ hs)

/-- A measurable random variable `X` together with a process `B` that is a.e. measurable at each time has a
measurable modification `G'`, in the sense that the preimages of measurable sets under `(X, B)` and `G'` are a.e.
equal. -/
theorem exists_measurable_preimage_ae_eq_prodMk_path [MeasurableSpace β] {ι : Type*} {X : Ω → β}
    {B : ι → Ω → ℝ} (hX : Measurable X) (hB : ∀ u, AEMeasurable (B u) P) :
    ∃ G' : Ω → β × (ι → ℝ), Measurable G' ∧
      ∀ Γ, MeasurableSet Γ → (fun ω => (X ω, fun u => B u ω)) ⁻¹' Γ =ᵐ[P] G' ⁻¹' Γ := by
  refine ⟨fun ω => (X ω, fun u => (hB u).mk (B u) ω),
    hX.prodMk (measurable_pi_iff.mpr fun u => (hB u).measurable_mk), fun Γ hΓ => ?_⟩
  refine preimage_ae_eq_prodMk (fun _ _ => Filter.EventuallyEq.rfl) (fun D hD => ?_) hΓ
  exact preimage_ae_eq_pi (fun u => (hB u).ae_eq_mk) hD

end Modification

section Combine

variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ]

/-- If `E` is independent of `C` and `Z` is independent of `(E, C)`, then `C` is independent of `(E, Z)`
(the same argument as `MatedCRTHarmonic.GMSAppA.indepFun_fst_prodMk_of` in Lattice-Probability). -/
theorem indepFun_prodMk_of_indepFun_of_indepFun_prodMk {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → α} {C : Ω → β} {Z : Ω → γ} (hE : Measurable E) (hC : Measurable C) (hZ : Measurable Z)
    (hEC : IndepFun E C P) (hZEC : IndepFun Z (fun ω => (E ω, C ω)) P) :
    IndepFun C (fun ω => (E ω, Z ω)) P := by
  have hZE : IndepFun Z E P := hZEC.comp measurable_id measurable_fst
  rw [indepFun_iff_map_prod_eq_prod_map_map hC.aemeasurable (hE.prodMk hZ).aemeasurable]
  have hCm : IsProbabilityMeasure (P.map C) :=
    (Measure.isProbabilityMeasure_map_iff hC.aemeasurable).2 ‹_›
  have hEZm : IsProbabilityMeasure (P.map fun ω => (E ω, Z ω)) :=
    (Measure.isProbabilityMeasure_map_iff (hE.prodMk hZ).aemeasurable).2 ‹_›
  symm
  let hD : (P.map fun ω => (E ω, Z ω)).FiniteSpanningSetsIn
      (Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set γ | MeasurableSet t}) :=
    { set := fun _ => univ
      set_mem := fun _ => ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, univ_prod_univ⟩
      finite := fun _ => measure_lt_top _ _
      spanning := iUnion_const univ }
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := Set.image2 (· ×ˢ ·) {s : Set α | MeasurableSet s} {t : Set γ | MeasurableSet t})
    MeasurableSpace.generateFrom_measurableSet generateFrom_prod
    MeasurableSpace.isPiSystem_measurableSet isPiSystem_prod
    (P.map C).toFiniteSpanningSetsIn hD ?_
  intro s hs t ht
  obtain ⟨A, hA, B, hB, rfl⟩ := ht
  have hmeas : MeasurableSet (s ×ˢ (A ×ˢ B)) := hs.prod (hA.prod hB)
  rw [Measure.map_apply (hC.prodMk (hE.prodMk hZ)) hmeas,
    Measure.map_apply hC hs, Measure.map_apply (hE.prodMk hZ) (hA.prod hB)]
  have e1 : (fun ω => (C ω, E ω, Z ω)) ⁻¹' (s ×ˢ (A ×ˢ B)) =
      Z ⁻¹' B ∩ (fun ω => (E ω, C ω)) ⁻¹' (A ×ˢ s) := by
    ext ω; simp [and_comm, and_assoc, and_left_comm]
  have e2 : (fun ω => (E ω, Z ω)) ⁻¹' (A ×ˢ B) = E ⁻¹' A ∩ Z ⁻¹' B := by ext ω; simp
  have e3 : (fun ω => (E ω, C ω)) ⁻¹' (A ×ˢ s) = E ⁻¹' A ∩ C ⁻¹' s := by ext ω; simp
  rw [e1, (indepFun_iff_measure_inter_preimage_eq_mul.1 hZEC) B (A ×ˢ s) hB (hA.prod hs), e3,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 hEC) A s hA hs, e2,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 hZE.symm) A B hA hB]
  ring

/-- Under a product of probability measures, the preimage of `A` under the first projection has mass `P A`
(any set `A`). -/
theorem measure_prod_preimage_fst {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set Ω) : (P.prod Q) (Prod.fst ⁻¹' A) = P A := by
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

/-- Under a product of probability measures, the preimage of `D` under the second projection has mass `Q D`
(any set `D`). -/
theorem measure_prod_preimage_snd {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (D : Set Ω') : (P.prod Q) (Prod.snd ⁻¹' D) = Q D := by
  rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]

/-- Independence under `P` of two random variables on the first factor persists under `P.prod Q`. -/
theorem indepFun_comp_fst_comp_fst {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Y : Ω → β} {Z : Ω → γ} (h : IndepFun Y Z P) :
    IndepFun (fun p : Ω × Ω' => Y p.1) (fun p => Z p.1) (P.prod Q) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  change (P.prod Q) (Prod.fst ⁻¹' (Y ⁻¹' s ∩ Z ⁻¹' t)) =
    (P.prod Q) (Prod.fst ⁻¹' (Y ⁻¹' s)) * (P.prod Q) (Prod.fst ⁻¹' (Z ⁻¹' t))
  rw [measure_prod_preimage_fst, measure_prod_preimage_fst, measure_prod_preimage_fst]
  exact h s t hs ht

/-- Under `P.prod Q`, a function of the first factor is independent of a function of the second factor. -/
theorem indepFun_comp_fst_comp_snd {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (f : Ω → β) (g : Ω' → γ) :
    IndepFun (fun p : Ω × Ω' => f p.1) (fun p => g p.2) (P.prod Q) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  change (P.prod Q) ((f ⁻¹' s) ×ˢ (g ⁻¹' t)) =
    (P.prod Q) (Prod.fst ⁻¹' (f ⁻¹' s)) * (P.prod Q) (Prod.snd ⁻¹' (g ⁻¹' t))
  rw [Measure.prod_prod, measure_prod_preimage_fst, measure_prod_preimage_snd]

/-- **Product step.** If `Y` is independent of `Z` under `P`, then under `P.prod Q` the variable `Y ∘ fst` is
independent of `(Z ∘ fst, snd)`. -/
theorem indepFun_comp_fst_prodMk_snd {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Y : Ω → β} {Z : Ω → γ} (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun Y Z P) :
    IndepFun (fun p : Ω × Ω' => Y p.1) (fun p => (Z p.1, p.2)) (P.prod Q) := by
  have hEC : IndepFun (fun p : Ω × Ω' => Z p.1) (fun p => Y p.1) (P.prod Q) :=
    indepFun_comp_fst_comp_fst h.symm
  have hZEC : IndepFun (fun p : Ω × Ω' => p.2) (fun p => (Z p.1, Y p.1)) (P.prod Q) :=
    (indepFun_comp_fst_comp_snd (Q := Q) (fun ω => (Z ω, Y ω)) id).symm
  exact indepFun_prodMk_of_indepFun_of_indepFun_prodMk (hZ.comp measurable_fst) (hY.comp measurable_fst)
    measurable_snd hEC hZEC

/-- **Product step**, composed with a measurable function `F` of `(Z ∘ fst, snd)`. -/
theorem indepFun_comp_fst_comp_prodMk_snd {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {Y : Ω → β} {Z : Ω → γ} (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun Y Z P) {F : γ × Ω' → α} (hF : Measurable F) :
    IndepFun (fun p : Ω × Ω' => Y p.1) (fun p => F (Z p.1, p.2)) (P.prod Q) :=
  (indepFun_comp_fst_prodMk_snd hY hZ h).comp measurable_id hF

/-- The relation "a.e. equal preimages of measurable sets" passes from `P` to the first factor of `P.prod Q`. -/
theorem preimage_comp_fst_ae_eq {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {f f' : Ω → β} (hf : ∀ s, MeasurableSet s → f ⁻¹' s =ᵐ[P] f' ⁻¹' s)
    (s : Set β) (hs : MeasurableSet s) :
    (fun p : Ω × Ω' => f p.1) ⁻¹' s =ᵐ[P.prod Q] (fun p : Ω × Ω' => f' p.1) ⁻¹' s := by
  have h := hf s hs
  rw [ae_eq_set] at h ⊢
  rw [show (fun p : Ω × Ω' => f p.1) ⁻¹' s \ (fun p : Ω × Ω' => f' p.1) ⁻¹' s =
      Prod.fst ⁻¹' (f ⁻¹' s \ f' ⁻¹' s) from rfl,
    show (fun p : Ω × Ω' => f' p.1) ⁻¹' s \ (fun p : Ω × Ω' => f p.1) ⁻¹' s =
      Prod.fst ⁻¹' (f' ⁻¹' s \ f ⁻¹' s) from rfl,
    measure_prod_preimage_fst, measure_prod_preimage_fst]
  exact h

/-- **Product step** for random variables that are not assumed measurable but have measurable modifications `Y'`,
`Z'` in the sense of a.e. equal preimages of measurable sets. -/
theorem indepFun_comp_fst_prodMk_snd_of_preimage_ae_eq {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {Y Y' : Ω → β} {Z Z' : Ω → γ}
    (hY' : Measurable Y') (hZ' : Measurable Z') (hYY : ∀ s, MeasurableSet s → Y ⁻¹' s =ᵐ[P] Y' ⁻¹' s)
    (hZZ : ∀ s, MeasurableSet s → Z ⁻¹' s =ᵐ[P] Z' ⁻¹' s) (h : IndepFun Y Z P) :
    IndepFun (fun p : Ω × Ω' => Y p.1) (fun p => (Z p.1, p.2)) (P.prod Q) := by
  have h' : IndepFun Y' Z' P := indepFun_of_preimage_ae_eq hYY hZZ h
  refine indepFun_of_preimage_ae_eq ?_ ?_ (indepFun_comp_fst_prodMk_snd (Q := Q) hY' hZ' h')
  · intro s hs
    exact (preimage_comp_fst_ae_eq hYY s hs).symm
  · intro Γ hΓ
    have hf : ∀ s, MeasurableSet s →
        (fun p : Ω × Ω' => Z p.1) ⁻¹' s =ᵐ[P.prod Q] (fun p : Ω × Ω' => Z' p.1) ⁻¹' s :=
      preimage_comp_fst_ae_eq hZZ
    exact (preimage_ae_eq_prodMk (g := fun p : Ω × Ω' => p.2) (g' := fun p : Ω × Ω' => p.2) hf
      (fun _ _ => Filter.EventuallyEq.rfl) hΓ).symm

end Combine

section Brownian

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}

/-- A measurable random variable `X`, a process `B` that is a.e. measurable at each time and a time `t`: the pair
formed by `X` and the increments `u ↦ B (t + u) - B t` has a measurable modification, in the sense of a.e. equal
preimages of measurable sets. -/
theorem exists_measurable_preimage_ae_eq_prodMk_increments {X : Ω → α} {B : ℝ≥0 → Ω → ℝ}
    (hX : Measurable X) (hB : ∀ u, AEMeasurable (B u) P) (t : ℝ≥0) :
    ∃ Z' : Ω → α × (ℝ≥0 → ℝ), Measurable Z' ∧ ∀ Γ, MeasurableSet Γ →
      (fun ω => (X ω, fun u : ℝ≥0 => B (t + u) ω - B t ω)) ⁻¹' Γ =ᵐ[P] Z' ⁻¹' Γ := by
  obtain ⟨G', hG'm, hGG⟩ := exists_measurable_preimage_ae_eq_prodMk_path hX hB
  let xs : α × (ℝ≥0 → ℝ) → α × (ℝ≥0 → ℝ) := fun p => (p.1, fun u : ℝ≥0 => p.2 (t + u) - p.2 t)
  have hxs : Measurable xs :=
    measurable_fst.prodMk (measurable_pi_iff.mpr fun u =>
      ((measurable_pi_apply (t + u)).comp measurable_snd).sub ((measurable_pi_apply t).comp measurable_snd))
  exact ⟨xs ∘ G', hxs.comp hG'm, fun Γ hΓ => hGG _ (hxs hΓ)⟩

/-- **Gaussian value independent of the field and of the later increments.** Let `B` be a pre-Brownian motion and
`X` a measurable random variable independent of the path of `B`. Then for every time `t` the value `B t` is
independent of the pair formed by `X` and the increments `u ↦ B (t + u) - B t`. -/
theorem indepFun_eval_prodMk_increments [IsProbabilityMeasure P] {X : Ω → α} {B : ℝ≥0 → Ω → ℝ}
    (hX : Measurable X) (hB : IsPreBrownianReal B P) (hXB : IndepFun X (fun ω u => B u ω) P) (t : ℝ≥0) :
    IndepFun (fun ω => B t ω) (fun ω => (X ω, fun u : ℝ≥0 => B (t + u) ω - B t ω)) P := by
  let G : Ω → α × (ℝ≥0 → ℝ) := fun ω => (X ω, fun u => B u ω)
  obtain ⟨G', hG'm, hGG⟩ : ∃ G' : Ω → α × (ℝ≥0 → ℝ), Measurable G' ∧
      ∀ Γ, MeasurableSet Γ → G ⁻¹' Γ =ᵐ[P] G' ⁻¹' Γ :=
    exists_measurable_preimage_ae_eq_prodMk_path hX hB.aemeasurable
  let ev : α × (ℝ≥0 → ℝ) → ℝ := fun p => p.2 t
  let sh : α × (ℝ≥0 → ℝ) → ℝ≥0 → ℝ := fun p u => p.2 (t + u) - p.2 t
  let xs : α × (ℝ≥0 → ℝ) → α × (ℝ≥0 → ℝ) := fun p => (p.1, sh p)
  let ψ : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) × ℝ := fun x => (fun u => x (t + u) - x t, x t)
  have hev : Measurable ev := (measurable_pi_apply t).comp measurable_snd
  have hsh : Measurable sh :=
    measurable_pi_iff.mpr fun u => ((measurable_pi_apply (t + u)).comp measurable_snd).sub hev
  have hxs : Measurable xs := measurable_fst.prodMk hsh
  have hψ : Measurable ψ :=
    (measurable_pi_iff.mpr fun u => (measurable_pi_apply (t + u)).sub (measurable_pi_apply t)).prodMk
      (measurable_pi_apply t)
  -- the field is independent of the path, for the modification
  have h1 : IndepFun (Prod.fst ∘ G') (Prod.snd ∘ G') P :=
    indepFun_comp_of_preimage_ae_eq hGG measurable_fst measurable_snd hXB
  -- weak Markov property at time `t`, for the modification
  have h2 : IndepFun (sh ∘ G) (ev ∘ G) P :=
    (hB.indepFun_shift t).comp measurable_id (measurable_pi_apply (⟨t, Set.mem_Iic.2 le_rfl⟩ : Set.Iic t))
  have h2' : IndepFun (sh ∘ G') (ev ∘ G') P := indepFun_comp_of_preimage_ae_eq hGG hsh hev h2
  have h3 : IndepFun (Prod.fst ∘ G') (fun ω => ((sh ∘ G') ω, (ev ∘ G') ω)) P :=
    h1.comp measurable_id hψ
  have h4 := indepFun_prodMk_of_indepFun_of_indepFun_prodMk (hsh.comp hG'm) (hev.comp hG'm)
    (measurable_fst.comp hG'm) h2' h3
  have h5 : IndepFun (ev ∘ G') (xs ∘ G') P := h4.comp measurable_id measurable_swap
  have h6 : IndepFun (ev ∘ G) (xs ∘ G) P :=
    indepFun_comp_of_preimage_ae_eq (fun Γ hΓ => (hGG Γ hΓ).symm) hev hxs h5
  exact h6

end Brownian

section Coupling

/-- **The mating-of-trees coupling.** For every time `t`, the radial Brownian motion `B` of the `γ`-quantum cone
`coneField X (coneRadial γ γ B B')` has `B t ~ gaussianReal 0 t`, and `B t` is independent of the whole-plane GFF
`X` together with the later increments `u ↦ B (t + u) - B t`. -/
theorem isMatingOfTreesCoupling_indepFun_eval_prodMk_increments {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (t : ℝ≥0) :
    IndepFun (fun ω => B t ω) (fun ω => (X ω, fun u : ℝ≥0 => B (t + u) ω - B t ω)) P ∧
      P.map (B t) = gaussianReal 0 t := by
  have := h.isProbabilityMeasure
  refine ⟨indepFun_eval_prodMk_increments h.gff.measurable h.bm_B.toIsPreBrownianReal ?_ t,
    (h.bm_B.toIsPreBrownianReal.hasLaw_eval t).map_eq⟩
  exact h.indep_cone.1.comp measurable_id measurable_fst

/-- **Valid environments.** The mating-of-trees coupling of a valid environment can be chosen so that, besides
the link of `matingOfTrees` with the field and the curve, for every time `t` the radial Brownian motion satisfies
`B t ~ gaussianReal 0 t` and `B t` is independent of the lateral field `X` together with the later increments
`u ↦ B (t + u) - B t`. -/
theorem MatedCRTEnv.IsValid.exists_matingOfTrees_indepFun_radial {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm ∧
      (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω ∧ ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      ∀ t : ℝ≥0,
        IndepFun (fun ω => B t ω) (fun ω => (X ω, fun u : ℝ≥0 => B (t + u) ω - B t ω)) S.P ∧
          S.P.map (B t) = gaussianReal 0 t := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae⟩ := hS.matingOfTrees
  exact ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae,
    fun t => isMatingOfTreesCoupling_indepFun_eval_prodMk_increments hC t⟩

/-- **Valid environments at `t₀ = log (5/3)`**, the time at which the radial part of the circle average reaches the
circle of radius `3/5`: `B t₀ ~ gaussianReal 0 t₀`, independent of the lateral field `X` and of the later increments
of `B`. -/
theorem MatedCRTEnv.IsValid.exists_matingOfTrees_indepFun_radial_log {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm ∧
      (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω ∧ ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      IndepFun (fun ω => B (Real.log (5 / 3)).toNNReal ω)
        (fun ω => (X ω, fun u : ℝ≥0 => B ((Real.log (5 / 3)).toNNReal + u) ω -
          B (Real.log (5 / 3)).toNNReal ω)) S.P ∧
      S.P.map (B (Real.log (5 / 3)).toNNReal) = gaussianReal 0 (Real.log (5 / 3)).toNNReal := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae, h⟩ :=
    hS.exists_matingOfTrees_indepFun_radial
  exact ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae, h _⟩

end Coupling

end MatedCRT
