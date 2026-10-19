/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Kähler differentials of a union of subalgebras

If `ω ∈ Ω_{A/R}` maps to zero in `Ω_{B/R}` for an `R`-algebra map `A → B`, then this is
witnessed by finitely many elements of `B`: there is a finite set `s ⊆ B` such that `ω` already
maps to zero in `Ω_{A'/R}` for every intermediate algebra `A → A' ↪ B` whose image contains `s`
(**`KaehlerDifferential.exists_finset_map_eq_zero`**). This is the statement
"`Ω_{B/R} = colim Ω_{A'/R}`" used in [Fo, §2.5] for `B = O_{K̄}`, `A' = O_L`.

The proof uses the presentation `Ω_{B/R} = (B →₀ B) / kerTotal` and induction over the span
defining `kerTotal`.
-/

open Finsupp

namespace PadicHodge

namespace KaehlerUnion

universe u

/-- The map `(A →₀ A) → (A' →₀ A')` induced by `A → A'` (as in `KaehlerDifferential.kerTotal_map`).
-/
noncomputable abbrev fmap (A A' : Type*) [CommRing A] [CommRing A'] [Algebra A A'] :
    (A →₀ A) →ₗ[A] (A' →₀ A') :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap A A')).comp
    (Finsupp.lmapDomain A A (algebraMap A A'))

variable {A A' A'' : Type*} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']

theorem fmap_single (a c : A) :
    fmap A A' (single a c) = single (algebraMap A A' a) (algebraMap A A' c) := by
  simp [fmap]

theorem fmap_comp [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A''] (f : A →₀ A) :
    fmap A' A'' (fmap A A' f) = fmap A A'' f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single a c => rw [fmap_single, fmap_single, fmap_single, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

theorem fmap_injective (h : Function.Injective (algebraMap A A')) :
    Function.Injective (fmap A A') := by
  intro f g hfg
  have h1 : Function.Injective (Finsupp.lmapDomain A A (algebraMap A A')) :=
    Finsupp.mapDomain_injective h
  have h2 : Function.Injective
      (Finsupp.mapRange.linearMap (Algebra.linearMap A A') : (A' →₀ A) →ₗ[A] (A' →₀ A')) :=
    Finsupp.mapRange_injective _ (map_zero _) h
  exact h1 (h2 hfg)

theorem fmap_smul (a : A) (f : A →₀ A) : fmap A A' (a • f) = algebraMap A A' a • fmap A A' f := by
  rw [map_smul, algebraMap_smul]

variable (R : Type*) [CommRing R]

/-- **Finite witnesses for `kerTotal`.** Every element of `kerTotal R B` comes from
`kerTotal R A` for every intermediate `A ↪ B` containing a suitable finite set. -/
theorem exists_finset_of_mem_kerTotal {B : Type*} [CommRing B] [Algebra R B] {x : B →₀ B}
    (hx : x ∈ KaehlerDifferential.kerTotal R B) :
    ∃ s : Finset B, ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra A B]
      [IsScalarTower R A B], ↑s ⊆ Set.range (algebraMap A B) →
      ∃ y ∈ KaehlerDifferential.kerTotal R A, fmap A B y = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem g hg =>
    rcases hg with (⟨⟨x1, x2⟩, rfl⟩ | ⟨⟨x1, x2⟩, rfl⟩) | ⟨r, rfl⟩
    · refine ⟨{x1, x2}, fun A _ _ _ _ hs => ?_⟩
      obtain ⟨a2, rfl⟩ := hs (Finset.mem_coe.mpr (by simp : x2 ∈ ({x1, x2} : Finset B)))
      obtain ⟨a1, rfl⟩ := hs (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
      refine ⟨single a1 1 + single a2 1 - single (a1 + a2) 1,
        Submodule.subset_span (Or.inl (Or.inl ⟨(a1, a2), rfl⟩)), ?_⟩
      rw [map_sub, map_add, fmap_single, fmap_single, fmap_single, map_one, map_add]
    · refine ⟨{x1, x2}, fun A _ _ _ _ hs => ?_⟩
      obtain ⟨a2, rfl⟩ := hs (Finset.mem_coe.mpr (by simp : x2 ∈ ({x1, x2} : Finset B)))
      obtain ⟨a1, rfl⟩ := hs (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
      refine ⟨single a2 a1 + single a1 a2 - single (a1 * a2) 1,
        Submodule.subset_span (Or.inl (Or.inr ⟨(a1, a2), rfl⟩)), ?_⟩
      rw [map_sub, map_add, fmap_single, fmap_single, fmap_single, map_one, map_mul]
    · refine ⟨∅, fun A _ _ _ _ _ => ⟨single (algebraMap R A r) 1,
        Submodule.subset_span (Or.inr ⟨r, rfl⟩), ?_⟩⟩
      rw [fmap_single, map_one, ← IsScalarTower.algebraMap_apply]
  | zero => exact ⟨∅, fun A _ _ _ _ _ => ⟨0, zero_mem _, map_zero _⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun A _ _ _ _ hst => ?_⟩
    obtain ⟨y1, hy1, rfl⟩ := hs A (fun z hz => hst (by simp [Finset.mem_coe.mp hz]))
    obtain ⟨y2, hy2, rfl⟩ := ht A (fun z hz => hst (by simp [Finset.mem_coe.mp hz]))
    exact ⟨y1 + y2, add_mem hy1 hy2, map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨insert c s, fun A _ _ _ _ hst => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hs A (fun z hz => hst (by simp [Finset.mem_coe.mp hz]))
    obtain ⟨a, rfl⟩ := hst (Finset.mem_coe.mpr (Finset.mem_insert_self c s))
    exact ⟨a • y, Submodule.smul_mem _ a hy, fmap_smul a y⟩

omit [Algebra A A'] in
/-- **`Ω_{B/R} = colim Ω_{A'/R}`** (kernel form): if `ω ∈ Ω_{A/R}` vanishes in `Ω_{B/R}`, it
vanishes in `Ω_{A'/R}` for every `A → A' ↪ B` whose image contains a certain finite set. -/
theorem exists_finset_map_eq_zero {B : Type*} [CommRing B] [Algebra R B]
    [Algebra R A] [Algebra A B] [IsScalarTower R A B] (ω : Ω[A⁄R])
    (hω : KaehlerDifferential.map R R A B ω = 0) :
    ∃ s : Finset B, ∀ (A' : Type u) [CommRing A'] [Algebra R A'] [Algebra A A'] [Algebra A' B]
      [IsScalarTower R A A'] [IsScalarTower R A' B] [IsScalarTower A A' B],
      Function.Injective (algebraMap A' B) → ↑s ⊆ Set.range (algebraMap A' B) →
      KaehlerDifferential.map R R A A' ω = 0 := by
  have hker : ω ∈ LinearMap.ker (KaehlerDifferential.map R R A B) := hω
  rw [KaehlerDifferential.ker_map] at hker
  obtain ⟨f, hf, rfl⟩ := hker
  obtain ⟨s, hs⟩ := exists_finset_of_mem_kerTotal R hf
  refine ⟨s, fun A' _ _ _ _ _ _ _ hinj hsub => ?_⟩
  obtain ⟨y, hy, hyf⟩ := hs A' hsub
  have hyf' : y = fmap A A' f := fmap_injective hinj (by rw [hyf, fmap_comp])
  change Finsupp.linearCombination A (KaehlerDifferential.D R A) f ∈
    LinearMap.ker (KaehlerDifferential.map R R A A')
  rw [KaehlerDifferential.ker_map]
  exact ⟨f, show fmap A A' f ∈ _ from hyf' ▸ hy, rfl⟩

section MapMap

variable (R : Type*) {P Q T : Type*} [CommRing R] [CommRing P] [CommRing Q] [CommRing T]
  [Algebra R P] [Algebra R Q] [Algebra R T] [Algebra P Q] [Algebra Q T] [Algebra P T]
  [IsScalarTower R P Q] [IsScalarTower R Q T] [IsScalarTower R P T] [IsScalarTower P Q T]

/-- Functoriality of Kähler differentials over `R` in towers `P → Q → T`. -/
theorem map_map_apply (ω : Ω[P⁄R]) :
    KaehlerDifferential.map R R Q T (KaehlerDifferential.map R R P Q ω) =
      KaehlerDifferential.map R R P T ω := by
  have h := Derivation.liftKaehlerDifferential_unique
    ((KaehlerDifferential.map R R Q T).restrictScalars P ∘ₗ KaehlerDifferential.map R R P Q)
    (KaehlerDifferential.map R R P T) (by
      ext a
      simp [IsScalarTower.algebraMap_apply P Q T])
  exact LinearMap.congr_fun h ω

/-- `x · da ↦ x · da` under `Ω_{P/R} → Ω_{T/R}`. -/
theorem map_smul_D (x a : P) :
    KaehlerDifferential.map R R P T (x • KaehlerDifferential.D R P a) =
      algebraMap P T x • KaehlerDifferential.D R T (algebraMap P T a) := by
  rw [map_smul, KaehlerDifferential.map_D, algebraMap_smul]

end MapMap

end KaehlerUnion

end PadicHodge
