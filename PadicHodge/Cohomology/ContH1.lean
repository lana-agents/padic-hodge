/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Continuous `H¹` via crossed homomorphisms

For a topological group `G` and a representation `ρ` of `G` on a topological `R`-module `M`
(no continuity of the action is assumed in the definitions), we define

* `ContH1.cocycles ρ`: continuous crossed homomorphisms `f : G → M`,
  `f (g h) = f g + ρ g (f h)`;
* `ContH1.coboundaries ρ`: those of the form `g ↦ ρ g m - m`;
* `ContH1.H1 ρ = cocycles ρ ⧸ coboundaries ρ`.

Mathlib's `continuousCohomology` has no crossed-homomorphism description of `H¹`; this is the
classical definition (e.g. [BC, Def. 2.2.5]).

For a normal subgroup `S` we construct restriction `H¹(G, M) → H¹(S, M)` and inflation
`H¹(G/S, M^S) → H¹(G, M)` and prove the **inflation–restriction exact sequence in degree one**
`0 → H¹(G/S, M^S) → H¹(G, M) → H¹(S, M)` (`inf_injective`, `res_comp_inf`,
`exists_inf_of_res_eq_zero`), the latter under the hypothesis that the orbit maps
`g ↦ ρ g m` are continuous (so that coboundaries are continuous).
-/

noncomputable section

open Topology

namespace PadicHodge.ContH1

variable {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

section Defs

variable (ρ : Representation R G M)

/-- Continuous crossed homomorphisms (`1`-cocycles). -/
def cocycles : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h)}
  add_mem' := fun {f f'} hf hf' =>
    ⟨hf.1.add hf'.1, fun g h => by
      simp only [Pi.add_apply, hf.2 g h, hf'.2 g h, map_add]; abel⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := fun c f hf =>
    ⟨hf.1.const_smul c, fun g h => by
      simp only [Pi.smul_apply, hf.2 g h, map_smul, smul_add]⟩

variable {ρ} in
theorem mem_cocycles {f : G → M} :
    f ∈ cocycles ρ ↔ Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h) := Iff.rfl

/-- Coboundaries `g ↦ ρ g m - m` (among continuous cocycles). -/
def coboundaries : Submodule R (cocycles ρ) where
  carrier := {f | ∃ m : M, ∀ g, (f : G → M) g = ρ g m - m}
  add_mem' := fun {f f'} ⟨m, hm⟩ ⟨m', hm'⟩ =>
    ⟨m + m', fun g => by simp only [Submodule.coe_add, Pi.add_apply, hm g, hm' g, map_add]; abel⟩
  zero_mem' := ⟨0, fun g => by simp⟩
  smul_mem' := fun c f ⟨m, hm⟩ =>
    ⟨c • m, fun g => by simp only [Submodule.coe_smul, Pi.smul_apply, hm g, map_smul, smul_sub]⟩

/-- Continuous `H¹(G, M)`. -/
abbrev H1 := cocycles ρ ⧸ coboundaries ρ

/-- The class of a cocycle. -/
abbrev mk : cocycles ρ →ₗ[R] H1 ρ := (coboundaries ρ).mkQ

variable {ρ} in
theorem mk_eq_zero_iff (f : cocycles ρ) :
    mk ρ f = 0 ↔ ∃ m : M, ∀ g, (f : G → M) g = ρ g m - m :=
  Submodule.Quotient.mk_eq_zero _

theorem cocycle_one {f : G → M} (hf : f ∈ cocycles ρ) : f 1 = 0 := by
  have h := hf.2 1 1
  rw [one_mul, map_one, Module.End.one_apply] at h
  simpa using h

end Defs

section Res

variable (ρ : Representation R G M) (S : Subgroup G)

/-- Restriction of cocycles to a subgroup. -/
def resCocycles : cocycles ρ →ₗ[R] cocycles (ρ.comp S.subtype) where
  toFun f := ⟨fun s => (f : G → M) s, f.2.1.comp continuous_subtype_val,
    fun s t => f.2.2 s t⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resCocycles_le :
    coboundaries ρ ≤ (coboundaries (ρ.comp S.subtype)).comap (resCocycles ρ S) := by
  rintro f ⟨m, hm⟩
  exact ⟨m, fun s => hm s⟩

/-- Restriction `H¹(G, M) → H¹(S, M)`. -/
def res : H1 ρ →ₗ[R] H1 (ρ.comp S.subtype) :=
  Submodule.mapQ _ _ (resCocycles ρ S) (resCocycles_le ρ S)

theorem res_mk (f : cocycles ρ) :
    res ρ S (mk ρ f) = mk (ρ.comp S.subtype) (resCocycles ρ S f) := rfl

end Res

section Inf

instance (p : Submodule R M) : ContinuousConstSMul R p :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

variable (ρ : Representation R G M) (S : Subgroup G) [S.Normal]

/-- Inflation of cocycles from `G ⧸ S` with values in `M^S`. -/
def infCocycles : cocycles (ρ.quotientToInvariants S) →ₗ[R] cocycles ρ where
  toFun f := ⟨fun g => ((f : G ⧸ S → Representation.invariants (ρ.comp S.subtype)) (g : G ⧸ S) : M),
    continuous_subtype_val.comp (f.2.1.comp continuous_quotient_mk'),
    fun g h => by
      have := f.2.2 (g : G ⧸ S) (h : G ⧸ S)
      rw [← QuotientGroup.mk_mul] at this
      exact congrArg Subtype.val this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem infCocycles_le :
    coboundaries (ρ.quotientToInvariants S) ≤ (coboundaries ρ).comap (infCocycles ρ S) := by
  rintro f ⟨m, hm⟩
  refine ⟨(m : M), fun g => ?_⟩
  change (((f : G ⧸ S → Representation.invariants (ρ.comp S.subtype)) (g : G ⧸ S)) : M) = _
  rw [hm (g : G ⧸ S)]
  rfl

/-- Inflation `H¹(G ⧸ S, M^S) → H¹(G, M)`. -/
def inf : H1 (ρ.quotientToInvariants S) →ₗ[R] H1 ρ :=
  Submodule.mapQ _ _ (infCocycles ρ S) (infCocycles_le ρ S)

theorem inf_mk (f : cocycles (ρ.quotientToInvariants S)) :
    inf ρ S (mk (ρ.quotientToInvariants S) f) = mk ρ (infCocycles ρ S f) := rfl

/-- `res ∘ inf = 0` (already on cocycles). -/
theorem res_comp_inf : res ρ S ∘ₗ inf ρ S = 0 := by
  ext f
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
  change res ρ S (inf ρ S (mk (ρ.quotientToInvariants S) f)) = 0
  rw [inf_mk, res_mk, mk_eq_zero_iff]
  refine ⟨0, fun s => ?_⟩
  simp only [map_zero, sub_zero]
  change (((f : G ⧸ S → Representation.invariants (ρ.comp S.subtype)) ((s : G) : G ⧸ S)) : M) = 0
  rw [(QuotientGroup.eq_one_iff (s : G)).mpr s.2, cocycle_one _ f.2]
  rfl

/-- Inflation is injective. -/
theorem inf_injective : Function.Injective (inf ρ S) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker] at hx
  change inf ρ S (mk (ρ.quotientToInvariants S) f) = 0 at hx
  rw [inf_mk, mk_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  -- `m` is `S`-invariant since the inflated cocycle vanishes on `S`
  have hmS : m ∈ Representation.invariants (ρ.comp S.subtype) := by
    intro s
    have h := hm (s : G)
    change (((f : G ⧸ S → Representation.invariants (ρ.comp S.subtype))
      ((s : G) : G ⧸ S)) : M) = _ at h
    rw [(QuotientGroup.eq_one_iff (s : G)).mpr s.2, cocycle_one _ f.2] at h
    exact (sub_eq_zero.mp h.symm)
  rw [Submodule.mem_bot]
  change mk (ρ.quotientToInvariants S) f = 0
  rw [mk_eq_zero_iff]
  refine ⟨⟨m, hmS⟩, fun g => ?_⟩
  induction g using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    exact hm g

/-- **Inflation–restriction** in degree one: a class whose restriction to `S` vanishes is
inflated from `G ⧸ S`, provided the orbit maps `g ↦ ρ g m` are continuous. -/
theorem exists_inf_of_res_eq_zero (hρ : ∀ m : M, Continuous fun g : G => ρ g m) (x : H1 ρ)
    (hx : res ρ S x = 0) : ∃ y, inf ρ S y = x := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change res ρ S (mk ρ f) = 0 at hx
  rw [res_mk, mk_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  -- `f' = f - dm` vanishes on `S`
  set f' : G → M := fun g => (f : G → M) g - (ρ g m - m) with hf'
  have hf'c : f' ∈ cocycles ρ := by
    refine ⟨f.2.1.sub ((hρ m).sub continuous_const), fun g h => ?_⟩
    simp only [hf', f.2.2 g h, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hS : ∀ s : S, f' s = 0 := fun s => by
    have h := hm s
    change (f : G → M) s = _ at h
    simp only [hf']; rw [h]; simp
  -- `f'` is constant on cosets of `S`
  have hcoset : ∀ g (s : S), f' (g * s) = f' g := by
    intro g s
    rw [hf'c.2, hS s, map_zero, add_zero]
  -- `f'` takes values in `M^S`
  have hinv : ∀ g, f' g ∈ Representation.invariants (ρ.comp S.subtype) := by
    intro g s
    change ρ s (f' g) = f' g
    have h1 := hf'c.2 (s : G) g
    rw [hS s, zero_add] at h1
    rw [← h1]
    have h2 : (s : G) * g = g * (g⁻¹ * s * g) := by group
    rw [h2]
    exact hcoset g ⟨g⁻¹ * s * g, Subgroup.Normal.conj_mem' ‹S.Normal› s s.2 g⟩
  -- descend to `G ⧸ S`
  set F : G ⧸ S → Representation.invariants (ρ.comp S.subtype) :=
    Quotient.lift (fun g => (⟨f' g, hinv g⟩ : Representation.invariants (ρ.comp S.subtype)))
      (fun a b hab => by
        have hab' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
        apply Subtype.ext
        change f' a = f' b
        have := hcoset a ⟨a⁻¹ * b, hab'⟩
        simp only [mul_inv_cancel_left] at this
        exact this.symm) with hF
  have hFc : F ∈ cocycles (ρ.quotientToInvariants S) := by
    refine ⟨?_, fun a b => ?_⟩
    · refine Continuous.quotient_lift ?_ _
      exact (hf'c.1).subtype_mk _
    · induction a using QuotientGroup.induction_on with
      | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        apply Subtype.ext
        rw [← QuotientGroup.mk_mul]
        exact hf'c.2 a b
  refine ⟨mk (ρ.quotientToInvariants S) ⟨F, hFc⟩, ?_⟩
  rw [inf_mk]
  refine (Submodule.Quotient.eq _).mpr ⟨-m, fun g => ?_⟩
  change f' g - (f : G → M) g = ρ g (-m) - -m
  simp only [hf', map_neg]
  abel

end Inf

section Finite

variable {R G M : Type*} [Field R] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] (ρ : Representation R G M)

/-- A cocycle vanishing on a subgroup `S` of finite index is a coboundary, provided `[G : S]` is
invertible in `R` (averaging over `G ⧸ S`). -/
theorem mk_eq_zero_of_vanish (S : Subgroup G) [S.FiniteIndex] (hS : (S.index : R) ≠ 0)
    (f : cocycles ρ) (hf : ∀ s ∈ S, (f : G → M) s = 0) : mk ρ f = 0 := by
  classical
  letI : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
  -- `f` is constant on left cosets
  have hconst : ∀ g s, s ∈ S → (f : G → M) (g * s) = (f : G → M) g := by
    intro g s hs
    rw [f.2.2 g s, hf s hs, map_zero, add_zero]
  set Φ : G ⧸ S → M := Quotient.lift (fun g => (f : G → M) g) (fun a b hab => by
    have hab' : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
    have := hconst a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm) with hΦ
  have hΦmk : ∀ g : G, Φ (g : G ⧸ S) = (f : G → M) g := fun g => rfl
  set T := ∑ c, Φ c with hT
  have hN : (Fintype.card (G ⧸ S) : R) = (S.index : R) := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have key : ∀ g : G, (Fintype.card (G ⧸ S) : R) • (f : G → M) g = T - ρ g T := by
    intro g
    have h1 : ∑ c, Φ (g • c) = T := Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun c => rfl)
    have h2 : ∀ c, Φ (g • c) = (f : G → M) g + ρ g (Φ c) := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H a => rw [MulAction.Quotient.smul_mk, hΦmk, hΦmk, smul_eq_mul, f.2.2 g a]
    simp only [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum] at h1
    rw [← hT] at h1
    rw [← Nat.cast_smul_eq_nsmul R] at h1
    exact eq_sub_of_add_eq h1
  rw [mk_eq_zero_iff]
  refine ⟨-((S.index : R)⁻¹ • T), fun g => ?_⟩
  have := key g
  rw [hN] at this
  rw [map_neg, map_smul, neg_sub_neg, ← smul_sub, ← this, smul_smul,
    inv_mul_cancel₀ hS, one_smul]

end Finite

end PadicHodge.ContH1
