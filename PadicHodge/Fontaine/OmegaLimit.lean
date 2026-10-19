/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.OmegaTower
import PadicHodge.Fontaine.KaehlerUnion

/-!
# `Ω = Ω_{O_{K̄}/O_L}` ([Fo, §2.5])

`OKbar p = O_{ℚ̄_p} = {x ∈ ℚ̄_p | |x| ≤ 1}`. For a finite extension `L/ℚ_p` inside `ℚ̄_p` let
`Ω_L = Ω_{O_{K̄}/O_L}`. Since `O_{K̄}` is the union of the `O_E` (`E ⊇ L` finite) and
`Ω_{O_{K̄}/O_L} = colim Ω_{O_E/O_L}` (`KaehlerUnion.exists_finset_map_eq_zero`), [Fo, Lemme 4]
(`OL.smul_map_smul_D_eq_zero_iff`) passes to the limit:

* **`OL.smul_mapOK_smul_D_eq_zero_iff`** ([Fo, §2.5]): for `L ⊆ E`, `O_E = O_L[b]`, `x ∈ O_E`,
  `y ∈ O_{K̄}`: `y · (x · db) = 0` in `Ω_L` iff `|y| |x| ≤ ‖𝔇_{E/L}‖`;
* `OL.mapOK_injective`: `Ω_{O_E/O_L} ↪ Ω_L`;
* `OL.exists_eq_smul_mapOK`: every element of `Ω_L` comes from some `Ω_{O_E/O_L}`.

## References

* [Fo] J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur
  les corps locaux*, Invent. Math. 65 (1982), §2.5.
-/

noncomputable section

open IsLocalRing Polynomial Module KaehlerDifferential

namespace PadicHodge

variable (p : ℕ) [hp : Fact p.Prime]

/-- `O_{ℚ̄_p}` as a subring of `ℚ̄_p`. -/
def OKbarSub : Subring (PadicAlgCl p) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

/-- **`O_{K̄} = O_{ℚ̄_p}`.** -/
abbrev OKbar : Type := OKbarSub p

variable {p}

theorem OKbar.norm_le_one (y : OKbar p) : ‖(y : PadicAlgCl p)‖ ≤ 1 := y.2

namespace OL

variable {L E E' : IntermediateField ℚ_[p] (PadicAlgCl p)}

instance algebraOKbar : Algebra (OL L) (OKbar p) :=
  ((algebraMap (OL L) (PadicAlgCl p)).codRestrict (OKbarSub p)
    fun x => norm_algebraMap_le_one x).toAlgebra

theorem coe_algebraMap_OKbar (x : OL L) :
    ((algebraMap (OL L) (OKbar p) x : OKbar p) : PadicAlgCl p) =
      algebraMap (OL L) (PadicAlgCl p) x := rfl

theorem algebraMap_OKbar_injective :
    Function.Injective (algebraMap (OL L) (OKbar p)) := fun x y h => by
  have h' := congrArg Subtype.val h
  rw [coe_algebraMap_OKbar, coe_algebraMap_OKbar, algebraMap_qbar_eq, algebraMap_qbar_eq] at h'
  exact toL_injective (Subtype.val_injective h')

theorem algebraMap_qbar_ofLE (h : L ≤ E) (x : OL L) :
    algebraMap (OL E) (PadicAlgCl p) (ofLE h x) = algebraMap (OL L) (PadicAlgCl p) x := by
  apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  change ((algebraMap (OL E) (PadicAlgCl p) (ofLE h x) : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap (OL L) (PadicAlgCl p) x : PadicAlgCl p) : ℂ_[p])
  rw [algebraMap_qbar_cp, algebraMap_qbar_cp]
  rfl

instance [hLE : Fact (L ≤ E)] : IsScalarTower (OL L) (OL E) (OKbar p) :=
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (algebraMap_qbar_ofLE hLE.out x).symm

theorem nrm_eq_norm_OKbar (x : OL L) :
    nrm x = ‖((algebraMap (OL L) (OKbar p) x : OKbar p) : PadicAlgCl p)‖ := nrm_eq_norm x

/-- An element of `O_{K̄}` lying in `E` comes from `O_E`. -/
theorem exists_algebraMap_eq {y : OKbar p} (hy : (y : PadicAlgCl p) ∈ E) :
    ∃ y' : OL E, algebraMap (OL E) (OKbar p) y' = y :=
  ⟨ofL ⟨_, hy⟩ y.2, Subtype.ext (algebraMap_ofL _ _)⟩

/-- A finite extension of `E` containing a given finite subset of `ℚ̄_p`. -/
def extend (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (s : Finset (PadicAlgCl p)) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  E ⊔ IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))

theorem le_extend (s : Finset (PadicAlgCl p)) : E ≤ extend E s := le_sup_left

theorem mem_extend {s : Finset (PadicAlgCl p)} {z : PadicAlgCl p} (hz : z ∈ s) :
    z ∈ extend E s :=
  le_sup_right (a := E) (IntermediateField.subset_adjoin ℚ_[p] _ (Finset.mem_coe.mpr hz))

instance [FiniteDimensional ℚ_[p] E] (s : Finset (PadicAlgCl p)) :
    FiniteDimensional ℚ_[p] (extend E s) := by
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  unfold extend
  infer_instance

theorem exists_extend [FiniteDimensional ℚ_[p] E] (s : Finset (PadicAlgCl p)) :
    ∃ E₁ : IntermediateField ℚ_[p] (PadicAlgCl p), E ≤ E₁ ∧ FiniteDimensional ℚ_[p] E₁ ∧
      ∀ z ∈ s, z ∈ E₁ :=
  ⟨extend E s, le_extend s, inferInstance, fun _ hz => mem_extend hz⟩

section Limit

variable [hLE : Fact (L ≤ E)] [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] E]

omit [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] E] in
/-- The key identity behind the limit: `y · (x · db)` computed in `O_{E'}` and in `O_{K̄}`. -/
theorem mapOK_smul_eq [Fact (E ≤ E')] [Fact (L ≤ E')] (b x : OL E) (y : OL E') :
    map (OL L) (OL L) (OL E') (OKbar p)
        (y • map (OL L) (OL L) (OL E) (OL E') (x • D (OL L) (OL E) b)) =
      algebraMap (OL E') (OKbar p) y •
        map (OL L) (OL L) (OL E) (OKbar p) (x • D (OL L) (OL E) b) := by
  rw [map_smul, KaehlerUnion.map_map_apply, algebraMap_smul]

/-- **[Fo, §2.5]**: for `O_E = O_L[b]`, `x ∈ O_E` and `y ∈ O_{K̄}`, `y · (x · db) = 0` in
`Ω_{O_{K̄}/O_L}` iff `|y| |x| ≤ ‖𝔇_{E/L}‖`. -/
theorem smul_mapOK_smul_D_eq_zero_iff {b : OL E} (hb : Algebra.adjoin (OL L) {b} = ⊤)
    (x : OL E) (y : OKbar p) :
    y • map (OL L) (OL L) (OL E) (OKbar p) (x • D (OL L) (OL E) b) = 0 ↔
      ‖(y : PadicAlgCl p)‖ * nrm x ≤ dnorm L E := by
  classical
  obtain ⟨E₁, hE₁, hFD₁, hy₁⟩ := exists_extend (E := E) {(y : PadicAlgCl p)}
  haveI : Fact (E ≤ E₁) := ⟨hE₁⟩
  haveI : Fact (L ≤ E₁) := ⟨hLE.out.trans hE₁⟩
  obtain ⟨y₁, rfl⟩ := exists_algebraMap_eq (E := E₁) (y := y)
    (hy₁ _ (Finset.mem_singleton_self _))
  rw [← mapOK_smul_eq, ← nrm_eq_norm_OKbar]
  constructor
  · intro h0
    obtain ⟨s, hs⟩ := KaehlerUnion.exists_finset_map_eq_zero (OL L) _ h0
    obtain ⟨E₂, hE₂, hFD₂, hs₂⟩ := exists_extend (E := E₁) (s.image Subtype.val)
    haveI : Fact (E₁ ≤ E₂) := ⟨hE₂⟩
    haveI : Fact (E ≤ E₂) := ⟨hE₁.trans hE₂⟩
    haveI : Fact (L ≤ E₂) := ⟨hLE.out.trans (hE₁.trans hE₂)⟩
    have h2 := hs (OL E₂) algebraMap_OKbar_injective (fun z hz => by
      obtain ⟨z', hz'⟩ := exists_algebraMap_eq (E := E₂) (y := z)
        (hs₂ _ (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hz)))
      exact ⟨z', hz'⟩)
    rw [map_smul, KaehlerUnion.map_map_apply, ← algebraMap_smul (OL E₂) y₁] at h2
    exact (smul_map_smul_D_eq_zero_iff (E' := E₂) hb x _).mp h2
  · intro h
    rw [(smul_map_smul_D_eq_zero_iff hb x y₁).mpr h, map_zero]

/-- **[Fo, §2.5]**: `Ω_{O_E/O_L} → Ω_{O_{K̄}/O_L}` is injective. -/
theorem mapOK_injective : Function.Injective (map (OL L) (OL L) (OL E) (OKbar p)) := by
  obtain ⟨b, hb⟩ := exists_adjoin_eq_top' L E
  refine (injective_iff_map_eq_zero _).mpr fun ω hω => ?_
  obtain ⟨x, rfl⟩ := exists_eq_smul_D hb ω
  have h := (smul_mapOK_smul_D_eq_zero_iff hb x 1).mp (by rw [one_smul]; exact hω)
  rw [OneMemClass.coe_one, norm_one, one_mul] at h
  exact (smul_D_eq_zero_iff hb x).mpr h

end Limit

section Lift

variable [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] L] in
/-- Every element of `Ω_{O_{K̄}/O_L}` comes from `Ω_{O_E/O_L}` for every finite `E ⊇ L`
containing a certain finite set. -/
theorem exists_finset_mapOK_eq (ω : Ω[OKbar p⁄OL L]) :
    ∃ s : Finset (PadicAlgCl p), ∀ (E : IntermediateField ℚ_[p] (PadicAlgCl p))
      [Fact (L ≤ E)] [FiniteDimensional ℚ_[p] E], (∀ z ∈ s, z ∈ E) →
      ∃ η : Ω[OL E⁄OL L], map (OL L) (OL L) (OL E) (OKbar p) η = ω := by
  classical
  have hω : ω ∈ Submodule.span (OKbar p) (Set.range (D (OL L) (OKbar p))) := by
    rw [span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨z, rfl⟩ := hg
    refine ⟨{(z : PadicAlgCl p)}, fun E _ _ hE => ?_⟩
    obtain ⟨z', hz'⟩ := exists_algebraMap_eq (E := E) (y := z) (hE _ (Finset.mem_singleton_self _))
    exact ⟨D (OL L) (OL E) z', by rw [map_D, hz']⟩
  | zero => exact ⟨∅, fun E _ _ _ => ⟨0, map_zero _⟩⟩
  | add ω₁ ω₂ _ _ h₁ h₂ =>
    obtain ⟨s₁, hs₁⟩ := h₁
    obtain ⟨s₂, hs₂⟩ := h₂
    refine ⟨s₁ ∪ s₂, fun E _ _ hE => ?_⟩
    obtain ⟨η₁, rfl⟩ := hs₁ E fun z hz => hE z (Finset.mem_union_left _ hz)
    obtain ⟨η₂, rfl⟩ := hs₂ E fun z hz => hE z (Finset.mem_union_right _ hz)
    exact ⟨η₁ + η₂, map_add _ _ _⟩
  | smul y ω₁ _ h₁ =>
    obtain ⟨s₁, hs₁⟩ := h₁
    refine ⟨insert (y : PadicAlgCl p) s₁, fun E _ _ hE => ?_⟩
    obtain ⟨η₁, rfl⟩ := hs₁ E fun z hz => hE z (Finset.mem_insert_of_mem hz)
    obtain ⟨y', rfl⟩ := exists_algebraMap_eq (E := E) (y := y) (hE _ (Finset.mem_insert_self _ _))
    exact ⟨y' • η₁, by rw [map_smul, algebraMap_smul]⟩

/-- **[Fo, Lemme 5]**: for `ω, ω' ∈ Ω_{O_{K̄}/O_L}`, if `Ann(ω) ⊆ Ann(ω')` then `ω' = c ω` for
some `c ∈ O_{K̄}`. -/
theorem exists_smul_eq_of_annihilator_le {ω ω' : Ω[OKbar p⁄OL L]}
    (h : ∀ y : OKbar p, y • ω = 0 → y • ω' = 0) : ∃ c : OKbar p, c • ω = ω' := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_mapOK_eq ω
  obtain ⟨s', hs'⟩ := exists_finset_mapOK_eq ω'
  obtain ⟨E, hLE, hFD, hE⟩ := exists_extend (E := L) (s ∪ s')
  haveI : Fact (L ≤ E) := ⟨hLE⟩
  obtain ⟨η, rfl⟩ := hs E fun z hz => hE z (Finset.mem_union_left _ hz)
  obtain ⟨η', rfl⟩ := hs' E fun z hz => hE z (Finset.mem_union_right _ hz)
  obtain ⟨b, hb⟩ := exists_adjoin_eq_top' L E
  obtain ⟨x, rfl⟩ := exists_eq_smul_D hb η
  obtain ⟨x', rfl⟩ := exists_eq_smul_D hb η'
  by_cases hx : nrm x ≤ dnorm L E
  · refine ⟨0, ?_⟩
    have h0 := (smul_mapOK_smul_D_eq_zero_iff hb x 1).mpr (by
      rw [OneMemClass.coe_one, norm_one, one_mul]; exact hx)
    rw [one_smul] at h0
    have h1 := h 1 (by rw [one_smul]; exact h0)
    rw [one_smul] at h1
    rw [zero_smul, h1]
  · push Not at hx
    have hx0 : x ≠ 0 := fun h0 => by
      rw [h0, nrm_zero] at hx; exact absurd hx (not_lt.mpr dnorm_pos.le)
    set X : PadicAlgCl p := algebraMap (OL E) (PadicAlgCl p) x with hX
    have hXn : ‖X‖ = nrm x := (nrm_eq_norm x).symm
    have hXpos : 0 < ‖X‖ := hXn ▸ nrm_pos hx0
    set Y : PadicAlgCl p := algebraMap (OL E) (PadicAlgCl p) (dgen L E) / X
    have hYn : ‖Y‖ = dnorm L E / nrm x := by
      rw [norm_div, hXn, ← nrm_eq_norm]; rfl
    have hY1 : ‖Y‖ ≤ 1 := by
      rw [hYn, div_le_one (nrm_pos hx0)]; exact hx.le
    have hy := h ⟨Y, hY1⟩ ((smul_mapOK_smul_D_eq_zero_iff hb x _).mpr (by
      change ‖Y‖ * nrm x ≤ _
      rw [hYn, div_mul_cancel₀ _ (nrm_pos hx0).ne']))
    rw [smul_mapOK_smul_D_eq_zero_iff hb x' _] at hy
    change ‖Y‖ * nrm x' ≤ _ at hy
    rw [hYn, div_mul_eq_mul_div, div_le_iff₀ (nrm_pos hx0),
      mul_le_mul_iff_of_pos_left dnorm_pos] at hy
    set X' : PadicAlgCl p := algebraMap (OL E) (PadicAlgCl p) x'
    have hc : ‖X' / X‖ ≤ 1 := by
      rw [norm_div, div_le_one hXpos, hXn, ← nrm_eq_norm]; exact hy
    refine ⟨⟨X' / X, hc⟩, ?_⟩
    rw [KaehlerUnion.map_smul_D, KaehlerUnion.map_smul_D, smul_smul]
    congr 1
    apply Subtype.ext
    change X' / X * X = X'
    rw [div_mul_cancel₀ _ (norm_pos_iff.mp hXpos)]

end Lift

end OL

end PadicHodge
