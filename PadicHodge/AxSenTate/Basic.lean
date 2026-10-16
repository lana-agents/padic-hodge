/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AxSenTate.Ax
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.KrullTopology

/-!
# The Ax–Sen–Tate theorem

For an intermediate field `L` of `ℚ̄_p / ℚ_p` the invariants of `G_L = Gal(ℚ̄_p/L)` in `ℂ_[p]`
are the closure of `L` ([BC, Prop. 2.1.2]); for `L / ℚ_p` finite they are `L` itself.

## Main results

* `PadicHodge.galCp_eq_self_iff_mem_closure`: `x ∈ ℂ_[p]` is `G_L`-invariant iff
  `x ∈ closure L` (**Ax–Sen–Tate**).
* `PadicHodge.galCp_eq_self_iff_mem`: for `L / ℚ_p` finite, `ℂ_[p]^{G_L} = L`.
* `PadicHodge.cpRep`: `ℂ_[p]` as a continuous `ℚ_[p]`-linear representation of `G_L`.
* `PadicHodge.H0CpIso`: `H⁰_cont(G_L, ℂ_[p]) ≅ L` (as topological `ℚ_[p]`-modules, `L` embedded in
  `ℂ_[p]`) for `L / ℚ_p` finite, via Mathlib's `continuousCohomology`.
-/

noncomputable section

open UniformSpace CategoryTheory

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The image of `L` in `ℂ_[p]`, as a `ℚ_[p]`-subspace. -/
def cpSubmodule : Submodule ℚ_[p] ℂ_[p] :=
  (Subalgebra.toSubmodule L.toSubalgebra).map
    (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).toLinearMap

variable {L}

theorem mem_cpSubmodule {x : ℂ_[p]} :
    x ∈ cpSubmodule L ↔ ∃ a ∈ L, ((a : PadicAlgCl p) : ℂ_[p]) = x := by
  simp only [cpSubmodule, Submodule.mem_map, Subalgebra.mem_toSubmodule,
    IntermediateField.mem_toSubalgebra]
  rfl

theorem coe_mem_cpSubmodule {a : PadicAlgCl p} (ha : a ∈ L) :
    ((a : PadicAlgCl p) : ℂ_[p]) ∈ cpSubmodule L :=
  mem_cpSubmodule.mpr ⟨a, ha, rfl⟩

theorem coe_sub_cp (a b : PadicAlgCl p) :
    ((a - b : PadicAlgCl p) : ℂ_[p]) = (a : ℂ_[p]) - (b : ℂ_[p]) := by
  simp only [PadicComplex.coe_eq, map_sub]

theorem galCp_eq_self_of_mem_closure {x : ℂ_[p]}
    (hx : x ∈ closure (cpSubmodule L : Set ℂ_[p])) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    galCp L σ x = x := by
  have hcl : IsClosed {y : ℂ_[p] | galCp L σ y = y} :=
    isClosed_eq (continuous_galCp σ) continuous_id
  refine closure_minimal ?_ hcl hx
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_cpSubmodule.mp hy
  change galCp L σ (a : ℂ_[p]) = (a : ℂ_[p])
  rw [galCp_coe]
  congr 1
  exact σ.commutes ⟨a, ha⟩

theorem mem_closure_of_galCp_eq_self {x : ℂ_[p]}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, galCp L σ x = x) :
    x ∈ closure (cpSubmodule L : Set ℂ_[p]) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set C : ℝ := (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) with hCdef
  have hp1 := one_lt_p_real (p := p)
  have hC : 0 < C := Real.rpow_pos_of_pos (by linarith) _
  set δ := ε / (2 * (C + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨y, hy⟩ : ∃ y : PadicAlgCl p, dist x y < δ :=
    Completion.denseRange_coe.exists_dist_lt x hδ
  have hσ : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ y - y‖ ≤ δ := by
    intro σ
    have e : ((σ y - y : PadicAlgCl p) : ℂ_[p]) =
        galCp L σ ((y : ℂ_[p]) - x) + (x - (y : ℂ_[p])) := by
      rw [map_sub, hx σ, galCp_coe, coe_sub_cp]; ring
    rw [← PadicComplex.norm_extends, e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_galCp, norm_sub_rev, ← dist_eq_norm]; exact hy.le
    · rw [← dist_eq_norm]; exact hy.le
  obtain ⟨a, haL, ha⟩ := ax y hδ.le hσ
  refine ⟨((a : PadicAlgCl p) : ℂ_[p]), coe_mem_cpSubmodule haL, ?_⟩
  rw [dist_eq_norm]
  have e : x - ((a : PadicAlgCl p) : ℂ_[p]) =
      (x - (y : ℂ_[p])) + ((y - a : PadicAlgCl p) : ℂ_[p]) := by
    rw [coe_sub_cp]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
  rw [PadicComplex.norm_extends, ← dist_eq_norm]
  have h1 : dist x (y : ℂ_[p]) ≤ (C + 1) * δ := by nlinarith [hy, dist_nonneg (x := x) (y := y)]
  have h2 : ‖y - (a : PadicAlgCl p)‖ ≤ (C + 1) * δ := by nlinarith
  have h3 : (C + 1) * δ < ε := by
    rw [hδdef]; field_simp; nlinarith
  exact lt_of_le_of_lt (max_le h1 h2) h3

/-- **Ax–Sen–Tate** ([BC, Prop. 2.1.2]): the `G_L`-invariants of `ℂ_[p]` are the closure of
`L`. -/
theorem galCp_eq_self_iff_mem_closure (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, galCp L σ x = x) ↔
      x ∈ closure (cpSubmodule L : Set ℂ_[p]) :=
  ⟨mem_closure_of_galCp_eq_self, fun hx σ => galCp_eq_self_of_mem_closure hx σ⟩

instance [FiniteDimensional ℚ_[p] L] : FiniteDimensional ℚ_[p] (cpSubmodule L) := by
  unfold cpSubmodule
  have : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule L.toSubalgebra) :=
    inferInstanceAs (FiniteDimensional ℚ_[p] L)
  infer_instance

theorem isClosed_cpSubmodule [FiniteDimensional ℚ_[p] L] :
    IsClosed (cpSubmodule L : Set ℂ_[p]) :=
  Submodule.closed_of_finiteDimensional _

/-- **Ax–Sen–Tate for finite extensions**: for `L / ℚ_p` finite, `ℂ_[p]^{G_L} = L`. -/
theorem galCp_eq_self_iff_mem [FiniteDimensional ℚ_[p] L] (x : ℂ_[p]) :
    (∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, galCp L σ x = x) ↔ x ∈ cpSubmodule L := by
  rw [galCp_eq_self_iff_mem_closure, isClosed_cpSubmodule.closure_eq, SetLike.mem_coe]

/-! ### `ℂ_[p]` as a continuous representation and `H⁰` -/

theorem galCp_algebraMap (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (q : ℚ_[p]) :
    galCp L σ (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    galCp_coe]
  congr 1
  exact (σ.restrictScalars ℚ_[p]).commutes q

theorem galCp_smul (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (q : ℚ_[p]) (x : ℂ_[p]) :
    galCp L σ (q • x) = q • galCp L σ x := by
  rw [Algebra.smul_def, map_mul, galCp_algebraMap, ← Algebra.smul_def]

variable (L) in
/-- The continuous semilinear action of `G_L` on `ℂ_[p]`, as a `ℚ_[p]`-linear continuous
representation. -/
def cpRep : ContRepresentation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℂ_[p] where
  toMonoidHom :=
    { toFun := fun σ =>
        { toFun := galCp L σ
          map_add' := map_add _
          map_smul' := galCp_smul σ
          cont := continuous_galCp σ }
      map_one' := by ext x; simp
      map_mul' := fun σ τ => by ext x; simp }

@[simp] theorem cpRep_apply (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p]) :
    cpRep L σ x = galCp L σ x := rfl

/-- The invariants of `cpRep L` are the closure of `L` (Ax–Sen–Tate). -/
theorem cpRep_invariants_eq_closure :
    ((cpRep L).invariants : Set ℂ_[p]) = closure (cpSubmodule L : Set ℂ_[p]) := by
  ext x
  exact galCp_eq_self_iff_mem_closure x

theorem cpRep_invariants_eq [FiniteDimensional ℚ_[p] L] :
    (cpRep L).invariants = cpSubmodule L := by
  ext x
  exact galCp_eq_self_iff_mem x

variable (L) in
/-- **`H⁰(G_L, ℂ_p) = L`** for `L / ℚ_p` finite: the zeroth continuous cohomology of `ℂ_[p]` is
isomorphic (as a topological `ℚ_[p]`-module) to the image of `L` in `ℂ_[p]`. -/
def H0CpIso [FiniteDimensional ℚ_[p] L] :
    continuousCohomology 0 (TopRep.of (cpRep L)) ≅ TopModuleCat.of ℚ_[p] (cpSubmodule L) :=
  ContinuousCohomology.zeroIso (TopRep.of (cpRep L)) ≪≫
    TopModuleCat.ofIso (ContinuousLinearEquiv.ofEq _ _ (cpRep_invariants_eq (L := L)))

end PadicHodge
