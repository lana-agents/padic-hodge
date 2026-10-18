/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Torsion

/-!
# The Galois action on `F(m_{ℂ_p})`

Let `F` be a formal group law over `R` (setting of `FormalGroup/Points.lean`) whose coefficients
are fixed by `Gal(ℚ̄_p/ℚ_p)` (`GalFixed`, e.g. `R → ℤ_p → O_{ℂ_p}`; `galFixed_of_factors`). Then
`Gal(ℚ̄_p/ℚ_p)` acts on `F(m_{ℂ_p})` coordinatewise (`galPt`) by group automorphisms
(`galPt_add`; evaluation of power series commutes with continuous automorphisms, `ev_autCp`),
the action preserves the torsion subgroups, and the logarithm is **Galois-equivariant**
(`logF_galPt`), as used in [Hong, Prop. 3.4.9].
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

variable (p R) in
/-- The coefficients `R → O_{ℂ_p}` are fixed by `Gal(ℚ̄_p/ℚ_p)`. -/
def GalFixed : Prop :=
  ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (r : R),
    autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r

omit [UniformSpace R] [DiscreteUniformity R] in
/-- Coefficients coming from `ℚ_p` are Galois-fixed. -/
theorem galFixed_of_factors (h : ∀ r : R, ∃ q : ℚ_[p],
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] q) : GalFixed p R :=
  fun σ r => by
    obtain ⟨q, hq⟩ := h r
    rw [hq, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p],
      ← PadicComplex.coe_eq, autCp_coe, σ.commutes]

/-- `σ` on `O_{ℂ_p}`. -/
def autOC (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : OC p) : OC p :=
  ⟨autCp σ x, by rw [mem_OC, norm_autCp]; exact x.2⟩

@[simp] theorem autOC_coe (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : OC p) :
    ((autOC σ x : OC p) : ℂ_[p]) = autCp σ x := rfl

variable {F}

/-- **Evaluation commutes with the Galois action.** -/
theorem ev_autCp (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {σ' : Type*}
    [Finite σ'] (f : MvPowerSeries σ' R) {a : σ' → OC p} (ha : ∀ s, ‖((a s : OC p) : ℂ_[p])‖ < 1) :
    autCp σ ((ev p f a : OC p) : ℂ_[p]) = ev p f (fun s => autOC σ (a s)) := by
  have ha' : ∀ s, ‖((autOC σ (a s) : OC p) : ℂ_[p])‖ < 1 := fun s => by
    rw [autOC_coe, norm_autCp]; exact ha s
  have h1 := ((hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one ha) f).map
    (OC p).subtype.toAddMonoidHom continuous_subtype_val).map (autCp σ).toAddMonoidHom
    (continuous_autCp σ)
  have h2 := (hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one ha') f).map
    (OC p).subtype.toAddMonoidHom continuous_subtype_val
  refine h1.unique (h2.congr_fun fun m => ?_)
  simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    Subring.coe_subtype, Subring.coe_mul, map_mul, coe_finsuppProd_OC, map_prod, map_pow,
    autOC_coe]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hR σ]

/-- **The Galois action on `F(m_{ℂ_p})`.** -/
def galPt (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : F.Pt p) :
    F.Pt p :=
  ⟨fun j => autOC σ (x.1 j), fun j => by rw [autOC_coe, norm_autCp]; exact x.2 j⟩

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
@[simp] theorem galPt_val (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : F.Pt p) (j : Fin d) :
    (((galPt σ x).1 j : OC p) : ℂ_[p]) = autCp σ (x.1 j) := rfl

theorem galPt_add (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x y : F.Pt p) : galPt σ (x + y) = galPt σ x + galPt σ y := by
  refine F.pt_ext fun i => Subtype.ext ?_
  rw [galPt_val, add_val, add_val, ev_autCp hR σ _ (norm_pairPt_lt x.2 y.2)]
  congr 2
  funext v
  unfold pairPt
  split_ifs <;> rfl

theorem galPt_nsmul (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (n : ℕ) (x : F.Pt p) : galPt σ (n • x) = n • galPt σ x := by
  induction n with
  | zero =>
    refine F.pt_ext fun i => Subtype.ext ?_
    rw [zero_nsmul, zero_nsmul, galPt_val, zero_val, ZeroMemClass.coe_zero, map_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, galPt_add hR, ih]

/-- The Galois action as a group automorphism of `F(m_{ℂ_p})`. -/
def galHom (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    F.Pt p →+ F.Pt p :=
  AddMonoidHom.mk' (galPt σ) (galPt_add hR σ)

theorem galPt_mem_torsionBy (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    {v : ℕ} {x : F.Pt p} (hx : x ∈ F.torsionBy v) : galPt σ x ∈ F.torsionBy v := by
  rw [mem_torsionBy] at *
  rw [← galPt_nsmul hR, hx]
  refine F.pt_ext fun i => Subtype.ext ?_
  rw [galPt_val, zero_val, ZeroMemClass.coe_zero, map_zero]

/-- **The logarithm is Galois-equivariant.** -/
theorem logF_galPt (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : F.Pt p) (i : Fin d) : F.logF (galPt σ x) i = autCp σ (F.logF x i) := by
  have hseq : ∀ n, F.logSeq (galPt σ x) i n = autCp σ (F.logSeq x i n) := fun n => by
    rw [logSeq, logSeq, ← galPt_nsmul hR, galPt_val, map_div₀, map_pow, map_natCast]
  have h := ((continuous_autCp σ).tendsto _).comp (F.tendsto_logSeq x i)
  refine tendsto_nhds_unique (F.tendsto_logSeq (galPt σ x) i) ?_
  refine h.congr fun n => ?_
  rw [Function.comp_apply, hseq]

end FGL

end PadicHodge
