/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.KummerTate
import PadicHodge.FormalGroup.FullyFaithful

/-!
# The identification `T_p F ≅ T_p(F[p^∞])` is a group isomorphism

For a `p`-divisible formal group law `F` over `R` the layer point of a sum of `p^v`-torsion points
is the convolution product of the layer points (`PDivFGL.layerPt_add`): on `A_v` the
comultiplication is `t ↦ Φ(t ⊗ 1, 1 ⊗ t)` (`PDivFGL.comul_t`), and an algebra map from a finite
free `R`-algebra to `O_{ℂ_p}` commutes with the evaluation of power series at topologically
nilpotent elements (`PDivFGL.map_evF_eq_ev`, uniqueness of continuous evaluation,
`AdicEval.algHom_ext`). Hence

* `tpToPDiv : T_p F → T_p(F[p^∞])(O_{ℂ_p})` is additive (`tpToPDiv_add`), an additive
  isomorphism `tpToPDivEquiv` (bijective by `tpToPDiv_bijective`);
* over `O_{K'}`: `tpToQbar : T_p F → T_p(F[p^∞]_{K'})(ℚ̄_p)` is an additive, `G_{K'}`-equivariant
  isomorphism (`tpToQbarEquiv`, `tpToQbarEquiv_tpRep`), so a `G_{K'}`-equivariant homomorphism
  of Tate modules `τ ∈ GalTateHom` acts on Kummer coefficients (`tpOfGalTate`), and by Tate's
  theorem ([Hong, Cor. 3.5.5], `PDivGroup.Hom.mapTate_bijective_OL`) together with Serre–Tate
  (`exists_fglHom_tpToPDiv`) this action is `T_p(f)` for a homomorphism `f : F → F'` of formal
  group laws, which carries `κ_F(x)` to `κ_{F'}(f(x))` (`map_kummer`).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval WithConv TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace PDivFGL

section General

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (P : PDivFGL R d p)

attribute [local instance] isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

/-- **Algebra maps to `O_{ℂ_p}` commute with evaluation**: for `g : S → O_{ℂ_p}` (`S` finite free
over `R`) and a topologically nilpotent family `x` with `g(x)` in the open polydisc,
`g(f(x)) = f(g(x))`. -/
theorem map_evF_eq_ev {S : Type} [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] (g : S →ₐ[R] OC p) {σ : Type} [Finite σ] {x : σ → S}
    (hx : FGL.TNF 𝔪R x) (hgx : ∀ s, ‖((g (x s) : OC p) : ℂ_[p])‖ < 1)
    (f : MvPowerSeries σ R) :
    g (FGL.evF 𝔪R x f) = FGL.ev p f (fun s => g (x s)) := by
  haveI := isHausdorff_span (fun s => g (x s)) hgx
  let e : MvPowerSeries σ R →ₐ[R] OC p :=
    { eval₂Hom (FGL.continuous_algebraMap_OC (p := p) (R := R)) (hasEval_of_norm_lt_one hgx) with
      commutes' := fun r => by
        change eval₂Hom (FGL.continuous_algebraMap_OC (p := p) (R := R))
          (hasEval_of_norm_lt_one hgx) (algebraMap R _ r) = _
        rw [coe_eval₂Hom (FGL.continuous_algebraMap_OC (p := p) (R := R)),
          MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact eval₂_C (algebraMap R (OC p)) _ r }
  have he : ∀ f, e f = FGL.ev p f (fun s => g (x s)) := fun f => by
    change eval₂Hom (FGL.continuous_algebraMap_OC (p := p) (R := R))
      (hasEval_of_norm_lt_one hgx) f = _
    rw [coe_eval₂Hom]
    rfl
  have key : g.comp (evalT x hx) = e := by
    refine AdicEval.algHom_ext (Ideal.span (Set.range fun s => g (x s))) (fun s => ?_)
      fun s => ?_
    · rw [AlgHom.comp_apply, evalT_X]
      exact Ideal.subset_span ⟨s, rfl⟩
    · rw [AlgHom.comp_apply, evalT_X, he, FGL.ev_X]
  rw [FGL.evF_of hx, ← AlgHom.comp_apply, key, he]

/-- **The layer point of a sum is the convolution product of the layer points**:
`(x + y)_v = μ ∘ (x_v ⊗ y_v) ∘ Δ` on `A_v`. -/
theorem layerPt_add (v : ℕ) (x y : P.F.torsionBy (p := p) v) :
    P.F.layerPt v ⟨x.1 + y.1, add_mem x.2 y.2⟩ =
      (Algebra.TensorProduct.lmul' R).comp
        ((Algebra.TensorProduct.map (P.F.layerPt v x) (P.F.layerPt v y)).comp (P.comul v)) := by
  set g : P.A v ⊗[R] P.A v →ₐ[R] OC p :=
    (Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map (P.F.layerPt v x) (P.F.layerPt v y)) with hg
  have hpair : (fun s => g (FGL.pairS (P.tL v) (P.tR v) s)) = FGL.pairPt x.1.1 y.1.1 := by
    funext s
    unfold FGL.pairS FGL.pairPt
    split_ifs
    · simp [hg, tL, t, FGL.layerPt_X]
    · simp [hg, tR, t, FGL.layerPt_X]
  have hz : ∀ s, ‖((g (FGL.pairS (P.tL v) (P.tR v) s) : OC p) : ℂ_[p])‖ < 1 := fun s => by
    rw [show g (FGL.pairS (P.tL v) (P.tR v) s) = FGL.pairPt x.1.1 y.1.1 s from
      congrFun hpair s]
    exact FGL.norm_pairPt_lt x.1.2 y.1.2 s
  apply Ideal.Quotient.algHom_ext R
  haveI := isHausdorff_span (x.1 + y.1).1 (x.1 + y.1).2
  refine AdicEval.algHom_ext (Ideal.span (Set.range (x.1 + y.1).1)) (fun j => ?_) fun j => ?_
  · rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, FGL.layerPt_X]
    exact Ideal.subset_span ⟨j, rfl⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, FGL.layerPt_X]
    change _ = (g.comp (P.comul v)) (P.t v j)
    rw [AlgHom.comp_apply, comul_t, wΔ, FGL.addE,
      map_evF_eq_ev g (FGL.tnf_pairS (P.tnf_tL v) (P.tnf_tR v)) hz, hpair]
    rfl

theorem ptV_add (v : ℕ) (x y : P.F.torsionBy (p := p) v) :
    P.ptV v ⟨x.1 + y.1, add_mem x.2 y.2⟩ = P.ptV v x * P.ptV v y := by
  apply WithConv.ofConv_injective
  exact P.layerPt_add v x y

theorem tateToPDiv_add (x y : P.F.tate p) :
    P.tateToPDiv (x + y) = P.tateToPDiv x * P.tateToPDiv y := by
  refine Subtype.ext (funext fun v => ?_)
  exact P.ptV_add v ⟨x.1 v, _⟩ ⟨y.1 v, _⟩

theorem tpToPDiv_add (x y : Kummer.Tp (P.F.Pt p) p) :
    P.tpToPDiv (x + y) = P.tpToPDiv x * P.tpToPDiv y :=
  P.tateToPDiv_add (P.tpToTate x) (P.tpToTate y)

/-- `tpToPDiv` as an additive map `T_p F → T_p(F[p^∞])(O_{ℂ_p})`. -/
def tpToPDivHom : Kummer.Tp (P.F.Pt p) p →+ Additive (P.pdivGroup.TateModule (OC p)) where
  toFun x := Additive.ofMul (P.tpToPDiv x)
  map_zero' := by
    have h := P.tpToPDiv_add 0 0
    rw [add_zero] at h
    exact Additive.toMul.injective (by
      change P.tpToPDiv 0 = 1
      exact (left_eq_mul.mp h))
  map_add' x y := P.tpToPDiv_add x y

@[simp] theorem tpToPDivHom_apply (x : Kummer.Tp (P.F.Pt p) p) :
    Additive.toMul (P.tpToPDivHom x) = P.tpToPDiv x := rfl

/-- **`T_p F ≅ T_p(F[p^∞])(O_{ℂ_p})` as groups.** -/
def tpToPDivEquiv (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    Kummer.Tp (P.F.Pt p) p ≃+ Additive (P.pdivGroup.TateModule (OC p)) :=
  AddEquiv.ofBijective P.tpToPDivHom (P.tpToPDiv_bijective hR)

end General

section OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (P : PDivFGL (OL L) d p)

theorem tpToQbar_add (x y : Kummer.Tp (P.F.Pt p) p) :
    P.tpToQbar (x + y) = P.tpToQbar x * P.tpToQbar y := by
  simp only [tpToQbar, tpToPDiv_add, map_mul]

/-- `tpToQbar` as an additive map. -/
def tpToQbarHom :
    Kummer.Tp (P.F.Pt p) p →+ Additive ((P.pdivGroup.baseChange L).TateModule (PadicAlgCl p)) where
  toFun x := Additive.ofMul (P.tpToQbar x)
  map_zero' := by
    have h := P.tpToQbar_add 0 0
    rw [add_zero] at h
    exact Additive.toMul.injective (left_eq_mul.mp h)
  map_add' := P.tpToQbar_add

/-- **Kummer coefficients `≅ T_p(F[p^∞]_{K'})(ℚ̄_p)` as groups** (`G_{K'}`-equivariant by
`tpToQbarEquiv_tpRep`). -/
def tpToQbarEquiv :
    Kummer.Tp (P.F.Pt p) p ≃+ Additive ((P.pdivGroup.baseChange L).TateModule (PadicAlgCl p)) :=
  AddEquiv.ofBijective P.tpToQbarHom P.tpToQbar_bijective

@[simp] theorem tpToQbarEquiv_apply (x : Kummer.Tp (P.F.Pt p) p) :
    Additive.toMul (P.tpToQbarEquiv x) = P.tpToQbar x := rfl

theorem tpToQbarEquiv_tpRep (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    Additive.toMul (P.tpToQbarEquiv (Kummer.tpRep P.galRepOL p σ x)) =
      (P.pdivGroup.baseChange L).galTate (IntermediateField.fixingSubgroupEquiv L σ)
        (Additive.toMul (P.tpToQbarEquiv x)) :=
  P.tpToQbar_tpRep σ x

/-- **Naturality of `tpToQbar`**: for a homomorphism `φ : F → F'` of formal group laws,
`T_p(φ)` on Kummer coefficients is `T_p(φ[p^∞]_{K'})` on `T_p(·)(ℚ̄_p)`. -/
theorem tpToQbar_map {d' : ℕ} {P' : PDivFGL (OL L) d' p} (φ : FGL.Hom P.F P'.F)
    (x : Kummer.Tp (P.F.Pt p) p) :
    P'.tpToQbar (Kummer.map φ.ptHom x) =
      (PDivGroup.Hom.baseChange (S := L) φ.toPDiv).mapTate (PadicAlgCl p) (P.tpToQbar x) := by
  set e := MulEquiv.ofBijective _ (P.pdivGroup.tateComp_bijective (OL.incOK L)
    fun _ => OL.postComp_incOK_bijective _)
  set e' := MulEquiv.ofBijective _ (P'.pdivGroup.tateComp_bijective (OL.incOK L)
    fun _ => OL.postComp_incOK_bijective _)
  have hy : e'.symm (P'.tpToPDiv (Kummer.map φ.ptHom x)) =
      φ.toPDiv.mapTate (OKbar p) (e.symm (P.tpToPDiv x)) := by
    apply e'.injective
    rw [MulEquiv.apply_symm_apply, P.tpToPDiv_map φ x]
    conv_lhs => rw [← e.apply_symm_apply (P.tpToPDiv x)]
    rfl
  unfold tpToQbar
  apply (P'.pdivGroup.baseChangeTateEquiv (S := L) (PadicAlgCl p)).injective
  rw [MulEquiv.apply_symm_apply, PDivGroup.Hom.baseChange_mapTate, MulEquiv.apply_symm_apply]
  change P'.pdivGroup.tateComp (OL.incQ L) (e'.symm _) = _
  rw [hy]
  rfl

/-- **Kummer classes and Tate's theorem**: every `G_{K'}`-equivariant homomorphism
`τ : T_p(F[p^∞]_{K'}) → T_p(F'[p^∞]_{K'})` of Tate modules (`GalTateHom`) is, on Kummer
coefficients, `T_p(φ)` for a homomorphism `φ : F → F'` of formal group laws ([Hong, Cor. 3.5.5]
over `O_{K'}` and Serre–Tate), and `T_p(φ)_*` carries the Kummer class `κ_F(x)` to
`κ_{F'}(φ(x))`. -/
theorem exists_fglHom_of_galTate {d' : ℕ} {P' : PDivFGL (OL L) d' p}
    (τ : PDivGroup.GalTateHom P.pdivGroup P'.pdivGroup) :
    ∃ φ : FGL.Hom P.F P'.F,
      (∀ x, P'.tpToQbar (Kummer.map φ.ptHom x) = τ.1 (P.tpToQbar x)) ∧
      ∀ x : P.galRepOL.invariants,
        ContH1.map (Kummer.map φ.ptHom) (Kummer.continuous_map φ.ptHom)
            (Kummer.tpMap_equivariant φ.ptHom (φ.ptHom_galRep coeffFixed_OL))
            (P.kummerOL x) =
          P'.kummerOL ⟨φ.ptHom x, Kummer.map_mem_invariants φ.ptHom
            (φ.ptHom_galRep coeffFixed_OL) x.2⟩ := by
  obtain ⟨f, hf⟩ := (PDivGroup.Hom.mapTate_bijective_OL (G := P.pdivGroup)
    (H := P'.pdivGroup)).2 τ
  obtain ⟨φ, hφ, -⟩ := P.exists_fglHom_tpToPDiv (P' := P') OL.p_mem f
  refine ⟨φ, fun x => ?_, fun x => P.map_kummer _ _ _ P' φ x⟩
  rw [P.tpToQbar_map φ x, hφ, ← hf]

end OL

end PDivFGL

end PadicHodge
