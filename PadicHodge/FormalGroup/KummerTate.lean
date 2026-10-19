/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Kummer
import PadicHodge.Fontaine.Galois
import PadicHodge.GroupScheme.QuotientPoints

/-!
# Kummer coefficients versus the Galois module `T_p(G_{K'})(ℚ̄_p)`

For a `p`-divisible formal group law `F` over `O_{K'} = OL L` with `p`-divisible group
`G = F[p^∞]`, the coefficients `T_p F = Kummer.Tp (F(m_{ℂ_p}))` of the Kummer map `kummerOL`
are identified Galois-equivariantly with the Tate module `T_p(G_L)(ℚ̄_p)` on which
`galTate` (and hence Tate's theorem `GalTateHom`, [Hong, Cor. 3.5.5]) operates:

* `OL.incOK : O_K̄ → O_{ℂ_p}`, `OL.incQ : O_K̄ → ℚ̄_p`; for a finite `O_{K'}`-algebra `A`,
  `Hom(A, O_K̄) → Hom(A, O_{ℂ_p})` and `Hom(A, O_K̄) → Hom(A, ℚ̄_p)` are bijective (the values
  are integral over `O_{K'}`; `OL.exists_incOK_eq_of_isIntegral`, `OL.norm_le_one_of_isIntegral`);
* `PDivGroup.tateComp φ : T_p G(S) → T_p G(S')` for an algebra map `φ : S → S'`;
* **`PDivFGL.tpToQbar`** `: T_p F → T_p(G_{K'})(ℚ̄_p)`, bijective (`tpToQbar_bijective`), additive
  (`tpToQbar_add`) and **`G_{K'}`-equivariant** (`tpToQbar_tpRep`):
  `tpToQbar (σ · x) = galTate σ (tpToQbar x)`.
-/

noncomputable section

open IsLocalRing Polynomial WithConv

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

variable (L) in
/-- `O_K̄ → O_{ℂ_p}`. -/
def incOK : OKbar p →ₐ[OL L] OC p where
  toFun y := ⟨((y : PadicAlgCl p) : ℂ_[p]), by
    rw [mem_OC, PadicComplex.norm_extends]; exact y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    simp only [Subring.coe_mul]; exact map_mul (algebraMap (PadicAlgCl p) ℂ_[p]) _ _)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by
    simp only [Subring.coe_add]; exact map_add (algebraMap (PadicAlgCl p) ℂ_[p]) _ _)
  commutes' x := Subtype.ext (algebraMap_qbar_cp x)

theorem coe_incOK (y : OKbar p) :
    ((incOK L y : OC p) : ℂ_[p]) = ((y : PadicAlgCl p) : ℂ_[p]) := rfl

theorem incOK_injective : Function.Injective (incOK L) := fun _ _ h =>
  Subtype.ext ((algebraMap (PadicAlgCl p) ℂ_[p]).injective (congrArg Subtype.val h))

variable (L) in
/-- `O_K̄ → ℚ̄_p`. -/
def incQ : OKbar p →ₐ[OL L] PadicAlgCl p where
  toFun y := y
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem incQ_injective : Function.Injective (incQ L) := Subtype.val_injective

/-- An element of `O_{ℂ_p}` integral over `O_{K'}` lies in `O_K̄`. -/
theorem exists_incOK_eq_of_isIntegral {z : OC p} (hz : IsIntegral (OL L) z) :
    ∃ y : OKbar p, incOK L y = z := by
  classical
  obtain ⟨f, hfm, hf⟩ := hz
  set g := f.map (algebraMap (OL L) (PadicAlgCl p))
  have hgm : g.Monic := hfm.map _
  have hspl : g.Splits := IsAlgClosed.splits g
  have hzero : (g.map (algebraMap (PadicAlgCl p) ℂ_[p])).eval (z : ℂ_[p]) = 0 := by
    have this : (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap (OL L) (PadicAlgCl p)) =
        (OC p).subtype.comp (algebraMap (OL L) (OC p)) := by
      ext x; exact algebraMap_qbar_cp x
    have key : eval₂ ((OC p).subtype.comp (algebraMap (OL L) (OC p))) ((OC p).subtype z) f = 0 := by
      rw [← hom_eval₂, show eval₂ (algebraMap (OL L) (OC p)) z f = 0 from hf, map_zero]
    rw [Polynomial.map_map, this, eval_map]
    exact key
  rw [hspl.eq_prod_roots_of_monic hgm, Polynomial.map_multiset_prod, Multiset.map_map,
    eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at hzero
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.mp hzero
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X,
    eval_C] at h0
  have hza : (z : ℂ_[p]) = ((a : PadicAlgCl p) : ℂ_[p]) := sub_eq_zero.mp h0
  have hn : ‖a‖ ≤ 1 := by
    rw [← PadicComplex.norm_extends, ← hza]; exact z.2
  exact ⟨⟨a, hn⟩, Subtype.ext hza.symm⟩

/-- An element of `ℚ̄_p` integral over `O_{K'}` has absolute value `≤ 1`. -/
theorem norm_le_one_of_isIntegral [FiniteDimensional ℚ_[p] L] {z : PadicAlgCl p}
    (hz : IsIntegral (OL L) z) : ‖z‖ ≤ 1 := by
  obtain ⟨E, hLE, hFD, hE⟩ := exists_extend (E := L) {z}
  haveI : Fact (L ≤ E) := ⟨hLE⟩
  have hzE : z ∈ E := hE z (Finset.mem_singleton_self _)
  let f : E →ₐ[OL L] PadicAlgCl p :=
    { toRingHom := algebraMap E (PadicAlgCl p)
      commutes' := fun _ => rfl }
  have hint : IsIntegral (OL L) (⟨z, hzE⟩ : E) :=
    (isIntegral_algHom_iff f (algebraMap E (PadicAlgCl p)).injective).mp hz
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := OL E)).mp hint
  have : algebraMap (OL E) (PadicAlgCl p) y = z := congrArg Subtype.val hy
  rw [← this, ← nrm_eq_norm]
  exact nrm_le_one y

theorem postComp_incOK_bijective (G : FFGroupScheme (OL L)) :
    Function.Bijective (G.postComp (incOK L)) := by
  refine ⟨G.postComp_injective incOK_injective, fun φ => ?_⟩
  have hφ : ∀ a, ofConv φ a ∈ (incOK L).range := fun a =>
    exists_incOK_eq_of_isIntegral
      ((Algebra.IsIntegral.isIntegral (R := OL L) a).map (ofConv φ))
  refine ⟨toConv ((AlgEquiv.ofInjective _ incOK_injective).symm.toAlgHom.comp
    ((ofConv φ).codRestrict _ hφ)), ?_⟩
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun a => ?_
  change incOK L ((AlgEquiv.ofInjective _ incOK_injective).symm ⟨ofConv φ a, hφ a⟩) = ofConv φ a
  rw [← AlgEquiv.ofInjective_apply _ incOK_injective, AlgEquiv.apply_symm_apply]

theorem postComp_incQ_bijective [FiniteDimensional ℚ_[p] L] (G : FFGroupScheme (OL L)) :
    Function.Bijective (G.postComp (incQ L)) := by
  refine ⟨G.postComp_injective incQ_injective, fun φ => ?_⟩
  have hφ : ∀ a, ofConv φ a ∈ (incQ L).range := fun a =>
    ⟨⟨_, norm_le_one_of_isIntegral
      ((Algebra.IsIntegral.isIntegral (R := OL L) a).map (ofConv φ))⟩, rfl⟩
  refine ⟨toConv ((AlgEquiv.ofInjective _ incQ_injective).symm.toAlgHom.comp
    ((ofConv φ).codRestrict _ hφ)), ?_⟩
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun a => ?_
  change incQ L ((AlgEquiv.ofInjective _ incQ_injective).symm ⟨ofConv φ a, hφ a⟩) = ofConv φ a
  rw [← AlgEquiv.ofInjective_apply _ incQ_injective, AlgEquiv.apply_symm_apply]

/-- `σ ∈ G_{K'}` acting on `O_{ℂ_p}` as an `O_{K'}`-algebra map. -/
def autOCAlg {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : FGL.CoeffFixed p (OL L) σ) :
    OC p →ₐ[OL L] OC p where
  toFun := FGL.autOC σ
  map_one' := Subtype.ext (by rw [FGL.autOC_coe, OneMemClass.coe_one, map_one])
  map_mul' x y := Subtype.ext (by
    rw [FGL.autOC_coe, Subring.coe_mul, map_mul, Subring.coe_mul, FGL.autOC_coe, FGL.autOC_coe])
  map_zero' := Subtype.ext (by rw [FGL.autOC_coe, ZeroMemClass.coe_zero, map_zero])
  map_add' x y := Subtype.ext (by
    rw [FGL.autOC_coe, Subring.coe_add, map_add, Subring.coe_add, FGL.autOC_coe, FGL.autOC_coe])
  commutes' r := Subtype.ext (hσ r)

theorem incOK_galOK [FiniteDimensional ℚ_[p] L] (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (y : OKbar p) :
    incOK L (galOK σ y) = autOCAlg (PDivFGL.coeffFixed_OL _
      ((IntermediateField.fixingSubgroupEquiv L).symm σ).2) (incOK L y) :=
  Subtype.ext (by
    change ((σ y : PadicAlgCl p) : ℂ_[p]) = autCp _ ((y : PadicAlgCl p) : ℂ_[p])
    rw [autCp_coe]
    rfl)

end OL

namespace PDivGroup

variable {R : Type} [CommRing R] (G : PDivGroup R p)

/-- Postcomposition with an algebra map on Tate modules. -/
def tateComp {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') : G.TateModule S →* G.TateModule S' where
  toFun x := ⟨fun v => (G.G v).postComp φ (x.1 v), fun v => by
    change (G.incl v).mapPoints S' ((G.G v).postComp φ (x.1 v)) =
      ((G.G (v + 1)).postComp φ (x.1 (v + 1))) ^ p
    rw [FFGroupScheme.Hom.mapPoints_postComp, x.2 v, map_pow]⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)

omit hp in
theorem tateComp_val {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : G.TateModule S) (v : ℕ) :
    (G.tateComp φ x).1 v = (G.G v).postComp φ (x.1 v) := rfl

omit hp in
theorem tateComp_bijective {S S' : Type} [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] (φ : S →ₐ[R] S') (h : ∀ v, Function.Bijective ((G.G v).postComp φ)) :
    Function.Bijective (G.tateComp φ) := by
  refine ⟨fun x y hxy => Subtype.ext (funext fun v => (h v).1 ?_), fun y => ?_⟩
  · exact congrFun (congrArg Subtype.val hxy) v
  · choose x hx using fun v => (h v).2 (y.1 v)
    refine ⟨⟨x, fun v => (h (v + 1)).1 ?_⟩, Subtype.ext (funext hx)⟩
    rw [← FFGroupScheme.Hom.mapPoints_postComp, hx, map_pow, hx]
    exact y.2 v

omit hp in
theorem tateComp_comp {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] [CommRing S''] [Algebra R S''] (φ : S →ₐ[R] S') (ψ : S' →ₐ[R] S'')
    (x : G.TateModule S) : G.tateComp ψ (G.tateComp φ x) = G.tateComp (ψ.comp φ) x := rfl

end PDivGroup

namespace PDivFGL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (P : PDivFGL (OL L) d p)

/-- **Galois equivariance of `T_p F → T_p(F[p^∞])(O_{ℂ_p})`.** -/
theorem tpToPDiv_tpRep (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    P.tpToPDiv (Kummer.tpRep P.galRepOL p σ x) =
      P.pdivGroup.tateComp (OL.autOCAlg (coeffFixed_OL _ σ.2)) (P.tpToPDiv x) := by
  refine Subtype.ext (funext fun v => ?_)
  apply WithConv.ofConv_injective
  apply Ideal.Quotient.algHom_ext (OL L)
  refine AlgHom.ext fun f => ?_
  change P.F.layerPt v ⟨_, _⟩ (Ideal.Quotient.mk _ f) =
    FGL.autOC σ (P.F.layerPt v ⟨Kummer.val _ p x v, _⟩ (Ideal.Quotient.mk _ f))
  rw [FGL.layerPt_mk, FGL.layerPt_mk]
  apply Subtype.ext
  rw [FGL.autOC_coe, FGL.ev_autCp_of (coeffFixed_OL _ σ.2) f (Kummer.val _ p x v).2]
  rfl

/-- **Kummer coefficients as the Galois module `T_p(G_{K'})(ℚ̄_p)`**:
`T_p F → T_p(F[p^∞])(O_{ℂ_p}) ≅ T_p(F[p^∞])(O_K̄) → T_p(F[p^∞])(ℚ̄_p) ≅ T_p(F[p^∞]_{K'})(ℚ̄_p)`. -/
def tpToQbar (x : Kummer.Tp (P.F.Pt p) p) :
    (P.pdivGroup.baseChange L).TateModule (PadicAlgCl p) :=
  (P.pdivGroup.baseChangeTateEquiv (S := L) (PadicAlgCl p)).symm
    (P.pdivGroup.tateComp (OL.incQ L)
      ((MulEquiv.ofBijective _ (P.pdivGroup.tateComp_bijective (OL.incOK L)
        fun _ => OL.postComp_incOK_bijective _)).symm (P.tpToPDiv x)))

theorem tpToQbar_bijective : Function.Bijective P.tpToQbar :=
  (MulEquiv.bijective _).comp ((P.pdivGroup.tateComp_bijective (OL.incQ L)
    fun _ => OL.postComp_incQ_bijective _).comp
    ((MulEquiv.bijective _).comp (P.tpToPDiv_bijective fun r hr => OL.norm_lt_one r hr)))

omit [FiniteDimensional ℚ_[p] L] in
/-- `galTate` on `T_p(G_{K'})(ℚ̄_p)` is postcomposition with `σ` on `T_p(G)(ℚ̄_p)`. -/
theorem baseChangeTateEquiv_galTate (G : PDivGroup (OL L) p) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (w : (G.baseChange L).TateModule (PadicAlgCl p)) :
    G.baseChangeTateEquiv (S := L) (PadicAlgCl p) ((G.baseChange L).galTate σ w) =
      G.tateComp ((σ : PadicAlgCl p →ₐ[L] PadicAlgCl p).restrictScalars (OL L))
        (G.baseChangeTateEquiv (S := L) (PadicAlgCl p) w) := rfl

/-- **Galois equivariance**: `tpToQbar (σ · x) = galTate σ (tpToQbar x)` for `σ ∈ G_{K'}`. -/
theorem tpToQbar_tpRep (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    P.tpToQbar (Kummer.tpRep P.galRepOL p σ x) =
      (P.pdivGroup.baseChange L).galTate (IntermediateField.fixingSubgroupEquiv L σ)
        (P.tpToQbar x) := by
  set σ' := IntermediateField.fixingSubgroupEquiv L σ
  set e := MulEquiv.ofBijective _ (P.pdivGroup.tateComp_bijective (OL.incOK L)
    fun _ => OL.postComp_incOK_bijective _)
  -- the `O_K̄`-point of `x`
  set y := e.symm (P.tpToPDiv x)
  have hy : P.pdivGroup.tateComp (OL.incOK L) y = P.tpToPDiv x := e.apply_symm_apply _
  have hσy : e.symm (P.tpToPDiv (Kummer.tpRep P.galRepOL p σ x)) =
      P.pdivGroup.tateComp (OL.galOK σ').toAlgHom y := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, P.tpToPDiv_tpRep, ← hy]
    change _ = P.pdivGroup.tateComp (OL.incOK L)
      (P.pdivGroup.tateComp (OL.galOK σ').toAlgHom y)
    have hcomp : (OL.autOCAlg (coeffFixed_OL _ σ.2)).comp (OL.incOK L) =
        (OL.incOK L).comp (OL.galOK σ').toAlgHom :=
      AlgHom.ext fun z => (OL.incOK_galOK σ' z).symm
    rw [PDivGroup.tateComp_comp, PDivGroup.tateComp_comp, hcomp]
  unfold tpToQbar
  rw [hσy]
  apply (P.pdivGroup.baseChangeTateEquiv (S := L) (PadicAlgCl p)).injective
  rw [MulEquiv.apply_symm_apply, baseChangeTateEquiv_galTate P.pdivGroup σ',
    MulEquiv.apply_symm_apply,
    PDivGroup.tateComp_comp, PDivGroup.tateComp_comp]
  rfl

end PDivFGL

end PadicHodge
