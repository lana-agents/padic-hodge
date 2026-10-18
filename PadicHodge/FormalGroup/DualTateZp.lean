/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Zp
import PadicHodge.GroupScheme.DualTateOC
import PadicHodge.GroupScheme.DualBaseChange
import PadicHodge.GroupScheme.CartierDualPDiv

/-!
# `T_p(G^∨)(O_{ℂ_p}) = T_p(G_{ℚ_p}^∨)(ℚ̄_p)` for `G` over `ℤ_p`

The map `α` of [Hong, Prop. 3.4.9] (`Alpha.lean`) is defined on `T_p(G^∨)(O_{ℂ_p})`, the limit of
the `G_v^∨(O_{ℂ_p})` along the transposes `i_v^∨` (`PDivGroup.DualTate`), for `G` over `ℤ_p`;
the Galois representation `V_p(G^∨)` and the Cartier pairing with values in `ℤ_p(1)`
(`TatePairing.lean`, `TateDual.lean`, `TateDualRep.lean`) are set up for the Cartier dual
`p`-divisible group `G_{ℚ_p}^∨ = dualPDiv` over `ℚ_p`. For `G` over `ℤ_p` (`ZpD p`):

* `ZpD` is a `ℚ_p`-algebra (`ZpD.algebraQp`; hence a `ℚ̄_p`-coefficient ring by Mathlib's
  `AlgebraicClosure.instAlgebra`);
* `FFGroupScheme.card_dual_points_sepClosed`: `#G^∨(Ω) = |G|` for `G` killed by `n` invertible
  in a separably closed field `Ω`;
* `dualPointsQbarCp`: `G^∨(ℚ̄_p) ≃ G^∨(ℂ_p)` (injective, same cardinality);
* **`dualTateZpEquiv : T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_{ℚ_p}^∨)(ℚ̄_p)`**, composed of
  `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G^∨)(ℂ_p)` ([Hong, Lemma 3.4.1], `dualTateOCEquiv`),
  `T_p(G^∨)(ℂ_p) ≃ T_p(G^∨)(ℚ̄_p)`, `T_p(G^∨)(ℚ̄_p) ≃ T_p((G_{ℚ_p})^∨)(ℚ̄_p)` (Cartier duality
  commutes with base change, `dualTateBaseChangeEquiv`) and `T_p(G_{ℚ_p}^∨) = DualTate`
  (`tateModule_dualPDiv`); it is Galois-equivariant (`dualTateZpEquiv_gal`).

The construction is done for any coefficient ring `R → O_{ℂ_p}` and field `F ⊆ ℚ̄_p` with
`R → F → ℚ̄_p → ℂ_p` equal to `R → O_{ℂ_p} ⊆ ℂ_p` (`qbarToCpOf`, `dualTateGenEquiv`:
`T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_F^∨)(ℚ̄_p)`), e.g. `R = O_{K'}`, `F = K'`.
-/

noncomputable section

open WithConv

namespace PadicHodge

namespace ZpD

variable {p : ℕ} [hp : Fact p.Prime]

instance : Nontrivial (ZpD p) := inferInstanceAs (Nontrivial ℤ_[p])

instance algebraQp : Algebra (ZpD p) ℚ_[p] := inferInstanceAs (Algebra ℤ_[p] ℚ_[p])

theorem algebraMap_Qp (r : ZpD p) : algebraMap (ZpD p) ℚ_[p] r = (val r : ℚ_[p]) := rfl

/-- `ℚ̄_p → ℂ_p` as a `ℤ_p`-algebra map (for the algebra structure on `ℂ_p` via `O_{ℂ_p}`). -/
def qbarToCp :
    letI := algebraCpOfOC (p := p) (ZpD p)
    PadicAlgCl p →ₐ[ZpD p] ℂ_[p] := by
  letI := algebraCpOfOC (p := p) (ZpD p)
  exact
    { algebraMap (PadicAlgCl p) ℂ_[p] with
      commutes' := fun r => by
        change algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap (ZpD p) (PadicAlgCl p) r) = _
        rw [IsScalarTower.algebraMap_apply (ZpD p) ℚ_[p] (PadicAlgCl p) r,
          ← IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
        rfl }

theorem qbarToCp_injective : Function.Injective (qbarToCp (p := p)) :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).injective

end ZpD

namespace FFGroupScheme

variable {R : Type} [CommRing R] [Nontrivial R]

/-- **`#G^∨(Ω) = |G|`** for `G` killed by `n`, `n` invertible in the separably closed field
`Ω`. -/
theorem card_dual_points_sepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (G : FFGroupScheme R) {n : ℕ} (hn : IsUnit (n : Ω)) (hG : G.univPt ^ n = 1) :
    Nat.card (G.dual.points Ω) = G.order := by
  have hD : G.dual.univPt ^ n = 1 := G.dual_univPt_pow_eq_one hG
  set H := G.dual.baseChange Ω
  have hH : H.univPt ^ n = 1 := by
    apply (G.dual.baseChangePointsEquiv H.A).injective
    rw [map_pow, map_one]
    exact G.dual.pow_eq_one_of_univPt hD _
  have hE : H.IsEtale := H.isEtale_of_univPt_pow_eq_one hn hH
  rw [← Nat.card_congr (G.dual.baseChangePointsEquiv (S := Ω) Ω).toEquiv,
    card_points_of_isEtale H hE, order_baseChange, order_dual]

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

theorem isUnit_p_pow_Qbar {p : ℕ} [hp : Fact p.Prime] (v : ℕ) :
    IsUnit ((p ^ v : ℕ) : PadicAlgCl p) :=
  isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (pow_ne_zero v hp.out.ne_zero))

theorem postComp_mapPoints {R : Type} [CommRing R] {H H' : FFGroupScheme R}
    (f : FFGroupScheme.Hom H H') {T T' : Type} [CommRing T] [Algebra R T] [CommRing T']
    [Algebra R T'] (ι : T →ₐ[R] T') (x : H.points T) :
    H'.postComp ι (f.mapPoints T x) = f.mapPoints T' (H.postComp ι x) := rfl

/-! ### General coefficient ring `R ⊆ O_{ℂ_p}` with generic fibre over a field `F ⊆ ℚ̄_p` -/

section General

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [Nontrivial R] [Algebra R (OC p)]
  {F : Type} [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))
  (G : PDivGroup R p)

omit [Nontrivial R] [CharZero F] [IsScalarTower R F (PadicAlgCl p)] in
/-- `ℚ̄_p → ℂ_p` as an `R`-algebra map, given that `R → ℚ̄_p → ℂ_p` is `R → O_{ℂ_p} ⊆ ℂ_p`. -/
def qbarToCpOf :
    letI := algebraCpOfOC (p := p) R
    PadicAlgCl p →ₐ[R] ℂ_[p] := by
  letI := algebraCpOfOC (p := p) R
  exact { algebraMap (PadicAlgCl p) ℂ_[p] with commutes' := fun r => hRF r }

omit [Nontrivial R] [CharZero F] [IsScalarTower R F (PadicAlgCl p)] in
theorem qbarToCpOf_injective : Function.Injective (qbarToCpOf (p := p) hRF) :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).injective

omit [CharZero F] [IsScalarTower R F (PadicAlgCl p)] in
/-- `G_v^∨(ℚ̄_p) → G_v^∨(ℂ_p)` is bijective. -/
theorem dualPointsQbarCpOf_bijective (v : ℕ) :
    letI := algebraCpOfOC (p := p) R
    Function.Bijective ((G.G v).dual.postComp (qbarToCpOf (p := p) hRF)) := by
  letI := algebraCpOfOC (p := p) R
  have hinj : Function.Injective ((G.G v).dual.postComp (qbarToCpOf (p := p) hRF)) := by
    intro x y h
    apply WithConv.ofConv_injective
    ext a
    exact qbarToCpOf_injective hRF
      (congrArg (fun z : (G.G v).dual.points ℂ_[p] => ofConv z a) h)
  have h1 := (G.G v).card_dual_points_sepClosed (PadicAlgCl p)
    (PDivGroup.isUnit_p_pow_Qbar (p := p) v)
    (G.univPt_pow_eq_one v)
  have h2 := G.card_dual_points_Cp' v
  have hfin : Finite ((G.G v).dual.points ℂ_[p]) :=
    (G.G v).dual.finite_points_of_free (S := ℂ_[p]) (Module.Free.chooseBasis _ _)
  exact hinj.bijective_of_nat_card_le (by rw [h1, h2])

omit [CharZero F] [IsScalarTower R F (PadicAlgCl p)] in
/-- `G_v^∨(ℚ̄_p) ≃* G_v^∨(ℂ_p)`. -/
def dualPointsQbarCpOf (v : ℕ) :
    letI := algebraCpOfOC (p := p) R
    (G.G v).dual.points (PadicAlgCl p) ≃* (G.G v).dual.points ℂ_[p] := by
  letI := algebraCpOfOC (p := p) R
  exact MulEquiv.ofBijective _ (G.dualPointsQbarCpOf_bijective hRF v)

omit [CharZero F] [IsScalarTower R F (PadicAlgCl p)] in
/-- **`T_p(G^∨)(ℚ̄_p) ≃* T_p(G^∨)(ℂ_p)`.** -/
def dualTateQbarCpOf :
    letI := algebraCpOfOC (p := p) R
    G.DualTate (PadicAlgCl p) ≃* G.DualTate ℂ_[p] := by
  letI := algebraCpOfOC (p := p) R
  exact
    { toFun := fun y => ⟨fun v => G.dualPointsQbarCpOf hRF v (y.1 v), fun v => by
        change (G.G v).dual.postComp _ (y.1 v) = _
        rw [y.2 v]
        rfl⟩
      invFun := fun z => ⟨fun v => (G.dualPointsQbarCpOf hRF v).symm (z.1 v), fun v => by
        apply (G.dualPointsQbarCpOf hRF v).injective
        rw [MulEquiv.apply_symm_apply]
        change z.1 v = (G.G v).dual.postComp _ ((G.incl v).dual.mapPoints _ _)
        rw [postComp_mapPoints]
        change z.1 v = (G.incl v).dual.mapPoints _ ((G.dualPointsQbarCpOf hRF (v + 1))
          ((G.dualPointsQbarCpOf hRF (v + 1)).symm (z.1 (v + 1))))
        rw [MulEquiv.apply_symm_apply]
        exact z.2 v⟩
      left_inv := fun y => Subtype.ext (funext fun v => MulEquiv.symm_apply_apply _ _)
      right_inv := fun z => Subtype.ext (funext fun v => MulEquiv.apply_symm_apply _ _)
      map_mul' := fun y y' => Subtype.ext (funext fun v => map_mul _ _ _) }

/-- **`T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_F^∨)(ℚ̄_p)`** for `G` over `R`, `G_F` its generic fibre. -/
def dualTateGenEquiv :
    G.DualTate (OCd p) ≃* (G.baseChange F).dualPDiv.TateModule (PadicAlgCl p) := by
  letI := algebraCpOfOC (p := p) R
  exact (G.dualTateOCEquiv.trans (G.dualTateQbarCpOf hRF).symm).trans
    ((G.dualTateBaseChangeEquiv (S := F) (PadicAlgCl p)).symm.trans
      (MulEquiv.subgroupCongr ((G.baseChange F).tateModule_dualPDiv (PadicAlgCl p)).symm))

end General

/-! ### `R = ℤ_p`, `F = ℚ_p` -/

section Zp

variable {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup (ZpD p) p)

theorem ZpD.algebraMap_qbar_cp (r : ZpD p) :
    ((algebraMap (ZpD p) (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
      ((algebraMap (ZpD p) (OC p) r : OC p) : ℂ_[p]) := by
  letI := algebraCpOfOC (p := p) (ZpD p)
  exact (ZpD.qbarToCp (p := p)).commutes r

/-- `G_v^∨(ℚ̄_p) ≃* G_v^∨(ℂ_p)`. -/
def dualPointsQbarCp (v : ℕ) :
    letI := algebraCpOfOC (p := p) (ZpD p)
    (G.G v).dual.points (PadicAlgCl p) ≃* (G.G v).dual.points ℂ_[p] :=
  G.dualPointsQbarCpOf ZpD.algebraMap_qbar_cp v

/-- **`T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_{ℚ_p}^∨)(ℚ̄_p)`** for `G` over `ℤ_p`. -/
def dualTateZpEquiv :
    G.DualTate (OCd p) ≃* (G.baseChange ℚ_[p]).dualPDiv.TateModule (PadicAlgCl p) :=
  G.dualTateGenEquiv ZpD.algebraMap_qbar_cp

end Zp

end PDivGroup

end PadicHodge
