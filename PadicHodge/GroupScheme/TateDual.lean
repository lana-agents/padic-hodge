/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateRep

/-!
# `T_p(G^∨) ≅ Hom_{ℤ_p}(T_p G, ℤ_p(1))`

([Stix, §11.2.2, Cor. 85], [Hong, Prop. 3.4.6].) For a `p`-divisible group `G` over `ℚ_p`, the
Cartier pairing `tatePairingZp : T_p G(ℚ̄_p) × T_p(G^∨)(ℚ̄_p) → ℤ_p` is `ℤ_p`-bilinear for the
module structures of `TateRep.lean` (`tatePairingZp_zpPow_left`, `tatePairingZp_zpPow_right`),
and the induced `ℤ_p`-linear map

`tateDualHom : T_p(G^∨)(ℚ̄_p) → Hom_{ℤ_p}(T_p G(ℚ̄_p), ℤ_p)`

is bijective (`tateDualHom_bijective`; from `dualTateCoord_bijective` and evaluation on a
basis), with `tateDualHom (σ y) (σ x) = χ(σ) · tateDualHom y x` (`tateDualHom_gal`): the twist
by `ℤ_p(1)`.
-/

noncomputable section

open WithConv

namespace PadicHodge

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [CharZero K] [Algebra K (PadicAlgCl p)]
  (G : PDivGroup K p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

theorem eps_pow_expo_mul (a b : ℤ_[p]) (v : ℕ) :
    (eps (p := p) v ^ expo b v) ^ expo a v = eps v ^ expo (a * b) v := by
  rw [← pow_mul, expo, expo, expo, map_mul, ZMod.val_mul, pow_mod_eq (eps_pow_card v), mul_comm]

omit [CharZero K] in
theorem tatePairingZp_zpPow_left (a : ℤ_[p]) (x : G.TateModule (PadicAlgCl p))
    (y : G.DualTate (PadicAlgCl p)) :
    G.tatePairingZp (G.zpPow _ a x) y = a * G.tatePairingZp x y := by
  have hb := (tatePairingZp_eq_iff x y (G.tatePairingZp x y)).mp rfl
  rw [tatePairingZp_eq_iff]
  intro v
  rw [zpPow_val, ← cartierPairingBase_apply, map_pow, MonoidHom.pow_apply,
    cartierPairingBase_apply, hb v, eps_pow_expo_mul]

omit [CharZero K] in
theorem tatePairingZp_pow_right (a : ℤ_[p]) (x : G.TateModule (PadicAlgCl p))
    (y : G.DualTate (PadicAlgCl p)) (y' : G.DualTate (PadicAlgCl p))
    (hy : ∀ v, y'.1 v = y.1 v ^ expo a v) :
    G.tatePairingZp x y' = a * G.tatePairingZp x y := by
  have hb := (tatePairingZp_eq_iff x y (G.tatePairingZp x y)).mp rfl
  rw [tatePairingZp_eq_iff]
  intro v
  rw [hy v, ← cartierPairingBase_apply, map_pow, cartierPairingBase_apply, hb v,
    eps_pow_expo_mul]

/-- `T_p(G^∨) = DualTate G` as groups. -/
def dualTateEquiv :
    G.dualPDiv.TateModule (PadicAlgCl p) ≃* G.DualTate (PadicAlgCl p) :=
  MulEquiv.subgroupCongr (G.tateModule_dualPDiv (PadicAlgCl p))

theorem dualTateEquiv_val (y : G.dualPDiv.TateModule (PadicAlgCl p)) (v : ℕ) :
    (G.dualTateEquiv y).1 v = y.1 v := rfl

/-- **The Cartier pairing as a `ℤ_p`-linear map** `T_p(G^∨) → Hom_{ℤ_p}(T_p G, ℤ_p)`. -/
def tateDualHom : Additive (G.dualPDiv.TateModule (PadicAlgCl p)) →ₗ[ℤ_[p]]
    (Additive (G.TateModule (PadicAlgCl p)) →ₗ[ℤ_[p]] ℤ_[p]) :=
  LinearMap.mk₂ ℤ_[p]
    (fun y x => G.tatePairingZp (Additive.toMul x) (G.dualTateEquiv (Additive.toMul y)))
    (fun y y' x => by
      change G.tatePairingZp _ (G.dualTateEquiv (Additive.toMul y * Additive.toMul y')) = _
      rw [map_mul, tatePairingZp_add_right])
    (fun a y x => by
      rw [smul_eq_mul]
      exact G.tatePairingZp_pow_right a _ _ _ fun v => rfl)
    (fun y x x' => by
      change G.tatePairingZp (Additive.toMul x * Additive.toMul x') _ = _
      rw [tatePairingZp_add_left])
    (fun a y x => by
      rw [smul_eq_mul]
      exact G.tatePairingZp_zpPow_left a _ _)

theorem tateDualHom_apply (y : Additive (G.dualPDiv.TateModule (PadicAlgCl p)))
    (x : Additive (G.TateModule (PadicAlgCl p))) :
    G.tateDualHom y x =
      G.tatePairingZp (Additive.toMul x) (G.dualTateEquiv (Additive.toMul y)) := rfl

omit [CharZero K] in
theorem phi_single (t : Fin G.height → G.TateModule (PadicAlgCl p)) (i : Fin G.height) :
    G.phi (PadicAlgCl p) t (Multiplicative.ofAdd (Pi.single i 1)) = t i := by
  apply Subtype.ext
  funext v
  rw [phi_apply]
  have : (Multiplicative.ofAdd fun j => PadicInt.toZModPow v
      (Multiplicative.toAdd (Multiplicative.ofAdd
        (Pi.single i (1 : ℤ_[p]) : Fin G.height → ℤ_[p])) j)) =
      Multiplicative.ofAdd (Pi.single i 1 : Fin G.height → ZMod (p ^ v)) := by
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [this, phiLevel_single]

/-- **`T_p(G^∨)(ℚ̄_p) ≅ Hom_{ℤ_p}(T_p G(ℚ̄_p), ℤ_p)`** via the Cartier pairing. -/
theorem tateDualHom_bijective : Function.Bijective G.tateDualHom := by
  obtain ⟨t, ht, hphi⟩ := G.exists_tateBasis
  let eT : (Fin G.height → ℤ_[p]) ≃ₗ[ℤ_[p]] Additive (G.TateModule (PadicAlgCl p)) :=
    LinearEquiv.ofBijective (G.phiLin _ t) ⟨fun c c' h =>
      Multiplicative.ofAdd.injective (hphi.1 (congrArg Additive.toMul h)), fun x => by
        obtain ⟨c, hc⟩ := hphi.2 (Additive.toMul x)
        exact ⟨Multiplicative.toAdd c, congrArg Additive.ofMul hc⟩⟩
  let bT : Module.Basis (Fin G.height) ℤ_[p] (Additive (G.TateModule (PadicAlgCl p))) :=
    Module.Basis.ofEquivFun eT.symm
  have hbT : ∀ i, bT i = Additive.ofMul (t i) := by
    intro i
    rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
    change Additive.ofMul (G.phi _ t (Multiplicative.ofAdd (Pi.single i 1))) = _
    rw [phi_single]
  let E := (bT.constr ℤ_[p] (M' := ℤ_[p])).symm
  have hcomp : ⇑E ∘ ⇑G.tateDualHom = fun y => Multiplicative.toAdd
      (dualTateCoord t (G.dualTateEquiv (Additive.toMul y))) := by
    funext y
    funext i
    simp only [Function.comp_apply, E, Module.Basis.constr_symm_apply, hbT, tateDualHom_apply,
      toMul_ofMul]
    rfl
  rw [← Function.Bijective.of_comp_iff' E.bijective, hcomp]
  exact (Multiplicative.toAdd.bijective.comp (dualTateCoord_bijective t ht)).comp
    (G.dualTateEquiv.bijective.comp Additive.toMul.bijective)

/-- **The twist by `ℤ_p(1)`**: `⟨σx, σy⟩ = χ(σ) ⟨x, y⟩` for `σ ∈ Gal(ℚ̄_p/K)`, `K ⊇ ℚ_p`. -/
theorem tateDualHom_galOver [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (y : Additive (G.dualPDiv.TateModule (PadicAlgCl p)))
    (x : Additive (G.TateModule (PadicAlgCl p))) :
    G.tateDualHom (G.dualPDiv.galLin σ y) (G.galLin σ x) =
      ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * G.tateDualHom y x := by
  rw [tateDualHom_apply, tateDualHom_apply, ← tatePairingZp_galOver]
  rfl

/-- **The twist by `ℤ_p(1)`**: `⟨σx, σy⟩ = χ(σ) ⟨x, y⟩`. -/
theorem tateDualHom_gal (G : PDivGroup ℚ_[p] p) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : Additive (G.dualPDiv.TateModule (PadicAlgCl p)))
    (x : Additive (G.TateModule (PadicAlgCl p))) :
    G.tateDualHom (G.dualPDiv.galLin σ y) (G.galLin σ x) =
      ((chi σ : ℤ_[p]ˣ) : ℤ_[p]) * G.tateDualHom y x :=
  G.tateDualHom_galOver σ y x

end PDivGroup

end PadicHodge
