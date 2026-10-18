/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierPairingBase
import PadicHodge.GroupScheme.PDivisibleHom
import PadicHodge.GroupScheme.ConstPDivTate

/-!
# The Cartier pairing on Tate modules

([Stix, §11.2.2], [Hong, Prop. 3.4.6].) For a `p`-divisible group `G = (G_v)` over `R`, the
Cartier duals `G_v^∨` with the transposes `i_v^∨ : G_{v+1}^∨ → G_v^∨` of the inclusions form an
inverse system; its limit `DualTate G S = lim_v G_v^∨(S)` is the Tate module of the Cartier
dual `p`-divisible group (we do not yet show that `(G_v^∨)` is a `p`-divisible group: that needs
the exactness of `0 → G_1 → G_{v+1} → G_v → 0`, i.e. fppf quotients). The levelwise Cartier
pairings `G_v(S) × G_v^∨(S) → μ_{p^v}(S)` are compatible:
`⟨x_v, y_v⟩_v = ⟨quot x_{v+1}, i_v^∨ y_{v+1}⟩_v = ⟨i_v quot x_{v+1}, y_{v+1}⟩_{v+1}
= ⟨x_{v+1}^p, y_{v+1}⟩_{v+1}`, so they define

* `PDivGroup.tatePairing : T_p G(S) →* DualTate G S →* RootSys p S` (compatible systems of
  `p`-power roots of unity), bimultiplicative;
* `tatePairing_gal`: over `ℚ_p`, `⟨σx, σy⟩ = σ⟨x, y⟩`; with `RootSys p ℚ̄_p ≃ ℤ_p`
  (`rootSysEquiv`), `tatePairingZp : T_p G(ℚ̄_p) × T_p G^∨(ℚ̄_p) → ℤ_p` satisfies
  `⟨σx, σy⟩ = χ(σ) ⟨x, y⟩` (`tatePairingZp_gal`): values in `ℤ_p(1)`.

Ingredients: `Cartier.transposeBialgHom` (the transpose of a bialgebra map is a bialgebra map;
checked after the injective `ev2`), `FFGroupScheme.Hom.dual`, `pairing_dual` (naturality), and
`pairing_postComp` (compatibility with algebra maps `S → S'`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

theorem ev2_map_transpose {G H : FFGroupScheme R} (f : Hom G H)
    (x : Cartier.Dual R G.A ⊗[R] Cartier.Dual R G.A) :
    Cartier.ev2 R H.A (TensorProduct.map (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A)).toLinearMap
      (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A)).toLinearMap x) =
      Cartier.ev2 R G.A x ∘ₗ TensorProduct.map (f : H.A →ₗ[R] G.A) (f : H.A →ₗ[R] G.A) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp]
  | tmul g h =>
    refine TensorProduct.ext' fun a b => ?_
    simp [Cartier.ev2_tmul_tmul]

/-- The **dual homomorphism** `f^∨ : H^∨ → G^∨` of `f : G → H`: the transpose `F ↦ F ∘ f^*`
of `f^* : O(H) → O(G)`. -/
def Hom.dual {G H : FFGroupScheme R} (f : Hom G H) : Hom H.dual G.dual :=
  BialgHom.ofAlgHom (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A))
    (by
      ext F
      change (show Cartier.Dual R G.A from F) (f 1) = (show Cartier.Dual R G.A from F) 1
      rw [map_one])
    (by
      ext F
      apply Cartier.ev2_injective
      change Cartier.ev2 R H.A (TensorProduct.map (Cartier.transposeAlgHom
        (f : H.A →ₗc[R] G.A)).toLinearMap (Cartier.transposeAlgHom
        (f : H.A →ₗc[R] G.A)).toLinearMap (Cartier.comulD R G.A F)) =
        Cartier.ev2 R H.A (Cartier.comulD R H.A (Cartier.transposeAlgHom
        (f : H.A →ₗc[R] G.A) F))
      rw [ev2_map_transpose, Cartier.ev2_comulD, Cartier.ev2_comulD]
      refine TensorProduct.ext' fun a b => ?_
      simp)

theorem Hom.dual_apply {G H : FFGroupScheme R} (f : Hom G H) (F : Cartier.Dual R G.A)
    (b : H.A) : (show Cartier.Dual R H.A from f.dual F) b = F (f b) := rfl

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Naturality of the Cartier pairing: `⟨f φ, ψ⟩_H = ⟨φ, f^∨ ψ⟩_G`. -/
theorem pairing_dual {G H : FFGroupScheme R} (f : Hom G H) (φ : G.points S)
    (ψ : H.dual.points S) :
    H.pairing S (f.mapPoints S φ) ψ = G.pairing S φ (f.dual.mapPoints S ψ) :=
  G.pairing_mapPoints S f φ ψ

/-- The Cartier pairing commutes with algebra maps `S → S'`. -/
theorem pairing_postComp (G : FFGroupScheme R) {S' : Type*} [CommRing S'] [Algebra R S']
    (σ : S →ₐ[R] S') (φ : G.points S) (ψ : G.dual.points S) :
    G.pairing S' (G.postComp σ φ) (G.dual.postComp σ ψ) = σ (G.pairing S φ ψ) := by
  let b := Module.Free.chooseBasis R G.A
  rw [pairing_eq_sum G S' b, pairing_eq_sum G S b, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  rfl

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ} [NeZero p] (G : PDivGroup R p) (S : Type u)
  [CommRing S] [Algebra R S]

/-- The Tate module of the Cartier dual: `lim_v G_v^∨(S)` along the transposes
`i_v^∨ : G_{v+1}^∨ → G_v^∨`. -/
def DualTate : Subgroup ((v : ℕ) → (G.G v).dual.points S) where
  carrier := {y | ∀ v, y v = (G.incl v).dual.mapPoints S (y (v + 1))}
  mul_mem' := fun {x y} hx hy v => by simp only [Pi.mul_apply, map_mul, hx v, hy v]
  one_mem' := fun v => by simp
  inv_mem' := fun {x} hx v => by simp only [Pi.inv_apply, map_inv, hx v]

/-- The level-`v` Cartier pairing, with values in `μ_{p^v}(S)`. -/
def levelPairing (v : ℕ) (x : (G.G v).points S) (y : (G.G v).dual.points S) :
    rootsOfUnity (p ^ v) S :=
  rootsOfUnity.mkOfPowEq ((G.G v).cartierPairingBase S x y)
    ((G.G v).cartierPairingBase_pow_eq_one S x (G.pow_eq_one v S x) y)

theorem levelPairing_val (v : ℕ) (x : (G.G v).points S) (y : (G.G v).dual.points S) :
    (((G.levelPairing S v x y : rootsOfUnity (p ^ v) S) : Sˣ) : S) = (G.G v).pairing S x y :=
  rootsOfUnity.coe_mkOfPowEq _

theorem levelPairing_compat (x : G.TateModule S) (y : G.DualTate S) (v : ℕ) :
    (((G.levelPairing S v (x.1 v) (y.1 v) : rootsOfUnity (p ^ v) S) : Sˣ) : S) =
      (((G.levelPairing S (v + 1) (x.1 (v + 1)) (y.1 (v + 1)) :
        rootsOfUnity (p ^ (v + 1)) S) : Sˣ) : S) ^ p := by
  rw [levelPairing_val, levelPairing_val, TateModule.val_eq_quot G x v, y.2 v,
    ← pairing_dual, G.incl_quot]
  change (G.G (v + 1)).cartierPairingBase S _ _ = (G.G (v + 1)).cartierPairingBase S _ _ ^ p
  rw [map_pow, MonoidHom.pow_apply]

/-- **The Cartier pairing on Tate modules** `T_p G(S) × T_p G^∨(S) → lim μ_{p^v}(S)`. -/
def tatePairing : G.TateModule S →* G.DualTate S →* RootSys p S where
  toFun x :=
    { toFun := fun y => ⟨fun v => G.levelPairing S v (x.1 v) (y.1 v), fun v =>
        Units.ext (by rw [Units.val_pow_eq_pow_val]; exact G.levelPairing_compat S x y v)⟩
      map_one' := Subtype.ext <| funext fun v => Subtype.ext <| Units.ext <|
        (G.levelPairing_val S v _ _).trans ((G.G v).pairing_one_right S (x.1 v))
      map_mul' := fun y y' => Subtype.ext <| funext fun v => Subtype.ext <| Units.ext <|
        (G.levelPairing_val S v _ _).trans (((G.G v).pairing_mul_right S (x.1 v) (y.1 v)
          (y'.1 v)).trans (congrArg₂ (· * ·) (G.levelPairing_val S v _ _).symm
            (G.levelPairing_val S v _ _).symm)) }
  map_one' := by
    refine MonoidHom.ext fun y => Subtype.ext <| funext fun v => Subtype.ext <| Units.ext ?_
    exact (G.levelPairing_val S v _ _).trans ((G.G v).pairing_one_left S (y.1 v))
  map_mul' x x' := by
    refine MonoidHom.ext fun y => Subtype.ext <| funext fun v => Subtype.ext <| Units.ext ?_
    exact (G.levelPairing_val S v _ _).trans (((G.G v).pairing_mul_left S (x.1 v) (x'.1 v)
      (y.1 v)).trans (congrArg₂ (· * ·) (G.levelPairing_val S v _ _).symm
        (G.levelPairing_val S v _ _).symm))

theorem tatePairing_val (x : G.TateModule S) (y : G.DualTate S) (v : ℕ) :
    ((((G.tatePairing S x y : RootSys p S) : (v : ℕ) → rootsOfUnity (p ^ v) S) v :
      Sˣ) : S) = (G.G v).pairing S (x.1 v) (y.1 v) := G.levelPairing_val S v _ _

/-! ### Galois equivariance -/

variable [hp : Fact p.Prime] {K : Type} [Field K] [Algebra K (PadicAlgCl p)] (H : PDivGroup K p)

/-- The Galois action on the dual Tate module (`G` over a field `K ⊆ ℚ̄_p`, e.g. `ℚ_p`). -/
def galDualTate (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    H.DualTate (PadicAlgCl p) →* H.DualTate (PadicAlgCl p) where
  toFun y := ⟨fun v => galPoints (H.G v).dual σ (y.1 v), fun v =>
    (congrArg (galPoints (H.G v).dual σ) (y.2 v)).trans rfl⟩
  map_one' := by ext1; funext v; exact map_one _
  map_mul' x y := by ext1; funext v; exact map_mul _ _ _

omit [NeZero p] in
/-- **Galois equivariance**: `⟨σx, σy⟩_v = σ ⟨x, y⟩_v`. -/
theorem tatePairing_gal (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : H.TateModule (PadicAlgCl p)) (y : H.DualTate (PadicAlgCl p)) (v : ℕ) :
    (H.G v).pairing (PadicAlgCl p) ((H.galTate σ x).1 v) ((H.galDualTate σ y).1 v) =
      σ ((H.G v).pairing (PadicAlgCl p) (x.1 v) (y.1 v)) :=
  (H.G v).pairing_postComp (PadicAlgCl p) (σ : PadicAlgCl p →ₐ[K] PadicAlgCl p) _ _

/-- The Cartier pairing with values in `ℤ_p`, via `RootSys p ℚ̄_p ≃ ℤ_p`. -/
def tatePairingZp (x : H.TateModule (PadicAlgCl p)) (y : H.DualTate (PadicAlgCl p)) : ℤ_[p] :=
  Multiplicative.toAdd (rootSysEquiv.symm (H.tatePairing (PadicAlgCl p) x y))

theorem tatePairingZp_add_left (x x' : H.TateModule (PadicAlgCl p))
    (y : H.DualTate (PadicAlgCl p)) :
    H.tatePairingZp (x * x') y = H.tatePairingZp x y + H.tatePairingZp x' y := by
  simp [tatePairingZp]

theorem tatePairingZp_add_right (x : H.TateModule (PadicAlgCl p))
    (y y' : H.DualTate (PadicAlgCl p)) :
    H.tatePairingZp x (y * y') = H.tatePairingZp x y + H.tatePairingZp x y' := by
  simp [tatePairingZp]

/-- **The Cartier pairing takes values in `ℤ_p(1)`**: `⟨σx, σy⟩ = χ(σ) ⟨x, y⟩` for
`σ ∈ Gal(ℚ̄_p/K)`, `K ⊇ ℚ_p` (`χ` of `σ|_{ℚ_p}`). -/
theorem tatePairingZp_galOver [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : H.TateModule (PadicAlgCl p)) (y : H.DualTate (PadicAlgCl p)) :
    H.tatePairingZp (H.galTate σ x) (H.galDualTate σ y) =
      ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * H.tatePairingZp x y := by
  set a := H.tatePairingZp x y
  have ha : H.tatePairing (PadicAlgCl p) x y = rootSysEquiv (Multiplicative.ofAdd a) := by
    simp [a, tatePairingZp]
  have key : rootSysEquiv.symm (H.tatePairing (PadicAlgCl p) (H.galTate σ x) (H.galDualTate σ y))
      = Multiplicative.ofAdd (((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * a) := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext; funext v; apply Subtype.ext; apply Units.ext
    rw [tatePairing_val, tatePairing_gal, ← tatePairing_val, ha]
    change (σ.restrictScalars ℚ_[p]) (eps v ^ expo a v) =
      eps v ^ expo (((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) * a) v
    exact gal_eps_pow _ a v
  unfold tatePairingZp
  rw [key]
  rfl

/-- **The Cartier pairing takes values in `ℤ_p(1)`**: `⟨σx, σy⟩ = χ(σ) ⟨x, y⟩`. -/
theorem tatePairingZp_gal (H : PDivGroup ℚ_[p] p) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : H.TateModule (PadicAlgCl p)) (y : H.DualTate (PadicAlgCl p)) :
    H.tatePairingZp (H.galTate σ x) (H.galDualTate σ y) =
      ((chi σ : ℤ_[p]ˣ) : ℤ_[p]) * H.tatePairingZp x y :=
  H.tatePairingZp_galOver σ x y

end PDivGroup

end PadicHodge
