/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateFree

/-!
# Perfectness of the Cartier pairing on Tate modules

([Stix, §11.2.2, Cor. 85], [Hong, Prop. 3.4.6]: `T_p(G^∨) ≅ Hom_{ℤ_p}(T_p G, ℤ_p(1))`.) For a
`p`-divisible group `G` of height `h` over `ℚ_p`, choose `t_1, …, t_h ∈ T_p G(ℚ̄_p)` such that
`a ↦ ∏ t_i^{a_i}` is an isomorphism `ℤ_p^h ≅ T_p G(ℚ̄_p)` (`exists_tateBasis`). Then
`y ↦ (⟨t_i, y⟩)_i` is an isomorphism `T_p(G^∨)(ℚ̄_p) = DualTate G ≅ ℤ_p^h`
(`dualTateCoord_bijective`), i.e. the Cartier pairing `T_p G × T_p G^∨ → ℤ_p(1)`
(`tatePairingZp`, Galois equivariant by `tatePairingZp_gal`) is perfect. Standard argument,
written up here:

* injectivity: if `⟨t_i, y⟩ = 0` for all `i`, then at each level `⟨(t_i)_v, y_v⟩_v = 1`, and the
  `(t_i)_v` generate `G_v(ℚ̄_p)`, so `y_v = 1` by perfectness at level `v`
  (`pairing_injective_right`);
* surjectivity: for `a ∈ ℤ_p^h`, perfectness at level `v` (`levelPairingHom_bijective`) gives
  `y_v ∈ G_v^∨(ℚ̄_p)` with `⟨(t_i)_v, y_v⟩ = ε_v^{a_i}` (`exists_dual_level`); these are
  compatible (`y_v = i_v^∨ y_{v+1}`, checked on the generators `(t_i)_v`, using
  `i_v((t_i)_v) = (t_i)_{v+1}^p` and `ε_{v+1}^p = ε_v`).
-/

noncomputable section

open WithConv

namespace PadicHodge

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup ℚ_[p] p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- A `ℤ_p`-basis of `T_p G(ℚ̄_p)` whose reductions are bases of the `G_v(ℚ̄_p)`. -/
theorem exists_tateBasis : ∃ t : Fin G.height → G.TateModule (PadicAlgCl p),
    (∀ v, Function.Bijective (G.phiLevel (PadicAlgCl p) t v)) ∧
      Function.Bijective (G.phi (PadicAlgCl p) t) := by
  obtain ⟨e, he⟩ := G.exists_basis_level_one (PadicAlgCl p)
    (by rw [G.card_points_padicAlgCl, mul_one])
  choose t ht using fun i =>
    TateModule.proj_surjective G _ G.quot_surjective_padicAlgCl 1 (e i)
  have hbasis : ∀ d : Fin G.height → ℕ, (∀ i, d i < p) →
      ∏ i, ((t i).1 1) ^ d i = 1 → ∀ i, d i = 0 := by
    intro d hd hprod
    apply he d hd
    simpa [← ht] using hprod
  exact ⟨t, fun v => G.phiLevel_bijective _ t G.card_points_padicAlgCl rfl hbasis v,
    G.phi_bijective _ t G.card_points_padicAlgCl rfl hbasis⟩

variable {G}

section Basis

variable (t : Fin G.height → G.TateModule (PadicAlgCl p))
  (ht : ∀ v, Function.Bijective (G.phiLevel (PadicAlgCl p) t v))

include ht

omit ht in
theorem pairing_phiLevel (v : ℕ) (c : Multiplicative (Fin G.height → ZMod (p ^ v)))
    (y : (G.G v).dual.points (PadicAlgCl p)) :
    (G.G v).pairing _ (G.phiLevel _ t v c) y =
      ∏ i, (G.G v).pairing _ ((t i).1 v) y ^ (Multiplicative.toAdd c i).val := by
  rw [phiLevel_apply, ← cartierPairingBase_apply, map_prod, MonoidHom.finsetProd_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, MonoidHom.pow_apply]
  rfl

/-- Two points of `G_v^∨(ℚ̄_p)` with the same pairings with the `(t_i)_v` agree. -/
theorem dual_eq_of_pairing_basis (v : ℕ) {y y' : (G.G v).dual.points (PadicAlgCl p)}
    (h : ∀ i, (G.G v).pairing _ ((t i).1 v) y = (G.G v).pairing _ ((t i).1 v) y') : y = y' := by
  refine (G.G v).pairing_injective_right (G.card_points_eq_order v) fun x => ?_
  obtain ⟨c, rfl⟩ := (ht v).2 x
  rw [pairing_phiLevel t, pairing_phiLevel t]
  simp_rw [h]

omit ht in
/-- `(t_i)_v` is the image of the `i`-th standard basis vector. -/
theorem phiLevel_single (v : ℕ) (i : Fin G.height) :
    G.phiLevel _ t v (Multiplicative.ofAdd (Pi.single i 1)) = (t i).1 v := by
  rw [phiLevel_apply]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp only [toAdd_ofAdd, Pi.single_eq_same]
  rw [ZMod.val_one_eq_one_mod, pow_mod_eq (G.pow_eq_one v _ _), pow_one]

/-- Points of `G_v^∨(ℚ̄_p)` with prescribed pairings with the `(t_i)_v`. -/
theorem exists_dual_level (v : ℕ) (ζ : Fin G.height → PadicAlgCl p)
    (hζ : ∀ i, ζ i ^ (p ^ v) = 1) :
    ∃ y : (G.G v).dual.points (PadicAlgCl p), ∀ i, (G.G v).pairing _ ((t i).1 v) y = ζ i := by
  let e := MulEquiv.ofBijective _ (ht v)
  let χ₀ : Multiplicative (Fin G.height → ZMod (p ^ v)) →* PadicAlgCl p :=
    { toFun := fun c => ∏ i, ζ i ^ (Multiplicative.toAdd c i).val
      map_one' := by simp
      map_mul' := fun c c' => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← pow_add, toAdd_mul, Pi.add_apply, ZMod.val_add, pow_mod_eq (hζ i)] }
  obtain ⟨y, hy⟩ := (G.levelPairingHom_bijective v).2 (χ₀.comp e.symm.toMonoidHom)
  refine ⟨y, fun i => ?_⟩
  have := DFunLike.congr_fun hy ((t i).1 v)
  change (G.G v).pairing _ ((t i).1 v) y = _ at this
  rw [this, ← phiLevel_single t v i]
  change χ₀ (e.symm (e (Multiplicative.ofAdd (Pi.single i 1)))) = _
  rw [MulEquiv.symm_apply_apply]
  change ∏ j, ζ j ^ (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single i 1 :
    Fin G.height → ZMod (p ^ v))) j).val = _
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp only [toAdd_ofAdd, Pi.single_eq_same]
  rw [ZMod.val_one_eq_one_mod, pow_mod_eq (hζ i), pow_one]

/-- The coordinates `y ↦ (⟨t_i, y⟩)_i` of the dual Tate module. -/
def dualTateCoord : G.DualTate (PadicAlgCl p) →* Multiplicative (Fin G.height → ℤ_[p]) where
  toFun y := Multiplicative.ofAdd fun i => G.tatePairingZp (t i) y
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [tatePairingZp]
  map_mul' y y' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    exact G.tatePairingZp_add_right (t i) y y'

omit ht in
theorem dualTateCoord_apply (y : G.DualTate (PadicAlgCl p)) (i : Fin G.height) :
    Multiplicative.toAdd (dualTateCoord t y) i = G.tatePairingZp (t i) y := rfl

omit ht in
/-- `tatePairingZp x y = a` iff the level pairings are `ε_v^{a mod p^v}`. -/
theorem tatePairingZp_eq_iff (x : G.TateModule (PadicAlgCl p)) (y : G.DualTate (PadicAlgCl p))
    (a : ℤ_[p]) : G.tatePairingZp x y = a ↔
      ∀ v, (G.G v).pairing _ (x.1 v) (y.1 v) = eps v ^ expo a v := by
  have key : G.tatePairingZp x y = a ↔
      G.tatePairing (PadicAlgCl p) x y = rootSysEquiv (Multiplicative.ofAdd a) := by
    rw [tatePairingZp]
    constructor <;> intro h
    · rw [← h, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    · rw [h, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  rw [key]
  constructor
  · intro h v
    rw [← tatePairing_val, h]
    rfl
  · intro h
    apply Subtype.ext; funext v; apply Subtype.ext; apply Units.ext
    rw [tatePairing_val, h v]
    rfl

/-- **Perfectness of the Cartier pairing on Tate modules**: `T_p(G^∨)(ℚ̄_p) ≅ ℤ_p^h` via
`y ↦ (⟨t_i, y⟩)_i` for a basis `(t_i)` of `T_p G(ℚ̄_p)`. -/
theorem dualTateCoord_bijective : Function.Bijective (dualTateCoord t) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro y hy
    apply Subtype.ext
    funext v
    apply dual_eq_of_pairing_basis t ht v
    intro i
    have h0 : G.tatePairingZp (t i) y = 0 := by
      have := congrFun (congrArg Multiplicative.toAdd hy) i
      rw [dualTateCoord_apply, toAdd_one, Pi.zero_apply] at this
      exact this
    rw [tatePairingZp_eq_iff] at h0
    rw [h0 v]
    change _ = (G.G v).pairing _ ((t i).1 v) 1
    rw [pairing_one_right, expo, map_zero, ZMod.val_zero, pow_zero]
  · intro a
    have hζ : ∀ v i, (eps (p := p) v ^ expo (Multiplicative.toAdd a i) v) ^ (p ^ v) = 1 := by
      intro v i
      rw [← pow_mul, mul_comm, pow_mul, eps_pow_card, one_pow]
    choose y hy using fun v => exists_dual_level t ht v _ (hζ v)
    have hcompat : ∀ v, y v = (G.incl v).dual.mapPoints _ (y (v + 1)) := by
      intro v
      apply dual_eq_of_pairing_basis t ht v
      intro i
      rw [hy v i, ← pairing_dual, (t i).2 v, ← cartierPairingBase_apply, map_pow,
        MonoidHom.pow_apply, cartierPairingBase_apply, hy (v + 1) i, eps_pow_expo_compat]
    refine ⟨⟨y, hcompat⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    rw [dualTateCoord_apply, tatePairingZp_eq_iff]
    exact fun v => hy v i

end Basis

/-- **`T_p(G^∨)(ℚ̄_p) ≅ Hom_{ℤ_p}(T_p G(ℚ̄_p), ℤ_p(1))`** in coordinates: there is a `ℤ_p`-basis
`(t_i)` of `T_p G(ℚ̄_p)` such that `y ↦ (⟨t_i, y⟩)_i` is an isomorphism `T_p(G^∨)(ℚ̄_p) ≅ ℤ_p^h`. -/
theorem exists_perfect_tatePairing (G : PDivGroup ℚ_[p] p) :
    ∃ t : Fin G.height → G.TateModule (PadicAlgCl p),
      Function.Bijective (G.phi (PadicAlgCl p) t) ∧ Function.Bijective (dualTateCoord t) := by
  obtain ⟨t, ht, hphi⟩ := G.exists_tateBasis
  exact ⟨t, hphi, dualTateCoord_bijective t ht⟩

/-- `T_p(G^∨)(ℚ̄_p) ≅ ℤ_p^h`: the Cartier dual has the same height. -/
theorem nonempty_dualTate_equiv (G : PDivGroup ℚ_[p] p) :
    Nonempty (G.dualPDiv.TateModule (PadicAlgCl p) ≃* Multiplicative (Fin G.height → ℤ_[p])) := by
  obtain ⟨t, -, h⟩ := G.exists_perfect_tatePairing
  rw [tateModule_dualPDiv]
  exact ⟨MulEquiv.ofBijective _ h⟩

end PDivGroup

end PadicHodge
