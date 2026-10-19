/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.GaloisDescent
import PadicHodge.GroupScheme.SubPDiv
import PadicHodge.GroupScheme.TateRep

/-!
# [Hong, Prop. 2.1.14] for direct summands, and [Hong, Prop. 3.5.3]

Over a field `F` with `ℚ̄_p / F` Galois (`Ω = ℚ̄_p`):

* `FFGroupScheme.vanIdeal S`: the vanishing ideal `I_S ⊆ O(G)` of a subgroup `S ⊆ G(Ω)`. For `S`
  `Γ_F`-stable and `G` killed by `n ≠ 0`, the indicator function of `S` lies in `O(G)`
  (`exists_indicator`, Galois descent via `exists_eq_of_equivariant`), so `I_S = (1 - e)` and
  `I_S` is a Hopf ideal (`vanIdeal_isHopfIdeal`; the comultiplication condition is checked on
  `(G × G)(Ω)` after multiplying by `e ⊗ e`).
* `FFGroupScheme.sub S`: the closed subgroup scheme `G_S = Spec O(G)/I_S`, the closed immersion
  `subHom`, `G_S(Ω) = S` (`mem_range_subHom_iff_qbar`), `|G_S| = #S` (`order_sub`);
  `subMap`: the restriction `G_S → G'_{S'}` of `f : G → G'` with `f(S) ⊆ S'`;
  `mem_range_subHom_of_map`: if `S = f⁻¹(S')` on `Ω`-points then `G_S = f⁻¹(G'_{S'})` on
  `T`-points for every `F`-algebra `T`.
* `PDivGroup.tateSub M`: for a `Γ_F`-stable saturated subgroup `M ⊆ T_p G(Ω)`, the `p`-divisible
  group with layers `G_{v,S_v}`, `S_v = im(M → G_v(Ω))`, of height `r` with `#S_1 = p^r`
  (`#S_{v+1} = #S_v · #S_1`, `card_levelSub_succ`); the kernel condition
  `H̃_{v+1}[p^v] = H̃_v` comes from `i_v⁻¹(S_{v+1}) = S_v` (`incl_mem_levelSub_iff`, saturation)
  and `mem_range_subHom_of_map`. `tateSubHom : tateSub M → G` has closed immersions as layers.
* **`PDivGroup.exists_tateSub_of_isCompl`** ([Hong, Prop. 2.1.14], essential surjectivity onto
  `Γ_F`-stable `ℤ_p`-direct summands): `T_p(ι)` is injective with image `M`.
* **`PDivGroup.exists_pdivGroup_of_isCompl`** ([Hong, Prop. 3.5.3]): over a local PID `R` with
  fraction field `K`, a `Γ_K`-stable `ℤ_p`-direct summand `M ⊆ T_p G(ℚ̄_p)` is `T_p H` for a
  `p`-divisible group `H` over `R` with `ι : H → G` (via `Hom.exists_pdivGroup_closure`).
* `subHeight_summandSub`, `exists_tateSub_of_isCompl_height`, `exists_pdivGroup_of_isCompl_height`:
  the height of `H̃` (resp. `H`) is `rank_{ℤ_p} M` (`S_1 ≅ M / pM`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 1.3.1, Prop. 2.1.14, Prop. 3.5.3.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {F : Type} [Field F] [Algebra F (PadicAlgCl p)]

local notation "Ω" => PadicAlgCl p

/-! ### The vanishing ideal of a subgroup of `G(Ω)` -/

section Van

variable (G : FFGroupScheme F) (S : Subgroup (G.points (PadicAlgCl p)))

/-- The vanishing ideal `I_S = {a ∈ O(G) | a(s) = 0 ∀ s ∈ S}` of a subgroup `S ⊆ G(Ω)`. -/
def vanIdeal : Ideal G.A :=
  RingHom.ker (AlgHom.pi fun s : S => ofConv (s : G.points Ω))

variable {G S} in
theorem mem_vanIdeal {a : G.A} : a ∈ G.vanIdeal S ↔ ∀ s ∈ S, ofConv s a = 0 := by
  rw [vanIdeal, RingHom.mem_ker]
  constructor
  · intro h s hs
    exact congrFun h ⟨s, hs⟩
  · intro h
    funext s
    exact h s.1 s.2

theorem galPoints_inv_galPoints (σ : Ω ≃ₐ[F] Ω) (x : G.points Ω) :
    galPoints G σ⁻¹ (galPoints G σ x) = x := by
  apply WithConv.ofConv_injective
  ext a
  change σ⁻¹ (σ (ofConv x a)) = ofConv x a
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

variable {n : ℕ} (hn : (n : PadicAlgCl p) ≠ 0) (hG : G.KilledBy n) [IsGalois F (PadicAlgCl p)]
  (hS : ∀ (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) x, x ∈ S → galPoints G σ x ∈ S)

include hn hG hS in
/-- **The indicator function of a `Γ_F`-stable subset of `G(Ω)` lies in `O(G)`** (Galois
descent, `exists_eq_of_equivariant`). -/
theorem exists_indicator : ∃ e : G.A, (∀ x ∈ S, ofConv x e = 1) ∧ (∀ x ∉ S, ofConv x e = 0) := by
  classical
  obtain ⟨e, he⟩ := exists_eq_of_equivariant hn hG (fun x => if x ∈ S then (1 : Ω) else 0)
    fun σ x => by
      by_cases hx : x ∈ S
      · rw [if_pos (hS σ x hx), if_pos hx, map_one]
      · have : galPoints G σ x ∉ S := fun h => hx (by
          have := hS σ⁻¹ _ h
          rwa [galPoints_inv_galPoints] at this)
        rw [if_neg this, if_neg hx, map_zero]
  refine ⟨e, fun x hx => ?_, fun x hx => ?_⟩
  · rw [he, if_pos hx]
  · rw [he, if_neg hx]

omit [IsGalois F (PadicAlgCl p)] in
variable {G S} in
theorem sub_one_mem_vanIdeal {e : G.A} (he : ∀ x ∈ S, ofConv x e = 1) :
    e - 1 ∈ G.vanIdeal S :=
  mem_vanIdeal.2 fun s hs => by rw [map_sub, map_one, he s hs, sub_self]

omit [IsGalois F (PadicAlgCl p)] in
include hn hG in
variable {G S} in
theorem mul_eq_of_mem_vanIdeal {e : G.A} (he' : ∀ x ∉ S, ofConv x e = 0) {a : G.A}
    (ha : a ∈ G.vanIdeal S) : (1 - e) * a = a := by
  refine eq_of_points_eq hn hG fun x => ?_
  rw [map_mul, map_sub, map_one]
  by_cases hx : x ∈ S
  · rw [mem_vanIdeal.1 ha x hx, mul_zero]
  · rw [he' x hx, sub_zero, one_mul]

include hn hG hS in
/-- **`I_S` is a Hopf ideal** for a `Γ_F`-stable subgroup `S`. -/
theorem vanIdeal_isHopfIdeal : (G.vanIdeal S).IsHopfIdeal F where
  counit_eq_zero x hx := by
    have h := mem_vanIdeal.1 hx 1 S.one_mem
    have h1 : ofConv (1 : G.points Ω) x = algebraMap F Ω (counit x) := rfl
    rw [h1] at h
    exact (algebraMap F Ω).injective (h.trans (map_zero _).symm)
  map_mkQ_comul_eq_zero x hx := by
    obtain ⟨e, he1, he0⟩ := G.exists_indicator S hn hG hS
    have hx' : x ∈ G.vanIdeal S := hx
    let q : G.A ⊗[F] G.A →ₐ[F] (G.A ⧸ G.vanIdeal S) ⊗[F] (G.A ⧸ G.vanIdeal S) :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F (G.vanIdeal S))
        (Ideal.Quotient.mkₐ F (G.vanIdeal S))
    have hq : ∀ w, TensorProduct.map ((G.vanIdeal S).restrictScalars F).mkQ
        ((G.vanIdeal S).restrictScalars F).mkQ w = q w := fun w => rfl
    have hme : Ideal.Quotient.mk (G.vanIdeal S) e = 1 := by
      rw [← map_one (Ideal.Quotient.mk (G.vanIdeal S)), Ideal.Quotient.eq]
      exact sub_one_mem_vanIdeal he1
    have hz : (e ⊗ₜ[F] e) * comul x = 0 := by
      refine eq_of_points_eq (G := G.prod G) hn (hG.prod hG) fun z => ?_
      obtain ⟨⟨s, t⟩, rfl⟩ := (G.prodPointsEquiv G Ω).symm.surjective z
      rw [map_mul, map_zero, prodPointsEquiv_symm_apply]
      have : ofConv ((G.prodPointsEquiv G Ω).symm (s, t)) (comul x) = ofConv (s * t) x := by
        rw [AlgHom.convMul_apply]
        rfl
      rw [this]
      by_cases hs : s ∈ S
      · by_cases ht : t ∈ S
        · rw [mem_vanIdeal.1 hx' _ (S.mul_mem hs ht), mul_zero]
        · rw [he0 t ht, mul_zero, zero_mul]
      · rw [he0 s hs, zero_mul, zero_mul]
    rw [hq]
    have : q (comul x) = q ((e ⊗ₜ[F] e) * comul x) := by
      rw [map_mul, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, hme,
        Algebra.TensorProduct.one_def.symm, one_mul]
    rw [this, hz]
    exact map_zero q
  antipode_mem x hx := by
    refine mem_vanIdeal.2 fun s hs => ?_
    have h : ofConv s (antipode F x) = ofConv s⁻¹ x := rfl
    rw [h]
    exact mem_vanIdeal.1 hx _ (S.inv_mem hs)

end Van

/-! ### The closed subgroup scheme -/

instance isCocomm_quotient (G : FFGroupScheme F) (I : Ideal G.A) [I.IsHopfIdeal F] :
    IsCocomm F (G.A ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    change TensorProduct.comm F _ _ (comul (R := F) (Ideal.Quotient.mk I a)) =
      comul (R := F) (Ideal.Quotient.mk I a)
    rw [Bialgebra.Quotient.comul_mk]
    have : ∀ w : G.A ⊗[F] G.A, TensorProduct.comm F _ _ (TensorProduct.map
        (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap w) =
        TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap
          (Ideal.Quotient.mkₐ F I).toLinearMap (TensorProduct.comm F _ _ w) := by
      intro w
      induction w with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a b => rfl
    rw [this, comm_comul]

instance finite_quotient (G : FFGroupScheme F) (I : Ideal G.A) : Module.Finite F (G.A ⧸ I) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ F I).toLinearMap Ideal.Quotient.mk_surjective

section Sub

variable (G : FFGroupScheme F) (S : Subgroup (G.points (PadicAlgCl p)))
  (hI : (G.vanIdeal S).IsHopfIdeal F)

/-- **The closed subgroup scheme `Spec O(G)/I_S` of `G` cut out by a `Γ_F`-stable subgroup
`S ⊆ G(Ω)`.** -/
def sub : FFGroupScheme F :=
  haveI := hI
  { A := G.A ⧸ G.vanIdeal S }

/-- The closed immersion `G_S → G`. -/
def subHom : Hom (G.sub S hI) G :=
  haveI := hI
  Bialgebra.Quotient.mkBialgHom (G.vanIdeal S)

theorem subHom_apply (a : G.A) : G.subHom S hI a = Ideal.Quotient.mk (G.vanIdeal S) a := rfl

theorem subHom_surjective : Function.Surjective (G.subHom S hI) :=
  Ideal.Quotient.mk_surjective

theorem subHom_mapPoints_injective (T : Type*) [CommRing T] [Algebra F T] :
    Function.Injective ((G.subHom S hI).mapPoints T) := by
  intro x y h
  apply WithConv.ofConv_injective
  ext a
  obtain ⟨b, rfl⟩ := G.subHom_surjective S hI a
  exact congrArg (fun φ : G.points T => ofConv φ b) h

/-- The `T`-points of `G_S`: the points of `G` vanishing on `I_S`. -/
theorem mem_range_subHom_iff {T : Type*} [CommRing T] [Algebra F T] (y : G.points T) :
    (∃ z, (G.subHom S hI).mapPoints T z = y) ↔ ∀ a ∈ G.vanIdeal S, ofConv y a = 0 := by
  constructor
  · rintro ⟨z, rfl⟩ a ha
    change ofConv z (G.subHom S hI a) = 0
    rw [show G.subHom S hI a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  · intro h
    refine ⟨toConv (Ideal.Quotient.liftₐ (G.vanIdeal S) (ofConv y) h), ?_⟩
    apply WithConv.ofConv_injective
    ext a
    rfl

variable {G S} {n : ℕ} (hn : (n : PadicAlgCl p) ≠ 0) (hG : G.KilledBy n)
  [IsGalois F (PadicAlgCl p)]
  (hS : ∀ (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) x, x ∈ S → galPoints G σ x ∈ S)

include hn hG hS in
/-- **`G_S(Ω) = S`.** -/
theorem mem_range_subHom_iff_qbar (x : G.points Ω) :
    (∃ z, (G.subHom S hI).mapPoints Ω z = x) ↔ x ∈ S := by
  rw [mem_range_subHom_iff]
  constructor
  · intro h
    obtain ⟨e, he1, he0⟩ := G.exists_indicator S hn hG hS
    by_contra hx
    have h1 := h _ (sub_one_mem_vanIdeal he1)
    rw [map_sub, map_one, he0 x hx, zero_sub, neg_eq_zero] at h1
    exact one_ne_zero h1
  · intro hx a ha
    exact mem_vanIdeal.1 ha x hx

omit [IsGalois F (PadicAlgCl p)] in
include hG in
theorem sub_killedBy : (G.sub S hI).KilledBy n :=
  KilledBy.of_injective (G.subHom S hI) (fun T _ _ => G.subHom_mapPoints_injective S hI T) hG

/-- `G_S(Ω) ≃* S`. -/
def subPointsEquiv : (G.sub S hI).points Ω ≃* S :=
  (MulEquiv.ofBijective ((G.subHom S hI).mapPoints Ω).rangeRestrict
    ⟨fun x y h => G.subHom_mapPoints_injective S hI Ω (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩).trans
    (MulEquiv.subgroupCongr (Subgroup.ext fun x => by
      rw [MonoidHom.mem_range]; exact mem_range_subHom_iff_qbar hI hn hG hS x))

include hn hG hS in
/-- **The order of `G_S` is `#S`.** -/
theorem order_sub : (G.sub S hI).order = Nat.card S := by
  rw [← (sub_killedBy hI hG).card_points Ω hn]
  exact Nat.card_congr (subPointsEquiv hI hn hG hS).toEquiv

end Sub

/-! ### Maps between closed subgroup schemes -/

section Map

variable {G G' : FFGroupScheme F} {S : Subgroup (G.points (PadicAlgCl p))}
  {S' : Subgroup (G'.points (PadicAlgCl p))}
  (hI : (G.vanIdeal S).IsHopfIdeal F) (hI' : (G'.vanIdeal S').IsHopfIdeal F) (f : Hom G G')
  (hf : ∀ z ∈ S, f.mapPoints (PadicAlgCl p) z ∈ S')

include hf in
theorem vanIdeal_le_comap : G'.vanIdeal S' ≤ (G.vanIdeal S).comap (f : G'.A →ₐ[F] G.A) :=
  fun _ ha => mem_vanIdeal.2 fun s hs => mem_vanIdeal.1 ha _ (hf s hs)

/-- The algebra map of `G_S → G'_{S'}`. -/
def subMapAlg : (G'.sub S' hI').A →ₐ[F] (G.sub S hI).A :=
  Ideal.quotientMapₐ (G.vanIdeal S) (f : G'.A →ₐ[F] G.A) (vanIdeal_le_comap f hf)

theorem subMapAlg_mk (a : G'.A) :
    subMapAlg hI hI' f hf (G'.subHom S' hI' a) = G.subHom S hI (f a) := rfl

/-- **The restriction `G_S → G'_{S'}` of `f : G → G'` when `f(S) ⊆ S'`.** -/
def subMap : Hom (G.sub S hI) (G'.sub S' hI') :=
  BialgHom.ofAlgHom (subMapAlg hI hI' f hf)
    (by
      haveI := hI; haveI := hI'
      refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => ?_)
      change counit (R := F) (Ideal.Quotient.mk (G.vanIdeal S) (f a)) =
        counit (R := F) (Ideal.Quotient.mk (G'.vanIdeal S') a)
      rw [Bialgebra.Quotient.counit_mk, Bialgebra.Quotient.counit_mk]
      exact CoalgHomClass.counit_comp_apply f a)
    (by
      haveI := hI; haveI := hI'
      refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => ?_)
      change Algebra.TensorProduct.map (subMapAlg hI hI' f hf) (subMapAlg hI hI' f hf)
          (comul (R := F) (G'.subHom S' hI' a)) = comul (R := F) (G.subHom S hI (f a))
      have h1 : comul (R := F) (G'.subHom S' hI' a) =
          TensorProduct.map (G'.subHom S' hI' : G'.A →ₗ[F] (G'.sub S' hI').A)
            (G'.subHom S' hI' : G'.A →ₗ[F] (G'.sub S' hI').A) (comul a) :=
        (LinearMap.congr_fun (CoalgHomClass.map_comp_comul (G'.subHom S' hI')) a).symm
      have h2 : comul (R := F) (G.subHom S hI (f a)) =
          TensorProduct.map (G.subHom S hI : G.A →ₗ[F] (G.sub S hI).A)
            (G.subHom S hI : G.A →ₗ[F] (G.sub S hI).A) (comul (f a)) :=
        (LinearMap.congr_fun (CoalgHomClass.map_comp_comul (G.subHom S hI)) (f a)).symm
      have hc : comul (R := F) (f a) =
          TensorProduct.map (f : G'.A →ₗ[F] G.A) (f : G'.A →ₗ[F] G.A) (comul a) :=
        (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) a).symm
      rw [h1, h2, hc]
      induction comul (R := F) a with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul b c => rfl)

theorem subMap_apply (a : G'.A) :
    subMap hI hI' f hf (G'.subHom S' hI' a) = G.subHom S hI (f a) := rfl

/-- `ι' ∘ f_S = f ∘ ι`. -/
theorem subMap_comm :
    BialgHom.comp (subMap hI hI' f hf) (G'.subHom S' hI') =
      BialgHom.comp (G.subHom S hI) f :=
  BialgHom.ext fun _ => rfl

theorem subMap_mapPoints {T : Type*} [CommRing T] [Algebra F T] (z : (G.sub S hI).points T) :
    (G'.subHom S' hI').mapPoints T ((subMap hI hI' f hf).mapPoints T z) =
      f.mapPoints T ((G.subHom S hI).mapPoints T z) := rfl

theorem subMap_surjective (hsurj : Function.Surjective f) :
    Function.Surjective (subMap hI hI' f hf) := by
  intro b
  obtain ⟨a, rfl⟩ := subHom_surjective G S hI b
  obtain ⟨a', rfl⟩ := hsurj a
  exact ⟨G'.subHom S' hI' a', rfl⟩

end Map

/-! ### Scheme-theoretic preimages -/

section Preimage

variable {G G' : FFGroupScheme F} {S : Subgroup (G.points (PadicAlgCl p))}
  {S' : Subgroup (G'.points (PadicAlgCl p))}
  (hI : (G.vanIdeal S).IsHopfIdeal F) (hI' : (G'.vanIdeal S').IsHopfIdeal F) (f : Hom G G')
  {n n' : ℕ} (hn : (n : PadicAlgCl p) ≠ 0) (hG : G.KilledBy n) (hn' : (n' : PadicAlgCl p) ≠ 0)
  (hG' : G'.KilledBy n')
  [IsGalois F (PadicAlgCl p)]
  (hS : ∀ (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) x, x ∈ S → galPoints G σ x ∈ S)
  (hS' : ∀ (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) x, x ∈ S' → galPoints G' σ x ∈ S')
  (hf : ∀ z : G.points (PadicAlgCl p), f.mapPoints (PadicAlgCl p) z ∈ S' ↔ z ∈ S)

include hn hG hn' hG' hS hS' hf in
/-- **`G_S = f⁻¹(G'_{S'})` scheme-theoretically when `S = f⁻¹(S')` on `Ω`-points**: a `T`-point
of `G` whose image lies in `G'_{S'}` lies in `G_S`, for every `F`-algebra `T`. -/
theorem mem_range_subHom_of_map {T : Type*} [CommRing T] [Algebra F T] (y : G.points T)
    (hy : ∃ z', (G'.subHom S' hI').mapPoints T z' = f.mapPoints T y) :
    ∃ z, (G.subHom S hI).mapPoints T z = y := by
  obtain ⟨e, he1, he0⟩ := G.exists_indicator S hn hG hS
  obtain ⟨e', he1', he0'⟩ := G'.exists_indicator S' hn' hG' hS'
  have hfe : f e' = e := by
    refine eq_of_points_eq hn hG fun x => ?_
    change ofConv (f.mapPoints Ω x) e' = ofConv x e
    by_cases hx : x ∈ S
    · rw [he1' _ ((hf x).2 hx), he1 x hx]
    · rw [he0' _ (fun h => hx ((hf x).1 h)), he0 x hx]
  have hy' := (G'.mem_range_subHom_iff S' hI' _).1 hy
  have h1 : ofConv y (1 - e) = 0 := by
    have := hy' _ (neg_mem (sub_one_mem_vanIdeal he1'))
    rw [neg_sub] at this
    change ofConv y (f (1 - e')) = 0 at this
    rwa [map_sub, map_one, hfe] at this
  refine (G.mem_range_subHom_iff S hI y).2 fun a ha => ?_
  rw [← mul_eq_of_mem_vanIdeal hn hG he0 ha, map_mul, h1, zero_mul]

end Preimage

end FFGroupScheme


/-! ### Levelwise injective homomorphisms of `p`-divisible groups -/

namespace PDivGroup

open FFGroupScheme

section Levels

variable {R : Type u} [CommRing R] {p : ℕ} {H G : PDivGroup R p} (φ : Hom H G)
  (S : Type u) [CommRing S] [Algebra R S]

theorem Hom.mapTate_injective_of_levels
    (hinj : ∀ v, Function.Injective ((φ.f v).mapPoints S)) :
    Function.Injective (φ.mapTate S) := fun _ _ h =>
  Subtype.ext (funext fun v => hinj v (congrArg (fun z : G.TateModule S => z.1 v) h))

/-- With levelwise injective maps, `x ∈ T_p G(S)` is in the image of `T_p H(S)` iff each
level `x_v` is in the image of `H_v(S)`. -/
theorem Hom.mem_range_mapTate_iff_levels
    (hinj : ∀ v, Function.Injective ((φ.f v).mapPoints S)) (x : G.TateModule S) :
    (∃ t, φ.mapTate S t = x) ↔ ∀ v, ∃ y, (φ.f v).mapPoints S y = x.1 v := by
  constructor
  · rintro ⟨t, rfl⟩ v
    exact ⟨t.1 v, rfl⟩
  · intro hx
    choose y hy using hx
    refine ⟨⟨y, fun v => hinj (v + 1) ?_⟩, Subtype.ext (funext hy)⟩
    rw [← φ.incl_mapPoints, hy, map_pow, hy, x.2 v]

end Levels

/-! ### The `p`-divisible subgroup attached to a `Γ_F`-stable saturated subgroup of `T_p G` -/

variable {p : ℕ} [hp : Fact p.Prime] {F : Type} [Field F] [Algebra F (PadicAlgCl p)]

local notation "Ω" => PadicAlgCl p

section Construction

variable (G : PDivGroup F p) (M : Subgroup (G.TateModule (PadicAlgCl p)))

/-- `S_v`: the image of `M` in `G_v(Ω)`. -/
def levelSub (v : ℕ) : Subgroup ((G.G v).points Ω) := M.map (TateModule.proj G Ω v)

variable {G M} in
theorem mem_levelSub {v : ℕ} {y : (G.G v).points Ω} :
    y ∈ G.levelSub M v ↔ ∃ x ∈ M, x.1 v = y :=
  Subgroup.mem_map

theorem natCast_pow_ne_zero (v : ℕ) : ((p ^ v : ℕ) : Ω) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)

omit hp [Algebra F (PadicAlgCl p)] in
theorem killedBy_level (v : ℕ) : (G.G v).KilledBy (p ^ v) :=
  KilledBy.of_pow_eq_one fun S _ _ x => G.pow_eq_one v S x

variable (hM : ∀ (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) x, x ∈ M → G.galTate σ x ∈ M)

include hM in
theorem levelSub_stable (v : ℕ) (σ : Ω ≃ₐ[F] Ω) (y : (G.G v).points Ω)
    (hy : y ∈ G.levelSub M v) : galPoints (G.G v) σ y ∈ G.levelSub M v := by
  obtain ⟨x, hx, rfl⟩ := mem_levelSub.1 hy
  exact mem_levelSub.2 ⟨G.galTate σ x, hM σ x hx, rfl⟩

variable (hsat : ∀ x : G.TateModule (PadicAlgCl p), x ^ p ∈ M → x ∈ M)

include hsat in
theorem mem_of_pow_mem (k : ℕ) (x : G.TateModule Ω) (hx : x ^ (p ^ k) ∈ M) : x ∈ M := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    refine ih (hsat _ ?_)
    rwa [← pow_mul, ← pow_succ]

theorem tate_pow_val (x : G.TateModule Ω) (n v : ℕ) : (x ^ n).1 v = (x.1 v) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Subgroup.coe_mul, Pi.mul_apply, ih]

include hsat in
/-- **`i_v^{-1}(S_{v+1}) = S_v`** (`M` saturated). -/
theorem incl_mem_levelSub_iff (v : ℕ) (z : (G.G v).points Ω) :
    (G.incl v).mapPoints Ω z ∈ G.levelSub M (v + 1) ↔ z ∈ G.levelSub M v := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  constructor
  · intro hz
    obtain ⟨m, hm, hmz⟩ := mem_levelSub.1 hz
    have h1 : m.1 1 = 1 := by
      rw [← TateModule.quotLE_apply G Ω m (show 1 ≤ v + 1 by omega), quotLE_eq_one_iff,
        Nat.add_sub_cancel, hmz, ← map_pow, G.pow_eq_one v Ω z, map_one]
    obtain ⟨y, hy⟩ := TateModule.exists_pow_eq_of_val_eq_one G Ω
      (G.quot_surjective_sepClosed Ω hpΩ) (G.card_points_sepClosed Ω hpΩ) m 1 h1
    rw [pow_one] at hy
    refine mem_levelSub.2 ⟨y, hsat y (hy ▸ hm), G.mapPoints_injective v Ω ?_⟩
    rw [y.2 v, ← hmz, ← hy, tate_pow_val]
  · intro hz
    obtain ⟨m, hm, rfl⟩ := mem_levelSub.1 hz
    exact mem_levelSub.2 ⟨m ^ p, M.pow_mem hm p, by rw [tate_pow_val, m.2 v]⟩

theorem card_eq_card_range_mul_card_ker {A B : Type*} [Group A] [Group B] (f : A →* B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

include hsat in
/-- **`#S_{v+1} = #S_v · #S_1`.** -/
theorem card_levelSub_succ (v : ℕ) :
    Nat.card (G.levelSub M (v + 1)) = Nat.card (G.levelSub M v) * Nat.card (G.levelSub M 1) := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set A := G.levelSub M (v + 1)
  let π : A →* (G.G v).points Ω := ((G.quot v).mapPoints Ω).comp A.subtype
  let Q : A →* (G.G 1).points Ω := (G.quotLE Ω (show 1 ≤ v + 1 by omega)).comp A.subtype
  let P : A →* A := powMonoidHom (p ^ v)
  have hπ : π.range = G.levelSub M v := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, hm, hma⟩ := mem_levelSub.1 a.2
      refine mem_levelSub.2 ⟨m, hm, ?_⟩
      change m.1 v = (G.quot v).mapPoints Ω a.1
      rw [← hma, ← TateModule.val_eq_quot]
    · intro hy
      obtain ⟨m, hm, rfl⟩ := mem_levelSub.1 hy
      exact ⟨⟨m.1 (v + 1), mem_levelSub.2 ⟨m, hm, rfl⟩⟩, (TateModule.val_eq_quot G m v).symm⟩
  have hQ : Q.range = G.levelSub M 1 := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, hm, hma⟩ := mem_levelSub.1 a.2
      refine mem_levelSub.2 ⟨m, hm, ?_⟩
      change m.1 1 = G.quotLE Ω _ a.1
      rw [← hma, TateModule.quotLE_apply]
    · intro hy
      obtain ⟨m, hm, rfl⟩ := mem_levelSub.1 hy
      exact ⟨⟨m.1 (v + 1), mem_levelSub.2 ⟨m, hm, rfl⟩⟩, TateModule.quotLE_apply G Ω m _⟩
  have hP : P.range = π.ker := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      change (G.quot v).mapPoints Ω ((b ^ (p ^ v) : A) : (G.G (v + 1)).points Ω) = 1
      rw [SubgroupClass.coe_pow, map_pow, G.pow_eq_one v Ω]
    · intro ha
      change (G.quot v).mapPoints Ω a.1 = 1 at ha
      obtain ⟨m, hm, hma⟩ := mem_levelSub.1 a.2
      have h1 : m.1 v = 1 := by rw [TateModule.val_eq_quot, hma, ha]
      obtain ⟨y, hy⟩ := TateModule.exists_pow_eq_of_val_eq_one G Ω
        (G.quot_surjective_sepClosed Ω hpΩ) (G.card_points_sepClosed Ω hpΩ) m v h1
      refine ⟨⟨y.1 (v + 1), mem_levelSub.2
        ⟨y, G.mem_of_pow_mem M hsat v y (hy ▸ hm), rfl⟩⟩, Subtype.ext ?_⟩
      change (y.1 (v + 1)) ^ (p ^ v) = a.1
      rw [← tate_pow_val, hy, hma]
  have hker : P.ker = Q.ker := by
    ext a
    change a ^ (p ^ v) = 1 ↔ G.quotLE Ω _ a.1 = 1
    rw [quotLE_eq_one_iff, Nat.add_sub_cancel, ← Subtype.val_inj (a := a ^ (p ^ v)),
      SubgroupClass.coe_pow, OneMemClass.coe_one]
  have h1 := card_eq_card_range_mul_card_ker π
  have h2 := card_eq_card_range_mul_card_ker P
  have h3 := card_eq_card_range_mul_card_ker Q
  rw [hπ, ← hP] at h1
  rw [hker] at h2
  rw [hQ] at h3
  have hfin : Finite ((G.G (v + 1)).points Ω) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [G.card_points_sepClosed Ω hpΩ]
    exact pow_ne_zero _ hp.out.ne_zero
  have hpos : 0 < Nat.card A := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card A * Nat.card A
      = (Nat.card (G.levelSub M v) * Nat.card P.range) *
        (Nat.card (G.levelSub M 1) * Nat.card Q.ker) := by rw [← h1, ← h3]
    _ = (Nat.card (G.levelSub M v) * Nat.card (G.levelSub M 1)) *
        (Nat.card P.range * Nat.card Q.ker) := by ring
    _ = _ := by rw [← h2]

theorem card_levelSub_zero : Nat.card (G.levelSub M 0) = 1 := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h0 := G.card_points_sepClosed Ω hpΩ 0
  rw [mul_zero, pow_zero] at h0
  have hfin : Finite ((G.G 0).points Ω) := Nat.finite_of_card_ne_zero (by rw [h0]; omega)
  refine le_antisymm ?_ Nat.card_pos
  exact h0 ▸ Subgroup.card_le_card_group _

theorem exists_card_levelSub_one : ∃ r, Nat.card (G.levelSub M 1) = p ^ r := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have h := Subgroup.card_subgroup_dvd_card (G.levelSub M 1)
  rw [G.card_points_sepClosed Ω hpΩ, mul_one] at h
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hp.out).1 h
  exact ⟨r, hr⟩

/-- The height `r` of the `p`-divisible subgroup: `#S_1 = p^r`. -/
def subHeight : ℕ := (G.exists_card_levelSub_one M).choose

theorem card_levelSub_one : Nat.card (G.levelSub M 1) = p ^ G.subHeight M :=
  (G.exists_card_levelSub_one M).choose_spec

include hsat in
theorem card_levelSub (v : ℕ) : Nat.card (G.levelSub M v) = p ^ (G.subHeight M * v) := by
  induction v with
  | zero => rw [card_levelSub_zero, mul_zero, pow_zero]
  | succ v ih =>
    rw [G.card_levelSub_succ M hsat, ih, card_levelSub_one, ← pow_add, mul_add, mul_one]

variable [IsGalois F (PadicAlgCl p)]

include hM in
theorem levelSub_isHopfIdeal (v : ℕ) : ((G.G v).vanIdeal (G.levelSub M v)).IsHopfIdeal F :=
  (G.G v).vanIdeal_isHopfIdeal _ (natCast_pow_ne_zero v) (G.killedBy_level v)
    (G.levelSub_stable M hM v)

/-- **The `p`-divisible group `H̃ ⊆ G` with `T_p H̃ = M`** ([Hong, Prop. 2.1.14]): its layers are
the closed subgroup schemes `H̃_v ⊆ G_v` cut out by `S_v`. -/
def tateSub : PDivGroup F p where
  height := G.subHeight M
  G v := (G.G v).sub (G.levelSub M v) (G.levelSub_isHopfIdeal M hM v)
  order_eq v := by
    rw [order_sub _ (natCast_pow_ne_zero v) (G.killedBy_level v) (G.levelSub_stable M hM v),
      G.card_levelSub M hsat]
  incl v := subMap _ _ (G.incl v) fun z hz => (G.incl_mem_levelSub_iff M hsat v z).2 hz
  incl_surjective v := subMap_surjective _ _ _ _ (G.incl_surjective v)
  range_eq v T _ _ y := by
    constructor
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (sub_killedBy _ (G.killedBy_level v)).pow_eq_one, map_one]
    · intro hy
      have h1 : (((G.G (v + 1)).subHom _ (G.levelSub_isHopfIdeal M hM (v + 1))).mapPoints T y) ^
          (p ^ v) = 1 := by
        rw [← map_pow, hy, map_one]
      obtain ⟨x', hx'⟩ := (G.range_eq v T _).2 h1
      obtain ⟨x, rfl⟩ := mem_range_subHom_of_map (G.levelSub_isHopfIdeal M hM v)
        (G.levelSub_isHopfIdeal M hM (v + 1)) (G.incl v) (natCast_pow_ne_zero v)
        (G.killedBy_level v) (natCast_pow_ne_zero (v + 1)) (G.killedBy_level (v + 1))
        (G.levelSub_stable M hM v) (G.levelSub_stable M hM (v + 1))
        (G.incl_mem_levelSub_iff M hsat v) x' ⟨y, hx'.symm⟩
      refine ⟨x, (G.G (v + 1)).subHom_mapPoints_injective _ _ T ?_⟩
      rw [subMap_mapPoints]
      exact hx'

/-- **The inclusion `ι : H̃ → G`**, levelwise the closed immersions `H̃_v ↪ G_v`. -/
def tateSubHom : Hom (G.tateSub M hM hsat) G where
  f v := (G.G v).subHom _ (G.levelSub_isHopfIdeal M hM v)
  comm _ := subMap_comm _ _ _ _

theorem tateSubHom_surjective (v : ℕ) : Function.Surjective ((G.tateSubHom M hM hsat).f v) :=
  (G.G v).subHom_surjective _ _

theorem tateSubHom_mapPoints_injective (v : ℕ) (T : Type) [CommRing T] [Algebra F T] :
    Function.Injective (((G.tateSubHom M hM hsat).f v).mapPoints T) :=
  (G.G v).subHom_mapPoints_injective _ _ T

/-- `ι(H̃_v(Ω)) = S_v`. -/
theorem mem_range_tateSubHom_iff (v : ℕ) (y : (G.G v).points Ω) :
    (∃ z, ((G.tateSubHom M hM hsat).f v).mapPoints Ω z = y) ↔ y ∈ G.levelSub M v :=
  mem_range_subHom_iff_qbar _ (natCast_pow_ne_zero v) (G.killedBy_level v)
    (G.levelSub_stable M hM v) y

theorem tateSubHom_mapTate_injective : Function.Injective ((G.tateSubHom M hM hsat).mapTate Ω) :=
  Hom.mapTate_injective_of_levels _ Ω fun v => G.tateSubHom_mapPoints_injective M hM hsat v Ω

/-- **`T_p(ι)(T_p H̃) = M`** for `M` closed. -/
theorem mem_range_tateSubHom_mapTate_iff
    (hclosed : ∀ x : G.TateModule Ω, (∀ v, ∃ m ∈ M, m.1 v = x.1 v) → x ∈ M)
    (x : G.TateModule Ω) :
    (∃ t, (G.tateSubHom M hM hsat).mapTate Ω t = x) ↔ x ∈ M := by
  rw [Hom.mem_range_mapTate_iff_levels _ Ω fun v => G.tateSubHom_mapPoints_injective M hM hsat v Ω]
  simp only [mem_range_tateSubHom_iff, mem_levelSub]
  exact ⟨hclosed x, fun hx v => ⟨x, hx, rfl⟩⟩

end Construction

end PDivGroup


/-! ### `ℤ_p`-direct summands -/

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime]

local notation "Ω" => PadicAlgCl p

section Summand

variable {F : Type} [Field F] [Algebra F (PadicAlgCl p)] (G : PDivGroup F p)
  {M N : Submodule ℤ_[p] (Additive (G.TateModule (PadicAlgCl p)))}

/-- The subgroup of `T_p G(Ω)` underlying a `ℤ_p`-submodule. -/
abbrev summandSub (M : Submodule ℤ_[p] (Additive (G.TateModule Ω))) :
    Subgroup (G.TateModule Ω) :=
  AddSubgroup.toSubgroup' M.toAddSubgroup

theorem exists_add_of_isCompl (hMN : IsCompl M N) (X : Additive (G.TateModule Ω)) :
    ∃ m ∈ M, ∃ n ∈ N, X = m + n := by
  have : X ∈ M ⊔ N := by
    rw [hMN.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨m, hm, n, hn, h⟩ := Submodule.mem_sup.1 this
  exact ⟨m, hm, n, hn, h.symm⟩

theorem tate_eq_one_of_pow_eq_one (x : G.TateModule Ω) (hx : x ^ p = 1) : x = 1 := by
  refine Subtype.ext (funext fun v => G.mapPoints_injective v Ω ?_)
  rw [x.2 v, ← tate_pow_val, hx]
  exact (map_one _).symm

/-- A direct summand is saturated: `x^p ∈ M ⇒ x ∈ M`. -/
theorem summandSub_sat (hMN : IsCompl M N) (x : G.TateModule Ω)
    (hx : x ^ p ∈ G.summandSub M) : x ∈ G.summandSub M := by
  change Additive.ofMul x ∈ M
  change Additive.ofMul (x ^ p) ∈ M at hx
  obtain ⟨m, hm, n, hn, hX⟩ := G.exists_add_of_isCompl hMN (Additive.ofMul x)
  rw [ofMul_pow, hX, smul_add] at hx
  have h1 : p • n ∈ M := by
    have := M.sub_mem hx (M.smul_of_tower_mem p hm)
    rwa [add_sub_cancel_left] at this
  have h2 : p • n = 0 := Submodule.disjoint_def.1 hMN.disjoint _ h1 (N.smul_of_tower_mem p hn)
  have h3 : n = 0 := by
    have := G.tate_eq_one_of_pow_eq_one (Additive.toMul n) (by
      rw [← toMul_nsmul, h2]
      rfl)
    exact congrArg Additive.ofMul this
  rw [hX, h3, add_zero]
  exact hm

/-- A direct summand is closed: if every level `x_v` comes from `M`, then `x ∈ M`. -/
theorem summandSub_closed (hMN : IsCompl M N) (x : G.TateModule Ω)
    (hx : ∀ v, ∃ m ∈ G.summandSub M, m.1 v = x.1 v) : x ∈ G.summandSub M := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  change Additive.ofMul x ∈ M
  obtain ⟨m, hm, n, hn, hX⟩ := G.exists_add_of_isCompl hMN (Additive.ofMul x)
  suffices h : Additive.toMul n = 1 by
    have : n = 0 := congrArg Additive.ofMul h
    rw [hX, this, add_zero]
    exact hm
  refine Subtype.ext (funext fun v => ?_)
  obtain ⟨m', hm', hm'v⟩ := hx v
  have h1 : (x * m'⁻¹).1 v = 1 := by
    rw [Subgroup.coe_mul, Pi.mul_apply, Subgroup.coe_inv, Pi.inv_apply, hm'v, mul_inv_cancel]
  obtain ⟨y, hy⟩ := TateModule.exists_pow_eq_of_val_eq_one G Ω
    (G.quot_surjective_sepClosed Ω hpΩ) (G.card_points_sepClosed Ω hpΩ) (x * m'⁻¹) v h1
  obtain ⟨a, ha, b, hb, hY⟩ := G.exists_add_of_isCompl hMN (Additive.ofMul y)
  have h2 : Additive.ofMul x - Additive.ofMul m' = p ^ v • (a + b) := by
    rw [← hY, ← ofMul_pow, hy, ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hkey : n - p ^ v • b = Additive.ofMul m' + p ^ v • a - m := by
    have hn' : n = Additive.ofMul x - m := by rw [hX]; abel
    have hx' : Additive.ofMul x = Additive.ofMul m' + (p ^ v • a + p ^ v • b) := by
      rw [← smul_add, ← h2]; abel
    rw [hn', hx']
    abel
  have hM' : n - p ^ v • b ∈ M := by
    rw [hkey]
    exact M.sub_mem (M.add_mem hm' (M.smul_of_tower_mem _ ha)) hm
  have hN' : n - p ^ v • b ∈ N := N.sub_mem hn (N.smul_of_tower_mem _ hb)
  have h3 : n = p ^ v • b := sub_eq_zero.1 (Submodule.disjoint_def.1 hMN.disjoint _ hM' hN')
  rw [h3, toMul_nsmul, tate_pow_val, G.pow_eq_one v Ω]
  rfl

variable [IsGalois F (PadicAlgCl p)]

/-- **[Hong, Prop. 2.1.14], essential surjectivity onto direct summands.** Over a field `F` with
`ℚ̄_p / F` Galois, a `Γ_F`-stable `ℤ_p`-direct summand `M` of `T_p G(ℚ̄_p)` is the Tate module of
a `p`-divisible group `H̃` with a homomorphism `ι : H̃ → G` whose layers are closed immersions:
`T_p(ι)` is injective with image `M`. -/
theorem exists_tateSub_of_isCompl (hMN : IsCompl M N)
    (hM : ∀ (σ : Ω ≃ₐ[F] Ω) (x : G.TateModule Ω), Additive.ofMul x ∈ M →
      Additive.ofMul (G.galTate σ x) ∈ M) :
    ∃ (H : PDivGroup F p) (ι : Hom H G), (∀ v, Function.Surjective (ι.f v)) ∧
      (∀ v, Function.Injective ((ι.f v).mapPoints Ω)) ∧ Function.Injective (ι.mapTate Ω) ∧
      ∀ x, (∃ t, ι.mapTate Ω t = x) ↔ Additive.ofMul x ∈ M :=
  ⟨G.tateSub (G.summandSub M) hM (G.summandSub_sat hMN),
    G.tateSubHom (G.summandSub M) hM (G.summandSub_sat hMN),
    G.tateSubHom_surjective _ hM (G.summandSub_sat hMN),
    fun v => G.tateSubHom_mapPoints_injective _ hM (G.summandSub_sat hMN) v Ω,
    G.tateSubHom_mapTate_injective _ hM (G.summandSub_sat hMN),
    G.mem_range_tateSubHom_mapTate_iff _ hM (G.summandSub_sat hMN)
      (G.summandSub_closed hMN)⟩

end Summand

/-! ### [Hong, Prop. 3.5.3] -/

/-- **[Hong, Prop. 3.5.3].** Let `R` be a local PID with fraction field `K ⊆ ℚ̄_p`, `ℚ̄_p / K`
Galois, `G` a `p`-divisible group over `R` and `M` a `Γ_K`-stable `ℤ_p`-direct summand of
`T_p G(ℚ̄_p) = T_p(G_K)(ℚ̄_p)`. There are a `p`-divisible group `H` over `R` and a homomorphism
`ι : H → G` inducing an isomorphism `T_p H(ℚ̄_p) ≅ M`: `T_p(ι)` is injective with image `M`. -/
theorem exists_pdivGroup_of_isCompl {R K : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [IsLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K Ω] [IsGalois K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω] (G : PDivGroup R p)
    {M N : Submodule ℤ_[p] (Additive ((G.baseChange K).TateModule Ω))} (hMN : IsCompl M N)
    (hM : ∀ (σ : Ω ≃ₐ[K] Ω) (x : (G.baseChange K).TateModule Ω), Additive.ofMul x ∈ M →
      Additive.ofMul ((G.baseChange K).galTate σ x) ∈ M) :
    ∃ (H : PDivGroup R p) (ι : Hom H G), Function.Injective (ι.mapTate Ω) ∧
      ∀ x : G.TateModule Ω,
        (∃ t, ι.mapTate Ω t = x) ↔
          Additive.ofMul ((G.baseChangeTateEquiv (S := K) Ω).symm x) ∈ M := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨H₀, ι₀, hsurj, hinj₀, -, hrange⟩ := (G.baseChange K).exists_tateSub_of_isCompl hMN hM
  obtain ⟨H, ι, -, he⟩ := ι₀.exists_pdivGroup_closure hsurj Ω hpΩ
  choose e he using he
  have hinj : ∀ v, Function.Injective ((ι.f v).mapPoints Ω) := fun v y y' h =>
    (e v).injective (hinj₀ v (((G.G v).baseChangePointsEquiv Ω).injective
      (by rw [← he, ← he]; exact h)))
  refine ⟨H, ι, Hom.mapTate_injective_of_levels ι Ω hinj, fun x => ?_⟩
  rw [Hom.mem_range_mapTate_iff_levels ι Ω hinj, ← hrange,
    Hom.mem_range_mapTate_iff_levels ι₀ Ω hinj₀]
  refine forall_congr' fun v => ⟨fun ⟨y, hy⟩ => ⟨e v y, ?_⟩, fun ⟨z, hz⟩ => ⟨(e v).symm z, ?_⟩⟩
  · exact (MulEquiv.eq_symm_apply _).2 ((he v y).symm.trans hy)
  · rw [he, MulEquiv.apply_symm_apply, hz]
    exact MulEquiv.apply_symm_apply _ _

/-! ### The height of `tateSub`: `h(H̃) = rank_{ℤ_p} M` -/

section SummandHeight

variable {F : Type} [Field F] [Algebra F (PadicAlgCl p)] (G : PDivGroup F p)
  {M N : Submodule ℤ_[p] (Additive (G.TateModule (PadicAlgCl p)))}

/-- The reduction `M → G_1(Ω)`, `m ↦ m_1`. -/
def summandRed (M : Submodule ℤ_[p] (Additive (G.TateModule Ω))) :
    M →+ Additive ((G.G 1).points Ω) :=
  (MonoidHom.toAdditive (TateModule.proj G Ω 1)).comp M.subtype.toAddMonoidHom

theorem summandRed_apply (m : M) :
    G.summandRed M m = Additive.ofMul ((Additive.toMul (m : Additive (G.TateModule Ω))).1 1) :=
  rfl

/-- **`ker(M → G_1(Ω)) = pM`** for a direct summand `M` (`M ∩ p T_p G = p M`). -/
theorem mem_ker_summandRed_iff (hMN : IsCompl M N) (m : M) :
    m ∈ (G.summandRed M).ker ↔ ∃ m' : M, p • m' = m := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [AddMonoidHom.mem_ker, summandRed_apply]
  change Additive.ofMul _ = Additive.ofMul 1 ↔ _
  rw [EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := TateModule.exists_pow_eq_of_val_eq_one G Ω
      (G.quot_surjective_sepClosed Ω hpΩ) (G.card_points_sepClosed Ω hpΩ) _ 1 h
    rw [pow_one] at hy
    have hyM : y ∈ G.summandSub M := G.summandSub_sat hMN y (by
      rw [hy]
      exact m.2)
    refine ⟨⟨Additive.ofMul y, hyM⟩, Subtype.ext ?_⟩
    change p • Additive.ofMul y = (m : Additive (G.TateModule Ω))
    rw [← ofMul_pow, hy]
    rfl
  · rintro ⟨m', rfl⟩
    change (Additive.toMul (p • (m' : Additive (G.TateModule Ω)))).1 1 = 1
    rw [toMul_nsmul, tate_pow_val]
    have := G.pow_eq_one 1 Ω ((Additive.toMul (m' : Additive (G.TateModule Ω))).1 1)
    rwa [pow_one] at this

/-- `#S_1 = #(M / ker(M → G_1(Ω)))`. -/
theorem card_levelSub_one_eq_card_quotient :
    Nat.card (G.levelSub (G.summandSub M) 1) = Nat.card (M ⧸ (G.summandRed M).ker) := by
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (G.summandRed M)).toEquiv]
  refine Nat.card_congr
    { toFun := fun y => ⟨Additive.ofMul y.1, ?_⟩
      invFun := fun y => ⟨Additive.toMul y.1, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · obtain ⟨x, hx, hxy⟩ := mem_levelSub.1 y.2
    exact ⟨⟨Additive.ofMul x, hx⟩, by rw [summandRed_apply, ← hxy]; rfl⟩
  · obtain ⟨⟨x, hx⟩, hxy⟩ := y.2
    exact mem_levelSub.2 ⟨Additive.toMul x, hx, by rw [← hxy, summandRed_apply]; rfl⟩

section Basis

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[p] M)

/-- Reduction mod `p` of the coordinates in a basis: `M → 𝔽_p^ι`. -/
def basisRed : M →+ (ι → ZMod p) where
  toFun m i := PadicInt.toZMod (b.equivFun m i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp

theorem basisRed_surjective : Function.Surjective (G.basisRed b) := by
  intro z
  choose c hc using fun i => ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) (z i)
  refine ⟨b.equivFun.symm c, funext fun i => ?_⟩
  change PadicInt.toZMod (b.equivFun (b.equivFun.symm c) i) = z i
  rw [LinearEquiv.apply_symm_apply, hc]

theorem mem_ker_basisRed_iff (m : M) : m ∈ (G.basisRed b).ker ↔ ∃ m' : M, p • m' = m := by
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h
    have hm : ∀ i, ∃ c : ℤ_[p], c * p = b.equivFun m i := fun i => by
      have h1 : b.equivFun m i ∈ RingHom.ker (PadicInt.toZMod (p := p)) :=
        congrFun h i
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at h1
      exact Ideal.mem_span_singleton'.1 h1
    choose c hc using hm
    refine ⟨b.equivFun.symm c, b.equivFun.injective ?_⟩
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, ← hc, mul_comm]
  · rintro ⟨m', rfl⟩
    funext i
    change PadicInt.toZMod (b.equivFun (p • m') i) = 0
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, ZMod.natCast_self,
      zero_mul]

end Basis

/-- **`#S_1 = p^{rank M}`** for a `ℤ_p`-direct summand `M` of `T_p G(Ω)`. -/
theorem card_levelSub_one_summandSub (hMN : IsCompl M N) :
    Nat.card (G.levelSub (G.summandSub M) 1) = p ^ Module.finrank ℤ_[p] M := by
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  let b := Module.finBasis ℤ_[p] M
  have hker : (G.summandRed M).ker = (G.basisRed b).ker := by
    ext m
    rw [G.mem_ker_summandRed_iff hMN, mem_ker_basisRed_iff]
  rw [card_levelSub_one_eq_card_quotient, hker,
    Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (G.basisRed_surjective b)).toEquiv,
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The height of `tateSub` is `rank_{ℤ_p} M`.** -/
theorem subHeight_summandSub (hMN : IsCompl M N) :
    G.subHeight (G.summandSub M) = Module.finrank ℤ_[p] M := by
  have h := (G.card_levelSub_one (G.summandSub M)).symm.trans (G.card_levelSub_one_summandSub hMN)
  exact Nat.pow_right_injective hp.out.two_le h

variable [IsGalois F (PadicAlgCl p)]

theorem tateSub_summandSub_height (hMN : IsCompl M N)
    (hM : ∀ (σ : Ω ≃ₐ[F] Ω) (x : G.TateModule Ω), Additive.ofMul x ∈ M →
      Additive.ofMul (G.galTate σ x) ∈ M) :
    (G.tateSub (G.summandSub M) hM (G.summandSub_sat hMN)).height = Module.finrank ℤ_[p] M :=
  G.subHeight_summandSub hMN

/-- **[Hong, Prop. 2.1.14] with the height**: `exists_tateSub_of_isCompl`, and moreover
`h(H̃) = rank_{ℤ_p} M`. -/
theorem exists_tateSub_of_isCompl_height (hMN : IsCompl M N)
    (hM : ∀ (σ : Ω ≃ₐ[F] Ω) (x : G.TateModule Ω), Additive.ofMul x ∈ M →
      Additive.ofMul (G.galTate σ x) ∈ M) :
    ∃ (H : PDivGroup F p) (ι : Hom H G), H.height = Module.finrank ℤ_[p] M ∧
      (∀ v, Function.Surjective (ι.f v)) ∧
      (∀ v, Function.Injective ((ι.f v).mapPoints Ω)) ∧ Function.Injective (ι.mapTate Ω) ∧
      ∀ x, (∃ t, ι.mapTate Ω t = x) ↔ Additive.ofMul x ∈ M :=
  ⟨G.tateSub (G.summandSub M) hM (G.summandSub_sat hMN),
    G.tateSubHom (G.summandSub M) hM (G.summandSub_sat hMN),
    G.tateSub_summandSub_height hMN hM,
    G.tateSubHom_surjective _ hM (G.summandSub_sat hMN),
    fun v => G.tateSubHom_mapPoints_injective _ hM (G.summandSub_sat hMN) v Ω,
    G.tateSubHom_mapTate_injective _ hM (G.summandSub_sat hMN),
    G.mem_range_tateSubHom_mapTate_iff _ hM (G.summandSub_sat hMN)
      (G.summandSub_closed hMN)⟩

end SummandHeight

/-- **[Hong, Prop. 3.5.3] with the height**: `exists_pdivGroup_of_isCompl`, and moreover
`h(H) = rank_{ℤ_p} M`. -/
theorem exists_pdivGroup_of_isCompl_height {R K : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra K Ω] [IsGalois K Ω] [Algebra R Ω] [IsScalarTower R K Ω] (G : PDivGroup R p)
    {M N : Submodule ℤ_[p] (Additive ((G.baseChange K).TateModule Ω))} (hMN : IsCompl M N)
    (hM : ∀ (σ : Ω ≃ₐ[K] Ω) (x : (G.baseChange K).TateModule Ω), Additive.ofMul x ∈ M →
      Additive.ofMul ((G.baseChange K).galTate σ x) ∈ M) :
    ∃ (H : PDivGroup R p) (ι : Hom H G), H.height = Module.finrank ℤ_[p] M ∧
      Function.Injective (ι.mapTate Ω) ∧
      ∀ x : G.TateModule Ω,
        (∃ t, ι.mapTate Ω t = x) ↔
          Additive.ofMul ((G.baseChangeTateEquiv (S := K) Ω).symm x) ∈ M := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨H₀, ι₀, hH₀, hsurj, hinj₀, -, hrange⟩ :=
    (G.baseChange K).exists_tateSub_of_isCompl_height hMN hM
  obtain ⟨H, ι, hH, he⟩ := ι₀.exists_pdivGroup_closure hsurj Ω hpΩ
  choose e he using he
  have hinj : ∀ v, Function.Injective ((ι.f v).mapPoints Ω) := fun v y y' h =>
    (e v).injective (hinj₀ v (((G.G v).baseChangePointsEquiv Ω).injective
      (by rw [← he, ← he]; exact h)))
  refine ⟨H, ι, hH.trans hH₀, Hom.mapTate_injective_of_levels ι Ω hinj, fun x => ?_⟩
  rw [Hom.mem_range_mapTate_iff_levels ι Ω hinj, ← hrange,
    Hom.mem_range_mapTate_iff_levels ι₀ Ω hinj₀]
  refine forall_congr' fun v => ⟨fun ⟨y, hy⟩ => ⟨e v y, ?_⟩, fun ⟨z, hz⟩ => ⟨(e v).symm z, ?_⟩⟩
  · exact (MulEquiv.eq_symm_apply _).2 ((he v y).symm.trans hy)
  · rw [he, MulEquiv.apply_symm_apply, hz]
    exact MulEquiv.apply_symm_apply _ _


end PDivGroup

end PadicHodge
