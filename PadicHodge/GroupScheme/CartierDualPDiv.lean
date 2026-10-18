/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierPerfect
import PadicHodge.GroupScheme.PDivisiblePoints

/-!
# The Cartier dual of a `p`-divisible group over `ℚ_p`

([Stix, §11.2.2], [Hong, Prop. 3.4.6]; [BC, §7.2].) For a `p`-divisible group `G = (G_v)` over
`ℚ_p`, the Cartier duals `G_v^∨` with the transposes `quot_v^∨ : G_v^∨ → G_{v+1}^∨` of the
quotient maps form a `p`-divisible group `G^∨` of the same height (`PDivGroup.dualPDiv`), and its
Tate module is the limit of the `G_v^∨` along the transposes `i_v^∨` of the inclusions
(`PDivGroup.tateModule_dualPDiv`: `T_p(G^∨) = DualTate G`), the second argument of the Cartier
pairing on Tate modules (`TatePairing.lean`). Standard arguments, written up here:

* `dual_quot_incl`: `quot_v^∨ ∘ i_v^∨ = (i_v ∘ quot_v)^∨ = [p]^∨ = [p]_{G_{v+1}^∨}` on points
  (via `[n]_{G^∨} = ([n]_G)^∨`, `CartierPerfect.lean`), for any base ring.
* `pow_range_eq_ker_pow`: if `#G_w(S) = p^{hw}` for all `w`, then `p^v G_{v+1}(S) = G_{v+1}(S)[p]`
  (counting).
* closed immersion: `quot_v^* : A_v → A_{v+1}` is injective (the `ℚ̄_p`-points of an étale
  `ℚ_p`-algebra separate its elements, `eq_zero_of_forall_algHom`, and `quot_v` is surjective on
  `ℚ̄_p`-points), so its transpose is surjective (`dual_quot_surjective`).
* kernel condition over `ℚ̄_p` (`exists_dual_quot_eq_padicAlgCl`): a point `y ∈ G_{v+1}^∨(ℚ̄_p)`
  killed by `p^v` gives the character `⟨·, y⟩` of `G_{v+1}(ℚ̄_p)`, which kills
  `p^v G_{v+1}(ℚ̄_p) = ker(quot_v)`, hence factors through `quot_v`; by perfectness at level `v`
  (`levelPairingHom_bijective`) it is `⟨quot_v(·), x⟩` and by naturality and perfectness at level
  `v + 1`, `y = quot_v^∨(x)`.
* kernel condition over any `ℚ_p`-algebra `S` (`exists_dual_quot_eq`): with
  `J = (u(b) - ε(b))_b ⊆ B = O(G_{v+1}^∨)`, `u = [p^v]^*`, a point `y` is killed by `p^v` iff it
  kills `J`; `B/J` is étale over `ℚ_p`, and its `ℚ̄_p`-points kill `ker(quot_v^{∨*})` by the
  previous item, so `ker(quot_v^{∨*}) ⊆ J` and `y` factors through `quot_v^∨`.
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (H : FFGroupScheme R)

theorem dual_univPt_pow_apply (n : ℕ) (F : Cartier.Dual R H.A) :
    ofConv (H.dual.univPt ^ n) F = toConv (ofConv F ∘ₗ (ofConv (H.univPt ^ n)).toLinearMap) :=
  congrArg (fun f : WithConv (Cartier.Dual R H.A →ₗ[R] Cartier.Dual R H.A) => ofConv f F)
    (H.dual_univPt_pow n)

theorem pow_apply_univPt {S : Type*} [CommRing S] [Algebra R S] (y : H.points S) (n : ℕ)
    (a : H.A) : ofConv (y ^ n) a = ofConv y (ofConv (H.univPt ^ n) a) := by
  conv_lhs => rw [← H.postComp_univPt y, ← map_pow]
  rfl

end FFGroupScheme

/-- The `L`-points of a (finite) étale algebra over `K` separate its elements, for `L` a
separably closed extension of `K`. -/
theorem eq_zero_of_forall_algHom {K L C : Type*} [Field K] [Field L] [IsSepClosed L]
    [Algebra K L] [CommRing C] [Algebra K C] [Algebra.Etale K C] (a : C)
    (h : ∀ φ : C →ₐ[K] L, φ a = 0) : a = 0 := by
  classical
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] C)
  have h1 : e (1 ⊗ₜ a) = 0 := by
    funext x
    let φ : C →ₐ[K] L := (((Pi.evalAlgHom L (fun _ => L) x).comp
      (e : L ⊗[K] C →ₐ[L] _)).restrictScalars K).comp Algebra.TensorProduct.includeRight
    exact h φ
  have h2 : (1 : L) ⊗ₜ[K] a = 0 := by
    rw [← map_zero e] at h1
    exact e.injective h1
  have hinj := Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := C)
    (algebraMap K L).injective
  exact hinj (h2.trans (map_zero _).symm)

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p)

theorem quot_incl_apply (v : ℕ) (a : (G.G (v + 1)).A) :
    G.quot v (G.incl v a) = ofConv ((G.G (v + 1)).univPt ^ p) a :=
  congrArg (fun z : (G.G (v + 1)).points (G.G (v + 1)).A => ofConv z a)
    (G.incl_quot v (G.G (v + 1)).univPt)

/-- **`quot_v^∨ ∘ i_v^∨ = [p]` on `G_{v+1}^∨`.** -/
theorem dual_quot_incl (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).dual.points S) :
    (G.quot v).dual.mapPoints S ((G.incl v).dual.mapPoints S y) = y ^ p := by
  apply WithConv.ofConv_injective
  ext F
  rw [pow_apply_univPt, dual_univPt_pow_apply]
  change ofConv y ((G.incl v).dual ((G.quot v).dual F)) = _
  congr 1
  apply WithConv.ofConv_injective
  ext a
  change ofConv F (G.quot v (G.incl v a)) = _
  rw [quot_incl_apply]
  rfl

/-- `p^v G_{v+1}(S) = G_{v+1}(S)[p]` if `#G_w(S) = p^{hw}` for all `w`. -/
theorem pow_range_eq_ker_pow (S : Type u) [CommRing S] [Algebra R S] (hp : 0 < p)
    (hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w)) (v : ℕ) :
    (powMonoidHom (p ^ v) : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).range =
      (powMonoidHom p : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker := by
  have hfin : Finite ((G.G (v + 1)).points S) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp _).ne')
  have hle : (powMonoidHom (p ^ v) : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).range ≤
      (powMonoidHom p : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker := by
    rintro _ ⟨x, rfl⟩
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    rw [← pow_mul, ← pow_succ]
    exact G.pow_eq_one (v + 1) S x
  -- `ker [p^v] = i_v(G_v(S))` has `p^{hv}` elements
  have hker : Nat.card (powMonoidHom (p ^ v) :
      (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker = p ^ (G.height * v) := by
    rw [← hcard v]
    refine (Nat.card_congr (Equiv.ofBijective (fun x : (G.G v).points S =>
      (⟨(G.incl v).mapPoints S x, (G.range_eq v S _).mp ⟨x, rfl⟩⟩ :
        (powMonoidHom (p ^ v) : (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker))
      ⟨fun x y h => G.mapPoints_injective v S (congrArg Subtype.val h), fun y => ?_⟩)).symm
    obtain ⟨x, hx⟩ := (G.range_eq v S y.1).mpr y.2
    exact ⟨x, Subtype.ext hx⟩
  have hrange : Nat.card (powMonoidHom (p ^ v) :
      (G.G (v + 1)).points S →* (G.G (v + 1)).points S).range = p ^ G.height := by
    have h := Subgroup.card_mul_index (powMonoidHom (p ^ v) :
      (G.G (v + 1)).points S →* (G.G (v + 1)).points S).ker
    rw [Subgroup.index_ker, hker, hcard, mul_add, mul_one, pow_add] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp _) h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hrange, G.card_ker_pow S v, hcard, mul_one]

end PDivGroup

/-! ### Over `ℚ_p` -/

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [CharZero K] [Algebra K (PadicAlgCl p)]
  (G : PDivGroup K p)

/-- `quot_v^* : A_v → A_{v+1}` is injective. -/
theorem quot_injective (v : ℕ) : Function.Injective (G.quot v : (G.G v).A → (G.G (v + 1)).A) := by
  have : Algebra.Etale K (G.G v).A := G.isEtale_of_isUnit (isUnit_p_of_charZero (p := p) (K := K)) v
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine eq_zero_of_forall_algHom (K := K) (L := PadicAlgCl p) a fun φ => ?_
  obtain ⟨ψ, hψ⟩ := G.quot_surjective_padicAlgCl v (toConv φ)
  have := congrArg (fun z : (G.G v).points (PadicAlgCl p) => ofConv z a) hψ
  simp only at this
  rw [← this]
  change ofConv ψ (G.quot v a) = 0
  rw [ha, map_zero]

/-- **`quot_v^∨ : G_v^∨ → G_{v+1}^∨` is a closed immersion.** -/
theorem dual_quot_surjective (v : ℕ) : Function.Surjective (G.quot v).dual := by
  intro F
  obtain ⟨F', hF'⟩ := LinearMap.dualMap_surjective_of_injective
    (f := (G.quot v : (G.G v).A →ₐ[K] (G.G (v + 1)).A).toLinearMap) (G.quot_injective v)
    (ofConv F)
  refine ⟨toConv F', WithConv.ofConv_injective ?_⟩
  ext a
  exact LinearMap.congr_fun hF' a

/-- `p^v G_{v+1}(ℚ̄_p) = ker(quot_v)`. -/
theorem pow_range_eq_ker_quot (v : ℕ) :
    (powMonoidHom (p ^ v) : (G.G (v + 1)).points (PadicAlgCl p) →*
      (G.G (v + 1)).points (PadicAlgCl p)).range = ((G.quot v).mapPoints (PadicAlgCl p)).ker := by
  rw [G.ker_quot, G.pow_range_eq_ker_pow _ hp.out.pos G.card_points_padicAlgCl]

/-- **Kernel condition for `G^∨` over `ℚ̄_p`**: a point of `G_{v+1}^∨(ℚ̄_p)` killed by `p^v`
comes from `G_v^∨(ℚ̄_p)`. -/
theorem exists_dual_quot_eq_padicAlgCl (v : ℕ) (y : (G.G (v + 1)).dual.points (PadicAlgCl p))
    (hy : y ^ (p ^ v) = 1) : ∃ x, (G.quot v).dual.mapPoints (PadicAlgCl p) x = y := by
  set q := (G.quot v).mapPoints (PadicAlgCl p)
  set χ := (G.G (v + 1)).pairingHom y
  have hχ : q.ker ≤ χ.ker := by
    rw [← G.pow_range_eq_ker_quot v]
    rintro _ ⟨ψ, rfl⟩
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    change (G.G (v + 1)).cartierPairingBase _ (ψ ^ (p ^ v)) y = 1
    rw [map_pow, MonoidHom.pow_apply, ← map_pow, hy, map_one]
  let e := QuotientGroup.quotientKerEquivOfSurjective q (G.quot_surjective_padicAlgCl v)
  let χ' : (G.G v).points (PadicAlgCl p) →* PadicAlgCl p :=
    (QuotientGroup.lift q.ker χ hχ).comp e.symm.toMonoidHom
  have hχ' : ∀ φ, χ' (q φ) = χ φ := by
    intro φ
    have : e.symm (q φ) = (φ : _ ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
    rfl
  obtain ⟨x, hx⟩ := (G.levelPairingHom_bijective v).2 χ'
  refine ⟨x, (G.G (v + 1)).pairing_injective_right (G.card_points_eq_order (v + 1)) fun φ => ?_⟩
  rw [← pairing_dual]
  have := DFunLike.congr_fun hx (q φ)
  rw [hχ' φ] at this
  exact this

/-- The ideal `J = ([p^v]^*(b) - ε(b))_b` of `O(G_{v+1}^∨)` cutting out `G_{v+1}^∨[p^v]`. -/
def dualTorsionIdeal (v : ℕ) : Ideal (G.G (v + 1)).dual.A :=
  Ideal.span (Set.range fun b => ofConv ((G.G (v + 1)).dual.univPt ^ (p ^ v)) b -
    algebraMap K _ (counit (R := K) b))

omit hp [CharZero K] [Algebra K (PadicAlgCl p)] in
theorem pow_eq_one_iff_le_ker (v : ℕ) {T : Type*} [CommRing T] [Algebra K T]
    (z : (G.G (v + 1)).dual.points T) :
    z ^ (p ^ v) = 1 ↔ G.dualTorsionIdeal v ≤ RingHom.ker (ofConv z) := by
  rw [dualTorsionIdeal, Ideal.span_le]
  constructor
  · rintro h _ ⟨b, rfl⟩
    have := congrArg (fun w : (G.G (v + 1)).dual.points T => ofConv w b) h
    rw [pow_apply_univPt, AlgHom.convOne_apply] at this
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes, this, sub_self]
  · intro h
    apply WithConv.ofConv_injective
    ext b
    have := h ⟨b, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    rw [pow_apply_univPt, this, AlgHom.convOne_apply]

/-- **Kernel condition for `G^∨` over any `ℚ_p`-algebra.** -/
theorem exists_dual_quot_eq (v : ℕ) {S : Type*} [CommRing S] [Algebra K S]
    (y : (G.G (v + 1)).dual.points S) (hy : y ^ (p ^ v) = 1) :
    ∃ x, (G.quot v).dual.mapPoints S x = y := by
  set π : (G.G (v + 1)).dual.A →ₐ[K] (G.G v).dual.A :=
    ((G.quot v).dual : (G.G (v + 1)).dual.A →ₐ[K] (G.G v).dual.A)
  set J := G.dualTorsionIdeal v
  have : Algebra.Etale K (G.G (v + 1)).dual.A := G.isEtale_dual (v + 1)
  have hkerJ : RingHom.ker π ≤ J := by
    intro b hb
    have : Algebra.FormallyUnramified K ((G.G (v + 1)).dual.A ⧸ J) := inferInstance
    have : Algebra.FinitePresentation K ((G.G (v + 1)).dual.A ⧸ J) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale K ((G.G (v + 1)).dual.A ⧸ J) :=
      Algebra.Etale.of_formallyUnramified_of_flat
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine eq_zero_of_forall_algHom (K := K) (L := PadicAlgCl p) _ fun φ => ?_
    let z : (G.G (v + 1)).dual.points (PadicAlgCl p) := toConv (φ.comp (Ideal.Quotient.mkₐ _ J))
    have hz : z ^ (p ^ v) = 1 := by
      rw [G.pow_eq_one_iff_le_ker]
      intro c hc
      change φ (Ideal.Quotient.mk J c) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero]
    obtain ⟨x, hx⟩ := G.exists_dual_quot_eq_padicAlgCl v z hz
    have := congrArg (fun w : (G.G (v + 1)).dual.points (PadicAlgCl p) => ofConv w b) hx
    change ofConv x (π b) = φ (Ideal.Quotient.mk J b) at this
    rw [← this, RingHom.mem_ker.mp hb, map_zero]
  have hyJ : RingHom.ker π.toRingHom ≤ RingHom.ker (ofConv y).toRingHom :=
    hkerJ.trans ((G.pow_eq_one_iff_le_ker v y).mp hy)
  refine ⟨toConv (AlgHom.liftOfSurjective π (G.dual_quot_surjective v) (ofConv y) hyJ), ?_⟩
  apply WithConv.ofConv_injective
  exact AlgHom.liftOfSurjective_comp π (G.dual_quot_surjective v) (ofConv y) hyJ

/-- **The Cartier dual `p`-divisible group** `G^∨ = (G_v^∨, quot_v^∨)` of a `p`-divisible group
over `ℚ_p`. -/
def dualPDiv : PDivGroup K p where
  height := G.height
  G v := (G.G v).dual
  order_eq v := by rw [FFGroupScheme.order_dual, G.order_eq]
  incl v := (G.quot v).dual
  incl_surjective v := G.dual_quot_surjective v
  range_eq v S _ _ y := by
    constructor
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (G.G v).dual.pow_eq_one_of_univPt (G.dual_univPt_pow_eq_one v) x, map_one]
    · exact G.exists_dual_quot_eq v y

@[simp] theorem dualPDiv_G (v : ℕ) : G.dualPDiv.G v = (G.G v).dual := rfl

@[simp] theorem dualPDiv_height : G.dualPDiv.height = G.height := rfl

/-- **`T_p(G^∨) = lim_v G_v^∨` along `i_v^∨`**: the Tate module of the dual `p`-divisible group is
the second argument `DualTate G` of the Cartier pairing on Tate modules. -/
theorem tateModule_dualPDiv (S : Type) [CommRing S] [Algebra K S] :
    G.dualPDiv.TateModule S = G.DualTate S := by
  ext y
  constructor
  · intro hy v
    apply G.dualPDiv.mapPoints_injective v S
    change (G.quot v).dual.mapPoints S (y v) =
      (G.quot v).dual.mapPoints S ((G.incl v).dual.mapPoints S (y (v + 1)))
    rw [G.dual_quot_incl]
    exact hy v
  · intro hy v
    change (G.quot v).dual.mapPoints S (y v) = y (v + 1) ^ p
    rw [hy v, G.dual_quot_incl]
    rfl

end PDivGroup

end PadicHodge
