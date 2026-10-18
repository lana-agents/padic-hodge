/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Frobenius

/-!
# Connected `p`-divisible groups over a field of characteristic `p`: the layers

Let `k` be a field of characteristic `p` with `x^p = x` for all `x ∈ k`, and `H = (G_v, i_v)` a
`p`-divisible group over `k` all of whose layers `G_v = Spec A_v` are connected (`A_v` local).
This file collects the facts about the layers needed for the structure theorem
`lim_v A_v ≅ k[[t_1, …, t_d]]` ([Hong, Prop. 2.2.13] for the special fibre; our proof is
different from Hong's, see `GroupScheme/SerreTateSpecial.lean`). We write `i_v^* : A_{v+1} ↠ A_v`
for the ring map of `i_v` and `quot_v^* : A_v → A_{v+1}` for the one of `quot_v`
(`i_v ∘ quot_v = [p]`).

* `PDivGroup.inclOne w : A_{w+1} ↠ A_1`, the iterated transition map, and
  `PDivGroup.exists_eq_comp_inclOne` (Yoneda): a point of `G_{w+1}` killed by `p` factors through
  `G_1`.
* **`PDivGroup.quot_injective_of_isConnected`**: `quot_v^*` is injective (`quot_v` is
  faithfully flat). Proof:
  `|G_{v+1}| ≤ |ker quot_v| · |im quot_v|` (Nakayama,
  `FFGroupScheme.order_le_finrank_mul_finrank_range`) and `ker quot_v ⊆ G_{v+1}[p] = G_1`, so
  `|im quot_v| ≥ p^{h(v+1)}/p^h = |G_v|`.
* **`PDivGroup.incl_eq_zero_of_pow_eq_zero`**: if `a ∈ A_{v+1}` has `a^p = 0`, then
  `i_v^*(a) = 0`: `[p]^*(a) = 0` (`FFGroupScheme.univPt_pow_apply_eq_zero`, from
  [Hong, Prop. 1.5.8]) and `[p]^* = quot_v^* ∘ i_v^*`.
* `FFGroupScheme.frobPoint_pow_eq_one`: the Frobenius kernel `ker φ_G = Spec A/frobKerIdeal`
  ([Hong, Lemma 1.5.2]) is killed by `p`; hence `ker(A_{w+1} ↠ A_1) ⊆ frobKerIdeal`
  (`PDivGroup.ker_inclOne_le_frobKerIdeal`, i.e. `ker φ_{G_{w+1}} ⊆ G_1`, cf.
  [Hong, Prop. 1.5.9]) and, as `frobKerIdeal ⊆ 𝔪²`, the cotangent spaces `𝔪_v/𝔪_v²` all agree
  with `𝔪_1/𝔪_1²`: `PDivGroup.counitKer_le_of_inclOne` (generators of `𝔪_1` modulo `𝔪_1²`
  lift to generators of `𝔪_{w+1}` modulo `𝔪_{w+1}²`; this is the step
  `J_1/J_1² ≅ J_v/J_v²` in [Hong, proof of Prop. 2.2.13]).
-/

noncomputable section

open Coalgebra WithConv TensorProduct Module

namespace PadicHodge

universe u

/-- The augmentation ideal `ker ε` of a bialgebra. -/
abbrev counitKer (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Bialgebra k A] : Ideal A :=
  RingHom.ker (Bialgebra.counitAlgHom k A)

section Bialg

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Bialgebra k A]

theorem mem_counitKer {a : A} : a ∈ counitKer k A ↔ counit (R := k) a = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]

theorem counit_sub_algebraMap (a : A) :
    counit (R := k) (a - algebraMap k A (counit (R := k) a)) = 0 := by
  rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul,
    mul_one, sub_self]

theorem mk_eq_algebraMap_counit (I : Ideal A) {a : A}
    (h : a - algebraMap k A (counit (R := k) a) ∈ I) :
    Ideal.Quotient.mk I a = algebraMap k (A ⧸ I) (counit (R := k) a) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  exact h

/-- `frobKerIdeal ⊆ 𝔪²` for `p ≥ 2`. -/
theorem frobKerIdeal_le_sq {p : ℕ} (hp : 2 ≤ p) : frobKerIdeal k A p ≤ counitKer k A ^ 2 := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨a, ha, rfl⟩
  have hm : a ∈ counitKer k A := mem_counitKer.mpr ha
  have e : a ^ p = a ^ 2 * a ^ (p - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [SetLike.mem_coe, e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hm 2)

end Bialg

namespace FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p]

omit hp [CharP k p] in
/-- `ε ∘ [p]^* = ε`. -/
theorem counit_univPt_pow (G : FFGroupScheme k) (a : G.A) :
    counit (R := k) (ofConv (G.univPt ^ p) a) = counit (R := k) a := by
  have h1 : G.postComp (Bialgebra.counitAlgHom k G.A) G.univPt = 1 := by
    apply WithConv.ofConv_injective
    ext b
    rw [AlgHom.convOne_apply]
    rfl
  have h : G.postComp (Bialgebra.counitAlgHom k G.A) (G.univPt ^ p) = 1 := by
    rw [map_pow, h1, one_pow]
  have := congrArg (fun φ : G.points k => ofConv φ a) h
  simpa [AlgHom.convOne_apply, postComp] using this

/-- The Frobenius kernel `ker φ_G = Spec A/frobKerIdeal` is killed by `p`: its universal point
`A ↠ A/frobKerIdeal` has `p`-th power `1`. -/
theorem frobPoint_pow_eq_one (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k) :
    (toConv (Ideal.Quotient.mkₐ k (frobKerIdeal k G.A p)) :
      G.points (G.A ⧸ frobKerIdeal k G.A p)) ^ p = 1 := by
  classical
  set F := frobKerIdeal k G.A p
  set x := Ideal.Quotient.mkₐ k F
  have hfrob : ∀ z : G.A, x (z ^ p) = algebraMap k _ (counit (R := k) (z ^ p)) := by
    intro z
    set c := algebraMap k G.A (counit (R := k) z)
    have e : z ^ p = (z - c) ^ p + c ^ p := by rw [← add_pow_of_algebra k, sub_add_cancel]
    have h0 : x ((z - c) ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (pow_mem_frobKerIdeal (counit_sub_algebraMap z))
    have hc : counit (R := k) (z ^ p) = counit (R := k) z ^ p := by
      rw [← Bialgebra.counitAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply]
    rw [e, map_add, h0, zero_add, map_pow, AlgHom.commutes, ← e, hc, map_pow]
  have hx : (toConv x : G.points (G.A ⧸ F)) ^ p = G.postComp x (G.univPt ^ p) := by
    rw [map_pow]
    rfl
  rw [hx]
  apply WithConv.ofConv_injective
  ext a
  change x (ofConv (G.univPt ^ p) a) = ofConv (1 : G.points (G.A ⧸ F)) a
  rw [AlgHom.convOne_apply, ← counit_univPt_pow (p := p) G a]
  let b := Module.Free.chooseBasis k G.A
  rw [univPt_pow_apply hk G b a, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, hfrob, smul_eq_mul, map_mul, Algebra.smul_def]

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {k : Type u} [Field k] {p : ℕ} (H : PDivGroup k p)

/-- The iterated transition map `A_{w+1} ↠ A_1` (the closed immersion `G_1 → G_{w+1}`). -/
def inclOne : ∀ w : ℕ, (H.G (w + 1)).A →ₐ[k] (H.G 1).A
  | 0 => AlgHom.id k _
  | w + 1 => (inclOne w).comp (H.incl (w + 1) : (H.G (w + 1 + 1)).A →ₐ[k] (H.G (w + 1)).A)

theorem inclOne_succ_apply (w : ℕ) (a : (H.G (w + 1 + 1)).A) :
    H.inclOne (w + 1) a = H.inclOne w (H.incl (w + 1) a) := rfl

theorem inclOne_surjective (w : ℕ) : Function.Surjective (H.inclOne w) := by
  induction w with
  | zero => exact Function.surjective_id
  | succ w ih => exact ih.comp (H.incl_surjective (w + 1))

theorem counit_inclOne (w : ℕ) (a : (H.G (w + 1)).A) :
    counit (R := k) (H.inclOne w a) = counit (R := k) a := by
  induction w with
  | zero => rfl
  | succ w ih => rw [inclOne_succ_apply, ih, CoalgHomClass.counit_comp_apply]

/-- **Yoneda**: a point of `G_{w+1}` killed by `p` comes from `G_1`. -/
theorem exists_eq_comp_inclOne (w : ℕ) {B : Type u} [CommRing B] [Algebra k B]
    (x : (H.G (w + 1)).points B) (hx : x ^ p = 1) :
    ∃ x₁ : (H.G 1).A →ₐ[k] B, ofConv x = x₁.comp (H.inclOne w) := by
  induction w with
  | zero => exact ⟨ofConv x, rfl⟩
  | succ w ih =>
    obtain ⟨x', hx'⟩ := (H.range_eq (w + 1) B x).mpr (by rw [pow_succ', pow_mul, hx, one_pow])
    have hp' : x' ^ p = 1 := by
      apply H.mapPoints_injective (w + 1) B
      rw [map_pow, hx', hx, map_one]
    obtain ⟨x₁, h₁⟩ := ih x' hp'
    refine ⟨x₁, ?_⟩
    rw [← hx']
    change (ofConv x').comp _ = _
    rw [h₁]
    rfl

/-- **`quot_v^* : A_v → A_{v+1}` is injective.** -/
theorem quot_injective_of_isConnected [hp : Fact p.Prime] (v : ℕ) (hc : (H.G (v + 1)).IsConnected) :
    Function.Injective (H.quot v) := by
  classical
  set f : (H.G v).A →ₐ[k] (H.G (v + 1)).A := (H.quot v : (H.G v).A →ₐ[k] (H.G (v + 1)).A)
  set I := Ideal.span (f '' {x | counit (R := k) x = 0})
  have hN := FFGroupScheme.order_le_finrank_mul_finrank_range (H.quot v) hc
  let x := Ideal.Quotient.mkₐ k I
  have h1 : (H.quot v).mapPoints _ (toConv x) = 1 := by
    apply WithConv.ofConv_injective
    ext a
    change x (f a) = ofConv (1 : (H.G v).points ((H.G (v + 1)).A ⧸ I)) a
    rw [AlgHom.convOne_apply, Ideal.Quotient.mkₐ_eq_mk]
    have hc' : counit (R := k) (f a) = counit (R := k) a :=
      CoalgHomClass.counit_comp_apply (H.quot v) a
    rw [← hc']
    refine mk_eq_algebraMap_counit I ?_
    rw [hc', ← AlgHom.commutes f, ← map_sub]
    exact Ideal.subset_span ⟨_, counit_sub_algebraMap a, rfl⟩
  have h2 : (toConv x : (H.G (v + 1)).points _) ^ p = 1 := by
    rw [← H.incl_quot v (toConv x), h1, map_one]
  obtain ⟨x₁, hx₁⟩ := H.exists_eq_comp_inclOne v (toConv x) h2
  have hsurj : Function.Surjective x₁ := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨H.inclOne v a, (congrArg (fun φ : (H.G (v + 1)).A →ₐ[k] _ => φ a) hx₁).symm⟩
  have hB : finrank k ((H.G (v + 1)).A ⧸ I) ≤ finrank k (H.G 1).A := by
    have := LinearMap.finrank_range_le x₁.toLinearMap
    rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at this
  have hr : finrank k (LinearMap.range f.toLinearMap) = finrank k (H.G v).A := by
    refine le_antisymm (LinearMap.finrank_range_le _) ?_
    have e1 := H.order_eq (v + 1)
    have e2 := H.order_eq 1
    have e3 := H.order_eq v
    simp only [order] at e1 e2 e3 hN
    rw [e2] at hB
    rw [e3]
    have hpos : 0 < p ^ (H.height * 1) := pow_pos hp.out.pos _
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc p ^ (H.height * 1) * p ^ (H.height * v) = p ^ (H.height * (v + 1)) := by
          rw [← pow_add]; ring_nf
      _ ≤ _ := e1 ▸ hN
      _ ≤ _ := Nat.mul_le_mul_right _ hB
  have hker := LinearMap.finrank_range_add_finrank_ker f.toLinearMap
  rw [hr, add_eq_left, Submodule.finrank_eq_zero] at hker
  exact LinearMap.ker_eq_bot.mp hker

/-- **If `a^p = 0` in `A_{v+1}`, then `i_v^*(a) = 0`**: `[p]^*(a) = quot_v^*(i_v^*(a))` vanishes
([Hong, Prop. 1.5.8]) and `quot_v^*` is injective. -/
theorem incl_eq_zero_of_pow_eq_zero [hp : Fact p.Prime] [CharP k p] (hk : ∀ x : k, x ^ p = x)
    (v : ℕ) (hc : (H.G (v + 1)).IsConnected) {a : (H.G (v + 1)).A} (ha : a ^ p = 0) :
    H.incl v a = 0 := by
  apply H.quot_injective_of_isConnected v hc
  rw [map_zero]
  have h := FFGroupScheme.univPt_pow_apply_eq_zero hk (H.G (v + 1)) ha
  rw [← H.incl_quot v (H.G (v + 1)).univPt] at h
  exact h

/-- **`ker(A_{w+1} ↠ A_1) ⊆ frobKerIdeal`**: the Frobenius kernel of `G_{w+1}` is killed by `p`,
hence lies in `G_1`. -/
theorem ker_inclOne_le_frobKerIdeal [Fact p.Prime] [CharP k p] (hk : ∀ x : k, x ^ p = x)
    (w : ℕ) : RingHom.ker (H.inclOne w) ≤ frobKerIdeal k (H.G (w + 1)).A p := by
  intro a ha
  obtain ⟨x₁, hx₁⟩ := H.exists_eq_comp_inclOne w _ (frobPoint_pow_eq_one hk (H.G (w + 1)))
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h := congrArg (fun φ : (H.G (w + 1)).A →ₐ[k] _ => φ a) hx₁
  simp only [AlgHom.comp_apply, RingHom.mem_ker.mp ha, map_zero] at h
  exact h

/-- `ker(A_{w+1} ↠ A_1) ⊆ 𝔪_{w+1}²`. -/
theorem ker_inclOne_le_sq [hp : Fact p.Prime] [CharP k p] (hk : ∀ x : k, x ^ p = x) (w : ℕ) :
    RingHom.ker (H.inclOne w) ≤ counitKer k (H.G (w + 1)).A ^ 2 :=
  (H.ker_inclOne_le_frobKerIdeal hk w).trans (frobKerIdeal_le_sq hp.out.two_le)

/-- **Cotangent spaces**: if `s_i ∈ A_{w+1}` are such that their images in `A_1` generate
`𝔪_1` modulo `𝔪_1²`, then the `s_i` generate `𝔪_{w+1}` modulo `𝔪_{w+1}²`. -/
theorem counitKer_le_of_inclOne [Fact p.Prime] [CharP k p] (hk : ∀ x : k, x ^ p = x) (w : ℕ)
    {ι : Type*} (s : ι → (H.G (w + 1)).A)
    (h1 : counitKer k (H.G 1).A ≤
      Ideal.span (Set.range (H.inclOne w ∘ s)) ⊔ counitKer k (H.G 1).A ^ 2) :
    counitKer k (H.G (w + 1)).A ≤
      Ideal.span (Set.range s) ⊔ counitKer k (H.G (w + 1)).A ^ 2 := by
  set π := H.inclOne w
  set J := Ideal.span (Set.range s) ⊔ counitKer k (H.G (w + 1)).A ^ 2
  have hM : counitKer k (H.G 1).A ≤ (counitKer k (H.G (w + 1)).A).map π := by
    intro b hb
    obtain ⟨a, rfl⟩ := H.inclOne_surjective w b
    refine Ideal.mem_map_of_mem _ (mem_counitKer.mpr ?_)
    rw [← H.counit_inclOne w a]
    exact mem_counitKer.mp hb
  have hJ : Ideal.span (Set.range (π ∘ s)) ⊔ counitKer k (H.G 1).A ^ 2 ≤ J.map π := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, ← Set.range_comp]
    exact sup_le_sup_left (Ideal.pow_right_mono hM 2) _
  intro m hm
  have hπm : π m ∈ counitKer k (H.G 1).A :=
    mem_counitKer.mpr ((H.counit_inclOne w m).trans (mem_counitKer.mp hm))
  obtain ⟨m', hm', he⟩ := (Ideal.mem_map_iff_of_surjective π (H.inclOne_surjective w)).mp
    (hJ (h1 hπm))
  have hd : m - m' ∈ J := by
    refine Ideal.mem_sup_right (H.ker_inclOne_le_sq hk w ?_)
    rw [RingHom.mem_ker, map_sub, he, sub_self]
  have := J.add_mem hd hm'
  rwa [sub_add_cancel] at this

end PDivGroup

end PadicHodge
