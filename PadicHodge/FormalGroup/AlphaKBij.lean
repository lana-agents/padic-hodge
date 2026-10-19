/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.HodgeTateOL
import PadicHodge.FormalGroup.DAlphaDual

/-!
# Bijectivity of `α_K` ([Hong, Thm. 3.4.10], the `α_K` half)

Let `P` be a `p`-divisible formal group law over `R` (`G = F[p^∞]`), `L` a finite extension of
`ℚ_p` inside `ℚ̄_p` whose Galois group `G_L` fixes the coefficients. [Hong, Thm. 3.4.10] says that
`α` restricts to a bijection
`α_K : G(O_L) = F(m_{ℂ_p})^{G_L} → Hom_{ℤ_p[G_L]}(T_p(G^∨), 1 + m_{ℂ_p})`.

* Codomain (`GalCharK`): characters `f : T_p(G^∨)(O_{ℂ_p}) →* O_{ℂ_p}` with values in
  `1 + m_{ℂ_p}`, continuous for the `p`-adic topology of `T_p(G^∨)` (`IsContPrincipalChar`:
  `f → 1` uniformly on `ker(T_p(G^∨) → G_v^∨)`), and `G_L`-equivariant (`IsGalEquivOver`).
  Continuity is what makes `log ∘ f` `ℤ_p`-linear (`smul_of_bounded`); it is the honest form of
  Hong's `Hom_{ℤ_p}` (abstract group homomorphisms `ℤ_p^h → 1 + m_{ℂ_p}` need not be
  `ℤ_p`-linear). `α(x)` lies in it (`alpha_mem_galCharK`, `alpha_cont`).
* `alphaKChar_injective`: from `eq_zero_of_alpha_eq_one_K`.
* `alphaKChar_surjective` (given surjectivity of `dα_K`): `log ∘ f = dα(z)`, `z ∈ L^d`
  (`exists_dalpha_eq`); a small `G_L`-invariant `x₀` with `log_F x₀ = p^n z` has
  `α(x₀) = f^{p^n}` (`exists_fixed_alpha_eq_pow`, injectivity of `log` near `0` in `Ĝ_m`);
  dividing, `α(x₂)/f` is a `p^n`-torsion character, hence `α(t)` with `t ∈ F[p^n]`
  (`exists_torsion_alpha_eq_char`, the `p^v`-generalisation of `exists_torsion_alpha_eq`), and
  `u = x₂ − t` has `α(u) = f`; `σu − u` is `p^n`-torsion with `α(σu − u) = 1`, so `u` is
  `G_L`-invariant (`exists_fixed_alpha_eq_of_pow`). Only injectivity of `α` on torsion is used,
  not injectivity of `α` on all of `F(m_{ℂ_p})`.
* `alphaKCharOL_bijective` (over `O_{K'}`, via `dalphaKOL_bijective`) and
  `alphaKCharZp_bijective` (over `ℤ_p`, `L = ℚ_p`, via `dalphaK_bijective`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.4.9, Thm. 3.4.10.
-/

noncomputable section

open MvPowerSeries IsLocalRing WithConv Module TensorProduct

namespace PadicHodge

namespace PDivFGL

open FFGroupScheme FGL PDivGroup

/-! ### The logarithm of `Ĝ_m` on principal units -/

section Gm

variable {p : ℕ} [hp : Fact p.Prime]

local notation "S" => OCd p

/-- A principal unit `c ∈ 1 + m_{ℂ_p}` as a point `c − 1` of `Ĝ_m` over `O_{ℂ_p}`. -/
def gmPt (c : ℂ_[p]) (hc : ‖c - 1‖ < 1) : (FGL.multiplicative S).Pt p :=
  (FGL.multiplicative S).ofVec (fun _ => c - 1) fun _ => hc

theorem gmPt_val (c : ℂ_[p]) (hc : ‖c - 1‖ < 1) (j : Fin 1) :
    (((gmPt c hc).1 j : OC p) : ℂ_[p]) = c - 1 := rfl

theorem norm_mul_sub_one_lt {a b : ℂ_[p]} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a * b - 1‖ < 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hb)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ha)
  rw [norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha hb.le

theorem gmPt_mul {a b : ℂ_[p]} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    gmPt (a * b) (norm_mul_sub_one_lt ha hb) = gmPt a ha + gmPt b hb := by
  refine (FGL.multiplicative S).pt_ext fun j => Subtype.ext ?_
  rw [Subsingleton.elim j 0, gmPt_val, multiplicative_add_val, Subring.coe_add, Subring.coe_add,
    Subring.coe_mul, gmPt_val, gmPt_val]
  ring

theorem gmPt_congr {a b : ℂ_[p]} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) (h : a = b) :
    gmPt a ha = gmPt b hb := by
  subst h; rfl

/-- `log(c)` for a principal unit `c`, as `log_{Ĝ_m}(c − 1)`. -/
def logGm (c : ℂ_[p]) (hc : ‖c - 1‖ < 1) : ℂ_[p] := (FGL.multiplicative S).logF (gmPt c hc) 0

theorem logGm_mul {a b : ℂ_[p]} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    logGm (a * b) (norm_mul_sub_one_lt ha hb) = logGm a ha + logGm b hb := by
  rw [logGm, gmPt_mul ha hb, logF_add]
  rfl

/-- `σ` commutes with `log` on principal units. -/
theorem logGm_autCp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {c : ℂ_[p]}
    (hc : ‖c - 1‖ < 1) (hc' : ‖autCp σ c - 1‖ < 1) :
    logGm (autCp σ c) hc' = autCp σ (logGm c hc) := by
  have hseq : ∀ n, (FGL.multiplicative S).logSeq (gmPt (autCp σ c) hc') 0 n =
      autCp σ ((FGL.multiplicative S).logSeq (gmPt c hc) 0 n) := fun n => by
    rw [logSeq, logSeq, gm_nsmul_val, gm_nsmul_val, gmPt_val, gmPt_val, map_div₀, map_pow,
      map_natCast, map_sub, map_pow, map_add, map_one, map_sub, map_one]
  have h := ((continuous_autCp σ).tendsto _).comp
    ((FGL.multiplicative S).tendsto_logSeq (gmPt c hc) 0)
  refine tendsto_nhds_unique ((FGL.multiplicative S).tendsto_logSeq _ 0) ?_
  refine h.congr fun n => ?_
  rw [Function.comp_apply, hseq]

theorem logGm_congr {a b : ℂ_[p]} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) (h : a = b) :
    logGm a ha = logGm b hb := by
  subst h; rfl

end Gm

/-! ### `p^v`-torsion characters, continuity of `α(x)`, `ℤ_p`-linearity of bounded maps -/

section Char

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)
  [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)

local notation "S" => OCd p

local instance : NeZero p := ⟨hp.out.ne_zero⟩

variable (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

include hR in
/-- **A `p^v`-torsion character of `T_p(G^∨)(O_{ℂ_p})` is `α(t)` for some `t ∈ F[p^v]`**
(the left square of [Hong, Prop. 3.4.9] is onto `Hom(T_p(G^∨), μ_{p^v})`; generalises
`exists_torsion_alpha_eq` from `p` to `p^v` and from `α(x)` to any character). -/
theorem exists_torsion_alpha_eq_char (v : ℕ) (χ : P.pdivGroup.DualTate S →* OC p)
    (hχ : ∀ y, χ y ^ (p ^ v) = 1) :
    ∃ t : P.F.torsionBy (p := p) v, ∀ y, P.alpha hpm t.1 y = χ y := by
  let π : P.pdivGroup.DualTate S →* (P.groupScheme v).dual.points S :=
    (Pi.evalMonoidHom (fun w => (P.groupScheme w).dual.points S) v).comp
      (P.pdivGroup.DualTate S).subtype
  have hπ : Function.Surjective π := fun ψ => P.proj_surjective_OCd v ψ
  have hker : π.ker ≤ χ.ker := by
    intro y hy
    obtain ⟨w, hw⟩ : ∃ w : P.pdivGroup.DualTate S, w ^ (p ^ v) = y :=
      DualTate.exists_pow_eq_of_val_eq_one_OC P.pdivGroup v y hy
    rw [MonoidHom.mem_ker, ← hw, map_pow]
    exact hχ w
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let χ' : (P.groupScheme v).dual.points S →* OC p :=
    (QuotientGroup.lift π.ker χ hker).comp e.symm.toMonoidHom
  have hχ' : ∀ y, χ' (π y) = χ y := by
    intro y
    have : e.symm (π y) = (y : _ ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
    rfl
  obtain ⟨t1, ht1⟩ := (P.groupScheme v).exists_pairing_eq_OC (p := p)
    (pow_ne_zero v hp.out.ne_zero) (P.pdivGroup.univPt_pow_eq_one v)
    (P.pdivGroup.card_points_Cp v) χ'
  obtain ⟨t, ht⟩ := P.layerPt_surjective hR v (ofConv t1)
  have ht' : toConv (P.F.layerPt v t) = t1 := by rw [ht, toConv_ofConv]
  subst ht'
  refine ⟨t, fun y => ?_⟩
  rw [P.alpha_torsion hpm v t y]
  change (P.groupScheme v).pairing (OC p) (toConv (P.F.layerPt v t)) (y.1 v) = χ y
  rw [ht1 (y.1 v)]
  exact hχ' y

/-- `|α(x)(y) − 1| ≤ s` for `x` in the polydisc of radius `s ≤ 1`. -/
theorem norm_alpha_sub_one_le {x : P.F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : P.F.Bnd x s) (y : P.pdivGroup.DualTate S) :
    ‖((P.alpha hpm x y : OC p) : ℂ_[p]) - 1‖ ≤ s := by
  have h := (P.charHom hpm y).bnd_ptMap hs0 hs1 (P.bnd_toPtS hx) 0
  rw [P.charHom_ptMap hpm x y] at h
  simpa using h

/-- **`α(x)` is continuous** for the `p`-adic topology of `T_p(G^∨)`: `α(x)(y) → 1` as
`y → 1`, i.e. uniformly on the kernels of `T_p(G^∨) → G_v^∨`. -/
theorem alpha_cont (x : P.F.Pt p) {ε : ℝ} (hε : 0 < ε) :
    ∃ v, ∀ y : P.pdivGroup.DualTate S, y.1 v = 1 →
      ‖((P.alpha hpm x y : OC p) : ℂ_[p]) - 1‖ < ε := by
  obtain ⟨N, hN⟩ := P.F.exists_bnd_pow x
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (FGL.np_lt_one (p := p))
  refine ⟨N + m, fun y hy => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w : P.pdivGroup.DualTate S, w ^ (p ^ (N + m)) = y :=
    DualTate.exists_pow_eq_of_val_eq_one_OC P.pdivGroup (N + m) y hy
  have hb := hN (N + m) (by omega)
  have e : N + m - N + 1 = m + 1 := by omega
  rw [e] at hb
  have hs0 : (0 : ℝ) ≤ FGL.np p ^ (m + 1) := pow_nonneg FGL.np_pos.le _
  have hs1 : FGL.np p ^ (m + 1) ≤ 1 := pow_le_one₀ FGL.np_pos.le FGL.np_le_one
  have h := P.norm_alpha_sub_one_le hpm hs0 hs1 hb w
  have e2 : P.alpha hpm x (w ^ (p ^ (N + m))) = P.alpha hpm ((p ^ (N + m)) • x) w := by
    rw [alpha_nsmul]
    exact (P.alphaHom hpm x).map_pow w _
  rw [e2]
  refine h.trans_lt (lt_of_le_of_lt ?_ hm)
  exact pow_le_pow_of_le_one FGL.np_pos.le FGL.np_le_one (by omega)

omit [UniformSpace R] [DiscreteUniformity R] hC in
theorem map_pow_of_add (ℓ : P.pdivGroup.DualTate S → ℂ_[p])
    (hℓ : ∀ y y', ℓ (y * y') = ℓ y + ℓ y') (y : P.pdivGroup.DualTate S) (n : ℕ) :
    ℓ (y ^ n) = n * ℓ y := by
  have h1 : ℓ 1 = 0 := by
    have := hℓ 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  induction n with
  | zero => rw [pow_zero, h1, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, hℓ, ih]; push_cast; ring

omit [UniformSpace R] [DiscreteUniformity R] hC in
/-- **A bounded additive map `T_p(G^∨)(O_{ℂ_p}) → ℂ_p` is `ℤ_p`-linear** (as `dU_smul`). -/
theorem smul_of_bounded (ℓ : P.pdivGroup.DualTate S → ℂ_[p])
    (hℓ : ∀ y y', ℓ (y * y') = ℓ y + ℓ y') {M : ℝ} (hM : ∀ y, ‖ℓ y‖ ≤ M) (a : ℤ_[p])
    (y : P.pdivGroup.DualTate S) :
    ℓ (Additive.toMul (a • Additive.ofMul y)) = algebraMap ℚ_[p] ℂ_[p] a * ℓ y := by
  set D := ℓ (Additive.toMul (a • Additive.ofMul y)) - algebraMap ℚ_[p] ℂ_[p] a * ℓ y
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hD : ∀ v : ℕ, ‖D‖ ≤ 2 * M * FGL.np p ^ v := by
    intro v
    set n := expo a v
    set y' := Additive.toMul (a • Additive.ofMul y)
    obtain ⟨b, hb⟩ : ∃ b : ℤ_[p], b * (p : ℤ_[p]) ^ v = a - (n : ℤ_[p]) := by
      have hk : a - (n : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) v) := by
        rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
      rw [PadicInt.ker_toZModPow] at hk
      exact Ideal.mem_span_singleton'.mp hk
    have hA : algebraMap ℚ_[p] ℂ_[p] a =
        (n : ℂ_[p]) + (p : ℂ_[p]) ^ v * algebraMap ℚ_[p] ℂ_[p] b := by
      have h1 : (a : ℚ_[p]) = (n : ℚ_[p]) + (p : ℚ_[p]) ^ v * (b : ℚ_[p]) := by
        have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hb
        simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
          PadicInt.coe_sub] at this
        linear_combination -this
      rw [h1, map_add, map_mul, map_pow, map_natCast, map_natCast]
    set z := y' * (y ^ n)⁻¹
    have hz : z.1 v = 1 := by
      change y.1 v ^ n * ((y ^ n)⁻¹ : P.pdivGroup.DualTate (OCd p)).1 v = 1
      rw [InvMemClass.coe_inv, Pi.inv_apply, pi_subgroup_pow_val, mul_inv_cancel]
    obtain ⟨w, hw⟩ : ∃ w : P.pdivGroup.DualTate (OCd p), w ^ (p ^ v) = z :=
      DualTate.exists_pow_eq_of_val_eq_one_OC P.pdivGroup v z hz
    have hy' : y' = y ^ n * z := by rw [mul_comm, inv_mul_cancel_right]
    have hl : ℓ y' = (n : ℂ_[p]) * ℓ y + (p : ℂ_[p]) ^ v * ℓ w := by
      rw [hy', hℓ, P.map_pow_of_add ℓ hℓ, ← hw, P.map_pow_of_add ℓ hℓ, Nat.cast_pow]
    have key : D = (p : ℂ_[p]) ^ v * (ℓ w - algebraMap ℚ_[p] ℂ_[p] b * ℓ y) := by
      change ℓ y' - _ = _
      rw [hl, hA]
      ring
    have hb1 : ‖algebraMap ℚ_[p] ℂ_[p] b‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
        PadicComplex.norm_extends' p]
      exact PadicInt.norm_le_one b
    rw [key, norm_mul, norm_pow, mul_comm]
    have e : 2 * M * FGL.np p ^ v = 2 * M * ‖(p : ℂ_[p])‖ ^ v := rfl
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) v)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 := hM w
    have h2 := hM y
    nlinarith [norm_nonneg (algebraMap ℚ_[p] ℂ_[p] b), norm_nonneg (ℓ y)]
  have hD0 : D = 0 := by
    by_contra hne
    have hpos : 0 < ‖D‖ / (2 * M + 1) := by
      have := norm_pos_iff.mpr hne; positivity
    obtain ⟨v, hv⟩ := exists_pow_lt_of_lt_one hpos (FGL.np_lt_one (p := p))
    have h1 := hD v
    have h2 : FGL.np p ^ v * (2 * M + 1) < ‖D‖ := (lt_div_iff₀ (by positivity)).mp hv
    have h3 : 0 ≤ FGL.np p ^ v := pow_nonneg FGL.np_pos.le v
    nlinarith
  exact sub_eq_zero.mp hD0

end Char

/-! ### `Γ_L`-equivariant `ℤ_p`-linear functionals are in the image of `dα_K` -/

section Gen

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R) {d : ℕ} (P : PDivFGL R d p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

variable (F : Type) [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))
  (ℓ : P.pdivGroup.DualTate (OCd p) → ℂ_[p]) (hℓ : ∀ y y', ℓ (y * y') = ℓ y + ℓ y')
  (hℓs : ∀ (a : ℤ_[p]) y, ℓ (Additive.toMul (a • Additive.ofMul y)) =
    algebraMap ℚ_[p] ℂ_[p] a * ℓ y)

/-- A `ℤ_p`-linear functional `ℓ` on `T_p(G^∨)(O_{ℂ_p})`, transported to `T_p(G_F^∨)(ℚ̄_p)`. -/
def ellZpLin : P.TateDualF F →ₗ[ℤ_[p]] ℂ_[p] where
  toFun t := ℓ (Additive.toMul ((P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF).symm t))
  map_add' t t' := by simp only [map_add, toMul_add, hℓ]
  map_smul' a t := by
    simp only [RingHom.id_apply]
    have h := hℓs a
      (Additive.toMul ((P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF).symm t))
    rw [ofMul_toMul] at h
    rw [map_smul, h, ← Algebra.smul_def]
    exact algebraMap_smul ℚ_[p] a _

/-- `ℓ` as a `ℂ_p`-linear functional on `ℂ_p ⊗ V_p(G_F^∨)`. -/
def ellCpLin : Dual ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)) :=
  ((P.ellZpLin F hRF ℓ hℓ hℓs).liftBaseChange ℚ_[p]).liftBaseChange ℂ_[p]

variable [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]
  (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (hRL : FGL.GalFixedOver p R L)
  (ι : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → (PadicAlgCl p ≃ₐ[F] PadicAlgCl p))
  (hι : ∀ σ x, ι σ x = σ x)
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F))
  (hρ : ∀ σ (a : ℚ_[p]) (t : P.TateDualF F),
    ρ σ (a ⊗ₜ t) = a ⊗ₜ (P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t)
  (hℓg : ∀ (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) y,
    ℓ (P.galDual (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (hRL σ) y) =
      autCp (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (ℓ y))

omit [UniformSpace R] [DiscreteUniformity R]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)] in
include hι hℓg in
theorem ellZpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (t : P.TateDualF F) :
    P.ellZpLin F hRF ℓ hℓ hℓs ((P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t) =
      galCp L σ (P.ellZpLin F hRF ℓ hℓ hℓs t) := by
  set E := P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF
  set σ' := AlgEquiv.restrictScalarsHom ℚ_[p] σ
  have e : (ι σ).restrictScalars ℚ_[p] = σ' := AlgEquiv.ext (hι σ)
  have hR' : ∀ r : R, autCp ((ι σ).restrictScalars ℚ_[p])
      ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r := by
    rw [e]
    exact hRL σ
  have hE : E.symm ((P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t) =
      Additive.ofMul (P.pdivGroup.galDualGen σ' (hRL σ) (Additive.toMul (E.symm t))) := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = Additive.ofMul (P.pdivGroup.dualTateGenEquiv (F := F) hRF
      (P.pdivGroup.galDualGen σ' (hRL σ) (Additive.toMul (E.symm t))))
    rw [← P.pdivGroup.galDualGen_congr e hR' (hRL σ), dualTateGenEquiv_gal]
    have h1 : P.pdivGroup.dualTateGenEquiv (F := F) hRF (Additive.toMul (E.symm t)) =
        Additive.toMul t :=
      (P.pdivGroup.dualTateGenLinearEquiv_apply hRF _).symm.trans
        (congrArg Additive.toMul (E.apply_symm_apply t))
    rw [h1]
    rfl
  change ℓ (Additive.toMul (E.symm _)) = galCp L σ (ℓ (Additive.toMul (E.symm t)))
  rw [hE]
  exact hℓg σ _

omit [UniformSpace R] [DiscreteUniformity R]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)] in
include hι hρ hℓg in
theorem ellCpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (u : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)) :
    P.ellCpLin F hRF ℓ hℓ hℓs (TensorProduct.map (galCpLin L σ) (ρ σ) u) =
      galCp L σ (P.ellCpLin F hRF ℓ hℓ hℓs u) := by
  have hQ : ∀ v : ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F,
      (P.ellZpLin F hRF ℓ hℓ hℓs).liftBaseChange ℚ_[p] (ρ σ v) =
        galCp L σ ((P.ellZpLin F hRF ℓ hℓ hℓs).liftBaseChange ℚ_[p] v) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      rw [hρ]
      change a • P.ellZpLin F hRF ℓ hℓ hℓs _ = galCp L σ (a • P.ellZpLin F hRF ℓ hℓ hℓs t)
      rw [galCp_smul, P.ellZpLin_gal F hRF ℓ hℓ hℓs L hRL ι hι hℓg σ]
    | add x y hx hy => simp only [map_add, hx, hy]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.map_tmul]
    change galCpLin L σ c * (P.ellZpLin F hRF ℓ hℓ hℓs).liftBaseChange ℚ_[p] (ρ σ v) =
      galCp L σ (c * (P.ellZpLin F hRF ℓ hℓ hℓs).liftBaseChange ℚ_[p] v)
    rw [galCpLin_apply, hQ, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

include hℓ hℓs hρ hℓg in
/-- **A `Γ_L`-equivariant `ℤ_p`-linear `ℓ : T_p(G^∨) → ℂ_p` is `dα(z)` for some `z ∈ L^d`**,
given that `dα_K` is surjective. -/
theorem exists_dalpha_eq [FiniteDimensional ℚ_[p] L]
    (hsurj : Function.Surjective (P.dalphaKGen hpm F hRF L hRL ι hι ρ hρ)) :
    ∃ z : Fin d → L, ∀ y, P.dalpha hpm (fun j => algebraMap L ℂ_[p] (z j)) y = ℓ y := by
  set w : CpTensor ρ.dual :=
    (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.ellCpLin F hRF ℓ hℓ hℓs) with hwdef
  have hw : w ∈ DHT ρ.dual 0 := by
    intro σ
    rw [(htSetup L).ψ_zero, one_smul]
    change TensorProduct.map (galCpLin L σ) (ρ.dual σ) w = w
    apply (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).injective
    refine LinearMap.ext fun u => ?_
    have hu := tensorAct_inv_cancel ρ σ u
    rw [← hu, dualEquiv_gal, hwdef, LinearEquiv.apply_symm_apply,
      P.ellCpLin_gal F hRF ℓ hℓ hℓs L hRL ι hι ρ hρ hℓg σ]
  obtain ⟨z, hz⟩ := hsurj ⟨w, hw⟩
  refine ⟨z, fun y => ?_⟩
  have h0 : P.dalphaCpLin hpm F hRF (fun j => algebraMap L ℂ_[p] (z j)) =
      P.ellCpLin F hRF ℓ hℓ hℓs := by
    have h := congrArg Subtype.val hz
    rw [dalphaKGen_apply] at h
    exact (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm.injective h
  have h := LinearMap.congr_fun h0
    ((1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ
      P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF (Additive.ofMul y)))
  rw [dalphaCpLin_tmul, dalphaQpLin_tmul, LinearEquiv.symm_apply_apply, one_smul, one_mul,
    toMul_ofMul] at h
  rw [h]
  change (1 : ℂ_[p]) * ((1 : ℚ_[p]) • ℓ (Additive.toMul
    ((P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF).symm
      (P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF (Additive.ofMul y))))) = ℓ y
  rw [LinearEquiv.symm_apply_apply, toMul_ofMul, one_smul, one_mul]

end Gen

/-! ### `α_K` -/

section AlphaK

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R) {d : ℕ} (P : PDivFGL R d p)
  (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (hRL : FGL.GalFixedOver p R L)

local notation "S" => OCd p

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- **The codomain of `α_K`**: characters `f : T_p(G^∨)(O_{ℂ_p}) → 1 + m_{ℂ_p}` that are
continuous for the `p`-adic topology of `T_p(G^∨)` (`f(y) → 1` uniformly on the kernels of
`T_p(G^∨) → G_v^∨`). This is the form of `f ∈ Hom_{ℤ_p}(T_p(G^∨), 1 + m_{ℂ_p})` of
[Hong, Prop. 3.4.9] used here: it makes `log ∘ f` `ℤ_p`-linear (`smul_of_bounded`); the converse
(`ℤ_p`-linear implies continuous) is standard but not formalised. -/
def IsContPrincipalChar (f : P.pdivGroup.DualTate S →* OC p) : Prop :=
  (∀ y, ‖((f y : OC p) : ℂ_[p]) - 1‖ < 1) ∧
    ∀ ε : ℝ, 0 < ε → ∃ v, ∀ y : P.pdivGroup.DualTate S, y.1 v = 1 →
      ‖((f y : OC p) : ℂ_[p]) - 1‖ < ε

/-- `f` is `G_L = Gal(ℚ̄_p/L)`-equivariant: `f(σ y) = σ(f(y))`. -/
def IsGalEquivOver (f : P.pdivGroup.DualTate S →* OC p) : Prop :=
  ∀ (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (y : P.pdivGroup.DualTate S),
    ((f (P.galDual (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (hRL σ) y) : OC p) : ℂ_[p]) =
      autCp (AlgEquiv.restrictScalarsHom ℚ_[p] σ) ((f y : OC p) : ℂ_[p])

/-- `Hom_{ℤ_p[G_L]}(T_p(G^∨), 1 + m_{ℂ_p})` (continuous characters, see
`IsContPrincipalChar`). -/
abbrev GalCharK : Type :=
  {f : P.pdivGroup.DualTate S →* OC p // P.IsContPrincipalChar f ∧ P.IsGalEquivOver L hRL f}

/-- `G(O_L) = F(m_{ℂ_p})^{G_L}`. -/
abbrev FixedPtK : Type :=
  {x : P.F.Pt p // ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
    galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x}

include hRL in
theorem alpha_mem_galCharK (x : P.FixedPtK L) :
    P.IsContPrincipalChar (P.alphaHom hpm x.1) ∧
      P.IsGalEquivOver L hRL (P.alphaHom hpm x.1) := by
  refine ⟨⟨fun y => P.norm_alpha_sub_one_lt hpm x.1 y, fun ε hε => P.alpha_cont hpm x.1 hε⟩,
    fun σ y => ?_⟩
  have h := P.alpha_gal (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (hRL σ) hpm x.1 y
  rw [x.2 σ] at h
  exact h

/-- **`α_K : G(O_L) → Hom_{ℤ_p[G_L]}(T_p(G^∨), 1 + m_{ℂ_p})`** ([Hong, Thm. 3.4.10]). -/
def alphaKChar (x : P.FixedPtK L) : P.GalCharK L hRL :=
  ⟨P.alphaHom hpm x.1, P.alpha_mem_galCharK hpm L hRL x⟩

theorem ne_zero_of_norm_sub_one_lt {c : ℂ_[p]} (hc : ‖c - 1‖ < 1) : c ≠ 0 := by
  rintro rfl
  rw [zero_sub, norm_neg, norm_one] at hc
  exact lt_irrefl _ hc

variable (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

include hR in
/-- **`α_K` is injective** ([Hong, Thm. 3.4.10]; `eq_zero_of_alpha_eq_one_K`). -/
theorem alphaKChar_injective [FiniteDimensional ℚ_[p] L] :
    Function.Injective (P.alphaKChar hpm L hRL) := by
  rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
  have h1 : ∀ y, P.alpha hpm x y = P.alpha hpm x' y := fun y =>
    DFunLike.congr_fun (congrArg Subtype.val h) y
  have hfix : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (x - x') = x - x' := fun σ => by
    have e := galPt_add_of (hRL σ) (x - x') x'
    rw [sub_add_cancel, hx σ, hx' σ] at e
    exact add_right_cancel (e.symm.trans (sub_add_cancel x x').symm)
  have hone : ∀ y, P.alpha hpm (x - x') y = 1 := fun y => by
    have e := P.alpha_add hpm (x - x') x' y
    rw [sub_add_cancel, h1 y] at e
    have hne := ne_zero_of_norm_sub_one_lt (P.norm_alpha_sub_one_lt hpm x' y)
    apply Subtype.ext
    have e' := congrArg (fun a : OC p => (a : ℂ_[p])) e
    simp only [Subring.coe_mul] at e'
    rw [OneMemClass.coe_one]
    exact (mul_eq_right₀ hne).mp e'.symm
  have := P.eq_zero_of_alpha_eq_one_K hpm hR L hRL (x - x') hone hfix
  exact Subtype.ext (sub_eq_zero.mp this)

/-- `log ∘ f` for a character `f` with values in `1 + m_{ℂ_p}`. -/
def logChar (f : P.pdivGroup.DualTate S →* OC p) (hf1 : ∀ y, ‖((f y : OC p) : ℂ_[p]) - 1‖ < 1)
    (y : P.pdivGroup.DualTate S) : ℂ_[p] :=
  logGm ((f y : OC p) : ℂ_[p]) (hf1 y)

omit [UniformSpace R] [DiscreteUniformity R] hC in
theorem logChar_mul (f : P.pdivGroup.DualTate S →* OC p)
    (hf1 : ∀ y, ‖((f y : OC p) : ℂ_[p]) - 1‖ < 1) (y y' : P.pdivGroup.DualTate S) :
    P.logChar f hf1 (y * y') = P.logChar f hf1 y + P.logChar f hf1 y' := by
  rw [logChar, logChar, logChar, ← logGm_mul (hf1 y) (hf1 y')]
  exact logGm_congr _ _ (by rw [map_mul, Subring.coe_mul])

omit [UniformSpace R] [DiscreteUniformity R] hC in
theorem pow_val_eq_one (y : P.pdivGroup.DualTate S) {v k : ℕ} (hvk : v ≤ k) :
    (y ^ (p ^ k)).1 v = 1 := by
  rw [pi_subgroup_pow_val, show p ^ k = p ^ v * p ^ (k - v) by
    rw [← pow_add, Nat.add_sub_cancel' hvk], pow_mul,
    dualTate_pow_eq_one P.pdivGroup S y v, one_pow]

omit [UniformSpace R] [DiscreteUniformity R] hC in
/-- `log ∘ f` is bounded for a continuous `f`. -/
theorem logChar_bounded (f : P.pdivGroup.DualTate S →* OC p) (hf : P.IsContPrincipalChar f) :
    ∃ M : ℝ, ∀ y, ‖P.logChar f hf.1 y‖ ≤ M := by
  have hnp := FGL.np_pos (p := p)
  obtain ⟨v0, hv0⟩ := hf.2 (FGL.np p) hnp
  refine ⟨FGL.np p / FGL.np p ^ v0, fun y => ?_⟩
  have hB : (FGL.multiplicative S).Bnd (gmPt _ (hf.1 (y ^ (p ^ v0)))) (FGL.np p) := fun j => by
    rw [gmPt_val]; exact (hv0 _ (P.pow_val_eq_one y le_rfl)).le
  have h := (FGL.multiplicative S).norm_logF_le hnp.le le_rfl hB 0
  change ‖P.logChar f hf.1 (y ^ (p ^ v0))‖ ≤ _ at h
  rw [P.map_pow_of_add _ (P.logChar_mul f hf.1), norm_mul, Nat.cast_pow, norm_pow] at h
  rw [le_div_iff₀ (pow_pos hnp v0), mul_comm]
  exact h

omit [UniformSpace R] [DiscreteUniformity R] hC in
theorem logChar_gal (f : P.pdivGroup.DualTate S →* OC p)
    (hf1 : ∀ y, ‖((f y : OC p) : ℂ_[p]) - 1‖ < 1) (hfg : P.IsGalEquivOver L hRL f)
    (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (y : P.pdivGroup.DualTate S) :
    P.logChar f hf1 (P.galDual (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (hRL σ) y) =
      autCp (AlgEquiv.restrictScalarsHom ℚ_[p] σ) (P.logChar f hf1 y) := by
  rw [logChar, logChar, ← logGm_autCp _ (hf1 y) (by rw [← hfg σ y]; exact hf1 _)]
  exact logGm_congr _ _ (hfg σ y)

include hRL in
/-- **Main step**: if `log ∘ f = dα(z)` with `z ∈ L^d`, then `f^{p^n} = α(x₀)` for some `n` and
some `G_L`-invariant `x₀` (in the polydisc where `log_F` is bijective). -/
theorem exists_fixed_alpha_eq_pow [FiniteDimensional ℚ_[p] L]
    (f : P.pdivGroup.DualTate S →* OC p) (hf : P.IsContPrincipalChar f)
    (z : Fin d → L)
    (hz : ∀ y, P.dalpha hpm (fun j => algebraMap L ℂ_[p] (z j)) y = P.logChar f hf.1 y) :
    ∃ (n : ℕ) (x0 : P.F.Pt p), (∀ σ₀ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀) x0 = x0) ∧
      ∀ y, P.alpha hpm x0 y = f (y ^ (p ^ n)) := by
  have hnp := FGL.np_pos (p := p)
  set r : ℝ := FGL.np p ^ 2
  have hr0 : 0 ≤ r := by positivity
  have hr : r < FGL.np p := by
    change FGL.np p ^ 2 < FGL.np p
    rw [sq]; exact mul_lt_of_lt_one_left hnp FGL.np_lt_one
  obtain ⟨v1, hv1⟩ := hf.2 r (by positivity)
  obtain ⟨M, hM0, hMz⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ‖algebraMap L ℂ_[p] (z j)‖ ≤ M :=
    ⟨∑ j, ‖algebraMap L ℂ_[p] (z j)‖, Finset.sum_nonneg fun j _ => norm_nonneg _,
      fun j => Finset.single_le_sum (fun k _ => norm_nonneg (algebraMap L ℂ_[p] (z k)))
        (Finset.mem_univ j)⟩
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one
    (div_pos (pow_pos hnp 2) (by linarith : 0 < M + 1)) (FGL.np_lt_one (p := p))
  set n := n0 + v1
  set τ : Fin d → ℂ_[p] := fun j => (p : ℂ_[p]) ^ n * algebraMap L ℂ_[p] (z j)
  have hτ : ∀ j, ‖τ j‖ ≤ r := fun j => by
    change ‖(p : ℂ_[p]) ^ n * _‖ ≤ FGL.np p ^ 2
    rw [norm_mul, norm_pow]
    have h1 : FGL.np p ^ n0 * (M + 1) < FGL.np p ^ 2 := (lt_div_iff₀ (by linarith)).mp hn0
    have h2 : FGL.np p ^ n ≤ FGL.np p ^ n0 :=
      pow_le_pow_of_le_one hnp.le FGL.np_le_one (by omega)
    calc FGL.np p ^ n * ‖algebraMap L ℂ_[p] (z j)‖ ≤ FGL.np p ^ n0 * (M + 1) :=
          mul_le_mul h2 ((hMz j).trans (by linarith)) (norm_nonneg _) (pow_nonneg hnp.le _)
      _ ≤ FGL.np p ^ 2 := h1.le
  obtain ⟨x0, hx0r, hlog⟩ := P.F.exists_logF_eq hr0 hr hτ
  refine ⟨n, x0, fun σ₀ => ?_, fun y => ?_⟩
  · have hzσ : ∀ i, autCp (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀)
        (algebraMap L ℂ_[p] (z i)) = algebraMap L ℂ_[p] (z i) := fun i =>
      galCp_algebraMap_L L σ₀ (z i)
    refine P.F.logF_injOn hr0 hr (fun j => ?_) hx0r fun i => ?_
    · rw [galPt_val, norm_autCp]; exact hx0r j
    · rw [logF_galPt_of (hRL σ₀), hlog]
      change autCp _ ((p : ℂ_[p]) ^ n * _) = _
      rw [map_mul, map_pow, map_natCast, hzσ]
  · have ha := P.norm_alpha_sub_one_le hpm hr0 (hr.le.trans FGL.np_le_one) hx0r y
    have ha' : ‖((P.alpha hpm x0 y : OC p) : ℂ_[p]) - 1‖ < 1 :=
      ha.trans_lt (hr.trans FGL.np_lt_one)
    have hb := hv1 _ (P.pow_val_eq_one y (show v1 ≤ n by omega))
    have hptA : (P.charHom hpm y).ptMap (P.toPtS x0) = gmPt _ ha' := by
      refine (FGL.multiplicative S).pt_ext fun j => Subtype.ext ?_
      rw [Subsingleton.elim j 0, gmPt_val, P.charHom_ptMap hpm x0 y]
      push_cast
      rfl
    have hlogA : (FGL.multiplicative S).logF (gmPt _ ha') 0 =
        (p : ℂ_[p]) ^ n * P.logChar f hf.1 y := by
      rw [← hptA, P.logGm_alpha hpm x0 y, ← hz y]
      have e : (fun j => P.F.logF x0 j) =
          fun j => (p : ℂ_[p]) ^ n * algebraMap L ℂ_[p] (z j) := funext hlog
      rw [e, dalpha_smul]
    have hlogB : (FGL.multiplicative S).logF (gmPt _ (hf.1 (y ^ (p ^ n)))) 0 =
        (p : ℂ_[p]) ^ n * P.logChar f hf.1 y := by
      change P.logChar f hf.1 (y ^ (p ^ n)) = _
      rw [P.map_pow_of_add _ (P.logChar_mul f hf.1), Nat.cast_pow]
    have hAB : gmPt _ ha' = gmPt _ (hf.1 (y ^ (p ^ n))) := by
      refine (FGL.multiplicative S).logF_injOn hr0 hr (fun j => ?_) (fun j => ?_) fun i => ?_
      · rw [gmPt_val]; exact ha
      · rw [gmPt_val]; exact hb.le
      · rw [Subsingleton.elim i 0, hlogA, hlogB]
    have e := congrArg (fun q : (FGL.multiplicative S).Pt p => ((q.1 0 : OC p) : ℂ_[p])) hAB
    simp only [gmPt_val, sub_left_inj] at e
    exact Subtype.ext e

include hR in
/-- **Division step**: if `f^{p^n} = α(x₀)` with `x₀` `G_L`-invariant and `f` `G_L`-equivariant,
then `f = α(u)` with `u` `G_L`-invariant (`p^n u = x₀`). -/
theorem exists_fixed_alpha_eq_of_pow (f : P.pdivGroup.DualTate S →* OC p)
    (hfg : P.IsGalEquivOver L hRL f) (n : ℕ) (x0 : P.F.Pt p)
    (hfix0 : ∀ σ₀ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀) x0 = x0)
    (hA : ∀ y, P.alpha hpm x0 y = f (y ^ (p ^ n))) :
    ∃ u : P.FixedPtK L, ∀ y, P.alpha hpm u.1 y = f y := by
  obtain ⟨x2, hx2⟩ := FGL.exists_pow_nsmul_eq (P.exists_p_nsmul_eq hR) n x0
  set χ : P.pdivGroup.DualTate S →* OC p := P.alphaHom hpm x2 * f.comp invMonoidHom
  have hχy : ∀ y, χ y = P.alpha hpm x2 y * f y⁻¹ := fun y => rfl
  have hfinv : ∀ y, f y * f y⁻¹ = 1 := fun y => by rw [← map_mul, mul_inv_cancel, map_one]
  have hχ : ∀ y, χ y ^ (p ^ n) = 1 := fun y => by
    rw [hχy, mul_pow, ← alpha_nsmul, hx2, hA, ← map_pow, ← map_mul, ← mul_pow,
      mul_inv_cancel, one_pow, map_one]
  obtain ⟨t, ht⟩ := P.exists_torsion_alpha_eq_char hpm hR n χ hχ
  set u := x2 - t.1
  have hu : ∀ y, P.alpha hpm u y = f y := fun y => by
    have h1 := P.alpha_add hpm u t.1 y
    rw [sub_add_cancel, ht y] at h1
    have hunit := P.isUnit_alpha_torsion hpm n t y
    rw [ht y] at hunit
    refine hunit.mul_right_cancel ?_
    rw [← h1, hχy, mul_left_comm, hfinv, mul_one]
  refine ⟨⟨u, fun σ₀ => ?_⟩, hu⟩
  have h1 : CoeffFixed p R (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀) := hRL σ₀
  have h2 : CoeffFixed p R (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀)⁻¹ := by
    rw [← map_inv]
    exact hRL σ₀⁻¹
  set σ := AlgEquiv.restrictScalarsHom ℚ_[p] σ₀
  set w := galPt σ u - u
  have hσ : ∀ y, P.alpha hpm (galPt σ u) y = P.alpha hpm u y := fun y => by
    rw [← P.galDual_galDual_inv_of σ h1 h2 y]
    apply Subtype.ext
    rw [P.alpha_gal σ h1 hpm, hu, hu]
    exact (hfg σ₀ _).symm
  have hneg : ∀ y, P.alpha hpm (-u) y * P.alpha hpm u y = 1 := fun y => by
    rw [← alpha_add, neg_add_cancel, alpha_zero]
  have hw1 : ∀ y, P.alpha hpm w y = 1 := fun y => by
    change P.alpha hpm (galPt σ u + -u) y = 1
    rw [alpha_add, hσ, mul_comm, hneg]
  have hwt : w ∈ P.F.torsionBy (p := p) n := by
    have ht0 : (p ^ n) • t.1 = 0 := t.2
    have hpu : (p ^ n) • u = x0 := by rw [nsmul_sub, ht0, sub_zero, hx2]
    rw [FGL.mem_torsionBy, nsmul_sub, ← galPt_nsmul_of h1, hpu, hfix0 σ₀, sub_self]
  have hw0 := P.eq_zero_of_alpha_torsion hpm n ⟨w, hwt⟩ hw1
  exact sub_eq_zero.mp hw0

variable (F : Type) [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))
  [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]
  (ι : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → (PadicAlgCl p ≃ₐ[F] PadicAlgCl p))
  (hι : ∀ σ x, ι σ x = σ x)
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F))
  (hρ : ∀ σ (a : ℚ_[p]) (t : P.TateDualF F),
    ρ σ (a ⊗ₜ t) = a ⊗ₜ (P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t)

include hR in
/-- **`α_K` is surjective** ([Hong, Thm. 3.4.10]) as soon as `dα_K` is surjective. -/
theorem alphaKChar_surjective [FiniteDimensional ℚ_[p] L]
    (hsurj : Function.Surjective (P.dalphaKGen hpm F hRF L hRL ι hι ρ hρ)) :
    Function.Surjective (P.alphaKChar hpm L hRL) := by
  rintro ⟨f, hf, hfg⟩
  obtain ⟨M, hM⟩ := P.logChar_bounded f hf
  have hℓs := fun a y => P.smul_of_bounded (P.logChar f hf.1) (P.logChar_mul f hf.1) hM a y
  obtain ⟨z, hz⟩ := P.exists_dalpha_eq hpm F hRF (P.logChar f hf.1) (P.logChar_mul f hf.1) hℓs
    L hRL ι hι ρ hρ (P.logChar_gal L hRL f hf.1 hfg) hsurj
  obtain ⟨n, x0, hfix0, hA⟩ := P.exists_fixed_alpha_eq_pow hpm L hRL f hf z hz
  obtain ⟨u, hu⟩ := P.exists_fixed_alpha_eq_of_pow hpm L hRL hR f hfg n x0 hfix0 hA
  exact ⟨u, Subtype.ext (MonoidHom.ext hu)⟩

include hR in
/-- **[Hong, Thm. 3.4.10] (`α_K` half)**, general coefficients: if `dα_K` is surjective, then
`α_K : G(O_L) = F(m_{ℂ_p})^{G_L} → Hom_{ℤ_p[G_L]}(T_p(G^∨), 1 + m_{ℂ_p})` is bijective. -/
theorem alphaKChar_bijective [FiniteDimensional ℚ_[p] L]
    (hsurj : Function.Surjective (P.dalphaKGen hpm F hRF L hRL ι hι ρ hρ)) :
    Function.Bijective (P.alphaKChar hpm L hRL) :=
  ⟨P.alphaKChar_injective hpm L hRL hR,
    P.alphaKChar_surjective hpm L hRL hR F hRF ι hι ρ hρ hsurj⟩

end AlphaK

/-! ### `O_{K'}` and `ℤ_p` -/

section OL

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L] {d : ℕ} (P : PDivFGL (OL L) d p)

/-- **[Hong, Thm. 3.4.10] (`α_K` half) over `O_{K'}`**: for `G = F[p^∞]` over `O_L`,
`α_K : G(O_L) = F(m_{ℂ_p})^{G_L} → Hom_{ℤ_p[G_L]}(T_p(G^∨), 1 + m_{ℂ_p})`, `x ↦ α(x)`, is
bijective onto the continuous `G_L`-equivariant characters with values in `1 + m_{ℂ_p}`. -/
theorem alphaKCharOL_bijective :
    Function.Bijective (P.alphaKChar OL.p_mem L (OL.galFixedOver (L := L))) :=
  P.alphaKChar_bijective OL.p_mem L OL.galFixedOver OL.norm_lt_one L OL.algebraMap_qbar_cp
    (fun σ => σ) (fun _ _ => rfl) P.tateRepDualOL (fun _ _ _ => rfl) P.dalphaKOL_bijective.2

end OL

section Zp

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

/-- **[Hong, Thm. 3.4.10] (`α_K` half) over `ℤ_p`**: for `G = F[p^∞]` over `ℤ_p`,
`α_K : G(ℤ_p) = F(m_{ℂ_p})^{Γ} → Hom_{ℤ_p[Γ]}(T_p(G^∨), 1 + m_{ℂ_p})` is bijective
(`Γ = Gal(ℚ̄_p/ℚ_p)`, `L = ⊥`). -/
theorem alphaKCharZp_bijective :
    Function.Bijective (P.alphaKChar ZpD.p_mem ⊥ (FGL.galFixedOver_of_galFixed ZpD.galFixed ⊥)) :=
  P.alphaKChar_bijective ZpD.p_mem ⊥ (FGL.galFixedOver_of_galFixed ZpD.galFixed ⊥)
    ZpD.norm_lt_one ℚ_[p] ZpD.algebraMap_qbar_cp (fun σ => σ.restrictScalars ℚ_[p])
    (fun _ _ => rfl) (P.tateRepDual ⊥) (fun _ _ _ => rfl) P.dalphaK_bijective.2

end Zp

end PDivFGL

end PadicHodge
