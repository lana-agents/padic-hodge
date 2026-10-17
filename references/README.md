# References

Citation list only (no PDFs in this repository). A reference is cited in the Lean sources only
for statements that were actually looked up in it; where a text was not available, this is said.

* [BC] O. Brinon, B. Conrad, *CMI summer school notes on p-adic Hodge theory* (preliminary
  version, June 24, 2009), https://math.stanford.edu/~conrad/papers/notes.pdf.
  Used: §2.1 (Proposition 2.1.2, `ℂ_K^H = \hat{L}`, proved from [Ax, Prop. 1]),
  §2.2 (Theorem 2.2.7, Tate–Sen), §2.3 (Lemma 2.3.1, Serre–Tate), §2.4 (Proposition 2.4.4),
  §5 (formalism of admissible representations), §14 (Tate–Sen formalism; §14.3, proof of
  Theorem 14.3.4: `H¹(Gal(K_∞/K), \hat K_∞) ≃ H¹(Gal(K_∞/K), K) ⊕ H¹(Gal(K_∞/K), X)`),
  §13.1 (Theorem 13.1.2, Tate's almost-étaleness theorem), §13.7 (Exercise 13.7.2, descent of
  finite extensions of `K_∞` to finite layers; Exercise 13.7.4, Faltings' proof: parts (1)–(6),
  formalised with `d = 0`; parts (3) and (6) say "δn→∞", but the inequality of part (6),
  `δ_n − δ_{n+1} ≥ β_n − (d+1)(δ_n − δ_{n+1})`, gives `δ_n → 0`, which is what is used), §14.1 (Lemma 14.1.3, axiom (TS1)).
* [Serre] J.-P. Serre, *Local Fields*, Ch. III, §6, Prop. 12 (rings of integers of complete DVR
  extensions with separable residue extension are monogenic) and §7, Prop. 14 (annihilator of
  `Ω¹` is the different). **Not available locally**; cited only as quoted in [BC, Ex. 13.7.1]
  ("[44, Ch. III, §7, Prop. 14]"); the monogenicity statement used is proved from scratch in
  `AlmostEtale/Mono.lean`.
* [Ax] J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15
  (1970). **Not available locally**; cited only through [BC, proof of Prop. 2.1.2], which
  quotes [Ax, Prop. 1] in the form "for each n there exists y_n ∈ K̄^H with
  v(x_n − y_n) ≥ n − p/(p−1)²". The proof formalised here is our own write-up of the
  standard argument (Hasse derivatives of the minimal polynomial), see `Blueprint.md`.
* [Tate] J. Tate, *p-divisible groups*, Proc. Conf. Local Fields (Driebergen, 1966).
  **Not available locally.** Statements attributed to it are taken from [BC] and from
  [LocAn] (Lemma 2.2, which quotes "[Tate], §3.3, Theorem 1 … Theorem 2", and the proof of
  Prop. 7.4, which quotes "Theorem 4 of [Tate]").
* [LocAn] S. Mochizuki, *The local pro-p anabelian geometry of curves*, Invent. Math. 138
  (1999). The consumer of this repository (Theorem A).
