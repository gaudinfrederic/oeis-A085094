import Mathlib
import A084013

open Classical Finset

/-! A084017 (conjecture OEIS, 2003) : pour tout n ≠ 0, il existe un
    entier N à exactement n chiffres, palindromique (avec zéros
    terminaux ignorés quand 10 ∣ n), multiple de n, et dont la somme
    des chiffres est aussi multiple de n.

    Encodage : N = P * 10^z avec P palindrome strict (premier chiffre
    non nul par convention Nat.digits), z = nombre de zéros terminaux.
    Corrections Argon : (1) implication parenthésée ; (2) P ≠ 0
    (Nat.digits 10 0 = [], palindrome vide dégénéré) ; (3) σ sur P
    (les zéros ajoutés ne changent pas la somme) ; (4) σ(P) = σ(N). -/

/-- Reservoir sigma : tout R ≤ 9t est somme de t chiffres ∈ {0..9}.
    Glouton : le nouvel index t recoit min 9 R, recursion sur le reste. -/
theorem digit_sum_interval (t R : ℕ) (hR : R ≤ 9 * t) :
    ∃ d : ℕ → ℕ, (∀ i, d i ≤ 9) ∧ (∀ i, t ≤ i → d i = 0)
      ∧ (Finset.range t).sum d = R := by
  induction t generalizing R with
  | zero =>
    interval_cases R
    exact ⟨fun _ => 0, fun i => by simp, fun i _ => rfl, by simp⟩
  | succ t ih =>
    set d0 := min 9 R
    have hrest : R - d0 ≤ 9 * t := by
      by_cases h9 : 9 ≤ R
      · have : d0 = 9 := min_eq_left h9
        omega
      · have : d0 = R := min_eq_right (by omega)
        omega
    rcases ih (R - d0) hrest with ⟨e, he1, he2, he3⟩
    refine ⟨Function.update e t d0, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = t
      · subst hi; simp [Function.update_self, d0]
      · rw [Function.update_of_ne hi]; exact he1 i
    · intro i hi
      have hi0 : i ≠ t := by omega
      rw [Function.update_of_ne hi0]
      exact he2 i (by omega)
    · rw [Finset.sum_range_succ, Function.update_self]
      have : (Finset.range t).sum (Function.update e t d0)
          = (Finset.range t).sum e := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (by
          have := Finset.mem_range.mp hi; omega)]
      rw [this, he3]
      have hle : d0 ≤ R := Nat.min_le_right _ _
      omega

/-- Factorisation du poids modifie : sous `10^(L-1) = 1`,
    `10^i * (w_i - 2) = (10^i - 1)^2` dans `ZMod m`. -/
theorem wshift_factor {m L i : ℕ} [NeZero m]
    (hL : (10 : ZMod m) ^ (L - 1) = 1) (hi : i < L) :
    (10 : ZMod m) ^ i * ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i) - 2)
      = ((10 : ZMod m) ^ i - 1) ^ 2 := by
  have hpow : (10 : ZMod m) ^ i * (10 : ZMod m) ^ (L - 1 - i) = 1 := by
    rw [← pow_add]
    have hsum : i + (L - 1 - i) = L - 1 := by omega
    rw [hsum, hL]
  have h2 : (10 : ZMod m) ^ i * (10 : ZMod m) ^ i = ((10 : ZMod m) ^ i) ^ 2 := by
    ring
  calc (10 : ZMod m) ^ i * ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i) - 2)
      = (10 : ZMod m) ^ i * (10 : ZMod m) ^ i
        + (10 : ZMod m) ^ i * (10 : ZMod m) ^ (L - 1 - i)
        - 2 * (10 : ZMod m) ^ i := by ring
    _ = ((10 : ZMod m) ^ i) ^ 2 + 1 - 2 * (10 : ZMod m) ^ i := by
        rw [hpow, h2]
    _ = ((10 : ZMod m) ^ i - 1) ^ 2 := by ring

/-- Unite du poids modifie : `w'_i` unite ssi `10^i - 1` unite
    (car `10^i` est une unite pour gcd(m,10)=1). -/
theorem wshift_unit_iff {m L i : ℕ} (hm : Nat.Coprime m 10) (hm0 : 0 < m)
    (hL : (10 : ZMod m) ^ (L - 1) = 1) (hi : i < L) :
    IsUnit ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i) - 2)
      ↔ IsUnit ((10 : ZMod m) ^ i - 1) := by
  haveI : NeZero m := ⟨hm0.ne'⟩
  have h10u : IsUnit (10 : ZMod m) := by
    have h := (ZMod.unitOfCoprime 10 hm.symm).isUnit
    rwa [ZMod.coe_unitOfCoprime] at h
  have hpu : IsUnit ((10 : ZMod m) ^ i) := h10u.pow i
  have hfac := wshift_factor hL hi
  constructor
  · intro h
    have hm2 : IsUnit ((10 : ZMod m) ^ i
        * ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i) - 2)) :=
      hpu.mul h
    rw [hfac] at hm2
    rw [pow_two] at hm2
    exact (IsUnit.mul_iff.mp hm2).1
  · intro h
    have hsq : IsUnit (((10 : ZMod m) ^ i - 1) ^ 2) := h.pow 2
    rw [← hfac] at hsq
    exact (IsUnit.mul_iff.mp hsq).2

/-- `IsUnit (10^i - 1 : ZMod m)` ssi `10^i - 1` copremier a `m`. -/
theorem pow_sub_one_unit_iff {m i : ℕ} (hm0 : 0 < m) :
    IsUnit ((10 : ZMod m) ^ i - 1)
      ↔ Nat.Coprime (10 ^ i - 1) m := by
  haveI : NeZero m := ⟨hm0.ne'⟩
  have h10 : (1 : ℕ) ≤ 10 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have hcast : ((10 ^ i - 1 : ℕ) : ZMod m) = (10 : ZMod m) ^ i - 1 := by
    rw [Nat.cast_sub h10]
    simp
  rw [← hcast, ZMod.isUnit_iff_coprime]

/-- `p | 10^i - 1` ssi `orderOf(10 mod p) | i` (p premier). -/
theorem prime_dvd_pow_sub_one {p i : ℕ} (hp : p.Prime) :
    p ∣ 10 ^ i - 1 ↔ orderOf (10 : ZMod p) ∣ i := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have h1 : (1 : ℕ) ≤ 10 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have key : ((10 ^ i - 1 : ℕ) : ZMod p) = 0 ↔ p ∣ 10 ^ i - 1 :=
    CharP.cast_eq_zero_iff (ZMod p) p _
  rw [← key, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-- Caracterisation complete : `w'_i` unite mod m ssi pour tout
    premier p | m, `orderOf(10 mod p) non | i`.
    (sous 10^(L-1) = 1 mod m) -/
theorem wshift_unit_iff_orders {m L i : ℕ} (hm : Nat.Coprime m 10)
    (hm0 : 0 < m)
    (hL : (10 : ZMod m) ^ (L - 1) = 1) (hi : i < L) :
    IsUnit ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i) - 2)
      ↔ ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ i := by
  rw [wshift_unit_iff hm hm0 hL hi, pow_sub_one_unit_iff hm0]
  constructor
  · intro hcop p hpm
    have hp := (Nat.mem_primeFactors.mp hpm).1
    have hpm_dvd := (Nat.mem_primeFactors.mp hpm).2.1
    have hp10 : ¬ p ∣ 10 := fun h => by
      have hgd : p ∣ Nat.gcd m 10 := Nat.dvd_gcd hpm_dvd h
      rw [hm] at hgd
      exact hp.ne_one (Nat.eq_one_of_dvd_one hgd)
    rw [← prime_dvd_pow_sub_one hp]
    intro hdvd
    have hgd : p ∣ Nat.gcd (10 ^ i - 1) m := Nat.dvd_gcd hdvd hpm_dvd
    rw [hcop] at hgd
    exact hp.ne_one (Nat.eq_one_of_dvd_one hgd)
  · intro hall
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
    have hpm_dvd : p ∣ m := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, hpm_dvd, hm0.ne'⟩
    have hp10 : ¬ p ∣ 10 := fun h => by
      have hgd : p ∣ Nat.gcd m 10 := Nat.dvd_gcd hpm_dvd h
      rw [hm] at hgd
      exact hp.ne_one (Nat.eq_one_of_dvd_one hgd)
    have hdiv : p ∣ 10 ^ i - 1 :=
      Nat.dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    exact hall p hpm ((prime_dvd_pow_sub_one hp).mp hdiv)

/-- Comptage des multiples de o dans range X : <= X/o + 1. -/
theorem card_multiples_le (X o : ℕ) (ho : 0 < o) :
    ((Finset.range X).filter (o ∣ ·)).card ≤ X / o + 1 := by
  have hsub : (Finset.range X).filter (o ∣ ·)
      ⊆ (Finset.range (X / o + 1)).image (· * o) := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_image]
    have hdiv : i / o ≤ X / o := Nat.div_le_div_right hi.1.le
    exact ⟨i / o, Finset.mem_range.mpr (by omega),
      Nat.div_mul_cancel hi.2⟩
  calc ((Finset.range X).filter (o ∣ ·)).card
      ≤ ((Finset.range (X / o + 1)).image (· * o)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (X / o + 1)).card := Finset.card_image_le
    _ = X / o + 1 := Finset.card_range _

/-- Borne d'union des positions mortes pour w'_i :
    |{i ∈ range X : ∃ p|m, ord_p | i}| ≤ Σ_{p|m} (X/ord_p + 1). -/
theorem dead_wshift_count {m X : ℕ} :
    ((Finset.range X).filter (fun i =>
        ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)).card
      ≤ (m.primeFactors.sum fun p =>
        X / orderOf (10 : ZMod p) + 1) := by
  have hsub : (Finset.range X).filter (fun i =>
      ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)
      ⊆ m.primeFactors.biUnion (fun p =>
        (Finset.range X).filter (orderOf (10 : ZMod p) ∣ ·)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with ⟨p, hpm, hpd⟩
    rw [Finset.mem_biUnion]
    exact ⟨p, hpm, Finset.mem_filter.mpr ⟨hi.1, hpd⟩⟩
  calc ((Finset.range X).filter (fun i =>
      ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)).card
      ≤ (m.primeFactors.biUnion (fun p =>
        (Finset.range X).filter (orderOf (10 : ZMod p) ∣ ·))).card :=
        Finset.card_le_card hsub
    _ ≤ m.primeFactors.sum fun p =>
        ((Finset.range X).filter (orderOf (10 : ZMod p) ∣ ·)).card :=
        Finset.card_biUnion_le
    _ ≤ m.primeFactors.sum fun p =>
        X / orderOf (10 : ZMod p) + 1 := by
        apply Finset.sum_le_sum
        intro p hpm
        by_cases hpo : orderOf (10 : ZMod p) = 0
        · rw [hpo]; by_cases hX : 0 < X <;> simp [hX]
        · exact card_multiples_le X _ (Nat.pos_of_ne_zero hpo)

/-- Union bound w' : les positions mortes (ord_p | i pour un p|m)
    dans range X. Directement dead_wshift_count. -/
theorem dead_wshift_union {m X : ℕ} :
    ((Finset.range X).filter (fun i =>
        ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)).card
      ≤ (m.primeFactors.sum fun p =>
        X / orderOf (10 : ZMod p) + 1) := dead_wshift_count

/-- Si gcd(m,30)=1 alors pour tout premier p | m, ord_p(10) != 1
    (ord=1 <=> 10≡1 mod p <=> p|9 <=> p=3). ord=0 est benin :
    seule la position 0 est morte pour ce p. -/
theorem orderOf_ne_one {m p : ℕ} (h3 : ¬ 3 ∣ m) (h10 : Nat.Coprime m 10)
    (hp : p ∈ m.primeFactors) :
    orderOf (10 : ZMod p) ≠ 1 := by
  have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
  haveI : NeZero p := ⟨hpP.pos.ne'⟩
  intro h1
  have hd : orderOf (10 : ZMod p) ∣ (1 : ℕ) := by
    rw [h1]
  have h10e : (10 : ZMod p) = 1 := by
    have h := orderOf_dvd_iff_pow_eq_one.mp hd
    simpa using h
  have h9 : ((9 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_ofNat]
    have h9e : (9 : ZMod p) = (10 : ZMod p) - 1 := by norm_num
    rw [h9e, h10e, sub_self]
  have hdvd : p ∣ 9 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 9).mp h9
  have hp3 : p = 3 := by
    have hp9 : p ∣ 3 := by
      apply hpP.dvd_of_dvd_pow (n := 2)
      rwa [show (9 : ℕ) = 3 ^ 2 by norm_num] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime (3:ℕ))).mp hp9
      with h1p | h3p
    · exact absurd h1p hpP.ne_one
    · exact h3p
  exact h3 (hp3 ▸ (Nat.mem_primeFactors.mp hp).2.1)

open scoped Pointwise

/-- Extraction w' (fenetre paire) : positions vivantes pour les
    poids modifies w'_i = w_i - 2. Sous 10^(L-1) = 1 mod m et
    assez de positions vivantes, tout residu t mod m est atteint
    par une somme de chiffres ponderee par w'. -/
theorem pal_window_extract_wshift {m L : ℕ} (hm : Nat.Coprime m 10)
    (hm0 : 0 < m) (hL1 : (10 : ZMod m) ^ (L - 1) = 1)
    (hLE : Even L)
    (hlive : m ≤ 1 + 9 * ((Finset.range (L / 2)).filter (fun i =>
        ∀ p ∈ m.primeFactors,
          ¬ orderOf (10 : ZMod p) ∣ i)).card)
    (t : ZMod m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i, d i < 10) ∧ U ⊆ Finset.range (L / 2) ∧
      (∀ i, i ∉ U → d i = 0) ∧
      ((U.sum fun i => d i •
          (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) - 2)) = t) := by
  haveI : NeZero m := ⟨hm0.ne'⟩
  set U := (Finset.range (L / 2)).filter (fun i =>
    ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ i) with hU_def
  have hUnit : ∀ i ∈ U, IsUnit
      (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) - 2) := by
    intro i hi
    have hiL : i < L := by
      have := (Finset.mem_filter.mp hi).1
      rw [Finset.mem_range] at this
      omega
    have hiff := wshift_unit_iff_orders hm hm0 hL1 hiL
    have hcast : (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) - 2)
        = (10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i) - 2 := by
      push_cast; ring
    rw [hcast, hiff]
    exact (Finset.mem_filter.mp hi).2
  set S := U.sum fun i => (Finset.range 10).image
    (fun d : ℕ => d • (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) - 2))
    with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card :=
    card_sum_intervals hUnit
  have hcover : m ≤ 1 + 9 * U.card := hlive
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hcover
  have hSm : m ≤ S.card := by rwa [hmin] at hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      omega
    exact Finset.eq_univ_of_card S hcard
  have hmem : t ∈ S := hS_univ ▸ Finset.mem_univ t
  rw [hS, mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧
      (i ∈ U → d •
        (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) - 2) = g i) ∧
      (i ∉ U → d = 0) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq,
        fun h' => absurd hi h'⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi, fun _ => rfl⟩
  choose d hd1 hd2 hd3 using hd_ex
  refine ⟨U, d, fun i => hd1 i,
    fun i hi => (Finset.mem_filter.mp hi).1,
    fun i hi => hd3 i hi, ?_⟩
  have hcongr : (U.sum fun i => d i •
        (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m) - 2))
      = U.sum g :=
    Finset.sum_congr rfl (fun i hi => hd2 i hi)
  rw [hcongr]
  exact hgsum

/-- Positions vivantes = complement des mortes dans range X :
    #vivantes = X - #mortes. -/
theorem alive_eq_sub {m X : ℕ} :
    ((Finset.range X).filter (fun i =>
        ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ i)).card
      = X - ((Finset.range X).filter (fun i =>
        ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)).card := by
  have hdisj : Disjoint
      ((Finset.range X).filter (fun i =>
        ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ i))
      ((Finset.range X).filter (fun i =>
        ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    rcases h2 with ⟨p, hpm, hpd⟩
    exact h1 p hpm hpd
  have hunion :
      ((Finset.range X).filter (fun i =>
        ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ i))
      ∪ ((Finset.range X).filter (fun i =>
        ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i))
        = Finset.range X := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hi
      by_cases h : ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i
      · exact Or.inr ⟨hi, h⟩
      · push_neg at h
        exact Or.inl ⟨hi, h⟩
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_range] at hc
  omega

/-- ord_p(10) = 2 entraine p | 99 = 3^2 * 11, donc p = 11
    (sous 3 non | m). Unicite : au plus un premier a ordre 2. -/
theorem orderOf_two_prime {m p : ℕ} (h3 : ¬ 3 ∣ m)
    (h10 : Nat.Coprime m 10) (hp : p ∈ m.primeFactors)
    (ho : orderOf (10 : ZMod p) = 2) : p = 11 := by
  have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
  haveI : NeZero p := ⟨hpP.pos.ne'⟩
  have h2dvd : orderOf (10 : ZMod p) ∣ (2 : ℕ) := by
    rw [ho]
  have hdvd : p ∣ 10 ^ 2 - 1 :=
    (prime_dvd_pow_sub_one hpP).mpr h2dvd
  norm_num at hdvd
  -- p | 99 = 9 * 11 : p = 3 ou p = 11
  have h99 : p ∣ 99 := hdvd
  have h9911 : p = 3 ∨ p = 11 := by
    have hpf : p ∣ 3 ^ 2 * 11 := by norm_num at h99 ⊢; exact h99
    rcases (hpP.dvd_mul.mp hpf) with h9 | h11
    · have := hpP.dvd_of_dvd_pow (n := 2) h9
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime (3:ℕ))).mp this
        with h1p | h3p
      · exact absurd h1p hpP.ne_one
      · exact Or.inl h3p
    · have := (Nat.dvd_prime (by norm_num : Nat.Prime (11:ℕ))).mp h11
      rcases this with h1p | h11p
      · exact absurd h1p hpP.ne_one
      · exact Or.inr h11p
  rcases h9911 with h3p | h11p
  · exact absurd (h3p ▸ (Nat.mem_primeFactors.mp hp).2.1) h3
  · exact h11p

/-- Borne vivantes pour omega(m) <= 2, gcd(m,30)=1 :
    #vivantes >= X - (X/2 + X/3 + 2) = X/6 - 2.
    Hypotheses : ord_p >= 2 pour tout p|m, omega <= 2. -/
theorem alive_lower_bound {m X : ℕ} (h3 : ¬ 3 ∣ m)
    (h10 : Nat.Coprime m 10) (hm0 : 0 < m)
    (hords2 : ∀ p ∈ m.primeFactors, 2 ≤ orderOf (10 : ZMod p))
    (hom : (m.primeFactors).card ≤ 2) :
    X - (X / 2 + X / 3 + 2) ≤
      ((Finset.range X).filter (fun i =>
        ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ i)).card := by
  rw [alive_eq_sub]
  have hdead := dead_wshift_count (m := m) (X := X)
  have hsum : (m.primeFactors.sum fun p =>
      X / orderOf (10 : ZMod p) + 1) ≤ X / 2 + X / 3 + 2 := by
    -- Partition : au plus un premier d'ordre 2 (p=11).
    set PF := m.primeFactors
    by_cases h2 : ∃ p ∈ PF, orderOf (10 : ZMod p) = 2
    · rcases h2 with ⟨p11, hp11, ho11⟩
      have hp11e : p11 = 11 := orderOf_two_prime h3 h10 hp11 ho11
      -- PF ⊆ {p11} ∪ {ordres >= 3}
      have hrest : PF \ {p11} ⊆
          PF.filter (fun p => 3 ≤ orderOf (10 : ZMod p)) := by
        intro p hpm
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hpm
        rw [Finset.mem_filter]
        exact ⟨hpm.1, by
          rcases lt_or_ge (orderOf (10 : ZMod p)) 3 with hlt | hge
          · have ho2 : orderOf (10 : ZMod p) = 2 :=
              le_antisymm (by omega) (hords2 p hpm.1)
            have hpe11 : p = 11 :=
              orderOf_two_prime h3 h10 hpm.1 ho2
            have hpeq : p = p11 := by rw [hpe11, ← hp11e]
            exact absurd hpeq hpm.2
          · exact hge⟩
      have hcard2 : (PF \ {p11}).card ≤ 1 := by
        have hsd : (PF \ {p11}).card
            = PF.card - ({p11} ∩ PF).card := Finset.card_sdiff
        have hinter : {p11} ∩ PF = {p11} :=
          Finset.inter_eq_left.mpr
            (Finset.singleton_subset_iff.mpr hp11)
        have hc1 : 1 ≤ PF.card := Finset.card_pos.mpr ⟨p11, hp11⟩
        rw [hsd, hinter, Finset.card_singleton]
        omega
      calc (PF.sum fun p => X / orderOf (10 : ZMod p) + 1)
          = (X / orderOf (10 : ZMod p11) + 1)
            + ((PF \ {p11}).sum fun p =>
              X / orderOf (10 : ZMod p) + 1) := by
            rw [Finset.sdiff_singleton_eq_erase,
              ← Finset.sum_erase_add _ _ hp11, add_comm]
        _ ≤ (X / 2 + 1) + ((PF \ {p11}).sum fun _ => X / 3 + 1) := by
            apply Nat.add_le_add (by rw [ho11])
            apply Finset.sum_le_sum
            intro p hpm
            have := hrest hpm
            rw [Finset.mem_filter] at this
            exact Nat.add_le_add_right
              (Nat.div_le_div_left this.2 (by norm_num)) 1
        _ ≤ (X / 2 + 1) + 1 * (X / 3 + 1) := by
            apply Nat.add_le_add_left
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
            exact Nat.mul_le_mul_right _ hcard2
        _ = X / 2 + X / 3 + 2 := by ring
    · push_neg at h2
      have hrest : PF ⊆
          PF.filter (fun p => 3 ≤ orderOf (10 : ZMod p)) := by
        intro p hpm
        rw [Finset.mem_filter]
        exact ⟨hpm, by
          rcases lt_or_ge (orderOf (10 : ZMod p)) 3 with hlt | hge
          · have hord : orderOf (10 : ZMod p) = 2 :=
              le_antisymm (by omega) (hords2 p hpm)
            exact absurd hord (h2 p hpm)
          · exact hge⟩
      calc (PF.sum fun p => X / orderOf (10 : ZMod p) + 1)
          ≤ (PF.sum fun _ => X / 3 + 1) := by
            apply Finset.sum_le_sum
            intro p hpm
            have := hrest hpm
            rw [Finset.mem_filter] at this
            exact Nat.add_le_add_right
              (Nat.div_le_div_left this.2 (by norm_num)) 1
        _ = PF.card * (X / 3 + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        _ ≤ 2 * (X / 3 + 1) := Nat.mul_le_mul_right _ hom
        _ ≤ X / 2 + X / 3 + 2 := by omega
  omega

/-- ord_{81}(10) = 9 : 10^i ≡ 1 + 9(i mod 9) mod 81. -/
theorem ten_pow_mod81 (i : ℕ) :
    (10 : ZMod 81) ^ i = 1 + 9 * ((i % 9 : ℕ) : ZMod 81) := by
  conv_lhs => rw [← Nat.div_add_mod i 9, pow_add, pow_mul]
  have h9 : (10 : ZMod 81) ^ 9 = 1 := by decide
  rw [h9, one_pow, one_mul]
  have hlt : i % 9 < 9 := Nat.mod_lt _ (by norm_num)
  set r := i % 9 with hr
  interval_cases r <;> decide

/-- 9·(i mod 9) = 9·i dans ZMod 81. -/
theorem nine_mul_cast_mod9 (i : ℕ) :
    (9 : ZMod 81) * ((i % 9 : ℕ) : ZMod 81) = 9 * (i : ZMod 81) := by
  have hcast : (i : ZMod 81) = 9 * ((i / 9 : ℕ) : ZMod 81)
      + ((i % 9 : ℕ) : ZMod 81) := by
    have h1 : (i : ZMod 81)
        = ((9 * (i / 9) + i % 9 : ℕ) : ZMod 81) := by
      rw [Nat.div_add_mod]
    rw [h1]; push_cast; ring
  have h81 : ((81 : ℕ) : ZMod 81) = 0 := ZMod.natCast_self 81
  calc (9 : ZMod 81) * ((i % 9 : ℕ) : ZMod 81)
      = 9 * ((i : ZMod 81) - 9 * ((i / 9 : ℕ) : ZMod 81)) := by
        rw [hcast]; ring
    _ = 9 * (i : ZMod 81) - 81 * ((i / 9 : ℕ) : ZMod 81) := by ring
    _ = 9 * (i : ZMod 81) := by
        have : (81 : ZMod 81) = 0 := by
          rw [← Nat.cast_ofNat] ; exact h81
        rw [show (81 : ZMod 81) = ((81 : ℕ) : ZMod 81) from rfl, h81]
        ring

/-- IDENTITÉ MOD-81 : pour L = 2M+1 impair, tout palindrome
    P = ofDigits (A ++ [c] ++ A.reverse) vérifie
    P ≡ σ(P)·(1 + 9M) mod 81, σ = 2·ΣA + c. -/
theorem pal_mod81 : ∀ (A : List ℕ) (c : ℕ),
    Nat.ofDigits (10 : ZMod 81) (A ++ [c] ++ A.reverse)
      = (1 + 9 * ((A.length : ℕ) : ZMod 81))
          * (2 * ((A.sum : ℕ) : ZMod 81) + (c : ZMod 81)) := by
  intro A; induction A with
  | nil => intro c; simp [Nat.ofDigits]
  | cons a A' ih =>
    intro c
    have h1 : (a :: A') ++ [c] ++ (a :: A').reverse
        = a :: ((A' ++ [c] ++ A'.reverse) ++ [a]) := by
      simp [List.reverse_cons]
    rw [h1]
    rw [show a :: ((A' ++ [c] ++ A'.reverse) ++ [a])
        = [a] ++ ((A' ++ [c] ++ A'.reverse) ++ [a]) from rfl]
    rw [ofDigits_append', ofDigits_singleton', List.length_singleton,
      pow_one,
      show (A' ++ [c] ++ A'.reverse) ++ [a]
        = A' ++ [c] ++ A'.reverse ++ [a] from rfl,
      ofDigits_append', ofDigits_singleton', ih]
    have hlen : ((A' ++ [c] ++ A'.reverse).length : ℕ)
        = 2 * A'.length + 1 := by
      simp [List.length_append]; omega
    rw [hlen]
    have hpow : (10 : ZMod 81) ^ (2 * A'.length + 2)
        = 1 + 9 * ((2 * A'.length + 2 : ℕ) : ZMod 81) := by
      rw [ten_pow_mod81]
      congr 1
      exact nine_mul_cast_mod9 _
    have h2 : (10 : ZMod 81) ^ (2 * A'.length + 2)
        = 10 * 10 ^ (2 * A'.length + 1) := pow_succ' _ _
    have hpow2 :
        (10 : ZMod 81) * (10 ^ (2 * A'.length + 1) * (a : ZMod 81))
          = 10 ^ (2 * A'.length + 2) * (a : ZMod 81) := by
      rw [← mul_assoc, ← h2]
    rw [mul_add, hpow2, hpow, List.sum_cons, List.length_cons]
    push_cast
    have h81 : (81 : ZMod 81) = 0 := by decide
    linear_combination
      (2 * ((A'.length : ℕ) : ZMod 81)
          * (List.map Nat.cast A').sum
        + ((A'.length : ℕ) : ZMod 81) * ((c : ℕ) : ZMod 81))
        * h81

/-- Cast ℕ-ofDigits → ZMod : le ofDigits polymorphe commute avec ↑. -/
theorem ofDigits_cast (l : List ℕ) :
    ((Nat.ofDigits 10 l : ℕ) : ZMod 81)
      = Nat.ofDigits (10 : ZMod 81) l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, ih]
    rw [show d :: ds = [d] ++ ds from rfl, ofDigits_append',
      ofDigits_singleton', List.length_singleton, pow_one,
      Nat.cast_ofNat]

/-- COROLLAIRE : 81 | σ ⟹ 81 | P (cas v ≤ 4 résolu automatiquement). -/
theorem pal_dvd81 (A : List ℕ) (c : ℕ)
    (hσ : 81 ∣ 2 * A.sum + c) :
    81 ∣ Nat.ofDigits 10 (A ++ [c] ++ A.reverse) := by
  rw [← CharP.cast_eq_zero_iff (ZMod 81) 81 _]
  rw [ofDigits_cast, pal_mod81]
  have h0 : ((2 * A.sum + c : ℕ) : ZMod 81) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mpr hσ
  push_cast at h0
  push_cast
  rw [h0, mul_zero]

/-- ord_243(10) = 27 : développement binomial tronqué
    10^i ≡ 1 + 9r + 81·(C(r,2) mod 3) mod 243 pour r = i%27. -/
theorem ten_pow_mod243 (i : ℕ) :
    (10 : ZMod 243) ^ i
      = 1 + 9 * ((i % 27 : ℕ) : ZMod 243)
        + 81 * (((i % 27).choose 2 % 3 : ℕ) : ZMod 243) := by
  conv_lhs => rw [← Nat.div_add_mod i 27, pow_add, pow_mul]
  have h27 : (10 : ZMod 243) ^ 27 = 1 := by decide
  rw [h27, one_pow, one_mul]
  have hlt : i % 27 < 27 := Nat.mod_lt _ (by norm_num)
  set r := i % 27 with hr
  interval_cases r <;> decide

/-- (10^i−1)² = 81·(i%27)² dans ZMod 243 — les termes croisés
    sont multiples de 243. -/
theorem pow_sub_one_sq_mod243 (i : ℕ) :
    ((10 : ZMod 243) ^ i - 1) ^ 2
      = 81 * (((i % 27 : ℕ) : ZMod 243)) ^ 2 := by
  have h := ten_pow_mod243 i
  have hsub : (10 : ZMod 243) ^ i - 1
      = 9 * ((i % 27 : ℕ) : ZMod 243)
        + 81 * ((((i % 27).choose 2) % 3 : ℕ) : ZMod 243) := by
    rw [h]; ring
  have h243 : (243 : ZMod 243) = 0 := by decide
  rw [hsub]
  linear_combination
    (6 * ((i % 27 : ℕ) : ZMod 243)
        * ((((i % 27).choose 2) % 3 : ℕ) : ZMod 243)
      + 27 * ((((i % 27).choose 2) % 3 : ℕ) : ZMod 243) ^ 2)
      * h243

/-- 243 | (10^i−1)² ⟺ 3 | i — chaîne pure ℕ. -/
theorem dvd243_pow_sub_one_sq_iff (i : ℕ) :
    243 ∣ (10 ^ i - 1) ^ 2 ↔ 3 ∣ i := by
  have h1 : 1 ≤ 10 ^ i := Nat.one_le_pow _ _ (by norm_num)
  rw [← CharP.cast_eq_zero_iff (ZMod 243) 243 _,
    Nat.cast_pow, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  push_cast
  rw [pow_sub_one_sq_mod243]
  rw [show (81 : ZMod 243) = ((81 : ℕ) : ZMod 243) from rfl,
    ← Nat.cast_pow, ← Nat.cast_mul,
    CharP.cast_eq_zero_iff (ZMod 243) 243 _]
  rw [show (243 : ℕ) = 81 * 3 from rfl,
    Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 81)]
  constructor
  · intro h
    have hp : Nat.Prime 3 := by norm_num
    have h2 : 3 ∣ i % 27 := hp.dvd_of_dvd_pow h
    have hm : i % 27 % 3 = i % 3 :=
      Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 27)
    have hmod : i % 3 = 0 := by
      have := Nat.dvd_iff_mod_eq_zero.mp h2
      omega
    exact Nat.dvd_of_mod_eq_zero hmod
  · intro h
    have h2 : 3 ∣ i % 27 := by
      have hm : i % 27 % 3 = i % 3 :=
        Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 27)
      have := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have h3 := h2.mul_right (i % 27)
    rwa [pow_two]

/-- Pour 3∤i : (10^i−1)² = 81·u dans ZMod(3^v) avec u unité —
    cœur du relèvement 3-adique : v₃ = 4 exactement. -/
theorem pow_sub_one_sq_unit3 {v i : ℕ} (hv : 5 ≤ v) (h3 : ¬ 3 ∣ i) :
    ∃ u : ZMod (3 ^ v), ((10 : ZMod (3 ^ v)) ^ i - 1) ^ 2
        = 81 * u ∧ IsUnit u := by
  have h1 : 1 ≤ 10 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have h9dvd : 9 ∣ 10 ^ i - 1 := by
    have h : (10 ^ i : ℕ) ≡ 1 ^ i [MOD 9] :=
      Nat.ModEq.pow _ (by norm_num : (10 : ℕ) ≡ 1 [MOD 9])
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' h1).mp h.symm
  have h81 : (81 : ℕ) ∣ (10 ^ i - 1) ^ 2 := by
    have := pow_dvd_pow_of_dvd h9dvd 2
    rwa [show (9 : ℕ) ^ 2 = 81 from rfl] at this
  obtain ⟨k, hk⟩ := h81
  have hk3 : ¬ 3 ∣ k := by
    intro h3k
    have : 243 ∣ (10 ^ i - 1) ^ 2 := by
      rw [hk, show (243 : ℕ) = 81 * 3 from rfl,
        Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 81)]
      exact h3k
    exact h3 ((dvd243_pow_sub_one_sq_iff i).mp this)
  refine ⟨(k : ZMod (3 ^ v)), ?_, ?_⟩
  · have hcast : ((10 : ZMod (3 ^ v)) ^ i - 1)
        = (((10 ^ i - 1 : ℕ)) : ZMod (3 ^ v)) := by
        rw [Nat.cast_sub h1]; push_cast; ring
    rw [hcast, ← Nat.cast_pow, hk,
      show (81 : ZMod (3 ^ v)) = ((81 : ℕ) : ZMod (3 ^ v)) from rfl,
      ← Nat.cast_mul]
  · have hcp : k.Coprime (3 ^ v) := by
      rw [Nat.coprime_pow_right_iff (by omega : 0 < v)]
      exact Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd
          (by norm_num : Nat.Prime 3)).mpr hk3)
    exact (ZMod.isUnit_iff_coprime k (3 ^ v)).mpr hcp

/-- w'_i = 10^i + 10^{L−1−i} − 2 = 81·u mod 3^v, u unité,
    quand ord_{3^v}(10) | L−1 et 3∤i. Relèvement 3-adique. -/
theorem wshift_unit3 {v i L : ℕ} (hv : 5 ≤ v) (h3 : ¬ 3 ∣ i)
    (hi : i ≤ L - 1) (hord : (10 : ZMod (3 ^ v)) ^ (L - 1) = 1) :
    ∃ u : ZMod (3 ^ v), ((10 : ZMod (3 ^ v)) ^ i
        + (10 : ZMod (3 ^ v)) ^ (L - 1 - i) - 2) = 81 * u
        ∧ IsUnit u := by
  obtain ⟨u0, hu0, hu0u⟩ := pow_sub_one_sq_unit3 hv h3
  have h10 : IsUnit (10 : ZMod (3 ^ v)) :=
    (ZMod.isUnit_iff_coprime 10 (3 ^ v)).mpr (by
      rw [Nat.coprime_pow_right_iff (by omega : 0 < v)]
      norm_num)
  have hui := h10.pow i
  have hsym : (10 : ZMod (3 ^ v)) ^ (L - 1 - i)
      = ↑(hui.unit⁻¹) := by
    have heq : (10 : ZMod (3 ^ v)) ^ (L - 1 - i)
        * (10 : ZMod (3 ^ v)) ^ i = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hi, hord]
    have hspec : ↑(hui.unit) = (10 : ZMod (3 ^ v)) ^ i :=
      hui.unit_spec
    calc (10 : ZMod (3 ^ v)) ^ (L - 1 - i)
        = (10 : ZMod (3 ^ v)) ^ (L - 1 - i)
          * (↑(hui.unit) * ↑(hui.unit⁻¹)) := by
          rw [Units.mul_inv, mul_one]
      _ = ↑(hui.unit⁻¹) := by
          rw [← mul_assoc, hspec, heq, one_mul]
  refine ⟨↑(hui.unit⁻¹) * u0, ?_, ?_⟩
  · have huu : ↑(hui.unit⁻¹) * (10 : ZMod (3 ^ v)) ^ i = 1 := by
      have := hui.unit.inv_mul
      rwa [hui.unit_spec] at this
    have huu2 : ↑(hui.unit⁻¹)
        * ((10 : ZMod (3 ^ v)) ^ i) ^ 2 = (10 : ZMod (3 ^ v)) ^ i := by
      have h2 : ↑(hui.unit⁻¹)
          * ((10 : ZMod (3 ^ v)) ^ i * (10 : ZMod (3 ^ v)) ^ i)
          = (10 : ZMod (3 ^ v)) ^ i := by
        rw [← mul_assoc, huu, one_mul]
      rwa [pow_two]
    rw [hsym]
    have hid : ↑(hui.unit⁻¹)
        * ((10 : ZMod (3 ^ v)) ^ i - 1) ^ 2
        = (10 : ZMod (3 ^ v)) ^ i
          + ↑(hui.unit⁻¹) - 2 := by
      calc ↑(hui.unit⁻¹)
            * ((10 : ZMod (3 ^ v)) ^ i - 1) ^ 2
          = ↑(hui.unit⁻¹)
              * ((10 : ZMod (3 ^ v)) ^ i) ^ 2
            - 2 * (↑(hui.unit⁻¹)
              * (10 : ZMod (3 ^ v)) ^ i)
            + ↑(hui.unit⁻¹) := by ring
        _ = (10 : ZMod (3 ^ v)) ^ i - 2
            + ↑(hui.unit⁻¹) := by rw [huu2, huu, mul_one]
        _ = _ := by ring
    rw [← hid, hu0]
    ring
  · exact (hui.unit⁻¹).isUnit.mul hu0u

/-- Bord 2/5-adique : si m coprime à 10, z ≥ max(a,b) et m | P,
    alors 2^a·5^b·m | P·10^z. Le suffixe de zéros absorbe 2^a·5^b. -/
theorem border_dvd {a b m P z : ℕ} (hm : m.Coprime 10)
    (hz : a ≤ z ∧ b ≤ z) (hmP : m ∣ P) :
    2 ^ a * 5 ^ b * m ∣ P * 10 ^ z := by
  have h2 : 2 ^ a ∣ 10 ^ z :=
    (pow_dvd_pow _ hz.1).trans ⟨5 ^ z, by rw [← mul_pow]; norm_num⟩
  have h5 : 5 ^ b ∣ 10 ^ z :=
    (pow_dvd_pow _ hz.2).trans ⟨2 ^ z, by
      rw [mul_comm, ← mul_pow]; norm_num⟩
  have h2m : m.Coprime 2 := hm.coprime_dvd_right (by norm_num)
  have h5m : m.Coprime 5 := hm.coprime_dvd_right (by norm_num)
  have h25 : (2 ^ a).Coprime (5 ^ b) := by
    have h : (2 : ℕ).Coprime 5 := by norm_num
    exact (h.pow_left a).pow_right b
  have h25z : 2 ^ a * 5 ^ b ∣ 10 ^ z := by
    obtain ⟨c, hc⟩ := h2
    have h5c : 5 ^ b ∣ c := by
      have h5ac : 5 ^ b ∣ 2 ^ a * c :=
        h5.trans ⟨1, by rw [mul_one]; exact hc.symm⟩
      exact (Nat.Coprime.symm h25).dvd_of_dvd_mul_left h5ac
    obtain ⟨d, hd⟩ := h5c
    exact ⟨d, by rw [hc, hd]; ring⟩
  have h25m : (2 ^ a * 5 ^ b).Coprime m :=
    ((h2m.symm).pow_left a).mul_left ((h5m.symm).pow_left b)
  have h25Pz : 2 ^ a * 5 ^ b ∣ P * 10 ^ z :=
    h25z.trans (dvd_mul_left _ _)
  have hmPz : m ∣ P * 10 ^ z := dvd_mul_of_dvd_left hmP _
  obtain ⟨c, hc⟩ := h25Pz
  have hmc : m ∣ c := by
    have h' : m ∣ 2 ^ a * 5 ^ b * c := by rwa [hc] at hmPz
    exact (Nat.Coprime.symm h25m).dvd_of_dvd_mul_left h' 
  obtain ⟨d, hd⟩ := hmc
  exact ⟨d, by rw [hc, hd]; ring⟩

/-- IsUnit se transporte par MulEquiv. -/
theorem isUnit_mulEquiv {R S : Type*} [Monoid R] [Monoid S]
    (e : R ≃* S) {x : R} : IsUnit (e x) ↔ IsUnit x :=
  ⟨fun h => by
     have h2 : IsUnit ((e.symm : S ≃* R) (e x)) := h.map e.symm.toMonoidHom
     rwa [MulEquiv.symm_apply_apply] at h2,
   fun h => h.map e.toMonoidHom⟩

/-- Poids CRT : élément de ZMod (M*s) image de (a,b) par
    l'isomorphisme chinois (M coprime s). -/
noncomputable def crtWeight {M s : ℕ} (h : M.Coprime s)
    (a : ZMod M) (b : ZMod s) : ZMod (M * s) :=
  (ZMod.chineseRemainder h).toMulEquiv.symm (a, b)

/-- Le poids CRT est unité ssi les deux composantes le sont. -/
theorem crtWeight_isUnit {M s : ℕ} (h : M.Coprime s)
    {a : ZMod M} {b : ZMod s} :
    IsUnit (crtWeight h a b) ↔ IsUnit a ∧ IsUnit b := by
  unfold crtWeight
  rw [isUnit_mulEquiv (ZMod.chineseRemainder h).toMulEquiv.symm,
    Prod.isUnit_iff]

/-- La composante mod-M du poids CRT est a. -/
theorem crtWeight_fst {M s : ℕ} (h : M.Coprime s)
    (a : ZMod M) (b : ZMod s) :
    (ZMod.chineseRemainder h) (crtWeight h a b) = (a, b) := by
  have hrw : crtWeight h a b
      = (ZMod.chineseRemainder h).symm (a, b) := rfl
  rw [hrw]
  exact (ZMod.chineseRemainder h).apply_symm_apply _

/-- fst d'une somme de paires. -/
theorem sum_fst {ι A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (U : Finset ι) (f : ι → A × B) :
    (U.sum f).1 = U.sum fun i => (f i).1 := by
  classical
  induction U using Finset.induction with
  | empty => simp
  | insert a U ha ih => simp [Finset.sum_insert ha, ih]

/-- snd d'une somme de paires. -/
theorem sum_snd {ι A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (U : Finset ι) (f : ι → A × B) :
    (U.sum f).2 = U.sum fun i => (f i).2 := by
  classical
  induction U using Finset.induction with
  | empty => simp
  | insert a U ha ih => simp [Finset.sum_insert ha, ih]

/-- CRT envoie ↑d sur (↑d, ↑d) — le relèvement est diagonal. -/
theorem chineseRemainder_natCast {M s : ℕ} (h : M.Coprime s)
    (d : ℕ) :
    (ZMod.chineseRemainder h) ((d : ZMod (M * s)))
      = ((d : ZMod M), (d : ZMod s)) := by
  rw [map_natCast]; rfl

/-- Somme pondérée des poids CRT, composante par composante. -/
theorem chineseRemainder_sum_smul {M s : ℕ} (h : M.Coprime s)
    {ι : Type*} (U : Finset ι) (d : ι → ℕ)
    (a : ι → ZMod M) (b : ι → ZMod s) :
    (ZMod.chineseRemainder h)
        (U.sum fun i =>
          (d i : ZMod (M * s)) * crtWeight h (a i) (b i))
      = (U.sum fun i => (d i : ZMod M) * (a i),
         U.sum fun i => (d i : ZMod s) * (b i)) := by
  rw [map_sum]
  apply Prod.ext
  · rw [sum_fst]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, chineseRemainder_natCast, crtWeight_fst,
      Prod.mk_mul_mk]
  · rw [sum_snd]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, chineseRemainder_natCast, crtWeight_fst,
      Prod.mk_mul_mk]

/-- Extraction générique : poids `w` unité sur les positions vivantes
    dans range X ⇒ tout résidu t ∈ ZMod m est une somme de chiffres. -/
theorem pal_window_extract_gen {m : ℕ} [NeZero m] (hm0 : 0 < m)
    (w : ℕ → ZMod m) (base : Finset ℕ)
    (live : ℕ → Prop) [DecidablePred live]
    (hUnit : ∀ i ∈ base.filter live, IsUnit (w i))
    (hlive : m ≤ 1 + 9 * (base.filter live).card)
    (t : ZMod m) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i, d i < 10) ∧ U ⊆ base ∧
      (∀ i, i ∉ U → d i = 0) ∧
      (∀ i ∈ U, live i) ∧
      ((U.sum fun i => d i • w i) = t) := by
  set U := base.filter live with hU_def
  set S := U.sum fun i => (Finset.range 10).image (· • w i) with hS
  have hgrow : min m (1 + 9 * U.card) ≤ S.card :=
    card_sum_intervals hUnit
  have hmin : min m (1 + 9 * U.card) = m := min_eq_left hlive
  have hSm : m ≤ S.card := by rwa [hmin] at hgrow
  have hS_univ : S = Finset.univ := by
    have hcard : S.card = Fintype.card (ZMod m) := by
      have hz : Fintype.card (ZMod m) = m := ZMod.card m
      have hle : S.card ≤ Fintype.card (ZMod m) :=
        Finset.card_le_univ S
      omega
    exact Finset.eq_univ_of_card S hcard
  have hmem : t ∈ S := hS_univ ▸ Finset.mem_univ t
  rw [hS, mem_finset_sum] at hmem
  rcases hmem with ⟨g, hgmem, hgsum⟩
  have hd_ex : ∀ i, ∃ d : ℕ, d < 10 ∧
      (i ∈ U → d • w i = g i) ∧ (i ∉ U → d = 0) := by
    intro i
    by_cases hi : i ∈ U
    · have h := hgmem i hi
      rw [Finset.mem_image] at h
      rcases h with ⟨d0, hd0, hd0eq⟩
      exact ⟨d0, Finset.mem_range.mp hd0, fun _ => hd0eq,
        fun h' => absurd hi h'⟩
    · exact ⟨0, by norm_num, fun h' => absurd h' hi, fun _ => rfl⟩
  choose d hd1 hd2 hd3 using hd_ex
  refine ⟨U, d, fun i => hd1 i, ?_, fun i hi => hd3 i hi, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).1
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have hcongr : (U.sum fun i => d i • w i) = U.sum g :=
      Finset.sum_congr rfl (fun i hi => hd2 i hi)
    rw [hcongr]
    exact hgsum

/-- Extraction CRT unifiée : mod M·3^s, poids (wM i, u i) —
    U0 = positions vivantes (caractérisées par iff, sans instance). -/
theorem pal_window_extract_crt {M s : ℕ}
    (hcop : M.Coprime (3 ^ s)) (hM0 : 0 < M) (hs0 : 0 < s)
    (wM : ℕ → ZMod M) (u : ℕ → ZMod (3 ^ s))
    (U0 : Finset ℕ)
    (hU0 : ∀ i, i ∈ U0 ↔ IsUnit (wM i) ∧ IsUnit (u i))
    (hlive : M * 3 ^ s ≤ 1 + 9 * U0.card)
    (t : ZMod (M * 3 ^ s)) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ,
      (∀ i, d i < 10) ∧ U ⊆ U0 ∧
      (∀ i, i ∉ U → d i = 0) ∧
      ((U.sum fun i =>
        (d i : ZMod (M * 3 ^ s)) * crtWeight hcop (wM i) (u i)) = t) := by
  haveI : NeZero (M * 3 ^ s) :=
    ⟨Nat.mul_ne_zero hM0.ne' (pow_ne_zero _ (by norm_num))⟩
  have hMs0 : 0 < M * 3 ^ s := Nat.mul_pos hM0 (pow_pos (by norm_num) _)
  obtain ⟨U, d, hd1, hsub, hd0, hlv, hsum⟩ :=
    pal_window_extract_gen hMs0
      (fun i => crtWeight hcop (wM i) (u i)) U0
      (fun i => i ∈ U0)
      (fun i hi => by
        rw [crtWeight_isUnit]
        exact (hU0 i).mp (Finset.mem_filter.mp hi).2)
      (by rwa [Finset.filter_eq_self.mpr fun i hi => hi]) t
  refine ⟨U, d, hd1, ?_, hd0, ?_⟩
  · intro i hi
    exact hlv i hi
  · rw [show (fun i => (d i : ZMod (M * 3 ^ s))
        * crtWeight hcop (wM i) (u i))
      = fun i => d i • crtWeight hcop (wM i) (u i)
      from funext fun i => (nsmul_eq_mul ..).symm]
    exact hsum

/-- Factorisation du poids de transfert :
    w_i − w_j = 10^i · (10^{j−i} − 1) · (10^{L−1−i−j} − 1) dans ZMod m. -/
theorem wsub_factor {L m : ℕ} {i j : ℕ} (hij : i < j)
    (hijL : i + j < L - 1) :
    ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i))
      - ((10 : ZMod m) ^ j + (10 : ZMod m) ^ (L - 1 - j))
      = (10 : ZMod m) ^ i * ((10 : ZMod m) ^ (j - i) - 1)
        * ((10 : ZMod m) ^ (L - 1 - i - j) - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [show L - 1 - i - (i + d) = L - 1 - i - i - d by omega]
  have h1 : (10 : ZMod m) ^ (L - 1 - i)
      = (10 : ZMod m) ^ (L - 1 - i - i - d) * 10 ^ (i + d) := by
    rw [← pow_add]; congr 1; omega
  have h2 : (10 : ZMod m) ^ (L - 1 - (i + d))
      = (10 : ZMod m) ^ (L - 1 - i - i - d) * 10 ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [h1, h2, pow_add]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- 10^k mod 27 a période 3 : 10^k ≡ 1 (mod 27) ssi 3 | k. -/
theorem ten_pow_eq_one_mod27 {k : ℕ} :
    (10 : ZMod 27) ^ k = 1 ↔ 3 ∣ k := by
  have h3 : (10 : ZMod 27) ^ 3 = 1 := by decide
  constructor
  · intro h
    rw [show k = 3 * (k / 3) + k % 3 from (Nat.div_add_mod k 3).symm,
      pow_add, pow_mul, h3, one_pow, one_mul] at h
    have hlt : k % 3 < 3 := Nat.mod_lt k (by norm_num)
    interval_cases hk3 : k % 3
    · exact Nat.dvd_of_mod_eq_zero hk3
    · exfalso; revert h; decide
    · exfalso; revert h; decide
  · rintro ⟨q, rfl⟩
    rw [pow_mul, h3, one_pow]

/-- 10^k − 1 = 9·u avec u unité dans ZMod (3^v), pour 3 ∤ k, v ≥ 2. -/
theorem ten_pow_sub_one_nine_unit {v k : ℕ} (hv : 2 ≤ v) (hk : ¬ 3 ∣ k) :
    ∃ u : ZMod (3 ^ v), IsUnit u ∧
      (10 : ZMod (3 ^ v)) ^ k - 1 = 9 * u := by
  have h9 : 9 ∣ 10 ^ k - 1 := by
    have h1 : ((10 ^ k - 1 : ℕ) : ZMod 9) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow k 10 (by norm_num))]
      push_cast
      have h10 : (10 : ZMod 9) = 1 := by decide
      rw [h10, one_pow, sub_self]
    exact (CharP.cast_eq_zero_iff (ZMod 9) 9 _).mp h1
  set u := (10 ^ k - 1) / 9 with hu_def
  have hu9 : 9 * u = 10 ^ k - 1 := Nat.mul_div_cancel' h9
  have h3nu : ¬ 3 ∣ u := by
    rintro ⟨t, ht⟩
    have h27 : 27 ∣ 10 ^ k - 1 :=
      ⟨t, by rw [← hu9, ht]; ring⟩
    have h1 : (10 : ZMod 27) ^ k = 1 := by
      have h0 : ((10 ^ k - 1 : ℕ) : ZMod 27) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod 27) 27 _).mpr h27
      rw [Nat.cast_sub (Nat.one_le_pow k 10 (by norm_num))] at h0
      push_cast at h0
      exact sub_eq_zero.mp h0
    exact hk (ten_pow_eq_one_mod27.mp h1)
  have hcop3 : u.Coprime 3 :=
    Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr h3nu)
  have hcop : u.Coprime (3 ^ v) :=
    (Nat.coprime_pow_right_iff (by omega : 0 < v) u 3).mpr hcop3
  refine ⟨(u : ZMod (3 ^ v)), ?_, ?_⟩
  · rw [ZMod.isUnit_iff_coprime]
    exact hcop
  · have hcast : ((10 : ZMod (3 ^ v)) ^ k - 1)
        = ((10 ^ k - 1 : ℕ) : ZMod (3 ^ v)) := by
      rw [Nat.cast_sub (Nat.one_le_pow k 10 (by norm_num))]
      push_cast
      ring
    rw [hcast, ← hu9, Nat.cast_mul]
    ring

/-- Transfert Δ_{i,j} = 81·u dans ZMod (3^v), u unité, quand
    3 ∤ (j−i) et 3 ∤ (L−1−i−j). -/
theorem transfer_unit3 {v i j L : ℕ} (hv : 2 ≤ v) (hij : i < j)
    (hijL : i + j < L - 1)
    (h3a : ¬ 3 ∣ j - i) (h3b : ¬ 3 ∣ L - 1 - i - j) :
    ∃ u : ZMod (3 ^ v), IsUnit u ∧
      (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod (3 ^ v))
        - ((10 ^ j + 10 ^ (L - 1 - j) : ℕ) : ZMod (3 ^ v)))
        = 81 * u := by
  obtain ⟨ua, hua, haeq⟩ := ten_pow_sub_one_nine_unit hv h3a
  obtain ⟨ub, hub, hbeq⟩ := ten_pow_sub_one_nine_unit hv h3b
  have h10 : IsUnit (10 : ZMod (3 ^ v)) :=
    (ZMod.isUnit_iff_coprime 10 (3 ^ v)).mpr
      ((Nat.coprime_pow_right_iff (by omega : 0 < v) 10 3).mpr
        (by decide))
  refine ⟨10 ^ i * ua * ub,
    ((h10.pow i).mul hua).mul hub, ?_⟩
  have hcast : (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod (3 ^ v))
      - ((10 ^ j + 10 ^ (L - 1 - j) : ℕ) : ZMod (3 ^ v)))
      = (10 : ZMod (3 ^ v)) ^ i + (10 : ZMod (3 ^ v)) ^ (L - 1 - i)
        - ((10 : ZMod (3 ^ v)) ^ j + (10 : ZMod (3 ^ v)) ^ (L - 1 - j)) := by
    push_cast; ring
  rw [hcast, wsub_factor hij hijL, haeq, hbeq]
  ring

/-- `Coprime (10^k − 1) m` ssi aucun premier de m n'a d'ordre divisant k. -/
theorem coprime_pow_sub_one_iff {m k : ℕ} (hm : Nat.Coprime m 10)
    (hm0 : 0 < m) :
    Nat.Coprime (10 ^ k - 1) m
      ↔ ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ k := by
  constructor
  · intro hcop p hpm
    have hp := (Nat.mem_primeFactors.mp hpm).1
    have hpm_dvd := (Nat.mem_primeFactors.mp hpm).2.1
    rw [← prime_dvd_pow_sub_one hp]
    intro hdvd
    have hgd : p ∣ Nat.gcd (10 ^ k - 1) m := Nat.dvd_gcd hdvd hpm_dvd
    rw [hcop] at hgd
    exact hp.ne_one (Nat.eq_one_of_dvd_one hgd)
  · intro hall
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
    have hpm_dvd : p ∣ m := Nat.dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    have hpm : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, hpm_dvd, hm0.ne'⟩
    have hdiv : p ∣ 10 ^ k - 1 :=
      Nat.dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    exact hall p hpm ((prime_dvd_pow_sub_one hp).mp hdiv)

/-- Critère mod-M pour un transfert : unité ssi les deux écarts
    ne sont divisés par aucun ordre premier de m. -/
theorem transfer_unit_iff_orders {m L i j : ℕ} (hm : Nat.Coprime m 10)
    (hm0 : 0 < m) (hij : i < j) (hijL : i + j < L - 1) :
    IsUnit (((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i))
      - ((10 : ZMod m) ^ j + (10 : ZMod m) ^ (L - 1 - j)))
      ↔ ∀ p ∈ m.primeFactors,
        ¬ orderOf (10 : ZMod p) ∣ j - i ∧
        ¬ orderOf (10 : ZMod p) ∣ L - 1 - i - j := by
  haveI : NeZero m := ⟨hm0.ne'⟩
  rw [wsub_factor hij hijL]
  have h10 : IsUnit ((10 : ZMod m) ^ i) :=
    ((ZMod.unitOfCoprime 10 hm.symm).isUnit).pow i
  rw [IsUnit.mul_iff, IsUnit.mul_iff]
  simp only [h10, true_and]
  rw [pow_sub_one_unit_iff hm0, pow_sub_one_unit_iff hm0,
    coprime_pow_sub_one_iff hm hm0, coprime_pow_sub_one_iff hm hm0]
  constructor
  · rintro ⟨h1, h2⟩ p hp
    exact ⟨h1 p hp, h2 p hp⟩
  · intro h
    exact ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩

/-- Identité mod-81 pour longueur paire : ofDigits(A ++ A.rev)
    ≡ A.sum · (2 + 9·(2·len − 1)) — le facteur est unité mod 81. -/
theorem pal_mod81_even : ∀ (A : List ℕ),
    Nat.ofDigits (10 : ZMod 81) (A ++ A.reverse)
      = ((A.sum : ℕ) : ZMod 81)
          * (2 + 9 * (2 * (A.length : ZMod 81) - 1)) := by
  intro A; induction A with
  | nil => simp [Nat.ofDigits]
  | cons a A' ih =>
    have h1 : (a :: A') ++ (a :: A').reverse
        = a :: ((A' ++ A'.reverse) ++ [a]) := by
      simp [List.reverse_cons]
    rw [h1]
    rw [show a :: ((A' ++ A'.reverse) ++ [a])
        = [a] ++ ((A' ++ A'.reverse) ++ [a]) from rfl]
    rw [ofDigits_append', ofDigits_singleton', List.length_singleton,
      pow_one,
      show (A' ++ A'.reverse) ++ [a] = A' ++ A'.reverse ++ [a]
        from rfl,
      ofDigits_append', ofDigits_singleton', ih]
    have hlen : ((A' ++ A'.reverse).length : ℕ) = 2 * A'.length := by
      simp; omega
    rw [hlen]
    have hpow : (10 : ZMod 81) ^ (2 * A'.length + 1)
        = 1 + 9 * ((2 * A'.length + 1 : ℕ) : ZMod 81) := by
      rw [ten_pow_mod81]
      congr 1
      exact nine_mul_cast_mod9 _
    have h2 : (10 : ZMod 81) ^ (2 * A'.length + 1)
        = 10 * 10 ^ (2 * A'.length) := pow_succ' _ _
    have hpow2 :
        (10 : ZMod 81) * (10 ^ (2 * A'.length) * (a : ZMod 81))
          = 10 ^ (2 * A'.length + 1) * (a : ZMod 81) := by
      rw [← mul_assoc, ← h2]
    rw [mul_add, hpow2, hpow, List.sum_cons, List.length_cons]
    push_cast
    have h81 : (81 : ZMod 81) = 0 := by decide
    linear_combination
      (((List.map Nat.cast A').sum : ZMod 81)
        * (2 * (A'.length : ZMod 81) - 1)) * h81

/-- Palindrome pair : P ≡ 0 mod 11 (10 ≡ −1, poids alternés). -/
theorem pal_even_mod11 : ∀ (A : List ℕ),
    Nat.ofDigits (10 : ZMod 11) (A ++ A.reverse) = 0 := by
  intro A; induction A with
  | nil => simp [Nat.ofDigits]
  | cons a A' ih =>
    have h1 : (a :: A') ++ (a :: A').reverse
        = a :: ((A' ++ A'.reverse) ++ [a]) := by
      simp [List.reverse_cons]
    rw [h1]
    rw [show a :: ((A' ++ A'.reverse) ++ [a])
        = [a] ++ ((A' ++ A'.reverse) ++ [a]) from rfl]
    rw [ofDigits_append', ofDigits_singleton', List.length_singleton,
      pow_one,
      show (A' ++ A'.reverse) ++ [a] = A' ++ A'.reverse ++ [a]
        from rfl,
      ofDigits_append', ofDigits_singleton', ih]
    have hlen : ((A' ++ A'.reverse).length : ℕ) = 2 * A'.length := by
      simp; omega
    have h10 : (10 : ZMod 11) = -1 := by decide
    rw [hlen, zero_add, h10]
    rw [show (-1 : ZMod 11) ^ (2 * A'.length) = 1 by
      rw [pow_mul]; norm_num]
    ring

/-- Cast général : ↑(ofDigits ℕ) = ofDigits ZMod. -/
theorem ofDigits_cast_gen {n : ℕ} (l : List ℕ) :
    ((Nat.ofDigits 10 l : ℕ) : ZMod n)
      = Nat.ofDigits (10 : ZMod n) l := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih =>
    rw [Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, ih]
    rw [show d :: ds = [d] ++ ds from rfl, ofDigits_append',
      ofDigits_singleton', List.length_singleton, pow_one]
    ring

/-- v ≤ 4, 3^v | σ (longueur paire) ⇒ 3^v | P. -/
theorem dvd3_pow_of_sigma_even (A : List ℕ) {v : ℕ} (hv : v ≤ 4)
    (hσ : 3 ^ v ∣ 2 * A.sum) :
    3 ^ v ∣ Nat.ofDigits 10 (A ++ A.reverse) := by
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hdiv : 3 ^ v ∣ 81 :=
    ⟨3 ^ (4 - v), by
      rw [← pow_add, show v + (4 - v) = 4 by omega]; norm_num⟩
  have hSdvd : 3 ^ v ∣ A.sum :=
    Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_left _ (by decide : Nat.Coprime 3 2)) hσ
  by_cases hA : A = []
  · subst hA; simp [Nat.ofDigits]
  have hl : 1 ≤ 2 * A.length := by
    have : A.length ≠ 0 := by
      intro h; apply hA; exact List.length_eq_zero_iff.mp h
    omega
  have hU : ((2 + 9 * (2 * A.length - 1) : ℕ) : ZMod 81)
      = 2 + 9 * (2 * (A.length : ZMod 81) - 1) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hl, Nat.cast_mul]
    norm_num
  have hmod : Nat.ofDigits 10 (A ++ A.reverse)
      ≡ A.sum * (2 + 9 * (2 * A.length - 1)) [MOD 81] := by
    have h := pal_mod81_even A
    rw [← ofDigits_cast] at h
    rw [← hU, ← Nat.cast_mul] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hmodv : Nat.ofDigits 10 (A ++ A.reverse)
      ≡ A.sum * (2 + 9 * (2 * A.length - 1)) [MOD 3 ^ v] :=
    Nat.ModEq.of_dvd hdiv hmod
  have hS0 : A.sum * (2 + 9 * (2 * A.length - 1)) ≡ 0 [MOD 3 ^ v] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hSdvd _)
  exact Nat.modEq_zero_iff_dvd.mp (hmodv.trans hS0)

/-- v ≤ 4, 3^v | σ (longueur impaire) ⇒ 3^v | P. -/
theorem dvd3_pow_of_sigma_odd (A : List ℕ) (c : ℕ) {v : ℕ}
    (hv : v ≤ 4) (hσ : 3 ^ v ∣ 2 * A.sum + c) :
    3 ^ v ∣ Nat.ofDigits 10 (A ++ [c] ++ A.reverse) := by
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hdiv : 3 ^ v ∣ 81 :=
    ⟨3 ^ (4 - v), by
      rw [← pow_add, show v + (4 - v) = 4 by omega]; norm_num⟩
  have hmod : Nat.ofDigits 10 (A ++ [c] ++ A.reverse)
      ≡ (2 * A.sum + c) * (1 + 9 * A.length) [MOD 81] := by
    have h := pal_mod81 A c
    rw [← ofDigits_cast] at h
    rw [mul_comm] at h
    have hcast : ((1 + 9 * A.length : ℕ) : ZMod 81)
        = 1 + 9 * (A.length : ZMod 81) := by push_cast; ring
    rw [← hcast] at h
    have hcast2 : ((2 * A.sum + c : ℕ) : ZMod 81)
        = 2 * ((A.sum : ℕ) : ZMod 81) + (c : ZMod 81) := by
      push_cast; ring
    rw [← hcast2, ← Nat.cast_mul] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hmodv : Nat.ofDigits 10 (A ++ [c] ++ A.reverse)
      ≡ (2 * A.sum + c) * (1 + 9 * A.length) [MOD 3 ^ v] :=
    Nat.ModEq.of_dvd hdiv hmod
  have hS0 : (2 * A.sum + c) * (1 + 9 * A.length) ≡ 0 [MOD 3 ^ v] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hσ _)
  exact Nat.modEq_zero_iff_dvd.mp (hmodv.trans hS0)


-- ============================================================
-- ASSEMBLAGE : pieces fusionnees (ex-Scratch017m/p/o/n)
-- ============================================================

def palW (m L i : ℕ) : ZMod m :=
  (10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)

/-- Coprimality to `P` forces `ord_p ∤ D` for every `p | m`,
    when each `ord_p` has a prime factor in `P`. -/
theorem coprime_imp_live {m P D : ℕ} (_hm0 : 0 < m)
    (hcov : ∀ p ∈ m.primeFactors,
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ P ∧ ℓ ∣ orderOf (10 : ZMod p))
    (hcop : D.Coprime P) :
    ∀ p ∈ m.primeFactors, ¬ orderOf (10 : ZMod p) ∣ D := by
  intro p hpm hord
  obtain ⟨ℓ, hℓ, hℓP, hℓord⟩ := hcov p hpm
  have hℓD : ℓ ∣ D := dvd_trans hℓord hord
  have hℓg : ℓ ∣ Nat.gcd D P := Nat.dvd_gcd hℓD hℓP
  rw [Nat.coprime_iff_gcd_eq_one] at hcop
  rw [hcop] at hℓg
  exact hℓ.ne_one (Nat.eq_one_of_dvd_one hℓg)

/-! Transfer weight `Δ_i = w_i - w_{i+1}` is a unit mod m whenever
    `L-2-2i` is coprime to a covering modulus `P`. -/

/-- `ord_p ≠ 1` for `p | m`, `gcd(m,10)=1`, `3∤m` — hence `ord_p ∤ 1`. -/
theorem orderOf_not_dvd_one {m p : ℕ} (h3 : ¬ 3 ∣ m) (h10 : Nat.Coprime m 10)
    (hpm : p ∈ m.primeFactors) :
    ¬ orderOf (10 : ZMod p) ∣ 1 := by
  intro h
  have h1 : orderOf (10 : ZMod p) = 1 := Nat.dvd_one.mp h
  exact orderOf_ne_one h3 h10 hpm h1

/-- Unit of `Δ_i = w_i − w_{i+1}` mod `m` from coprimality of `L−2−2i`
    to a modulus `P` covering each `ord_p`. -/
theorem twt_unit_of_coprime {m P L i : ℕ} (hm : Nat.Coprime m 10)
    (hm0 : 0 < m) (h3 : ¬ 3 ∣ m)
    (hcov : ∀ p ∈ m.primeFactors,
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ P ∧ ℓ ∣ orderOf (10 : ZMod p))
    (hi : 2 * i + 3 ≤ L) (hL : 3 ≤ L)
    (hcop : (L - 2 - 2 * i).Coprime P) :
    IsUnit (((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i))
      - ((10 : ZMod m) ^ (i + 1) + (10 : ZMod m) ^ (L - 1 - (i + 1)))) := by
  rw [transfer_unit_iff_orders hm hm0 (by omega : i < i + 1)
    (by omega : i + (i + 1) < L - 1)]
  intro p hpm
  constructor
  · rw [show i + 1 - i = 1 by omega]
    exact orderOf_not_dvd_one h3 hm hpm
  · have h : L - 1 - i - (i + 1) = L - 2 - 2 * i := by omega
    rw [h]
    exact coprime_imp_live hm0 hcov hcop p hpm
/-- `twt_unit_of_coprime` repackaged on `palW` (defeq). -/
theorem twt_unit_of_coprime' {m P L i : ℕ} (hm : Nat.Coprime m 10)
    (hm0 : 0 < m) (h3 : ¬ 3 ∣ m)
    (hcov : ∀ p ∈ m.primeFactors,
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ P ∧ ℓ ∣ orderOf (10 : ZMod p))
    (hi : 2 * i + 3 ≤ L) (hL : 3 ≤ L)
    (hcop : (L - 2 - 2 * i).Coprime P) :
    IsUnit (palW m L i - palW m L (i + 1)) :=
  twt_unit_of_coprime hm hm0 h3 hcov hi hL hcop

/-- Pair digit layout: position `2k` carries `e k`, position `2k+1`
    carries `9 − e k` — every pair has digit-sum `9`. -/
def pairDigit (e : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i % 2 = 0 then e (i / 2) else 9 - e (i / 2)

theorem pairDigit_even (e : ℕ → ℕ) (k : ℕ) :
    pairDigit e (2 * k) = e k := by
  unfold pairDigit
  rw [show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]
  simp

theorem pairDigit_odd (e : ℕ → ℕ) (k : ℕ) :
    pairDigit e (2 * k + 1) = 9 - e k := by
  unfold pairDigit
  rw [show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  simp

-- ============================================================
-- DELIVERABLE 1 — covering modulus + coprime bridge
-- ============================================================

/-- Covering modulus for the transfer lemma: `3` times the product
    of the odd orders `ord_p(10)` over primes `p ∣ m`. -/
noncomputable def coverQ (m : ℕ) : ℕ :=
  3 * (m.primeFactors.filter fun p =>
    Odd (orderOf (10 : ZMod p))).prod fun p => orderOf (10 : ZMod p)

/-- A product of odd naturals is odd. -/
theorem odd_prod_of_odd {s : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ s, Odd (f p)) : Odd (∏ p ∈ s, f p) := by
  induction s using Finset.induction with
  | empty => exact ⟨0, rfl⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- (a1) `Q` is odd (product of odd orders, times odd `3`). -/
theorem coverQ_odd (m : ℕ) : Odd (coverQ m) := by
  unfold coverQ
  apply Odd.mul ⟨1, rfl⟩
  apply odd_prod_of_odd
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- (a2) `3 ∣ Q`. -/
theorem coverQ_three_dvd (m : ℕ) : 3 ∣ coverQ m :=
  dvd_mul_right 3 _

/-- (b) coverage: for `m` coprime to `30`, every `ord_p` has a
    prime divisor `ℓ ∣ 2 * Q` (ℓ = 2 for even orders; an odd prime
    factor of `ord_p`, itself a factor of the product, for odd
    orders — `ord_p ≠ 1` by `orderOf_ne_one`). -/
theorem coverQ_covers {m : ℕ} (hm : Nat.Coprime m 30) :
    ∀ p ∈ m.primeFactors, ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ 2 * coverQ m
      ∧ ℓ ∣ orderOf (10 : ZMod p) := by
  have h10 : Nat.Coprime m 10 :=
    hm.coprime_dvd_right (by norm_num)
  have h3 : ¬ 3 ∣ m :=
    (Nat.prime_three.coprime_iff_not_dvd).mp
      (hm.coprime_dvd_right (by norm_num)).symm
  intro p hpm
  rcases Nat.even_or_odd (orderOf (10 : ZMod p)) with hev | hod
  · obtain ⟨r, hr⟩ := hev
    exact ⟨2, Nat.prime_two, dvd_mul_right 2 _, ⟨r, by omega⟩⟩
  · have hne1 : orderOf (10 : ZMod p) ≠ 1 :=
      orderOf_ne_one h3 h10 hpm
    obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hpmem : p ∈ m.primeFactors.filter
        (fun p => Odd (orderOf (10 : ZMod p))) :=
      Finset.mem_filter.mpr ⟨hpm, hod⟩
    have hord : orderOf (10 : ZMod p)
        ∣ (m.primeFactors.filter fun p =>
            Odd (orderOf (10 : ZMod p))).prod
            fun p => orderOf (10 : ZMod p) :=
      Finset.dvd_prod_of_mem _ hpmem
    have hQ : ℓ ∣ coverQ m :=
      dvd_mul_of_dvd_right (dvd_trans hℓdvd hord) 3
    exact ⟨ℓ, hℓ, dvd_mul_of_dvd_right hQ 2, hℓdvd⟩

/-- (c) for odd `D`, coprimality to `2·Q` reduces to coprimality
    to `Q` (the factor `2` is already coprime to `D`). -/
theorem coprime_two_mul_of_odd {D Q : ℕ} (hD : Odd D) :
    D.Coprime (2 * Q) ↔ D.Coprime Q := by
  constructor
  · intro h
    exact (Nat.coprime_mul_iff_right.mp h).2
  · intro h
    exact Nat.coprime_mul_iff_right.mpr
      ⟨(Nat.coprime_two_right).mpr hD, h⟩

/-- (c) specialised to the covering modulus. -/
theorem coprime_two_mul_coverQ_of_odd {m D : ℕ} (hD : Odd D) :
    D.Coprime (2 * coverQ m) ↔ D.Coprime (coverQ m) :=
  coprime_two_mul_of_odd hD

-- ============================================================
-- DELIVERABLE 2 — pair-ofDigits computation
-- ============================================================

/-- Sums over `2K` positions split into `K` adjacent pairs. -/
theorem sum_range_pair {α : Type*} [AddCommMonoid α] (f : ℕ → α) (K : ℕ) :
    ∑ i ∈ Finset.range (2 * K), f i
      = ∑ k ∈ Finset.range K, (f (2 * k) + f (2 * k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : ∑ i ∈ Finset.range (2 * (K + 1)), f i
        = ∑ i ∈ Finset.range (2 * K), f i + f (2 * K)
          + f (2 * K + 1) := by
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
    rw [h1, ih, Finset.sum_range_succ, add_assoc]

/-- Generic palindrome window: `ofDigits` of
    `map d (range j) ++ [c] ++ reverse` in `ZMod m` equals
    `c·10^j + Σ_i d_i·w_i` with `w_i = 10^i + 10^{L-1-i}`, `L = 2j+1`.
    (Template: `hMz` in A085094.lean.) -/
theorem ofDigits_pal_window {m j L : ℕ} (d : ℕ → ℕ) (c : ℕ)
    (hL : L = 2 * j + 1) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range j).map d ++ [c] ++ ((List.range j).map d).reverse)
    = (c : ZMod m) * (10 : ZMod m) ^ j
      + ∑ i ∈ Finset.range j, (d i : ZMod m) * palW m L i := by
  have h2 : (10 : ZMod m) ^ (j + 1)
      * ∑ i ∈ Finset.range j,
          (d i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i)
      = ∑ i ∈ Finset.range j,
          (d i : ZMod m) * (10 : ZMod m) ^ (2 * j - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    calc (10 : ZMod m) ^ (j + 1)
          * ((d i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i))
        = (d i : ZMod m) * ((10 : ZMod m) ^ (j + 1)
            * (10 : ZMod m) ^ (j - 1 - i)) := by ring
      _ = (d i : ZMod m) * (10 : ZMod m) ^ (j + 1 + (j - 1 - i)) := by
          rw [← pow_add]
      _ = (d i : ZMod m) * (10 : ZMod m) ^ (2 * j - i) := by
          rw [show j + 1 + (j - 1 - i) = 2 * j - i by omega]
  have hterm : ∀ i ∈ Finset.range j,
      (d i : ZMod m) * (10 : ZMod m) ^ i
        + (d i : ZMod m) * (10 : ZMod m) ^ (2 * j - i)
      = (d i : ZMod m) * palW m L i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hexp : L - 1 - i = 2 * j - i := by omega
    unfold palW
    rw [hexp, ← mul_add]
  have hS12 : (∑ i ∈ Finset.range j, (d i : ZMod m) * (10 : ZMod m) ^ i)
      + ∑ i ∈ Finset.range j,
          (d i : ZMod m) * (10 : ZMod m) ^ (2 * j - i)
      = ∑ i ∈ Finset.range j, (d i : ZMod m) * palW m L i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  rw [ofDigits_append', ofDigits_append', ofDigits_singleton',
    List.length_append, List.length_singleton,
    List.length_map, List.length_range,
    ofDigits_zmod_range, ofDigits_zmod_rev,
    h2, mul_comm ((10 : ZMod m) ^ j) ((c : ℕ) : ZMod m)]
  have hexpand : (∑ i ∈ Finset.range j,
        (d i : ZMod m) * (10 : ZMod m) ^ i)
      + (c : ZMod m) * (10 : ZMod m) ^ j
      + ∑ i ∈ Finset.range j,
          (d i : ZMod m) * (10 : ZMod m) ^ (2 * j - i)
      = (c : ZMod m) * (10 : ZMod m) ^ j
        + (∑ i ∈ Finset.range j, (d i : ZMod m) * (10 : ZMod m) ^ i
          + ∑ i ∈ Finset.range j,
              (d i : ZMod m) * (10 : ZMod m) ^ (2 * j - i)) := by
    ring
  rw [hexpand, hS12]

/-- The `K` pair contributions regroup:
    `Σ_{i<2K} d_i·w_i = Σ_{k<K} (9·w_{2k+1} + e k·(w_{2k} − w_{2k+1}))`. -/
theorem sum_pair_weights {m K : ℕ} (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) :
    ∑ i ∈ Finset.range (2 * K),
        (pairDigit e i : ZMod m) * palW m (4 * K + 1) i
    = ∑ k ∈ Finset.range K,
        ((9 : ZMod m) * palW m (4 * K + 1) (2 * k + 1)
        + (e k : ZMod m) * (palW m (4 * K + 1) (2 * k)
            - palW m (4 * K + 1) (2 * k + 1))) := by
  rw [sum_range_pair
    (fun i => (pairDigit e i : ZMod m) * palW m (4 * K + 1) i) K]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pairDigit_even, pairDigit_odd]
  rw [Nat.cast_sub (he k)]
  push_cast
  ring

/-- DELIVERABLE 2 — paired-digit window identity.
    `Db = map (pairDigit e) (range 2K)`, `L = 4K+1`, centre `c` at
    position `M = 2K`:
    `ofDigits (Db ++ [c] ++ Db.reverse) ≡
      c·10^{2K} + Σ_{k<K} (9·w_{2k+1} + e k·Δ_{2k})` in `ZMod m`,
    `Δ_{2k} = w_{2k} − w_{2k+1}` the `twt_unit_of_coprime` weight. -/
theorem ofDigits_pair_window {m K : ℕ} (e : ℕ → ℕ)
    (he : ∀ k, e k ≤ 9) (c : ℕ) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range (2 * K)).map (pairDigit e) ++ [c]
        ++ ((List.range (2 * K)).map (pairDigit e)).reverse)
    = (c : ZMod m) * (10 : ZMod m) ^ (2 * K)
      + ∑ k ∈ Finset.range K,
          ((9 : ZMod m) * palW m (4 * K + 1) (2 * k + 1)
          + (e k : ZMod m) * (palW m (4 * K + 1) (2 * k)
              - palW m (4 * K + 1) (2 * k + 1))) := by
  rw [ofDigits_pal_window (pairDigit e) c
      (by omega : (4 * K + 1) = 2 * (2 * K) + 1), sum_pair_weights e he]
theorem sigma_pal_odd (Db : List ℕ) (c : ℕ) :
    (Db ++ [c] ++ Db.reverse).sum = 2 * Db.sum + c := by
  rw [List.sum_append, List.sum_append, List.sum_reverse,
      List.sum_singleton]
  ring

/-- Somme des chiffres d'un bloc de K paires (e_k, 9−e_k) : 9·K. -/
theorem sum_pairDigit_block (e : ℕ → ℕ) (K : ℕ) (he : ∀ k, e k ≤ 9) :
    ((List.range (2 * K)).map (pairDigit e)).sum = 9 * K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h2K : List.range (2 * (K + 1)) =
        List.range (2 * K) ++ [2 * K, 2 * K + 1] := by
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring,
          List.range_succ,
          show 2 * K + 1 = 2 * K + 1 from rfl]
      rw [show (2 * K + 1 : ℕ) = 2 * K + 1 from rfl]
      have h1 : List.range (2 * K + 1) = List.range (2 * K) ++ [2 * K] :=
        List.range_succ
      rw [h1, List.append_assoc]
      simp
    rw [h2K, List.map_append, List.sum_append, ih]
    have h0 := pairDigit_even e K
    have h1 := pairDigit_odd e K
    rw [show ([2 * K, 2 * K + 1]).map (pairDigit e)
        = [e K, 9 - e K] by simp [h0, h1]]
    simp
    have := he K
    omega

/-- σ totale : paires + bloc libre + centre.
    σ(P) = 18·K + 2·F.sum + c. -/
theorem sigma_pal_pairs_free (e : ℕ → ℕ) (K : ℕ)
    (he : ∀ k, e k ≤ 9) (F : List ℕ) (c : ℕ) :
    ((List.range (2 * K)).map (pairDigit e) ++ F ++ [c]
      ++ ((List.range (2 * K)).map (pairDigit e) ++ F).reverse).sum
      = 18 * K + 2 * F.sum + c := by
  have hb := sum_pairDigit_block e K he
  rw [List.sum_append, List.sum_append, List.sum_append,
      List.sum_reverse, List.sum_append, hb, List.sum_singleton]
  ring

/-- Le bloc libre réalise toute somme R ≤ 9·t (reliure du
    réservoir `digit_sum_interval` sous forme de liste). -/
theorem exists_free_block (t R : ℕ) (hR : R ≤ 9 * t) :
    ∃ F : List ℕ, F.length = t ∧ (∀ x ∈ F, x ≤ 9) ∧ F.sum = R := by
  obtain ⟨d, hd9, _, hdsum⟩ := digit_sum_interval t R hR
  refine ⟨(List.range t).map d, by simp, ?_, ?_⟩
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hd9 i
  · have hsum : ((List.range t).map d).sum
        = (Finset.range t).sum d := by
      rw [Finset.sum_list_map_count]
      apply Finset.sum_congr (List.toFinset_range t)
      intro x hx
      rw [List.count_eq_one_of_mem List.nodup_range
            (List.mem_range.mpr (Finset.mem_range.mp hx)), one_smul]
    rw [hsum, hdsum]
/-- The trailing `len e` digits of the sandwich are `e`:
    `ofDigits (Dbe ++ MID ++ Dbe.reverse) ≡ e [MOD 10^{len e}]`
    (`ofDigits_append'` splits off the low block, which is exactly
    `Nat.digits 10 e`; the rest is a multiple of `10^{len e}`). -/
theorem pow_dvd_ofDigits_border (e : ℕ) (MID : List ℕ) :
    Nat.ofDigits 10
        (Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse)
      ≡ e [MOD 10 ^ (Nat.digits 10 e).length] := by
  rw [List.append_assoc, ofDigits_append', Nat.ofDigits_digits]
  have h0 : 10 ^ (Nat.digits 10 e).length
        * Nat.ofDigits 10 (MID ++ (Nat.digits 10 e).reverse)
      ≡ 0 [MOD 10 ^ (Nat.digits 10 e).length] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
  have h := (Nat.ModEq.refl e).add h0
  exact h

/-- `2^{a-z}·5^{b-z}` divides the sandwiched palindrome once it divides
    `e` and the border covers `max (a-z) (b-z)` digits (so it also
    divides `10^{len e}`).  Route: `pow_dvd_ofDigits_border` +
    `Nat.ModEq.of_dvd` (the modulus shrinks from `10^{len e}` to `d`)
    then transitivity through `e ≡ 0`. -/
theorem border_dvd_pal {a b e : ℕ} (MID : List ℕ)
    (_heu : e % 10 ≠ 0)
    (hlen : max (a - min a b) (b - min a b) ≤ (Nat.digits 10 e).length)
    (hde : 2 ^ (a - min a b) * 5 ^ (b - min a b) ∣ e) :
    2 ^ (a - min a b) * 5 ^ (b - min a b) ∣
      Nat.ofDigits 10
        (Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse) := by
  have h2z : 2 ^ (a - min a b) ∣ 10 ^ (Nat.digits 10 e).length :=
    (pow_dvd_pow _ (le_trans (le_max_left _ _) hlen)).trans
      ⟨5 ^ (Nat.digits 10 e).length, by rw [← mul_pow]; norm_num⟩
  have h5z : 5 ^ (b - min a b) ∣ 10 ^ (Nat.digits 10 e).length :=
    (pow_dvd_pow _ (le_trans (le_max_right _ _) hlen)).trans
      ⟨2 ^ (Nat.digits 10 e).length, by
        rw [mul_comm, ← mul_pow]; norm_num⟩
  have hcop : (2 ^ (a - min a b)).Coprime (5 ^ (b - min a b)) := by
    have h : (2 : ℕ).Coprime 5 := by norm_num
    exact (h.pow_left _).pow_right _
  have hd10 : 2 ^ (a - min a b) * 5 ^ (b - min a b)
      ∣ 10 ^ (Nat.digits 10 e).length :=
    hcop.mul_dvd_of_dvd_of_dvd h2z h5z
  have hmod := pow_dvd_ofDigits_border e MID
  have hmodv : Nat.ofDigits 10
        (Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse)
      ≡ e [MOD 2 ^ (a - min a b) * 5 ^ (b - min a b)] :=
    Nat.ModEq.of_dvd hd10 hmod
  have he0 : e ≡ 0 [MOD 2 ^ (a - min a b) * 5 ^ (b - min a b)] :=
    Nat.modEq_zero_iff_dvd.mpr hde
  exact Nat.modEq_zero_iff_dvd.mp (hmodv.trans he0)

/-- Existence of the border block `e`: nonzero unit digit, divisible by
    the leftover `2^{a-z}·5^{b-z}` (a pure power since `z = min a b` —
    `5^{b-a}` for `a ≤ b` via `exists_e_five_pow`, `2^{a-b}` for `b ≤ a`
    via `exists_e_two_pow`), and of the exact covering length
    `max 1 (max (a-z) (b-z))` digits. -/
theorem exists_border_e {a b : ℕ} :
    ∃ e : ℕ, e % 10 ≠ 0 ∧
      2 ^ (a - min a b) * 5 ^ (b - min a b) ∣ e ∧
      (Nat.digits 10 e).length
        = max 1 (max (a - min a b) (b - min a b)) := by
  rcases le_total a b with hab | hba
  · -- a ≤ b : min a b = a ; leftover = 5^{b-a}
    rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
    · -- a = b : leftover = 1 ; take a one-digit e (2^1 block), len = 1
      obtain ⟨e, hde, hge, hlt, hmod⟩ := exists_e_two_pow (a := 1) le_rfl
      refine ⟨e, hmod, ?_, ?_⟩
      · have h1 : a - min a b = 0 := by omega
        have h2 : b - min a b = 0 := by omega
        rw [h1, h2]; simp
      · have h1 : a - min a b = 0 := by omega
        have h2 : b - min a b = 0 := by omega
        have he0 : e ≠ 0 := by
          have hten : 0 < 10 ^ (1 - 1 : ℕ) := by norm_num
          omega
        have hlen : (Nat.digits 10 e).length = 1 := by
          rw [Nat.length_digits 10 e (by norm_num) he0]
          have hlog : Nat.log 10 e = 1 - 1 := by
            apply Nat.log_eq_of_pow_le_of_lt_pow hge
            rw [Nat.sub_add_cancel le_rfl]; exact hlt
          omega
        rw [h1, h2, hlen]; omega
    · -- a < b : e on b - a digits divisible by 5^{b-a}
      obtain ⟨e, hde, hge, hlt, hmod⟩ := exists_e_five_pow hpos
      refine ⟨e, hmod, ?_, ?_⟩
      · have h1 : a - min a b = 0 := by omega
        have h2 : b - min a b = b - a := by omega
        rw [h1, h2, pow_zero, one_mul]; exact hde
      · have h1 : a - min a b = 0 := by omega
        have h2 : b - min a b = b - a := by omega
        have he0 : e ≠ 0 := by
          have hten : 0 < 10 ^ (b - a - 1) := by positivity
          omega
        have hlen : (Nat.digits 10 e).length = b - a := by
          rw [Nat.length_digits 10 e (by norm_num) he0]
          have hlog : Nat.log 10 e = b - a - 1 := by
            apply Nat.log_eq_of_pow_le_of_lt_pow hge
            rw [Nat.sub_add_cancel hpos]; exact hlt
          omega
        rw [h1, h2, hlen]; omega
  · -- b ≤ a : min a b = b ; leftover = 2^{a-b}
    rcases Nat.eq_zero_or_pos (a - b) with h0 | hpos
    · -- a = b : leftover = 1 ; same one-digit e, len = 1
      obtain ⟨e, hde, hge, hlt, hmod⟩ := exists_e_two_pow (a := 1) le_rfl
      refine ⟨e, hmod, ?_, ?_⟩
      · have h1 : a - min a b = 0 := by omega
        have h2 : b - min a b = 0 := by omega
        rw [h1, h2]; simp
      · have h1 : a - min a b = 0 := by omega
        have h2 : b - min a b = 0 := by omega
        have he0 : e ≠ 0 := by
          have hten : 0 < 10 ^ (1 - 1 : ℕ) := by norm_num
          omega
        have hlen : (Nat.digits 10 e).length = 1 := by
          rw [Nat.length_digits 10 e (by norm_num) he0]
          have hlog : Nat.log 10 e = 1 - 1 := by
            apply Nat.log_eq_of_pow_le_of_lt_pow hge
            rw [Nat.sub_add_cancel le_rfl]; exact hlt
          omega
        rw [h1, h2, hlen]; omega
    · -- b < a : e on a - b digits divisible by 2^{a-b}
      obtain ⟨e, hde, hge, hlt, hmod⟩ := exists_e_two_pow hpos
      refine ⟨e, hmod, ?_, ?_⟩
      · have h1 : a - min a b = a - b := by omega
        have h2 : b - min a b = 0 := by omega
        rw [h1, h2, pow_zero, mul_one]; exact hde
      · have h1 : a - min a b = a - b := by omega
        have h2 : b - min a b = 0 := by omega
        have he0 : e ≠ 0 := by
          have hten : 0 < 10 ^ (a - b - 1) := by positivity
          omega
        have hlen : (Nat.digits 10 e).length = a - b := by
          rw [Nat.length_digits 10 e (by norm_num) he0]
          have hlog : Nat.log 10 e = a - b - 1 := by
            apply Nat.log_eq_of_pow_le_of_lt_pow hge
            rw [Nat.sub_add_cancel hpos]; exact hlt
          omega
        rw [h1, h2, hlen]; omega
def twt (m L k : ℕ) : ZMod m := palW m L (2 * k) - palW m L (2 * k + 1)

/-- Stage-live predicate (mod-`p_i` neutralization version):
    `ord_{p_i} | X_k` for all `i < j` and `ord_{p_j} ∤ X_k`,
    where `X_k = L − 2 − 4k`. -/
def stageLive (prev : Finset ℕ) (p L k : ℕ) : Prop :=
  (∀ q ∈ prev, orderOf (10 : ZMod q) ∣ L - 2 - 4 * k)
    ∧ ¬ orderOf (10 : ZMod p) ∣ L - 2 - 4 * k

/-- Stage-live predicate, prime-power version: neutralization by
    `ord_{q^{e q}} | X_k` (so `Δ_{2k} ≡ 0 mod q^{e q}`), unit by
    `ord_p ∤ X_k`.  This is the version `extract_all` consumes. -/
def stageLivePow (e : ℕ → ℕ) (prev : Finset ℕ) (p L k : ℕ) : Prop :=
  (∀ q ∈ prev, orderOf (10 : ZMod (q ^ e q)) ∣ L - 2 - 4 * k)
    ∧ ¬ orderOf (10 : ZMod p) ∣ L - 2 - 4 * k

-- ============================================================
-- Section 1 — vanishing and unit of `Δ_{2k}` (deliverable 1)
-- ============================================================

/-- Factorization `w_{2k} − w_{2k+1} = 10^{2k}·9·(10^{X_k} − 1)`
    specialized from `wsub_factor`. -/
theorem twt_factor {m L k : ℕ} (hk : 4 * k + 3 ≤ L) :
    twt m L k
      = (10 : ZMod m) ^ (2 * k) * ((10 : ZMod m) ^ 1 - 1)
        * ((10 : ZMod m) ^ (L - 2 - 4 * k) - 1) := by
  have h := wsub_factor (m := m) (L := L) (i := 2 * k) (j := 2 * k + 1)
    (by omega) (by omega)
  unfold twt palW
  rw [h]
  have hji : 2 * k + 1 - 2 * k = 1 := by omega
  have hX : L - 1 - 2 * k - (2 * k + 1) = L - 2 - 4 * k := by omega
  rw [hji, hX]

/-- Vanishing: `ord_r(10) | X_k` forces `Δ_{2k} = 0` in `ZMod r`
    — works for `r = p_i` (deliverable 1) and `r = p_i^{α_i}`
    (strong neutralization). -/
theorem twt_eq_zero_of_orderOf_dvd {r L k : ℕ} (hk : 4 * k + 3 ≤ L)
    (hord : orderOf (10 : ZMod r) ∣ L - 2 - 4 * k) :
    twt r L k = 0 := by
  rw [twt_factor hk, orderOf_dvd_iff_pow_eq_one.mp hord]
  simp

/-- Unit: `ord_q ∤ X_k` for every `q | r` (and `3 ∤ r`, killing the
    first-gap condition `ord_q ∤ 1`) gives `IsUnit (Δ_{2k})` in
    `ZMod r` — glue onto `transfer_unit_iff_orders`.  Instantiates
    to `r = p_j` or `r = p_j^{α_j}`. -/
theorem twt_isUnit {r L k : ℕ} (hrcop : r.Coprime 10) (hr0 : 0 < r)
    (h3 : ¬ 3 ∣ r) (hk : 4 * k + 3 ≤ L)
    (hlive : ∀ q ∈ r.primeFactors,
      ¬ orderOf (10 : ZMod q) ∣ L - 2 - 4 * k) :
    IsUnit (twt r L k) := by
  have hiff := transfer_unit_iff_orders (m := r) (L := L)
    (i := 2 * k) (j := 2 * k + 1) hrcop hr0 (by omega) (by omega)
  unfold twt palW
  rw [hiff]
  intro q hq
  have hji : 2 * k + 1 - 2 * k = 1 := by omega
  have hX : L - 1 - 2 * k - (2 * k + 1) = L - 2 - 4 * k := by omega
  rw [hji, hX]
  exact ⟨orderOf_not_dvd_one h3 hrcop hq, hlive q hq⟩

/-- `p ≠ 3` prime implies `¬ 3 ∣ p` — helper for the `h3`
    hypotheses. -/
theorem three_not_dvd_of_prime_ne_three {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) : ¬ 3 ∣ p := by
  intro hd
  rcases (Nat.dvd_prime hp).mp hd with h1 | h3
  · exact absurd h1 (by norm_num)
  · exact hp3 h3.symm

/-- `(p^α)` for `p` prime `≥ 7`-ish (`¬ p | 10`, `p ≠ 3`) is
    coprime to `10` and not divisible by `3`. -/
theorem coprime_pow_prime {p α : ℕ} (hp : p.Prime) (hp10 : ¬ p ∣ 10)
    (hα : 0 < α) : (p ^ α).Coprime 10 :=
  (Nat.coprime_pow_left_iff hα p 10).mpr
    (hp.coprime_iff_not_dvd.mpr hp10)

theorem three_not_dvd_pow {p α : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hα : 0 < α) : ¬ 3 ∣ p ^ α := by
  intro hd
  exact three_not_dvd_of_prime_ne_three hp hp3
    (Nat.prime_three.dvd_of_dvd_pow hd)

/-- DELIVERABLE 1 — at a `stageLive` index `k`, `Δ_{2k}` vanishes
    mod every earlier prime `q ∈ prev` and is a unit mod `p`. -/
theorem stageLive_spec {prev : Finset ℕ} {p L k : ℕ}
    (hprev : ∀ q ∈ prev, q.Prime) (hp : p.Prime)
    (hp10 : ¬ p ∣ 10) (hp3 : p ≠ 3) (hk : 4 * k + 3 ≤ L)
    (h : stageLive prev p L k) :
    (∀ q ∈ prev, twt q L k = 0) ∧ IsUnit (twt p L k) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · haveI : NeZero q := ⟨(hprev q hq).pos.ne'⟩
    exact twt_eq_zero_of_orderOf_dvd hk (h.1 q hq)
  · apply twt_isUnit (hp.coprime_iff_not_dvd.mpr hp10) hp.pos
      (three_not_dvd_of_prime_ne_three hp hp3) hk
    intro q hq
    rw [hp.primeFactors] at hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact h.2

/-- DELIVERABLE 1 (prime-power version) — at a `stageLivePow` index,
    `Δ_{2k}` vanishes in `ZMod (q^{e q})` for every `q ∈ prev` and
    is a unit in `ZMod (p^α)`. -/
theorem stageLivePow_spec {e : ℕ → ℕ} {prev : Finset ℕ} {p L k α : ℕ}
    (he : ∀ q ∈ prev, 0 < e q)
    (hprev : ∀ q ∈ prev, q.Prime) (hp : p.Prime)
    (hp10 : ¬ p ∣ 10) (hp3 : p ≠ 3) (hα : 0 < α) (hk : 4 * k + 3 ≤ L)
    (h : stageLivePow e prev p L k) :
    (∀ q ∈ prev, twt (q ^ e q) L k = 0) ∧ IsUnit (twt (p ^ α) L k) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · haveI : NeZero (q ^ e q) :=
      ⟨pow_ne_zero _ (hprev q hq).pos.ne'⟩
    exact twt_eq_zero_of_orderOf_dvd hk (h.1 q hq)
  · apply twt_isUnit (coprime_pow_prime hp hp10 hα)
      (pow_pos hp.pos α) (three_not_dvd_pow hp hp3 hα) hk
    intro q hq
    rw [Nat.primeFactors_pow p hα.ne', hp.primeFactors] at hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact h.2

-- ============================================================
-- Section 2 — counting live positions (deliverable 2)
-- ============================================================

/-- Positions `k ∈ Ico a (a+N)` with `O | C − 4k` lie in a single
    residue class mod `s = O / gcd(O,4)` — hence at most `N/s + 1`
    of them (needs `4k ≤ C` on the whole block, i.e. no truncated
    subtraction). -/
theorem card_dvd_affine_le {C O a N : ℕ} (hO : 0 < O)
    (hb : 4 * (a + N) ≤ C + 4) :
    ((Finset.Ico a (a + N)).filter (fun k => O ∣ C - 4 * k)).card
      ≤ 4 * N / O + 1 := by
  classical
  set s := O / Nat.gcd O 4 with hs
  have hgO : Nat.gcd O 4 ∣ O := Nat.gcd_dvd_left O 4
  have hgs : s * Nat.gcd O 4 = O := Nat.div_mul_cancel hgO
  have hgpos : 0 < Nat.gcd O 4 :=
    Nat.gcd_pos_of_pos_right O (by norm_num)
  have hspos : 0 < s := Nat.div_pos (Nat.le_of_dvd hO hgO) hgpos
  -- spacing: two distinct solutions differ by a multiple of `s`
  have hgap : ∀ k₁ k₂ : ℕ,
      k₁ ∈ (Finset.Ico a (a + N)).filter (fun k => O ∣ C - 4 * k) →
      k₂ ∈ (Finset.Ico a (a + N)).filter (fun k => O ∣ C - 4 * k) →
      k₁ < k₂ → s ∣ k₂ - k₁ := by
    intro k₁ k₂ hk₁ hk₂ hlt
    rw [Finset.mem_filter, Finset.mem_Ico] at hk₁ hk₂
    have hle2 : 4 * k₂ ≤ C := by omega
    have hsub : (C - 4 * k₁) - (C - 4 * k₂) = 4 * (k₂ - k₁) := by
      omega
    have hd : O ∣ 4 * (k₂ - k₁) := by
      rw [← hsub]
      exact Nat.dvd_sub hk₁.2 hk₂.2
    have hme : (4 * (k₂ - k₁)) ≡ (4 * 0) [MOD O] :=
      Nat.modEq_zero_iff_dvd.mpr hd
    have hme' : (k₂ - k₁) ≡ 0 [MOD s] :=
      Nat.ModEq.cancel_left_div_gcd hO hme
    exact Nat.modEq_zero_iff_dvd.mp hme'
  -- inject `k ↦ (k − a)/s` into `range (N/s + 1)`
  have hinj : Set.InjOn (fun k => (k - a) / s)
      ((Finset.Ico a (a + N)).filter (fun k => O ∣ C - 4 * k)) := by
    intro k₁ hk₁ k₂ hk₂ h
    change (k₁ - a) / s = (k₂ - a) / s at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨u, hu⟩ := hgap k₁ k₂ hk₁ hk₂ hlt
      have hu0 : 0 < u := by
        rcases u with _ | u
        · rw [mul_zero] at hu
          omega
        · exact Nat.succ_pos _
      have hke : k₂ - a = (k₁ - a) + s * u := by
        have h1 : a ≤ k₁ :=
          (Finset.mem_Ico.mp
            (Finset.mem_filter.mp (Finset.mem_coe.mp hk₁)).1).1
        omega
      have hdiv : ((k₁ - a) + s * u) / s = (k₁ - a) / s + u :=
        Nat.add_mul_div_left _ _ hspos
      rw [hke, hdiv] at h
      omega
    · obtain ⟨u, hu⟩ := hgap k₂ k₁ hk₂ hk₁ hlt
      have hu0 : 0 < u := by
        rcases u with _ | u
        · rw [mul_zero] at hu
          omega
        · exact Nat.succ_pos _
      have hke : k₁ - a = (k₂ - a) + s * u := by
        have h2 : a ≤ k₂ :=
          (Finset.mem_Ico.mp
            (Finset.mem_filter.mp (Finset.mem_coe.mp hk₂)).1).1
        omega
      have hdiv : ((k₂ - a) + s * u) / s = (k₂ - a) / s + u :=
        Nat.add_mul_div_left _ _ hspos
      rw [hke, hdiv] at h
      omega
  have hcard := Finset.card_le_card_of_injOn
    (fun k => (k - a) / s)
    (t := Finset.range (N / s + 1))
    (by
      intro k hk
      simp only [Finset.mem_coe, Finset.mem_range]
      have : k - a < N := by
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hk
        omega
      have hle : (k - a) / s ≤ (N - 1) / s :=
        Nat.div_le_div_right (by omega)
      have hle2 : (N - 1) / s ≤ N / s :=
        Nat.div_le_div_right (by omega)
      omega)
    hinj
  rw [Finset.card_range] at hcard
  -- `N/s + 1 = N·gcd(O,4)/O + 1 ≤ 4N/O + 1`
  have hNs : N / s = N * Nat.gcd O 4 / O := by
    have h1 : N * Nat.gcd O 4 / O
        = N * Nat.gcd O 4 / (s * Nat.gcd O 4) := by
      rw [hgs]
    rw [h1, Nat.mul_div_mul_right N s hgpos]
  rw [hNs] at hcard
  have hg4 : Nat.gcd O 4 ≤ 4 := Nat.gcd_le_right O (by norm_num)
  have hNg : N * Nat.gcd O 4 ≤ 4 * N := by
    calc N * Nat.gcd O 4 ≤ N * 4 := Nat.mul_le_mul_left N hg4
      _ = 4 * N := Nat.mul_comm N 4
  exact le_trans hcard
    (Nat.add_le_add_right (Nat.div_le_div_right hNg) 1)

/-- At least `N/O` positions `k ∈ Ico a (a+N)` satisfy `O | C−4k`
    whenever one solution `k₀` lies in `[a, a+O)` — injection of
    `t ↦ k₀ + O·t` (valid even past the truncation point, since
    `O | 0`). -/
theorem card_dvd_affine_ge {C O a N : ℕ} (hO : 0 < O)
    (hk0 : ∃ k₀ ∈ Finset.Ico a (a + O), O ∣ C - 4 * k₀) :
    N / O ≤ ((Finset.Ico a (a + N)).filter
      (fun k => O ∣ C - 4 * k)).card := by
  classical
  rcases hk0 with ⟨k₀, hk0mem, hk0dvd⟩
  rw [Finset.mem_Ico] at hk0mem
  by_cases hN : k₀ < a + N
  · set T := (a + N - 1 - k₀) / O + 1 with hT
    have hmap : ∀ t ∈ Finset.range T,
        k₀ + O * t ∈ (Finset.Ico a (a + N)).filter
          (fun k => O ∣ C - 4 * k) := by
      intro t ht
      rw [Finset.mem_range] at ht
      have ht' : t ≤ (a + N - 1 - k₀) / O := by omega
      have hOt : O * t ≤ a + N - 1 - k₀ :=
        le_trans (Nat.mul_le_mul_left O ht') (Nat.mul_div_le _ _)
      have hkmem : k₀ + O * t ∈ Finset.Ico a (a + N) := by
        rw [Finset.mem_Ico]
        omega
      have hdvd : O ∣ C - 4 * (k₀ + O * t) := by
        by_cases h4 : 4 * (k₀ + O * t) ≤ C
        · have heq : C - 4 * (k₀ + O * t)
              = (C - 4 * k₀) - 4 * (O * t) := by omega
          rw [heq]
          exact Nat.dvd_sub hk0dvd ⟨4 * t, by ring⟩
        · rw [Nat.sub_eq_zero_of_le
            (by omega : C ≤ 4 * (k₀ + O * t))]
          exact dvd_zero O
      exact Finset.mem_filter.mpr ⟨hkmem, hdvd⟩
    have hinj : Set.InjOn (fun t => k₀ + O * t) (Finset.range T) := by
      intro t₁ _ t₂ _ h
      change k₀ + O * t₁ = k₀ + O * t₂ at h
      have hmul : O * t₁ = O * t₂ := by omega
      exact Nat.eq_of_mul_eq_mul_left hO hmul
    have hcard := Finset.card_le_card_of_injOn
      (fun t => k₀ + O * t) hmap hinj
    rw [Finset.card_range] at hcard
    have hTge : N / O ≤ T := by
      have h1 : N - O ≤ a + N - 1 - k₀ := by omega
      have h2 : (N - O) / O ≤ (a + N - 1 - k₀) / O :=
        Nat.div_le_div_right h1
      have h3 : N / O ≤ (N - O) / O + 1 := by
        by_cases hNO : N < O
        · have hz : N / O = 0 := (Nat.div_eq_zero_iff_lt hO).mpr hNO
          rw [hz]
          exact Nat.zero_le _
        · have hNO' : O ≤ N := not_lt.mp hNO
          have key : N / O - 1 ≤ (N - O) / O := by
            rw [Nat.le_div_iff_mul_le hO]
            have h7 : N / O * O ≤ N := Nat.div_mul_le_self _ _
            calc (N / O - 1) * O = N / O * O - O := by
                    rw [Nat.sub_mul, Nat.one_mul]
              _ ≤ N - O := by omega
          omega
      rw [hT]
      exact le_trans h3 (Nat.add_le_add_right h2 1)
    exact le_trans hTge hcard
  · have hN' : a + N ≤ k₀ := not_lt.mp hN
    have hlt : N < O := by omega
    have hz : N / O = 0 := (Nat.div_eq_zero_iff_lt hO).mpr hlt
    rw [hz]
    exact Nat.zero_le _

/-- DELIVERABLE 2 — live-position count in a block: writing
    `O = ∏_{q∈prev} ord_q(10)` and `o = ord_p(10)`, the block
    `Ico a (a+N)` contains at least `N/O − (4N/o + 1)`
    `stageLive`-positions (`X_k = C − 4k` affine, `O|X_k` implies
    every `ord_q | X_k`; the bound is `≥ N/O − #dead`, `#dead ≤
    4N/o + 1` by the AP argument of `card_dvd_affine_le`). -/
theorem card_stage_live {prev : Finset ℕ} {p C a N : ℕ}
    (hpos : ∀ q ∈ prev, 0 < orderOf (10 : ZMod q))
    (hopos : 0 < orderOf (10 : ZMod p))
    (hb : 4 * (a + N) ≤ C + 4)
    (hk0 : ∃ k₀ ∈ Finset.Ico a
        (a + (prev.prod fun q => orderOf (10 : ZMod q))),
      (prev.prod fun q => orderOf (10 : ZMod q)) ∣ C - 4 * k₀) :
    N / (prev.prod fun q => orderOf (10 : ZMod q))
      ≤ ((Finset.Ico a (a + N)).filter (fun k =>
          (∀ q ∈ prev, orderOf (10 : ZMod q) ∣ C - 4 * k)
            ∧ ¬ orderOf (10 : ZMod p) ∣ C - 4 * k)).card
        + (4 * N / orderOf (10 : ZMod p) + 1) := by
  classical
  set O := prev.prod fun q => orderOf (10 : ZMod q) with hO
  set o := orderOf (10 : ZMod p) with ho
  have hOpos : 0 < O := Finset.prod_pos hpos
  set A := (Finset.Ico a (a + N)).filter (fun k => O ∣ C - 4 * k)
    with hA
  set S := (Finset.Ico a (a + N)).filter (fun k =>
      (∀ q ∈ prev, orderOf (10 : ZMod q) ∣ C - 4 * k)
        ∧ ¬ o ∣ C - 4 * k) with hS
  -- `O | X_k` implies every `ord_q | X_k`
  have hsub1 : A.filter (fun k => ¬ o ∣ C - 4 * k) ⊆ S := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    rcases hk with ⟨hkA, hk2⟩
    rw [Finset.mem_filter] at hkA
    refine ⟨hkA.1, ⟨fun q hq => ?_, hk2⟩⟩
    exact (Finset.dvd_prod_of_mem _ hq).trans hkA.2
  -- cardinal bookkeeping : #S ≥ #A − #dead
  have hcardA : N / O ≤ A.card := card_dvd_affine_ge hOpos hk0
  have hcardB : ((Finset.Ico a (a + N)).filter
      (fun k => o ∣ C - 4 * k)).card ≤ 4 * N / o + 1 :=
    card_dvd_affine_le hopos hb
  have hAcard : A.card =
      (A.filter (fun k => o ∣ C - 4 * k)).card
      + (A.filter (fun k => ¬ o ∣ C - 4 * k)).card :=
    (Finset.card_filter_add_card_filter_not (s := A)
      (fun k => o ∣ C - 4 * k)).symm
  have hsub2 : A.filter (fun k => o ∣ C - 4 * k)
      ⊆ (Finset.Ico a (a + N)).filter (fun k => o ∣ C - 4 * k) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨(Finset.mem_filter.mp hk.1).1, hk.2⟩
  have hle1 : (A.filter (fun k => o ∣ C - 4 * k)).card
      ≤ 4 * N / o + 1 :=
    le_trans (Finset.card_le_card hsub2) hcardB
  have hle2 : N / O - (4 * N / o + 1) ≤ S.card := by
    have h1 : N / O ≤ A.card := hcardA
    have h2 : (A.filter (fun k => ¬ o ∣ C - 4 * k)).card ≤ S.card :=
      Finset.card_le_card hsub1
    omega
  omega

-- ============================================================
-- Section 3 — one CRT stage (deliverable 3)
-- ============================================================

/-- The first component of `ZMod.chineseRemainder` is `castHom`. -/
theorem chineseRemainder_fst {M s : ℕ} (h : M.Coprime s)
    (x : ZMod (M * s)) :
    ((ZMod.chineseRemainder h) x).1
      = ZMod.castHom (dvd_mul_right M s) (ZMod M) x := by
  have hx : ZMod.chineseRemainder h x =
      ZMod.castHom (show M.lcm s ∣ M * s by simp [Nat.lcm_dvd_iff])
        (ZMod M × ZMod s) x := rfl
  rw [hx, ZMod.castHom_apply, Prod.fst_zmod_cast, ZMod.castHom_apply]

/-- The second component of `ZMod.chineseRemainder` is `castHom`. -/
theorem chineseRemainder_snd {M s : ℕ} (h : M.Coprime s)
    (x : ZMod (M * s)) :
    ((ZMod.chineseRemainder h) x).2
      = ZMod.castHom (dvd_mul_left s M) (ZMod s) x := by
  have hx : ZMod.chineseRemainder h x =
      ZMod.castHom (show M.lcm s ∣ M * s by simp [Nat.lcm_dvd_iff])
        (ZMod M × ZMod s) x := rfl
  rw [hx, ZMod.castHom_apply, Prod.snd_zmod_cast, ZMod.castHom_apply]

/-- DELIVERABLE 3 — one stage of sequential extraction.

    All weights `w k` on the block `base` vanish on the `R`-component
    (`(e (w k)).1 = 0`, the strong neutralization `R | w k`), and the
    `live` ones have a unit `q`-component.  With `q ≤ 1 + 9·#live`
    positions, any `t : ZMod q` is reachable by a digit-sum whose
    total in `ZMod (R·q)` is `(0, t)` under CRT — i.e. the stage
    moves only the `q`-component. -/
theorem extract_stage {R q : ℕ} (hR : 0 < R) (hq : 0 < q)
    (hcop : R.Coprime q) (w : ℕ → ZMod (R * q)) (base : Finset ℕ)
    (live : ℕ → Prop) [DecidablePred live]
    (hvan : ∀ k ∈ base,
      ((ZMod.chineseRemainder hcop) (w k)).1 = 0)
    (hunit : ∀ k ∈ base.filter live,
      IsUnit ((ZMod.chineseRemainder hcop (w k)).2))
    (hcard : q ≤ 1 + 9 * (base.filter live).card)
    (t : ZMod q) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ, (∀ i, d i < 10) ∧ U ⊆ base ∧
      (∀ i, i ∉ U → d i = 0) ∧ (∀ i ∈ U, live i) ∧
      (U.sum fun i => d i • w i)
        = (ZMod.chineseRemainder hcop).symm (0, t) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (R * q) := ⟨Nat.mul_ne_zero hR.ne' hq.ne'⟩
  obtain ⟨U, d, hd10, hUb, hd0, hdlv, hsum⟩ :=
    pal_window_extract_gen hq
      (fun k => (ZMod.chineseRemainder hcop (w k)).2)
      base live hunit hcard t
  refine ⟨U, d, hd10, hUb, hd0, hdlv, ?_⟩
  -- `w i` is the `crtWeight` of its own CRT components
  have hwrw : ∀ i, crtWeight hcop
      ((ZMod.chineseRemainder hcop (w i)).1)
      ((ZMod.chineseRemainder hcop (w i)).2) = w i := by
    intro i
    unfold crtWeight
    rw [Prod.mk.eta]
    exact (ZMod.chineseRemainder hcop).toMulEquiv.symm_apply_apply
      (w i)
  have hcongr : (U.sum fun i => d i • w i)
      = U.sum fun i => (d i : ZMod (R * q)) * crtWeight hcop
        ((ZMod.chineseRemainder hcop (w i)).1)
        ((ZMod.chineseRemainder hcop (w i)).2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [nsmul_eq_mul, hwrw i]
  have hmain : (ZMod.chineseRemainder hcop)
      (U.sum fun i => d i • w i) = (0, t) := by
    rw [hcongr, chineseRemainder_sum_smul]
    apply Prod.ext
    · show (U.sum fun i =>
          (d i : ZMod R) *
            ((ZMod.chineseRemainder hcop) (w i)).1) = 0
      apply Finset.sum_eq_zero
      intro i hi
      rw [hvan i (hUb hi), mul_zero]
    · show (U.sum fun i =>
          (d i : ZMod q) *
            ((ZMod.chineseRemainder hcop) (w i)).2) = t
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsmul_eq_mul]
  have hcongr2 : (U.sum fun i => d i • w i)
      = (ZMod.chineseRemainder hcop).symm (0, t) := by
    rw [← hmain]
    exact ((ZMod.chineseRemainder hcop).left_inv _).symm
  exact hcongr2

-- ============================================================
-- Section 4 — iterating the stages (deliverable 4)
-- ============================================================

/-- Cast into `ZMod d` factors through `ZMod b` when `d ∣ b ∣ m`.
    `ZMod.cast` is the proof-free `.val`-cast, so the two `castHom`
    proofs need not be mentioned. -/
theorem cast_through {d b m : ℕ} (h1 : d ∣ b) (h2 : b ∣ m)
    (x : ZMod m) :
    ZMod.castHom h1 (ZMod d) (ZMod.castHom h2 (ZMod b) x)
      = ZMod.cast x := by
  rw [← RingHom.comp_apply, ZMod.castHom_comp]
  rfl

/-- Elements of `l` strictly before the first occurrence of `j`. -/
def lBefore {ι : Type*} [DecidableEq ι] (l : List ι) (j : ι) :
    Finset ι :=
  (l.takeWhile (· ≠ j)).toFinset

theorem lBefore_cons_self {ι : Type*} [DecidableEq ι]
    (j : ι) (rest : List ι) :
    lBefore (j :: rest) j = ∅ := by
  simp [lBefore]

theorem lBefore_cons_of_ne {ι : Type*} [DecidableEq ι]
    {j k : ι} (hjk : k ≠ j) (rest : List ι) :
    lBefore (k :: rest) j = insert k (lBefore rest j) := by
  simp [lBefore, hjk]

/-- A product of pairwise-coprime naturals divides `N` when each factor
    does. -/
theorem prod_dvd_of_pairwise_coprime {ι : Type*} {s : Finset ι}
    {f : ι → ℕ} {N : ℕ}
    (hs : ∀ i ∈ s, f i ∣ N)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    (∏ i ∈ s, f i) ∣ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact (Nat.coprime_prod_left_iff.mpr fun i hi =>
        hc i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s)
          (fun e => ha (e ▸ hi))).symm
    · exact hs a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
        (fun i hi j' hj' hne =>
          hc i (Finset.mem_insert_of_mem hi) j'
            (Finset.mem_insert_of_mem hj') hne)

/-- DELIVERABLE 4, fold form.  Stage list `l` (process in order):
    `prev` = already-fixed stages; `S0` = accumulated sum already
    satisfying `cast (S0) = u i` on `prev`.  Every stage-`j` weight
    vanishes mod `q i` for every `i ∈ prev` and every `i` strictly
    before `j` in `l` (`lBefore`).  Produces a digit-sum over blocks
    `I j` (`live j`-positions) that fixes every component of
    `prev ∪ l` without disturbing `prev`. -/
theorem extract_all_aux {ι : Type*} [DecidableEq ι] {m : ℕ}
    (q : ι → ℕ) (I : ι → Finset ℕ) (w : ℕ → ZMod m)
    (live : ι → ℕ → Prop) [∀ j, DecidablePred (live j)]
    (u : ∀ i, ZMod (q i)) (t : Finset ι)
    (hm : 0 < m) (hmq : m = ∏ i ∈ t, q i)
    (hq : ∀ i, 0 < q i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (q i) (q j))
    (hI : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (prev : Finset ι) (l : List ι) (S0 : ZMod m)
    (hnd : l.Nodup) (hdisjl : Disjoint prev l.toFinset)
    (hsub : prev ∪ l.toFinset ⊆ t)
    (hS0 : ∀ i ∈ prev, (ZMod.cast S0 : ZMod (q i)) = u i)
    (hvan : ∀ j ∈ l.toFinset, ∀ k ∈ I j,
        ∀ i ∈ prev ∪ lBefore l j,
          (ZMod.cast (w k) : ZMod (q i)) = 0)
    (hunit : ∀ j ∈ t, ∀ k ∈ (I j).filter (live j),
        IsUnit (ZMod.cast (w k) : ZMod (q j)))
    (hcard : ∀ j ∈ t,
        q j ≤ 1 + 9 * ((I j).filter (live j)).card) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ, (∀ i, d i < 10) ∧
      U ⊆ l.toFinset.biUnion (fun j => (I j).filter (live j)) ∧
      (∀ i, i ∉ U → d i = 0) ∧
      (∀ i ∈ prev ∪ l.toFinset,
          (ZMod.cast (S0 + U.sum fun k => d k • w k) : ZMod (q i))
            = u i) := by
  induction l generalizing prev S0 with
  | nil =>
    refine ⟨∅, fun _ => 0, fun _ => by norm_num, ?_, ?_, ?_⟩
    · intro x hx
      exact absurd hx (Finset.notMem_empty x)
    · intro i _
      rfl
    · intro i hi
      simp only [List.toFinset_nil, Finset.union_empty] at hi
      rw [Finset.sum_empty, add_zero]
      exact hS0 i hi
  | cons j rest ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hjrest, hrest_nd⟩ := hnd
    have hjl : j ∈ (j :: rest).toFinset :=
      List.mem_toFinset.mpr List.mem_cons_self
    have hjprev : j ∉ prev :=
      fun hj => (Finset.disjoint_left.mp hdisjl hj) hjl
    have hsubr : rest.toFinset ⊆ (j :: rest).toFinset := by
      intro x hx
      exact List.mem_toFinset.mpr
        (List.mem_cons_of_mem j (List.mem_toFinset.mp hx))
    have hdisjr : Disjoint prev rest.toFinset :=
      Finset.disjoint_of_subset_right hsubr hdisjl
    have hjt : j ∈ t := hsub (Finset.mem_union_right _ hjl)
    -- products
    set P : ℕ := ∏ i ∈ prev, q i with hP_def
    have hP0 : 0 < P := Finset.prod_pos (fun i _ => hq i)
    have hPmt : prev ⊆ t := Finset.subset_union_left.trans hsub
    have hPdvd : P ∣ m := by
      rw [hP_def, hmq]
      exact Finset.prod_dvd_prod_of_subset prev t q hPmt
    have hcPq : Nat.Coprime P (q j) := by
      rw [hP_def]
      exact Nat.coprime_prod_left_iff.mpr fun i hi =>
        hcop i j (fun e => hjprev (e ▸ hi))
    have hPq : P * q j = ∏ i ∈ insert j prev, q i := by
      rw [Finset.prod_insert hjprev, mul_comm]
    have hPqm : P * q j ∣ m := by
      rw [hPq, hmq]
      exact Finset.prod_dvd_prod_of_subset (insert j prev) t q
        (by
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hjt
          · exact hPmt hx)
    haveI : NeZero m := ⟨hm.ne'⟩
    haveI : NeZero (P * q j) :=
      ⟨Nat.mul_ne_zero hP0.ne' (hq j).ne'⟩
    -- stage-j weights vanish modulo `P`
    have hvanP : ∀ k ∈ I j, (ZMod.cast (w k) : ZMod P) = 0 := by
      intro k hk
      rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
      apply prod_dvd_of_pairwise_coprime
      · intro i hi
        have hx := hvan j hjl k hk i
          (Finset.mem_union_left _ hi)
        rwa [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
      · intro i _ i' _ hne
        exact hcop i i' hne
    -- extract_stage hypotheses at stage j
    have hvan_st : ∀ k ∈ I j,
        ((ZMod.chineseRemainder hcPq)
          (ZMod.castHom hPqm (ZMod (P * q j)) (w k))).1 = 0 := by
      intro k hk
      rw [chineseRemainder_fst, cast_through]
      exact hvanP k hk
    have hunit_st : ∀ k ∈ (I j).filter (live j),
        IsUnit ((ZMod.chineseRemainder hcPq)
          (ZMod.castHom hPqm (ZMod (P * q j)) (w k))).2 := by
      intro k hk
      rw [chineseRemainder_snd, cast_through]
      exact hunit j hjt k hk
    obtain ⟨Uj, dj, hdj10, hUjb, hdj0, hdjlv, hsumj⟩ :=
      extract_stage hP0 (hq j) hcPq
        (fun k => ZMod.castHom hPqm (ZMod (P * q j)) (w k))
        (I j) (live j) hvan_st hunit_st (hcard j hjt)
        ((u j : ZMod (q j)) - ZMod.cast S0)
    set Sj : ZMod m := Uj.sum fun i => dj i • w i with hSj_def
    have hcastSj : ZMod.castHom hPqm (ZMod (P * q j)) Sj
        = (ZMod.chineseRemainder hcPq).symm
            (0, u j - ZMod.cast S0) := by
      rw [hSj_def, map_sum]
      calc (Uj.sum fun i => ZMod.castHom hPqm (ZMod (P * q j))
              (dj i • w i))
          = Uj.sum fun i => dj i •
              ZMod.castHom hPqm (ZMod (P * q j)) (w i) :=
            Finset.sum_congr rfl fun i _ => map_nsmul _ _ _
        _ = (ZMod.chineseRemainder hcPq).symm
              (0, u j - ZMod.cast S0) := hsumj
    have hSjP : (ZMod.cast Sj : ZMod P) = 0 := by
      rw [← cast_through (dvd_mul_right P (q j)) hPqm Sj,
        hcastSj, ← chineseRemainder_fst hcPq,
        RingEquiv.apply_symm_apply]
    have hSjq : (ZMod.cast Sj : ZMod (q j))
        = u j - ZMod.cast S0 := by
      rw [← cast_through (dvd_mul_left (q j) P) hPqm Sj,
        hcastSj, ← chineseRemainder_snd hcPq,
        RingEquiv.apply_symm_apply]
    have hSji : ∀ i ∈ prev, (ZMod.cast Sj : ZMod (q i)) = 0 := by
      intro i hi
      have hid : q i ∣ P := by
        rw [hP_def]
        exact Finset.dvd_prod_of_mem q hi
      rw [← cast_through hid hPdvd Sj]
      simp only [ZMod.castHom_apply, hSjP, ZMod.cast_zero]
    -- recursive call on rest with prev' = insert j prev
    have hdisj' : Disjoint (insert j prev) rest.toFinset :=
      Finset.disjoint_insert_left.mpr
        ⟨fun h => hjrest (List.mem_toFinset.mp h), hdisjr⟩
    have hsub' : insert j prev ∪ rest.toFinset ⊆ t := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_insert] at hx
      apply hsub
      rw [Finset.mem_union, List.toFinset_cons, Finset.mem_insert]
      rcases hx with (rfl | hx) | hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
    have hit : ∀ i ∈ insert j prev, i ∈ t := by
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hjt
      · exact hPmt hi
    have qd : ∀ i ∈ t, q i ∣ m := fun i hi => by
      rw [hmq]
      exact Finset.dvd_prod_of_mem q hi
    have hS0' : ∀ i ∈ insert j prev,
        (ZMod.cast (S0 + Sj) : ZMod (q i)) = u i := by
      intro i hi
      have hcast : (ZMod.cast (S0 + Sj) : ZMod (q i))
          = (ZMod.cast S0 : ZMod (q i))
              + (ZMod.cast Sj : ZMod (q i)) :=
        ZMod.cast_add (qd i (hit i hi)) S0 Sj
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [hcast, hSjq, add_comm, sub_add_cancel]
      · rw [hcast, hSji i hi, hS0 i hi, add_zero]
    have hvan' : ∀ j' ∈ rest.toFinset, ∀ k ∈ I j',
        ∀ i ∈ insert j prev ∪ lBefore rest j',
          (ZMod.cast (w k) : ZMod (q i)) = 0 := by
      intro j' hj' k hk i hi
      have hj'l : j' ∈ (j :: rest).toFinset :=
        List.mem_toFinset.mpr
          (List.mem_cons_of_mem j (List.mem_toFinset.mp hj'))
      have hjne : j ≠ j' := fun e =>
        hjrest (e ▸ List.mem_toFinset.mp hj')
      apply hvan j' hj'l k hk i
      rw [Finset.mem_union, Finset.mem_insert] at hi
      rw [Finset.mem_union, lBefore_cons_of_ne hjne rest,
        Finset.mem_insert]
      rcases hi with (rfl | hi) | hi
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hi
      · exact Or.inr (Or.inr hi)
    obtain ⟨Ur, dr, hdr10, hUrb, hdr0, hcomp⟩ :=
      ih (insert j prev) (S0 + Sj) hrest_nd hdisj' hsub' hS0' hvan'
    -- disjointness of the two chosen position sets
    have hdisjU : Disjoint Uj Ur := by
      rw [Finset.disjoint_left]
      intro x hxj hxr
      have hxIj : x ∈ I j := hUjb hxj
      obtain ⟨j', hj'mem, hxIj'⟩ := Finset.mem_biUnion.mp (hUrb hxr)
      have hxIj'2 : x ∈ I j' := (Finset.mem_filter.mp hxIj').1
      have hj'ne : j' ≠ j := fun e =>
        hjrest (e ▸ List.mem_toFinset.mp hj'mem)
      exact (Finset.disjoint_left.mp (hI j' j hj'ne) hxIj'2) hxIj
    refine ⟨Uj ∪ Ur,
      fun k => if k ∈ Uj then dj k else dr k, ?_, ?_, ?_, ?_⟩
    · intro i
      show (if i ∈ Uj then dj i else dr i) < 10
      by_cases h : i ∈ Uj
      · rw [if_pos h]; exact hdj10 i
      · rw [if_neg h]; exact hdr10 i
    · intro x hx
      rw [Finset.mem_union] at hx
      apply Finset.mem_biUnion.mpr
      rcases hx with hx | hx
      · exact ⟨j, hjl, Finset.mem_filter.mpr
          ⟨hUjb hx, hdjlv x hx⟩⟩
      · obtain ⟨j', hj'mem, hxI⟩ := Finset.mem_biUnion.mp (hUrb hx)
        exact ⟨j', List.mem_toFinset.mpr
          (List.mem_cons_of_mem j (List.mem_toFinset.mp hj'mem)), hxI⟩
    · intro i hi
      show (if i ∈ Uj then dj i else dr i) = 0
      rw [Finset.mem_union] at hi
      push_neg at hi
      rw [if_neg hi.1]
      exact hdr0 i hi.2
    · have hsumsplit : ((Uj ∪ Ur).sum fun k =>
          (if k ∈ Uj then dj k else dr k) • w k)
          = Uj.sum (fun k => dj k • w k)
              + Ur.sum (fun k => dr k • w k) := by
        rw [Finset.sum_union hdisjU]
        congr 1
        · apply Finset.sum_congr rfl
          intro x hx
          show (if x ∈ Uj then dj x else dr x) • w x = dj x • w x
          rw [if_pos hx]
        · apply Finset.sum_congr rfl
          intro x hx
          show (if x ∈ Uj then dj x else dr x) • w x = dr x • w x
          rw [if_neg (fun hxj =>
            (Finset.disjoint_left.mp hdisjU hxj) hx)]
      have hset : prev ∪ (j :: rest).toFinset
          = insert j prev ∪ rest.toFinset := by
        rw [List.toFinset_cons, Finset.union_insert,
          Finset.insert_union]
      intro i hi
      rw [hset] at hi
      rw [hsumsplit, ← add_assoc]
      exact hcomp i hi

/-- DELIVERABLE 4 — sequential CRT extraction over all stages of `l`.

    If `m = ∏_{j∈l} q j` (pairwise coprime `q j`, pairwise disjoint
    blocks `I j`), every stage-`j` weight vanishes mod every `q_i`
    with `i` strictly before `j` in `l`, live positions have a unit
    `q_j`-component, and each block has enough live positions, then
    every tuple of targets `(u j)` is simultaneously attained by one
    digit sum over the disjoint blocks. -/
theorem extract_all {ι : Type*} [DecidableEq ι] {m : ℕ}
    (q : ι → ℕ) (I : ι → Finset ℕ) (w : ℕ → ZMod m)
    (live : ι → ℕ → Prop) [∀ j, DecidablePred (live j)]
    (u : ∀ i, ZMod (q i)) (l : List ι)
    (hm : 0 < m) (hmq : m = ∏ i ∈ l.toFinset, q i)
    (hq : ∀ i, 0 < q i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (q i) (q j))
    (hI : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (hnd : l.Nodup)
    (hvan : ∀ j ∈ l.toFinset, ∀ k ∈ I j,
        ∀ i ∈ lBefore l j, (ZMod.cast (w k) : ZMod (q i)) = 0)
    (hunit : ∀ j ∈ l.toFinset, ∀ k ∈ (I j).filter (live j),
        IsUnit (ZMod.cast (w k) : ZMod (q j)))
    (hcard : ∀ j ∈ l.toFinset,
        q j ≤ 1 + 9 * ((I j).filter (live j)).card) :
    ∃ U : Finset ℕ, ∃ d : ℕ → ℕ, (∀ i, d i < 10) ∧
      U ⊆ l.toFinset.biUnion (fun j => (I j).filter (live j)) ∧
      (∀ i, i ∉ U → d i = 0) ∧
      (∀ i ∈ l.toFinset,
          (ZMod.cast (U.sum fun k => d k • w k) : ZMod (q i))
            = u i) := by
  obtain ⟨U, d, hd10, hUb, hd0, hcomp⟩ :=
    extract_all_aux q I w live u l.toFinset hm hmq hq hcop hI
      ∅ l 0 hnd
      (by simp)
      (by simp)
      (by intro i hi; exact absurd hi (Finset.notMem_empty i))
      (by
        intro j hj k hk i hi
        exact hvan j hj k hk i (by simpa using hi))
      hunit hcard
  refine ⟨U, d, hd10, hUb, hd0, ?_⟩
  intro i hi
  have hcomp' := hcomp i (by simpa using hi)
  rw [zero_add] at hcomp'
  exact hcomp'
/-- Borne morte étendue : positions {∃p|m, ord_p|i} ∪ {3|i} —
    requis pour l'extraction CRT mod M·3^{v-4}. -/
theorem dead_wshift_count3 {m X : ℕ} :
    ((Finset.range X).filter (fun i =>
        (∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)
        ∨ 3 ∣ i)).card
      ≤ (m.primeFactors.sum fun p =>
          X / orderOf (10 : ZMod p) + 1) + (X / 3 + 1) := by
  have hsub : (Finset.range X).filter (fun i =>
      (∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i) ∨ 3 ∣ i)
      ⊆ ((Finset.range X).filter (fun i =>
          ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i))
        ∪ ((Finset.range X).filter (3 ∣ ·)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hi.1, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hi.1, h⟩)
  calc ((Finset.range X).filter (fun i =>
        (∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)
        ∨ 3 ∣ i)).card
      ≤ (((Finset.range X).filter (fun i =>
          ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i))
        ∪ ((Finset.range X).filter (3 ∣ ·))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range X).filter (fun i =>
          ∃ p ∈ m.primeFactors, orderOf (10 : ZMod p) ∣ i)).card
        + ((Finset.range X).filter (3 ∣ ·)).card :=
        Finset.card_union_le _ _
    _ ≤ (m.primeFactors.sum fun p =>
          X / orderOf (10 : ZMod p) + 1) + (X / 3 + 1) :=
        Nat.add_le_add dead_wshift_count
          (card_multiples_le X 3 three_pos)

/-! Counting "live" positions: `i` with `(c - 2i)` a unit mod `E` (E odd).
    Per full block of `E` consecutive indices the count is `φ E`:
    `i ↦ c - 2i` is a bijection of `ZMod E` (slope 2 is a unit). -/

/-- Equivalence between the IsUnit subtype and the units type. -/
noncomputable def isUnitEquivUnits {M : Type*} [Monoid M] : {x : M // IsUnit x} ≃ Mˣ where
  toFun := fun x => x.2.unit
  invFun := fun u => ⟨u.val, u.isUnit⟩
  left_inv := fun x => Subtype.ext x.2.unit_spec
  right_inv := fun u => Units.ext u.isUnit.unit_spec

theorem card_filter_isUnit (E : ℕ) [NeZero E] :
    ((Finset.univ : Finset (ZMod E)).filter IsUnit).card = Nat.totient E := by
  rw [← ZMod.card_units_eq_totient, ← Fintype.card_subtype IsUnit]
  exact Fintype.card_congr isUnitEquivUnits

/-- Affine map `x ↦ c - u*x` with unit slope is an equiv. -/
def affineEquiv (R : Type*) [Ring R] (u : Rˣ) (c : R) : R ≃ R where
  toFun := fun x => c - u * x
  invFun := fun y => u⁻¹ * (c - y)
  left_inv := fun x => by simp [← mul_assoc]
  right_inv := fun y => by simp [← mul_assoc]

/-- In one full residue system mod `E`, exactly `φ E` indices are live. -/
theorem card_live_block (E : ℕ) [NeZero E] (h2 : IsUnit (2 : ZMod E)) (c : ZMod E) :
    ((Finset.univ : Finset (ZMod E)).filter
      (fun i => IsUnit (c - 2 * i))).card = Nat.totient E := by
  rw [← card_filter_isUnit E]
  let u : (ZMod E)ˣ := h2.unit
  let e := affineEquiv (ZMod E) u c
  have h2' : (2 : ZMod E) = (u : ZMod E) := h2.unit_spec.symm
  rw [Finset.filter_congr (fun i _ => show
      IsUnit (c - 2 * i) ↔ IsUnit (c - u * i) by rw [h2'])]
  have heq : ∀ x : ZMod E, e x = c - u * x := fun x => rfl
  have hmap : (Finset.univ : Finset (ZMod E)).filter (fun i => IsUnit (c - u * i))
      = (Finset.univ.filter IsUnit).map e.symm.toEmbedding := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_symm, heq]
  rw [hmap, Finset.card_map]

/-- Bridge: counting over `range E` equals counting over `ZMod E`. -/
theorem card_live_range (E : ℕ) [NeZero E] (c : ZMod E) :
    ((Finset.range E).filter fun i : ℕ =>
        IsUnit (c - 2 * (i : ZMod E))).card =
      ((Finset.univ : Finset (ZMod E)).filter fun i =>
        IsUnit (c - 2 * i)).card := by
  apply Finset.card_bij (fun (i : ℕ) _ => (i : ZMod E))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and]
    exact (mem_filter.mp hi).2
  · intro i hi j hj h
    have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hi).1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)] at hv
    exact hv
  · intro a ha
    refine ⟨a.val, mem_filter.2 ⟨mem_range.2 (ZMod.val_lt a), ?_⟩, ?_⟩
    · rw [ZMod.natCast_zmod_val]
      exact (mem_filter.mp ha).2
    · simp [ZMod.natCast_zmod_val]

/-- Shift by a multiple of `E` preserves the live predicate. -/
theorem live_shift (E : ℕ) [NeZero E] (c : ZMod E) (k i : ℕ) :
    (IsUnit (c - 2 * ((k * E + i : ℕ) : ZMod E))) ↔
      IsUnit (c - 2 * (i : ZMod E)) := by
  have h : ((k * E + i : ℕ) : ZMod E) = (i : ZMod E) := by
    push_cast
    simp [CharP.cast_eq_zero]
  rw [h]

/-- At least `φ E * ⌊X/E⌋` of the first `X` indices are live. -/
theorem card_live_ge (X E : ℕ) [NeZero E] (h2 : IsUnit (2 : ZMod E)) (c : ℕ) :
    Nat.totient E * (X / E) ≤
      ((Finset.range X).filter fun i : ℕ =>
        IsUnit ((c : ZMod E) - 2 * (i : ZMod E))).card := by
  suffices h : Nat.totient E * (X / E) ≤
      ((Finset.range ((X / E) * E)).filter fun i : ℕ =>
        IsUnit ((c : ZMod E) - 2 * (i : ZMod E))).card from
    le_trans h (Finset.card_le_card
      (Finset.filter_subset_filter (fun i : ℕ => IsUnit ((c : ZMod E) - 2 * (i : ZMod E)))
        (Finset.range_mono (Nat.mul_comm (X / E) E ▸ Nat.div_mul_le_self X E))))
  generalize X / E = k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.range_add_eq_union, Finset.filter_union,
      Finset.card_union_of_disjoint, Nat.mul_succ]
    · refine Nat.add_le_add ih ?_
      rw [Finset.filter_map, Finset.card_map,
        Finset.filter_congr (fun i _ => by
          simp only [Function.comp_apply, addLeftEmbedding_apply]
          exact live_shift E (c : ZMod E) k i),
        card_live_range, card_live_block E h2]
    · rw [Finset.disjoint_left]
      intro a ha hb
      have ha' : a < k * E := mem_range.mp (mem_filter.mp ha).1
      have hb' := (mem_filter.mp hb).1
      simp only [Finset.mem_map, mem_range, addLeftEmbedding_apply] at hb'
      obtain ⟨b, _, hab⟩ := hb'
      omega

/-! Bridge: `gcd(D, P) = 1` implies the live-transfer condition
    `∀ p | m, ord_p ∤ D`, provided every `ord_p` has a prime factor
    dividing `P` (coverage hypothesis). Combined with `card_live_ge`
    this yields `φ P · ⌊X/P⌋` live positions. -/

/-- `2` is a unit mod `P` for odd `P`. -/
theorem two_unit_of_odd {P : ℕ} [NeZero P] (hP : Odd P) :
    IsUnit (2 : ZMod P) := by
  exact (ZMod.isUnit_iff_coprime 2 P).mpr ((Nat.coprime_two_left).mpr hP)

/-- Coprimality mod `P` agrees with coprimality of the residue. -/
theorem coprime_mod_iff {D P : ℕ} (hP : 0 < P) :
    (D % P).Coprime P ↔ D.Coprime P := by
  constructor
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one] at h ⊢
    rw [Nat.gcd_comm D P, Nat.gcd_rec P D]; exact h
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one] at h ⊢
    rw [← Nat.gcd_rec P D, Nat.gcd_comm]; exact h

/-- The unit predicate on `ZMod P` corresponds to coprimality
    of the natural difference `L - 2 - 2i`. -/
theorem live_iff_coprime {P L i : ℕ} [NeZero P] (hi : 2 * i ≤ L - 2) :
    IsUnit (((L - 2 : ℕ) : ZMod P) - 2 * (i : ZMod P)) ↔
      (L - 2 - 2 * i).Coprime P := by
  have hcast : (((L - 2 : ℕ) : ZMod P) - 2 * (i : ZMod P))
      = ((L - 2 - 2 * i : ℕ) : ZMod P) := by
    rw [Nat.cast_sub hi]
    push_cast
    ring
  rw [hcast, ZMod.isUnit_iff_coprime]

-- ============================================================
-- SS4 — decomposition 2^a·5^b·3^v·m et comptage d'etage lcm-aigu
-- ============================================================

/-- Decomposition `n = 2^a·5^b·3^v·m` avec `m` coprime a `30`, plus les
    donnees brutes (non-divisibilites).  Pattern `divMaxPow`
    (cf. `A085094`). -/
theorem decomp235 (n : ℕ) (hn : n ≠ 0) :
    ∃ a b v m : ℕ, n = 2 ^ a * 5 ^ b * 3 ^ v * m
      ∧ m.Coprime 30 ∧ (¬ 2 ∣ m) ∧ (¬ 5 ∣ m) ∧ (¬ 3 ∣ m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a := padicValNat 2 n with ha
  set q1 := Nat.divMaxPow n 2 with hq1d
  set b := padicValNat 5 q1 with hb
  set q2 := Nat.divMaxPow q1 5 with hq2d
  set v := padicValNat 3 q2 with hv
  set m := Nat.divMaxPow q2 3 with hmd
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hq2 : q2 * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hmq : m * 3 ^ v = q2 := Nat.divMaxPow_mul_pow_padicValNat 3 q2
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn hq1.symm
  have hq20 : q2 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq2; exact hq10 hq2.symm
  have hm0 : m ≠ 0 := by
    intro h; rw [h, zero_mul] at hmq; exact hq20 hmq.symm
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn
  have h5q2 : ¬ 5 ∣ q2 := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have h3m : ¬ 3 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq20
  have hmq2 : m ∣ q2 := ⟨3 ^ v, hmq.symm⟩
  have hq2q1 : q2 ∣ q1 := ⟨5 ^ b, hq2.symm⟩
  have h2m : ¬ 2 ∣ m := fun h =>
    h2q1 (h.trans (hmq2.trans hq2q1))
  have h5m : ¬ 5 ∣ m := fun h => h5q2 (h.trans hmq2)
  have hc30 : m.Coprime 30 := by
    have h2 : Nat.Coprime m 2 :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
    have h3 : Nat.Coprime m 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).mpr h3m).symm
    have h5 : Nat.Coprime m 5 :=
      ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
    have h6 : Nat.Coprime m 6 := Nat.Coprime.mul_right h2 h3
    have h30 : Nat.Coprime m (6 * 5) := Nat.Coprime.mul_right h6 h5
    exact h30
  refine ⟨a, b, v, m, ?_, hc30, h2m, h5m, h3m⟩
  have e1 : n = q1 * 2 ^ a := hq1.symm
  rw [e1, ← hq2, ← hmq]; ring

/-- Tous les `ord_q` divisent `X` ssi leur `lcm` divise `X`. -/
theorem all_ord_dvd_iff_lcm {prev : Finset ℕ} {X : ℕ} :
    (∀ q ∈ prev, orderOf (10 : ZMod q) ∣ X) ↔
      (prev.lcm fun q => orderOf (10 : ZMod q)) ∣ X :=
  (Finset.lcm_dvd_iff).symm

/-- Comptage d'etage aigu : positions `k ∈ Ico a (a+N)` mortes pour
    tous les ordres precedents (`L | C−4k`, `L = lcm` des ordres) et
    vivantes pour `o` (`o ∤ C−4k`), borne `N/L − (4N/lcm(L,o) + 1)`.
    Renforce `card_stage_live` (borne `N/∏ − 4N/o`, inutilisable des
    que `o ≤ 4·∏`) : ici le denominateur `lcm` absorbe les ordres
    partageant des facteurs, et la condition de faisabilite devient
    `o > 4·gcd(L,o)` — chaque etage doit apporter un facteur neuf. -/
theorem card_stage_live' {prev : Finset ℕ} {p C a N : ℕ}
    (hpos : ∀ q ∈ prev, 0 < orderOf (10 : ZMod q))
    (hopos : 0 < orderOf (10 : ZMod p))
    (hb : 4 * (a + N) ≤ C + 4)
    (hk0 : ∃ k₀ ∈ Finset.Ico a
        (a + (prev.lcm fun q => orderOf (10 : ZMod q))),
      (prev.lcm fun q => orderOf (10 : ZMod q)) ∣ C - 4 * k₀) :
    N / (prev.lcm fun q => orderOf (10 : ZMod q))
      - (4 * N / Nat.lcm (prev.lcm fun q => orderOf (10 : ZMod q))
          (orderOf (10 : ZMod p)) + 1)
    ≤ ((Finset.Ico a (a + N)).filter (fun k =>
        (∀ q ∈ prev, orderOf (10 : ZMod q) ∣ C - 4 * k)
          ∧ ¬ orderOf (10 : ZMod p) ∣ C - 4 * k)).card := by
  classical
  set L := prev.lcm fun q => orderOf (10 : ZMod q) with hL
  set o := orderOf (10 : ZMod p) with ho
  have hLpos : 0 < L := by
    rw [hL]
    rcases Finset.eq_empty_or_nonempty prev with h | h
    · rw [h]; simp
    · obtain ⟨q₀, hq₀⟩ := h
      refine Nat.pos_of_ne_zero fun h0 => ?_
      obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h0
      exact absurd hx0 (Nat.pos_iff_ne_zero.mp (hpos x hx))
  set A := (Finset.Ico a (a + N)).filter (fun k => L ∣ C - 4 * k)
    with hA
  set S := (Finset.Ico a (a + N)).filter (fun k =>
    (∀ q ∈ prev, orderOf (10 : ZMod q) ∣ C - 4 * k)
      ∧ ¬ o ∣ C - 4 * k) with hS
  have hsub1 : A.filter (fun k => ¬ o ∣ C - 4 * k) ⊆ S := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    rcases hk with ⟨hkA, hk2⟩
    rw [Finset.mem_filter] at hkA
    refine ⟨hkA.1, ⟨fun q hq => ?_, hk2⟩⟩
    exact (Finset.dvd_lcm hq).trans hkA.2
  have hcardA : N / L ≤ A.card := card_dvd_affine_ge hLpos hk0
  have hBsub : A.filter (fun k => o ∣ C - 4 * k)
      ⊆ (Finset.Ico a (a + N)).filter
        (fun k => Nat.lcm L o ∣ C - 4 * k) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    rcases hk with ⟨hkA, hko⟩
    rw [Finset.mem_filter] at hkA
    exact ⟨hkA.1, Nat.lcm_dvd hkA.2 hko⟩
  have hcardB : ((Finset.Ico a (a + N)).filter
      (fun k => Nat.lcm L o ∣ C - 4 * k)).card
      ≤ 4 * N / Nat.lcm L o + 1 :=
    card_dvd_affine_le (Nat.lcm_pos hLpos hopos) hb
  have hle1 : (A.filter (fun k => o ∣ C - 4 * k)).card
      ≤ 4 * N / Nat.lcm L o + 1 :=
    le_trans (Finset.card_le_card hBsub) hcardB
  have hAcard : A.card =
      (A.filter (fun k => o ∣ C - 4 * k)).card
      + (A.filter (fun k => ¬ o ∣ C - 4 * k)).card :=
    (Finset.card_filter_add_card_filter_not (s := A)
      (fun k => o ∣ C - 4 * k)).symm
  have hle2 : N / L - (4 * N / Nat.lcm L o + 1) ≤ S.card := by
    have h1 : N / L ≤ A.card := hcardA
    have h2 : (A.filter (fun k => ¬ o ∣ C - 4 * k)).card ≤ S.card :=
      Finset.card_le_card hsub1
    omega
  exact hle2

/-! Etape C — cloture sandwich.

    `P = ofDigits 10 (digits e ++ MID ++ rev(digits e))` : chiffres
    palindromiques (si `MID.Palindrome`), longueur `2·le + |MID|`,
    somme `2·σe + σMID`, `P ≠ 0` (dernier chiffre = `e % 10 ≠ 0`). -/

theorem sandwich_spec (e : ℕ) (he0 : e % 10 ≠ 0) (MID : List ℕ)
    (hMID : MID.Palindrome) (hd : ∀ x ∈ MID, x < 10) {L : List ℕ}
    (hL : L = Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse)
    {P : ℕ} (hP : P = Nat.ofDigits 10 L) :
    P ≠ 0 ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length
        = 2 * (Nat.digits 10 e).length + MID.length
      ∧ (Nat.digits 10 P).sum
        = 2 * (Nat.digits 10 e).sum + MID.sum := by
  subst hP
  subst hL
  have he : e ≠ 0 := fun h => by rw [h] at he0; norm_num at he0
  have hne : Nat.digits 10 e ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr he
  have hrevne : (Nat.digits 10 e).reverse ≠ [] :=
    List.reverse_ne_nil_iff.mpr hne
  have hdig : ∀ x ∈ Nat.digits 10 e, x < 10 := fun x hx =>
    Nat.digits_lt_base' (b := 8) hx
  have hall : ∀ x ∈ Nat.digits 10 e ++ MID
      ++ (Nat.digits 10 e).reverse, x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hdig x hx
      · exact hd x hx
    · exact hdig x (List.mem_reverse.mp hx)
  have hLne : Nat.digits 10 e ++ MID
      ++ (Nat.digits 10 e).reverse ≠ [] := by
    intro h
    exact hrevne (List.append_eq_nil_iff.mp h).2
  have hgl? : (Nat.digits 10 e ++ MID
      ++ (Nat.digits 10 e).reverse).getLast? = some (e % 10) := by
    rw [List.getLast?_append, List.getLast?_reverse]
    have hhd : (Nat.digits 10 e).head? = some (e % 10) := by
      rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero he)]
      rfl
    rw [hhd]
    rfl
  have hlast : ∀ h : Nat.digits 10 e ++ MID
      ++ (Nat.digits 10 e).reverse ≠ [],
      (Nat.digits 10 e ++ MID
        ++ (Nat.digits 10 e).reverse).getLast h ≠ 0 := by
    intro h
    have heq := (List.getLast_eq_iff_getLast?_eq_some h
      (a := e % 10)).mpr hgl?
    rw [heq]; exact he0
  have hdigits : Nat.digits 10 (Nat.ofDigits 10
      (Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse))
      = Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse :=
    Nat.digits_ofDigits 10 (by norm_num) _ hall hlast
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hP0
    rw [hP0] at hdigits
    rw [Nat.digits_zero] at hdigits
    exact hLne hdigits.symm
  · rw [hdigits]
    apply List.Palindrome.of_reverse_eq
    show (Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse).reverse
      = Nat.digits 10 e ++ MID ++ (Nat.digits 10 e).reverse
    rw [List.reverse_append, List.reverse_append,
      List.reverse_reverse, hMID.reverse_eq, List.append_assoc]
  · rw [hdigits]
    show (Nat.digits 10 e ++ MID
        ++ (Nat.digits 10 e).reverse).length = _
    simp only [List.length_append, List.length_reverse]
    ring
  · rw [hdigits]
    show (Nat.digits 10 e ++ MID
        ++ (Nat.digits 10 e).reverse).sum = _
    simp only [List.sum_append, List.sum_reverse]
    ring
/-! Etape D — forme paire : `ofDigits (map f range j ++ rev)` en ZMod m. -/

/-- `ofDigits (map f (range j) ++ (map f (range j)).reverse)`
    en `ZMod m` vaut `Σ_{i<j} f_i·palW m (2j) i`. -/
theorem ofDigits_pal_even {m j : ℕ} (f : ℕ → ℕ) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range j).map f ++ ((List.range j).map f).reverse)
      = ∑ i ∈ Finset.range j,
          (f i : ZMod m) * palW m (2 * j) i := by
  rw [ofDigits_append', ofDigits_zmod_range, ofDigits_zmod_rev,
    List.length_map, List.length_range]
  rw [Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range j,
      (10 : ZMod m) ^ j * ((f i : ZMod m) * 10 ^ (j - 1 - i))
      = (f i : ZMod m) * (10 : ZMod m) ^ (2 * j - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    calc (10 : ZMod m) ^ j * ((f i : ZMod m) * 10 ^ (j - 1 - i))
        = (f i : ZMod m) * ((10 : ZMod m) ^ j * 10 ^ (j - 1 - i)) := by
          ring
      _ = (f i : ZMod m) * (10 : ZMod m) ^ (j + (j - 1 - i)) := by
          rw [← pow_add]
      _ = (f i : ZMod m) * (10 : ZMod m) ^ (2 * j - 1 - i) := by
          rw [show j + (j - 1 - i) = 2 * j - 1 - i by omega]
  calc (∑ i ∈ Finset.range j, (f i : ZMod m) * (10 : ZMod m) ^ i)
      + ∑ i ∈ Finset.range j,
          (10 : ZMod m) ^ j * ((f i : ZMod m) * 10 ^ (j - 1 - i))
      = ∑ i ∈ Finset.range j,
          ((f i : ZMod m) * 10 ^ i
            + (f i : ZMod m) * (10 : ZMod m) ^ (2 * j - 1 - i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hterm i hi]
    _ = ∑ i ∈ Finset.range j, (f i : ZMod m) * palW m (2 * j) i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        unfold palW
        rw [mul_add]

/-- `sum_pair_weights` généralisé à `L` paramétrique :
    `Σ_{i<2K} pairD(e,i)·w_i = Σ_{k<K} (9·w_{2k+1} + e_k·(w_{2k}−w_{2k+1}))`. -/
theorem sum_pair_weights_gen {m K L : ℕ} (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) :
    ∑ i ∈ Finset.range (2 * K),
        (pairDigit e i : ZMod m) * palW m L i
    = ∑ k ∈ Finset.range K,
        ((9 : ZMod m) * palW m L (2 * k + 1)
        + (e k : ZMod m) * (palW m L (2 * k)
            - palW m L (2 * k + 1))) := by
  rw [sum_range_pair
    (fun i => (pairDigit e i : ZMod m) * palW m L i) K]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pairDigit_even, pairDigit_odd]
  rw [Nat.cast_sub (he k)]
  push_cast
  ring

/-- Si `gcd(4,O) | C`, l'équation `O | C - 4k` a une solution dans
    tout bloc `Ico a (a+O)` — via Bézout `4·gcdA + O·gcdB = g`. -/
theorem exists_k0 {O C a : ℕ} (hO : 0 < O) (hg : Nat.gcd 4 O ∣ C) :
    ∃ k₀ ∈ Finset.Ico a (a + O), O ∣ C - 4 * k₀ := by
  haveI : NeZero O := ⟨hO.ne'⟩
  have hgc : (Nat.gcd 4 O : ℤ)
      = 4 * Int.gcdA 4 O + O * Int.gcdB 4 O := Int.gcd_eq_gcd_ab 4 O
  obtain ⟨c, hc⟩ := hg
  -- `4·(gcdA·c) ≡ C` dans `ZMod O`
  have hsol : (4 : ZMod O) * ((Int.gcdA 4 O : ℤ) * c) = (C : ZMod O) := by
    have hdecomp : (C : ℤ)
        = 4 * (Int.gcdA 4 O * c) + O * (Int.gcdB 4 O * c) := by
      rw [hc]; push_cast; rw [hgc]; ring
    have hdvd : (↑O : ℤ) ∣ 4 * (Int.gcdA 4 O * c) - (C : ℤ) :=
      ⟨-(Int.gcdB 4 O * c), by rw [hdecomp]; ring⟩
    have hmodeq := (Int.modEq_iff_dvd).mpr hdvd
    rw [← ZMod.intCast_eq_intCast_iff] at hmodeq
    -- `hmodeq : ↑(4 * (gcdA·c)) = ↑↑C` dans `ZMod O`
    have hcast : (4 : ZMod O) * ((Int.gcdA 4 O : ℤ) * c)
        = ((4 : ℤ) * (Int.gcdA 4 O * c) : ZMod O) := by
      push_cast; ring
    rw [hcast, ← Int.cast_natCast C, hmodeq]
    push_cast
    rfl
  -- `s := val` du représentant
  set x₀ : ZMod O := ((Int.gcdA 4 O : ℤ) * c : ZMod O) with hx₀
  set s := x₀.val with hs
  have hslt : s < O := ZMod.val_lt x₀
  have h4s : (4 : ZMod O) * (s : ZMod O) = (C : ZMod O) := by
    rw [hs, ZMod.natCast_val, ZMod.cast_id]
    exact hsol
  -- `k₀ = s + O·q` dans `[a, a+O)`, `q = (a+O-1-s)/O` littéral
  refine ⟨s + O * ((a + O - 1 - s) / O), ?_, ?_⟩
  · rw [Finset.mem_Ico]
    have hdm := Nat.div_add_mod (a + O - 1 - s) O
    have hmlt : (a + O - 1 - s) % O < O := Nat.mod_lt _ hO
    have hs' : s ≤ O - 1 := Nat.le_pred_of_lt hslt
    constructor <;> omega
  · -- `4·k₀ ≡ C` puis `O | C - 4k₀`
    have hmeq : C ≡ 4 * (s + O * ((a + O - 1 - s) / O)) [MOD O] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      show (↑C : ZMod O)
          = ((4 * (s + O * ((a + O - 1 - s) / O)) : ℕ) : ZMod O)
      push_cast
      rw [ZMod.natCast_self]
      simp only [zero_mul, add_zero]
      exact h4s.symm
    rcases le_total (4 * (s + O * ((a + O - 1 - s) / O))) C
        with hle | hle
    · have h1 : C - 4 * (s + O * ((a + O - 1 - s) / O)) ≡
          4 * (s + O * ((a + O - 1 - s) / O))
            - 4 * (s + O * ((a + O - 1 - s) / O)) [MOD O] :=
        Nat.ModEq.sub hle le_rfl hmeq (Nat.ModEq.refl _)
      rw [Nat.sub_self] at h1
      exact Nat.modEq_zero_iff_dvd.mp h1
    · rw [Nat.sub_eq_zero_of_le hle]
      exact dvd_zero O

/-! Etape F — comptage live a pente s (generalisation de card_live_ge). -/

/-- `s` quelconque : dans un systeme complet mod `E`, `#{i : IsUnit (c - s·i)}
    = φ(E)` quand `s` est unite. -/
theorem card_live_block_s (E : ℕ) [NeZero E] {s : ℕ}
    (hs : IsUnit (s : ZMod E)) (c : ZMod E) :
    ((Finset.univ : Finset (ZMod E)).filter
      (fun i => IsUnit (c - s * i))).card = Nat.totient E := by
  rw [← card_filter_isUnit E]
  let u : (ZMod E)ˣ := hs.unit
  let e := affineEquiv (ZMod E) u c
  have hs' : (s : ZMod E) = (u : ZMod E) := hs.unit_spec.symm
  rw [Finset.filter_congr (fun i _ => show
      IsUnit (c - s * i) ↔ IsUnit (c - u * i) by rw [hs'])]
  have heq : ∀ x : ZMod E, e x = c - u * x := fun x => rfl
  have hmap : (Finset.univ : Finset (ZMod E)).filter (fun i => IsUnit (c - u * i))
      = (Finset.univ.filter IsUnit).map e.symm.toEmbedding := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_symm, heq]
  rw [hmap, Finset.card_map]

/-- Bridge `range E` ↔ `ZMod E`, pente `s`. -/
theorem card_live_range_s (E : ℕ) [NeZero E] (s : ℕ) (c : ZMod E) :
    ((Finset.range E).filter fun i : ℕ =>
        IsUnit (c - (s : ZMod E) * (i : ZMod E))).card =
      ((Finset.univ : Finset (ZMod E)).filter fun i =>
        IsUnit (c - s * i)).card := by
  apply Finset.card_bij (fun (i : ℕ) _ => (i : ZMod E))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and]
    exact (mem_filter.mp hi).2
  · intro i hi j hj h
    have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hi).1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)] at hv
    exact hv
  · intro a ha
    refine ⟨a.val, mem_filter.2 ⟨mem_range.2 (ZMod.val_lt a), ?_⟩, ?_⟩
    · rw [ZMod.natCast_zmod_val]
      exact (mem_filter.mp ha).2
    · simp [ZMod.natCast_zmod_val]

/-- Shift par un multiple de `E` preserve `IsUnit (c - s·i)`. -/
theorem live_shift_s (E : ℕ) [NeZero E] (c : ZMod E) (s k i : ℕ) :
    (IsUnit (c - (s : ZMod E) * ((k * E + i : ℕ) : ZMod E))) ↔
      IsUnit (c - (s : ZMod E) * (i : ZMod E)) := by
  have h : ((k * E + i : ℕ) : ZMod E) = (i : ZMod E) := by
    push_cast
    simp [CharP.cast_eq_zero]
  rw [h]

/-- Au moins `φ E · ⌊X/E⌋` des `X` premiers indices sont vivants,
    pente `s` unite. -/
theorem card_live_ge_s (X E : ℕ) [NeZero E] {s : ℕ}
    (hs : IsUnit (s : ZMod E)) (c : ℕ) :
    Nat.totient E * (X / E) ≤
      ((Finset.range X).filter fun i : ℕ =>
        IsUnit ((c : ZMod E) - (s : ZMod E) * (i : ZMod E))).card := by
  suffices h : Nat.totient E * (X / E) ≤
      ((Finset.range ((X / E) * E)).filter fun i : ℕ =>
        IsUnit ((c : ZMod E) - (s : ZMod E) * (i : ZMod E))).card from
    le_trans h (Finset.card_le_card
      (Finset.filter_subset_filter
        (fun i : ℕ => IsUnit ((c : ZMod E) - (s : ZMod E) * (i : ZMod E)))
        (Finset.range_mono
          (Nat.mul_comm (X / E) E ▸ Nat.div_mul_le_self X E))))
  generalize X / E = k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.range_add_eq_union, Finset.filter_union,
      Finset.card_union_of_disjoint, Nat.mul_succ]
    · refine Nat.add_le_add ih ?_
      rw [Finset.filter_map, Finset.card_map,
        Finset.filter_congr (fun i _ => by
          simp only [Function.comp_apply, addLeftEmbedding_apply]
          exact live_shift_s E (c : ZMod E) s k i),
        card_live_range_s, card_live_block_s E hs]
    · rw [Finset.disjoint_left]
      intro a ha hb
      have ha' : a < k * E := mem_range.mp (mem_filter.mp ha).1
      have hb' := (mem_filter.mp hb).1
      simp only [Finset.mem_map, mem_range, addLeftEmbedding_apply] at hb'
      obtain ⟨b, _, hab⟩ := hb'
      omega

/-! Etape G — extraction unifiee sur les paires (m x 3^s). -/

/-- Wrapper `pal_window_extract_crt` : produit `d : ℕ → ℕ` (digits < 10,
    nuls hors `U0`) dont les sommes ponderees atteignent `(tm, t3)` dans
    les deux composantes. Poids = coefficients reels sur `e_k` dans `P` :
    `10^{le}·twt` mod `m`, `10^{le+2k}·(10^{X_k}-1)` mod `3^s` (twt/9). -/
theorem extract_pairs_crt {m s K le : ℕ}
    (hcop : m.Coprime (3 ^ s)) (hm0 : 0 < m) (hs0 : 0 < s)
    (U0 : Finset ℕ)
    (hU0 : ∀ k : ℕ, k ∈ U0 ↔
        IsUnit ((10 : ZMod m) ^ le * twt m (4 * K + 1) k)
        ∧ IsUnit ((10 : ZMod (3 ^ s)) ^ (le + 2 * k)
            * ((10 : ZMod (3 ^ s)) ^ (4 * K + 1 - 2 - 4 * k) - 1)))
    (hlive : m * 3 ^ s ≤ 1 + 9 * U0.card)
    (tm : ZMod m) (t3 : ZMod (3 ^ s)) :
    ∃ d : ℕ → ℕ, (∀ k, d k < 10) ∧
      (∀ k, k ∉ U0 → d k = 0) ∧
      (∑ k ∈ U0, (d k : ZMod m)
          * ((10 : ZMod m) ^ le * twt m (4 * K + 1) k) = tm) ∧
      (∑ k ∈ U0, (d k : ZMod (3 ^ s))
          * ((10 : ZMod (3 ^ s)) ^ (le + 2 * k)
              * ((10 : ZMod (3 ^ s)) ^ (4 * K + 1 - 2 - 4 * k) - 1))
        = t3) := by
  classical
  obtain ⟨U, d, hd10, hUsub, hd0, hsum⟩ := pal_window_extract_crt
    hcop hm0 hs0
    (fun k => (10 : ZMod m) ^ le * twt m (4 * K + 1) k)
    (fun k => (10 : ZMod (3 ^ s)) ^ (le + 2 * k)
        * ((10 : ZMod (3 ^ s)) ^ (4 * K + 1 - 2 - 4 * k) - 1))
    U0 hU0 hlive (crtWeight hcop tm t3)
  -- decomposer la somme CRT en ses deux composantes
  have hdec := chineseRemainder_sum_smul hcop U d
    (fun k => (10 : ZMod m) ^ le * twt m (4 * K + 1) k)
    (fun k => (10 : ZMod (3 ^ s)) ^ (le + 2 * k)
        * ((10 : ZMod (3 ^ s)) ^ (4 * K + 1 - 2 - 4 * k) - 1))
  rw [hsum, crtWeight_fst] at hdec
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hdec
  refine ⟨d, hd10, ?_, ?_, ?_⟩
  · intro k hk
    exact hd0 k (fun hkU => hk (hUsub hkU))
  · -- `∑_{U0} = ∑_{U}` car `d = 0` hors `U`
    have hsumU : ∑ k ∈ U0, (d k : ZMod m)
        * ((10 : ZMod m) ^ le * twt m (4 * K + 1) k)
        = ∑ k ∈ U, (d k : ZMod m)
            * ((10 : ZMod m) ^ le * twt m (4 * K + 1) k) := by
      refine (Finset.sum_subset hUsub ?_).symm
      intro k hkU hknotU
      rw [hd0 k hknotU]
      simp
    rw [hsumU]
    exact h1.symm
  · have hsumU : ∑ k ∈ U0, (d k : ZMod (3 ^ s))
        * ((10 : ZMod (3 ^ s)) ^ (le + 2 * k)
            * ((10 : ZMod (3 ^ s)) ^ (4 * K + 1 - 2 - 4 * k) - 1))
        = ∑ k ∈ U, (d k : ZMod (3 ^ s))
            * ((10 : ZMod (3 ^ s)) ^ (le + 2 * k)
                * ((10 : ZMod (3 ^ s)) ^ (4 * K + 1 - 2 - 4 * k) - 1)) := by
      refine (Finset.sum_subset hUsub ?_).symm
      intro k hkU hknotU
      rw [hd0 k hknotU]
      simp
    rw [hsumU]
    exact h2.symm

/-- Wrapper `m`-seul (`v ≤ 4`, pas d'etage 3) : `d` digits < 10, nuls
    hors `U0`, dont la somme ponderee atteint `tm` dans `ZMod m`. -/
theorem extract_pairs_m {m K le : ℕ} [NeZero m] (hm0 : 0 < m)
    (U0 : Finset ℕ)
    (hU0 : ∀ k : ℕ, k ∈ U0 →
        IsUnit ((10 : ZMod m) ^ le * twt m (4 * K + 1) k))
    (hlive : m ≤ 1 + 9 * U0.card)
    (tm : ZMod m) :
    ∃ d : ℕ → ℕ, (∀ k, d k < 10) ∧
      (∀ k, k ∉ U0 → d k = 0) ∧
      (∑ k ∈ U0, (d k : ZMod m)
          * ((10 : ZMod m) ^ le * twt m (4 * K + 1) k) = tm) := by
  classical
  obtain ⟨U, d, hd10, hUsub, hd0, _hlive', hsum⟩ := pal_window_extract_gen
    hm0 (fun k => (10 : ZMod m) ^ le * twt m (4 * K + 1) k) U0
    (fun _ => True)
    (fun i hi => hU0 i (Finset.mem_filter.mp hi).1)
    (by
      rw [Finset.filter_eq_self.mpr fun k _ => trivial]
      exact hlive) tm
  refine ⟨d, hd10, ?_, ?_⟩
  · intro k hk
    exact hd0 k (fun hkU => hk (hUsub hkU))
  · have hsumU : ∑ k ∈ U0, (d k : ZMod m)
        * ((10 : ZMod m) ^ le * twt m (4 * K + 1) k)
        = ∑ k ∈ U, (d k : ZMod m)
            * ((10 : ZMod m) ^ le * twt m (4 * K + 1) k) := by
      refine (Finset.sum_subset hUsub ?_).symm
      intro k hkU hknotU
      rw [hd0 k hknotU]
      simp
    rw [hsumU]
    simp only [← nsmul_eq_mul]
    exact hsum

/-! Etape H — valeur `ofDigits` pour `pairs ++ C ++ rev pairs` (C centre
    palindrome), puis specialisation `C = F ++ [c] ++ rev F`. -/

/-- Partie externe : `ofDigits(A ++ zeros_gap ++ rev A)` se reduit a
    `ofDigits A + 10^{|A|+gap}·ofDigits(rev A)` — la contribution des
    zeros est nulle. -/
theorem ofDigits_pal_gap {m : ℕ} (f : ℕ → ℕ) (j g : ℕ) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range j).map f ++ List.replicate g 0
        ++ ((List.range j).map f).reverse)
    = ∑ i ∈ Finset.range j,
        (f i : ZMod m) * palW m (2 * j + g) i := by
  rw [ofDigits_append', ofDigits_append',
    List.length_append, List.length_map, List.length_range,
    List.length_replicate]
  rw [ofDigits_zmod_range]
  rw [show Nat.ofDigits (10 : ZMod m) (List.replicate g 0) = 0 from by
    induction g with
    | zero => rfl
    | succ g ih =>
      rw [List.replicate_succ]
      simp only [Nat.ofDigits, List.foldr_cons, ih]
      simp]
  rw [ofDigits_zmod_rev]
  simp
  rw [Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range j,
      (10 : ZMod m) ^ (j + g) * ((f i : ZMod m) * 10 ^ (j - 1 - i))
      = (f i : ZMod m) * (10 : ZMod m) ^ (2 * j + g - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    calc (10 : ZMod m) ^ (j + g) * ((f i : ZMod m) * 10 ^ (j - 1 - i))
        = (f i : ZMod m)
            * ((10 : ZMod m) ^ (j + g) * 10 ^ (j - 1 - i)) := by ring
      _ = (f i : ZMod m) * (10 : ZMod m) ^ (j + g + (j - 1 - i)) := by
          rw [← pow_add]
      _ = (f i : ZMod m) * (10 : ZMod m) ^ (2 * j + g - 1 - i) := by
          rw [show j + g + (j - 1 - i) = 2 * j + g - 1 - i by omega]
  calc (∑ i ∈ Finset.range j, (f i : ZMod m) * (10 : ZMod m) ^ i)
      + ∑ i ∈ Finset.range j,
          (10 : ZMod m) ^ (j + g)
            * ((f i : ZMod m) * 10 ^ (j - 1 - i))
      = ∑ i ∈ Finset.range j,
          ((f i : ZMod m) * 10 ^ i
            + (f i : ZMod m) * (10 : ZMod m) ^ (2 * j + g - 1 - i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hterm i hi]
    _ = ∑ i ∈ Finset.range j, (f i : ZMod m) * palW m (2 * j + g) i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        unfold palW
        rw [mul_add]

/-- `ofDigits(pairs ++ C ++ rev pairs)` avec `|C| = g` (C centre
    quelconque), `L = 4K + g`. -/
theorem ofDigits_pair_center {m K g : ℕ} (e : ℕ → ℕ)
    (he : ∀ k, e k ≤ 9) (C : List ℕ) (hC : C.length = g) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range (2 * K)).map (pairDigit e) ++ C
        ++ ((List.range (2 * K)).map (pairDigit e)).reverse)
    = Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      + ∑ k ∈ Finset.range K,
          ((9 : ZMod m) * palW m (4 * K + g) (2 * k + 1)
          + (e k : ZMod m)
            * (palW m (4 * K + g) (2 * k)
              - palW m (4 * K + g) (2 * k + 1))) := by
  have hlen : ((List.range (2 * K)).map (pairDigit e)).length = 2 * K := by
    rw [List.length_map, List.length_range]
  rw [ofDigits_append', ofDigits_append', hlen,
    List.length_append, hlen, hC]
  rw [ofDigits_zmod_range, ofDigits_zmod_rev]
  rw [Finset.mul_sum]
  -- regrouper `ofDigits C·10^{2K} + Σ f·(10^i + 10^{4K+g-1-i})`
  have hterm : ∀ i ∈ Finset.range (2 * K),
      (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigit e i : ZMod m) * 10 ^ (2 * K - 1 - i))
      = (pairDigit e i : ZMod m)
          * (10 : ZMod m) ^ (4 * K + g - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    calc (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigit e i : ZMod m) * 10 ^ (2 * K - 1 - i))
        = (pairDigit e i : ZMod m)
            * ((10 : ZMod m) ^ (2 * K + g) * 10 ^ (2 * K - 1 - i)) := by
          ring
      _ = (pairDigit e i : ZMod m)
            * (10 : ZMod m) ^ (2 * K + g + (2 * K - 1 - i)) := by
          rw [← pow_add]
      _ = (pairDigit e i : ZMod m)
            * (10 : ZMod m) ^ (4 * K + g - 1 - i) := by
          rw [show 2 * K + g + (2 * K - 1 - i)
              = 4 * K + g - 1 - i by omega]
  have hsum : ∑ i ∈ Finset.range (2 * K),
        (pairDigit e i : ZMod m) * (10 : ZMod m) ^ i
      + ∑ i ∈ Finset.range (2 * K), (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigit e i : ZMod m) * 10 ^ (2 * K - 1 - i))
      = ∑ i ∈ Finset.range (2 * K),
          (pairDigit e i : ZMod m) * palW m (4 * K + g) i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hterm i (Finset.mem_range.mpr hi)]
    unfold palW
    rw [mul_add]
  -- goal : `(Σfwd + 10^{2K}·Cval) + Σrev = Cval·10^{2K} + Σpairs`
  rw [add_right_comm, hsum]
  rw [show (10 : ZMod m) ^ (2 * K) * Nat.ofDigits (10 : ZMod m) C
      = Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      from mul_comm _ _, add_comm]
  rw [sum_pair_weights_gen e he]

/-- Longueur de `pairs ++ C ++ rev pairs` avec `|C| = 2t+1`. -/
theorem len_mid (K t : ℕ) (e : ℕ → ℕ) (C : List ℕ)
    (hC : C.length = 2 * t + 1) :
    (((List.range (2 * K)).map (pairDigit e) ++ C
        ++ ((List.range (2 * K)).map (pairDigit e)).reverse)).length
      = 4 * K + (2 * t + 1) := by
  rw [List.length_append, List.length_append, List.length_reverse,
    List.length_map, List.length_range, hC]
  ring
/-- Valeur `P mod m` : `ofDigits(de ++ MID ++ rev de)` avec
    `MID = pairs ++ C ++ rev pairs`, `|de| = le`, `|C| = 2t+1` —
    isole la somme `Σ d_k·(10^{le}·twt_k)` extraite. -/
theorem P_val_m {m le K t e : ℕ} (d : ℕ → ℕ)
    (hd : ∀ k, d k ≤ 9) (C : List ℕ) (hC : C.length = 2 * t + 1)
    (hle : (Nat.digits 10 e).length = le) :
    (Nat.ofDigits (10 : ZMod m)
        (Nat.digits 10 e
          ++ ((List.range (2 * K)).map (pairDigit d) ++ C
            ++ ((List.range (2 * K)).map (pairDigit d)).reverse)
          ++ (Nat.digits 10 e).reverse))
      = (Nat.ofDigits (10 : ZMod m) (Nat.digits 10 e))
        + (10 : ZMod m) ^ (le + 4 * K + (2 * t + 1))
            * Nat.ofDigits (10 : ZMod m) (Nat.digits 10 e).reverse
        + (10 : ZMod m) ^ le
            * (Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
              + ∑ k ∈ Finset.range K,
                  (9 : ZMod m) * palW m (4 * K + (2 * t + 1)) (2 * k + 1))
        + ∑ k ∈ Finset.range K,
            (d k : ZMod m)
              * ((10 : ZMod m) ^ le * twt m (4 * K + (2 * t + 1)) k) := by
  set de := Nat.digits 10 e with hde
  set MID := (List.range (2 * K)).map (pairDigit d) ++ C
      ++ ((List.range (2 * K)).map (pairDigit d)).reverse with hMID
  have hlenMID : MID.length = 4 * K + (2 * t + 1) := len_mid K t d C hC
  have hle' : de.length = le := hle
  rw [ofDigits_append', ofDigits_append', List.length_append,
    hle', hlenMID]
  rw [ofDigits_pair_center d hd C hC]
  -- decomposer `Σ (9·palW + d·twt)` en `Σ 9·palW + Σ d·twt`
  have hsplit : ∑ k ∈ Finset.range K,
      ((9 : ZMod m) * palW m (4 * K + (2 * t + 1)) (2 * k + 1)
      + (d k : ZMod m)
        * (palW m (4 * K + (2 * t + 1)) (2 * k)
          - palW m (4 * K + (2 * t + 1)) (2 * k + 1)))
      = ∑ k ∈ Finset.range K,
          (9 : ZMod m) * palW m (4 * K + (2 * t + 1)) (2 * k + 1)
        + ∑ k ∈ Finset.range K, (d k : ZMod m)
            * twt m (4 * K + (2 * t + 1)) k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold twt
    ring
  rw [hsplit]
  -- distribuer `10^le` sur `Cval + (Σ9 + Σd)`
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  have hterm : ∀ k : ℕ, (10 : ZMod m) ^ le
      * ((d k : ZMod m) * twt m (4 * K + (2 * t + 1)) k)
      = (d k : ZMod m)
          * ((10 : ZMod m) ^ le * twt m (4 * K + (2 * t + 1)) k) :=
    fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  ring
