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

/-- Conjecture A084017 (OEIS, Murthy 2003) : aucune entree nulle —
    pour tout n ≠ 0 il existe un palindromique a n chiffres multiple
    de n dont la somme de chiffres est multiple de n.
    STATUT : SPEC AUDITEE (Argon "OUI — fige") — preuve en cours. -/
theorem A084017 (n : ℕ) (hn : n ≠ 0) :
    ∃ P z : ℕ, P ≠ 0
    ∧ (0 < z → 10 ∣ n)
    ∧ (Nat.digits 10 P).Palindrome
    ∧ (Nat.digits 10 P).length + z = n
    ∧ n ∣ P * 10 ^ z
    ∧ n ∣ (Nat.digits 10 P).sum := by
  sorry

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
