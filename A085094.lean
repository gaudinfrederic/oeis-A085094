import Mathlib
import A084017

open Classical Finset

/-! A085094 (conjecture OEIS) : pour tout n ≠ 0, il existe un
    palindrome décimal P ≠ 0 avec n ∣ P + 1 — i.e. « no entry is
    zero » : tout n divise un successeur de palindrome
    (P = n·k − 1 palindrome).

    Stratégie : n = 2^a·5^b·m avec gcd(m,10) = 1, c = max(a,b).
    Le palindrome P finit par c + 1 neufs (et commence pareil, par
    symétrie) : P ≡ 10^c − 1 ≡ −1 (mod 10^c), donc
    s = 2^a·5^b ∣ 10^c ∣ P + 1 automatiquement.
    Fenêtre centrale W = Db ++ [0] ++ Db.reverse de longueur
    L = 2·T·m + 1 (T = φ(m)) : toute position i multiple de T a un
    poids w_i = 10^i + 10^{L−1−i} ≡ 2 (mod m), une unité —
    `pal_window_extract_gen` atteint alors le résidu visé mod m.
    CRT : n = s·m ∣ P + 1. -/

/-- Nombre de multiples de `T` dans `range (T * K)`. -/
theorem card_range_filter_dvd {T K : ℕ} (hT : 0 < T) :
    ((Finset.range (T * K)).filter (fun i => T ∣ i)).card = K := by
  have himg : (Finset.range (T * K)).filter (fun i => T ∣ i)
      = (Finset.range K).image (· * T) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hi, q, rfl⟩
      exact ⟨q, Nat.lt_of_mul_lt_mul_left hi, mul_comm q T⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, q, mul_comm q T⟩
      have h := (Nat.mul_lt_mul_right hT).mpr hq
      rwa [mul_comm K T] at h
  rw [himg, Finset.card_image_of_injective _
    (fun a b h => Nat.mul_right_cancel hT h), Finset.card_range]

/-- Conjecture A085094 : aucune entrée nulle — pour tout n ≠ 0 il
    existe un palindrome décimal non nul `P` avec `n ∣ P + 1`. -/
theorem A085094 (n : ℕ) (hn : n ≠ 0) :
    ∃ P : ℕ, P ≠ 0 ∧ (Nat.digits 10 P).Palindrome ∧ n ∣ P + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set a := padicValNat 2 n
  set q1 := Nat.divMaxPow n 2
  set b := padicValNat 5 q1
  set m := Nat.divMaxPow q1 5
  have hn0 : n ≠ 0 := hn
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn0 hq1.symm
  have hdecomp : n = 2 ^ a * 5 ^ b * m := by
    rw [← hmq] at hq1; rw [← hq1]; ring
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  have hc10 : Nat.Coprime m 10 := by
    have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hm0 : m ≠ 0 := by
    intro hmz; rw [hmz, zero_mul] at hmq; exact hq10 hmq.symm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  haveI : NeZero m := ⟨hm0⟩
  -- bord 2·5-adique : s = 2^a·5^b divise 10^c avec c = max a b
  set s := 2 ^ a * 5 ^ b with hs
  set c := max a b with hc
  have hsc : s ∣ 10 ^ c := by
    have h2a : 2 ^ a ∣ 10 ^ c := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (le_max_left a b)) _
    have h5b : 5 ^ b ∣ 10 ^ c := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
      exact dvd_mul_of_dvd_right (pow_dvd_pow 5 (le_max_right a b)) _
    exact (Nat.Coprime.pow_right b (Nat.Coprime.pow_left a
      (by norm_num : Nat.Coprime 2 5))).mul_dvd_of_dvd_of_dvd h2a h5b
  have hsm : s.Coprime m :=
    (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
      (Nat.Coprime.pow_right b h5)).symm
  -- fenêtre : T = φ(m), j = T·m, L = 2j+1
  set T := m.totient with hT
  have hTpos : 0 < T := Nat.totient_pos.mpr hmpos
  have hT10 : (10 : ZMod m) ^ T = 1 := by
    have h1 : (10 : ℕ) ^ m.totient ≡ 1 [MOD m] :=
      Nat.ModEq.pow_totient hc10.symm
    have h2c : ((10 ^ m.totient : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    rw [Nat.cast_pow, Nat.cast_one] at h2c
    rw [hT]; exact h2c
  set j := T * m with hj
  set L := 2 * j + 1 with hL
  -- cible modulo m : extraction doit produire Σ d·w = t avec
  -- 10^{c+1}·t = −1 − (10^{c+1} − 1)(1 + 10^{c+1+L})
  set u : (ZMod m)ˣ := ZMod.unitOfCoprime 10 hc10.symm with hu
  set c' := c + 1 with hc'
  set t : ZMod m := (-1 - ((10 : ZMod m) ^ c' - 1)
      * (1 + (10 : ZMod m) ^ (c' + L))) * (↑((u ^ c')⁻¹) : ZMod m)
      with ht
  have hct : (10 : ZMod m) ^ c' * t
      = -1 - ((10 : ZMod m) ^ c' - 1)
        * (1 + (10 : ZMod m) ^ (c' + L)) := by
    have hu10 : (↑u : ZMod m) = 10 := ZMod.coe_unitOfCoprime 10 _
    have h1 : (10 : ZMod m) ^ c' * (↑((u ^ c')⁻¹) : ZMod m) = 1 := by
      rw [← hu10, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv _
    rw [ht, mul_left_comm, h1, mul_one]
  -- positions vivantes : les multiples de T dans range j,
  -- toutes de poids 2 (unité)
  have hUnit : ∀ i ∈ (Finset.range j).filter (fun i => T ∣ i),
      IsUnit (((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m)) := by
    intro i hi
    obtain ⟨hij, q, rfl⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_range] at hij
    rw [hj] at hij
    have hqm : q < m := Nat.lt_of_mul_lt_mul_left hij
    have h10i : (10 : ZMod m) ^ (T * q) = 1 := by
      rw [pow_mul, hT10, one_pow]
    have hLq : L - 1 - T * q = T * (2 * m - q) := by
      have h2e : L - 1 = 2 * (T * m) := by omega
      rw [h2e, Nat.mul_sub_left_distrib]
      congr 1; ring
    have h10m : (10 : ZMod m) ^ (L - 1 - T * q) = 1 := by
      rw [hLq, pow_mul, hT10, one_pow]
    have hw2 : (((10 ^ (T * q) + 10 ^ (L - 1 - T * q) : ℕ) : ZMod m))
        = ((2 : ℕ) : ZMod m) := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        h10i, h10m]
      norm_num
    rw [hw2, ZMod.isUnit_iff_coprime]
    exact h2.symm
  have hliveN : m ≤
      1 + 9 * ((Finset.range j).filter (fun i => T ∣ i)).card := by
    have hcard : ((Finset.range j).filter (fun i => T ∣ i)).card = m :=
      card_range_filter_dvd hTpos
    rw [hcard]; omega
  -- extraction : Σ_{i ∈ U} d_i·w_i = t, U ⊆ range j, d_i < 10
  obtain ⟨U, d, hd_lt, hUsub, hd0, _hlv, hsum⟩ :=
    pal_window_extract_gen hmpos
      (fun i => ((10 ^ i + 10 ^ (L - 1 - i) : ℕ) : ZMod m))
      (Finset.range j) (fun i => T ∣ i) hUnit hliveN t
  -- assemblage : DL = 9^{c+1} ++ W ++ 9^{c+1}, W palindrome
  set Db := (List.range j).map d with hDb
  set W := Db ++ [0] ++ Db.reverse with hW
  set DL := List.replicate c' 9 ++ W ++ List.replicate c' 9 with hDL
  set P := Nat.ofDigits 10 DL with hP
  have hWd : ∀ x ∈ W, x < 10 := by
    intro x hx
    simp only [hW, hDb, List.mem_append, List.mem_reverse,
      List.mem_singleton, List.mem_map, List.mem_range] at hx
    rcases hx with (⟨i, hi, rfl⟩ | rfl) | ⟨i, hi, rfl⟩
    · exact hd_lt i
    · norm_num
    · exact hd_lt i
  have hWpal : List.Palindrome W :=
    List.Palindrome.iff_reverse_eq.mpr (by
      rw [hW, List.reverse_append, List.reverse_append,
        List.reverse_reverse, List.reverse_singleton,
        ← List.append_assoc])
  have hWlen : W.length = L := by
    rw [hW, List.length_append, List.length_append, List.length_reverse,
      List.length_singleton, hDb, List.length_map, List.length_range, hL]
    omega
  have hrepne : List.replicate c' 9 ≠ [] := by
    intro hnil
    have h0 : (List.replicate c' 9).length = 0 := by rw [hnil]; rfl
    rw [List.length_replicate] at h0
    omega
  have hrep9 : (List.replicate c' 9).getLast hrepne = 9 :=
    List.getLast_replicate_succ c 9

  have hdig : Nat.digits 10 P = DL := by
    apply Nat.digits_ofDigits 10 (by norm_num)
    · intro l hl
      rw [hDL, List.mem_append, List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · have := List.eq_of_mem_replicate hl; omega
      · exact hWd l hl
      · have := List.eq_of_mem_replicate hl; omega
    · intro hne2 h0
      have hgl : DL.getLast? = some 0 := by
        rw [List.getLast?_eq_some_getLast hne2, h0]
      rw [hDL, List.getLast?_append_of_ne_nil _ hrepne,
        List.getLast?_eq_some_getLast hrepne, hrep9] at hgl
      exact absurd hgl (by norm_num)
  have hDLne : DL ≠ [] := by
    intro hnil
    rw [hDL] at hnil
    exact hrepne (List.append_eq_nil_iff.mp hnil).2
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at hdig
    exact hDLne hdig.symm
  have hPpal : (Nat.digits 10 P).Palindrome := by
    have hWrev : W.reverse = W :=
      (List.Palindrome.iff_reverse_eq).mp hWpal
    have hArev : (List.replicate c' 9).reverse = List.replicate c' 9 :=
      List.reverse_replicate
    rw [hdig, List.Palindrome.iff_reverse_eq, hDL]
    simp only [List.reverse_append, hWrev, hArev, List.append_assoc]
  -- ofDigits W en ZMod m = somme des poids
  have hMz : Nat.ofDigits (10 : ZMod m) W =
      ∑ i ∈ Finset.range j, (d i : ZMod m) *
        ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) := by
    rw [hW, hDb, ofDigits_append', ofDigits_append',
      ofDigits_singleton', Nat.cast_zero, mul_zero, add_zero,
      ofDigits_zmod_range, ofDigits_zmod_rev,
      List.length_append, List.length_map, List.length_range,
      List.length_singleton, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    calc (d i : ZMod m) * (10 : ZMod m) ^ i
        + (10 : ZMod m) ^ (j + 1) *
          ((d i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i))
        = (d i : ZMod m) * (10 : ZMod m) ^ i
            + (d i : ZMod m) * (10 : ZMod m) ^ (j + 1 + (j - 1 - i))
          := by rw [pow_add]; ring
      _ = (d i : ZMod m) * ((10 : ZMod m) ^ i
            + (10 : ZMod m) ^ (L - 1 - i)) := by
          rw [show j + 1 + (j - 1 - i) = L - 1 - i by omega]; ring
  have hsumU : ∑ i ∈ U, (d i : ZMod m) *
      ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) = t := by
    rw [← hsum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat]
  have hMt : Nat.ofDigits (10 : ZMod m) W = t := by
    rw [hMz]
    have hsp : ∑ i ∈ Finset.range j, (d i : ZMod m) *
        ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i))
        = ∑ i ∈ U, (d i : ZMod m) *
          ((10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)) := by
      apply (Finset.sum_subset hUsub ?_).symm
      intro i _ hiU
      rw [hd0 i hiU]; simp
    rw [hsp]; exact hsumU
  -- (P : ZMod m) = -1 ⇒ m ∣ P + 1
  have hofD : Nat.ofDigits (10 : ZMod m) (List.replicate c' 9)
      = (10 : ZMod m) ^ c' - 1 := by
    rw [← ofDigits_cast_gen, ofDigits_replicate_nine]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
    push_cast; ring
  have hcastP : ((P : ℕ) : ZMod m) = -1 := by
    rw [hP, ofDigits_cast_gen, hDL,
      ofDigits_append', ofDigits_append', hofD, hMt,
      List.length_append, List.length_replicate, hWlen, hct]
    ring
  have hmP : m ∣ P + 1 := by
    have h0 : ((P + 1 : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_add, Nat.cast_one, hcastP]
      simp
    exact (CharP.cast_eq_zero_iff (ZMod m) m (P + 1)).mp h0
  -- bord : les c derniers chiffres sont 9 ⇒ 10^c ∣ P + 1
  have h10c : 10 ^ c ∣ P + 1 := by
    set REST := [9] ++ W ++ List.replicate c' 9 with hREST
    have hDLsplit : DL = List.replicate c 9 ++ REST := by
      rw [hDL, hREST]
      have h : List.replicate c' 9 = List.replicate c 9 ++ [9] := by
        rw [hc', List.replicate_succ']
      rw [h]; simp only [List.append_assoc]
    have hQ : Nat.ofDigits 10 DL
        = (10 ^ c - 1) + 10 ^ c * Nat.ofDigits 10 REST := by
      rw [hDLsplit, ofDigits_append', ofDigits_replicate_nine,
        List.length_replicate]
    set Q := Nat.ofDigits 10 REST with hQ'
    refine ⟨Q + 1, ?_⟩
    rw [hP, hQ]
    have hge : 1 ≤ 10 ^ c := Nat.one_le_pow _ _ (by norm_num)
    have h10 : (10 ^ c - 1 : ℕ) + 1 = 10 ^ c := Nat.sub_add_cancel hge
    calc (10 ^ c - 1) + 10 ^ c * Q + 1
        = ((10 ^ c - 1) + 1) + 10 ^ c * Q := by ring
      _ = 10 ^ c + 10 ^ c * Q := by rw [h10]
      _ = 10 ^ c * (Q + 1) := by ring
  have hsP : s ∣ P + 1 := hsc.trans h10c
  have hnm : n ∣ P + 1 := by
    rw [hdecomp]
    exact hsm.mul_dvd_of_dvd_of_dvd hsP hmP
  exact ⟨P, hPne, hPpal, hnm⟩
