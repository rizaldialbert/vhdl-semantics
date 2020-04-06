(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Bits_Int_Aux
  imports
    Main "HOL-Word.Word" "HOL.Archimedean_Field"
begin

text \<open>The function @{term "bl_to_bin_aux"} is the auxiliary function for converting a bit vector
(list of booleans) into an integer with unsigned number interpretation. This semantics or conversion
is taken from @{cite "Bryant2010"} (Chapter 2.2). Given a list x = [x_{n-1}, x_{n-2}, ... , x_0] of
booleans with conversion False \<mapsto> 0 and True \<mapsto> 1, the unsigned number it represents is

    B2U (x) \<equiv> \<Sum>i=0..<n. x_i * 2 ^ i   .

The following lemma formalises this correctness.\<close>

lemma bl_to_bin_aux_correctness:
  " bl_to_bin_aux bs w =  w * 2 ^ length bs + (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)"
proof (induction bs arbitrary: w)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
    \<comment> \<open>from left hand side\<close>
  have " bl_to_bin_aux (a # bs) w = bl_to_bin_aux bs (w BIT a)"
    by auto
  also have "... =  (w BIT a) * 2 ^ length bs + (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)" (is "_ = _ + ?rhs2")
    using Cons by auto
  also have "... = (2 * w + (int o of_bool) a) * 2 ^ length bs + ?rhs2"
    unfolding Bit_def by auto
  also have "... = w * 2 ^ (length (a # bs)) + (int o of_bool) a * 2 ^ length bs + ?rhs2"
    by (auto simp add: field_simps)
  also have "... = w * 2 ^ length (a # bs) + (\<Sum>i = 0..<length (a # bs). (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i)"
  proof -
    have "(\<Sum>i = 0..<length (a # bs). (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) =
          (\<Sum>i = 0..<Suc (length bs). (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) "
      by auto
    also have "... = (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) + (int \<circ> of_bool) a * 2 ^ length bs "
      using nth_rev_alt by fastforce
    also have "... = (\<Sum>i= 0..< length bs. (int o of_bool) (rev bs ! i) * 2 ^ i) + (int o of_bool) a * 2 ^ length bs"
      unfolding cancel_semigroup_add_class.add_right_cancel
    proof (intro sum.mono_neutral_cong)
      fix x
      assume "x \<in> {0..<length bs} \<inter> {0..<length bs}"
      hence "x \<in> {0 ..< length bs}"
        by auto
      thus "(int \<circ> of_bool) (rev (a # bs) ! x) * 2 ^ x = (int \<circ> of_bool) (rev bs ! x) * 2 ^ x"
        by (smt atLeastLessThan_iff bin_nth_of_bl_aux bl_to_bin_aux.simps(2) length_Cons less_Suc_eq not_less)
    qed (auto)
    finally show ?thesis
      by auto
  qed
  finally show ?case
    by auto
qed

lemma bl_to_bin_correctness:
  "bl_to_bin bs = (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)"
  unfolding bl_to_bin_def using bl_to_bin_aux_correctness by auto

text \<open> In case it is interpreted as unsigned number, the equation is

    B2S (x) \<equiv> - x_{n-1} * 2 ^ {n - 1} + \<Sum>i=0..<n-1. x_i * 2 ^ i .

Note that the most significant bit has the value of (- 2 ^ {n - 1}) instead of (2 ^ {n - 1}).
Unfortunately there is no such function in @{theory "HOL-Word.Bits_Int"}. Fortunately we can
easily obtain such function with simple arithmetic as follows.
\<close>

fun sbl_to_bin :: "bool list \<Rightarrow> int" where
  "sbl_to_bin [] = 0"
| "sbl_to_bin bs = bl_to_bin bs - (int o of_bool) (hd bs) * 2 ^ (length bs)"

text \<open>This is the correctness theorem according to the definition of B2S. \<close>

lemma sbl_to_bin_correctness:
  "sbl_to_bin (a # bs) = - (int o of_bool) a * 2 ^ (length bs) + (\<Sum>i = 0 ..< length bs. ((int o of_bool) (rev bs ! i)) * 2 ^ i) "
proof -
  have "sbl_to_bin (a # bs) = bl_to_bin (a # bs) - (int o of_bool) a * 2 ^ (1 + length bs)"
    by auto
  also have "... = bl_to_bin (a # bs) - 2 * (int o of_bool) a * 2 ^ length bs"
    by auto
  also have "... = (\<Sum>i = 0..< Suc (length bs). (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) - 2 * (int o of_bool) a * 2 ^ length bs"
    unfolding bl_to_bin_correctness by auto
  also have "... = (\<Sum>i = 0..< length bs. (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) + (int o of_bool) a * 2 ^ length bs - 2 * (int o of_bool) a * 2 ^ length bs"
    using list.size(4) nth_rev_alt by fastforce
  also have "... = (\<Sum>i = 0..< length bs. (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) - (int o of_bool) a * 2 ^ length bs"
    by auto
  also have "... = (\<Sum>i = 0..< length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i) - (int o of_bool) a * 2 ^ length bs"
  proof -
    have "(\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev (a # bs) ! i) * 2 ^ i) =
          (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)"
      apply (intro sum.mono_neutral_cong[rotated 4])
      by (smt One_nat_def add.commute atLeastLessThan_iff bin_nth_of_bl bin_nth_of_bl_aux
      bl_to_bin_aux.Cons inf.idem less_Suc_eq list.size(4) not_less plus_1_eq_Suc) auto
    thus ?thesis
      by auto
  qed
  finally show ?thesis
    by auto
qed

lemma sign_bit_is_0:
  assumes "0 \<le> w" and "w < 2 ^ len"
  shows   "hd (bin_to_bl (Suc len) w) = False"
  using assms sbintrunc_mod2p sign_Min_lt_0 unfolding bl_sbin_sign by auto

lemma sign_bit_is_1:
  assumes "w < 0" and "- w < 2 ^ len"
  shows   "hd (bin_to_bl (Suc len) w) = True"
  using assms bin_sign_def no_sbintr_alt2 unfolding bl_sbin_sign by auto

lemma sbin_bl_bin:
  assumes "0 < n" and "\<bar>w\<bar> < 2 ^ (n - 1)"
  shows "sbl_to_bin (bin_to_bl n w) = w"
proof -
  obtain a bs where "bin_to_bl n w = (a # bs)"
    using assms  size_bin_to_bl  by (metis list.size(3) not_less_zero sbl_to_bin.cases)
  have "sbl_to_bin (bin_to_bl n w) = sbl_to_bin (a # bs)"
    using \<open>bin_to_bl n w = (a # bs)\<close> by auto
  also have "... = - (int o of_bool) a * 2 ^ (length bs)
                 + (\<Sum>i = 0 ..< length bs. ((int o of_bool) (rev bs ! i)) * 2 ^ i)"
    unfolding sbl_to_bin_correctness by auto
  finally have "sbl_to_bin (bin_to_bl n w) = - (int o of_bool) a * 2 ^ (length bs)
                                           + (\<Sum>i = 0 ..< length bs. ((int o of_bool) (rev bs ! i)) * 2 ^ i)"
    by auto
  have "sbl_to_bin (bin_to_bl n w) = sbl_to_bin (a # bs)"
    using \<open>bin_to_bl n w = a # bs\<close> by auto
  also have "... = bl_to_bin (a # bs) - (int o of_bool) a * 2 ^ (1 + length bs)"
    by auto
  also have "... = bl_to_bin (bin_to_bl n w) - (int o of_bool) a * 2 ^ (1 + length bs)"
    using \<open>bin_to_bl n w = a # bs\<close> by auto
  also have "... = bintrunc n w - (int o of_bool) a * 2 ^ (1 + length bs)"
    unfolding bin_bl_bin by auto
  also have "... = w mod (2 ^ n) - (int o of_bool) a * 2 ^ (1 + length bs)"
    by (simp add: no_bintr_alt1)
  also have "... = w mod (2 ^ n) - (int o of_bool) a * 2 ^ n"
    by (metis \<open>bin_to_bl n w = a # bs\<close> length_Cons plus_1_eq_Suc size_bin_to_bl)
  also have "... = w"
  proof (cases "0 \<le> w")
    case True
    hence "a = False"
      using sign_bit_is_0
      by (smt One_nat_def \<open>bin_to_bl n w = a # bs\<close> add.commute add_diff_cancel_left' assms(2)
      length_Cons list.sel(1) list.size(4) size_bin_to_bl)
    then show ?thesis
      by (smt Bit_B1_2t One_nat_def True \<open>bin_to_bl n w = a # bs\<close> add.commute add_diff_cancel_left'
      assms(2) comp_apply int_mod_eq' list.size(4) mult_eq_0_iff of_bool_eq(1) plus_1_eq_Suc
      power_BIT semiring_1_class.of_nat_0 size_bin_to_bl)
  next
    case False
    hence "a = True"
      using sign_bit_is_1
      by (smt One_nat_def \<open>bin_to_bl n w = a # bs\<close> add.commute add_diff_cancel_left' assms(2)
      list.sel(1) list.size(4) plus_1_eq_Suc size_bin_to_bl)
    obtain w' where "w = -w'"
      using False  by (metis add.inverse_inverse)
    hence *: "- w' mod 2 ^ n = (if w' mod 2 ^ n = 0 then 0 else 2 ^ n - w' mod 2 ^ n)"
      unfolding zmod_zminus1_eq_if by auto
    have "w' < 2 ^ n"
      by (smt One_nat_def \<open>bin_to_bl n w = a # bs\<close> \<open>w = - w'\<close> add.commute add_diff_cancel_left'
      assms(2) less_Suc_eq list.size(4) plus_1_eq_Suc power_strict_increasing_iff size_bin_to_bl)
    hence "w' mod 2 ^ n \<noteq> 0"
      using False \<open>w = - w'\<close> by auto
    hence "- w' mod 2 ^ n = 2 ^ n - (w' mod 2 ^ n)"
      using * by auto
    hence "w mod 2 ^ n = 2 ^ n - (\<bar>w\<bar> mod 2 ^ n)"
      using False \<open>w = - w'\<close> by auto
    hence "w mod 2 ^ n - (int \<circ> of_bool) a * 2 ^ n = 2 ^ n - (\<bar>w\<bar> mod 2 ^ n) - 2 ^ n"
      by (simp add: \<open>a = True\<close>)
    also have "... = - (\<bar>w\<bar> mod 2 ^ n)"
      by auto
    also have "... = w"
      using False \<open>w = - w'\<close> \<open>w' < 2 ^ n\<close> by auto
    finally show ?thesis
      by auto
  qed
  finally show ?thesis
    by auto
qed

lemma sbin_bl_bin':
  assumes "0 < n"
  shows   "sbl_to_bin (bin_to_bl n w) mod 2 ^ n = w mod 2 ^ n"
proof -
  obtain a bs where "bin_to_bl n w = (a # bs)"
    using assms  size_bin_to_bl  by (metis list.size(3) not_less_zero sbl_to_bin.cases)
  have "sbl_to_bin (bin_to_bl n w) = sbl_to_bin (a # bs)"
    using \<open>bin_to_bl n w = (a # bs)\<close> by auto
  also have "... = - (int o of_bool) a * 2 ^ (length bs)
                 + (\<Sum>i = 0 ..< length bs. ((int o of_bool) (rev bs ! i)) * 2 ^ i)"
    unfolding sbl_to_bin_correctness by auto
  finally have "sbl_to_bin (bin_to_bl n w) = - (int o of_bool) a * 2 ^ (length bs)
                                           + (\<Sum>i = 0 ..< length bs. ((int o of_bool) (rev bs ! i)) * 2 ^ i)"
    by auto
  have "sbl_to_bin (bin_to_bl n w) = sbl_to_bin (a # bs)"
    using \<open>bin_to_bl n w = a # bs\<close> by auto
  also have "... = bl_to_bin (a # bs) - (int o of_bool) a * 2 ^ (1 + length bs)"
    by auto
  also have "... = bl_to_bin (bin_to_bl n w) - (int o of_bool) a * 2 ^ (1 + length bs)"
    using \<open>bin_to_bl n w = a # bs\<close> by auto
  also have "... = bintrunc n w - (int o of_bool) a * 2 ^ (1 + length bs)"
    unfolding bin_bl_bin by auto
  also have "... = w mod (2 ^ n) - (int o of_bool) a * 2 ^ (1 + length bs)"
    by (simp add: no_bintr_alt1)
  also have "... = w mod (2 ^ n) - (int o of_bool) a * 2 ^ n"
    by (metis \<open>bin_to_bl n w = a # bs\<close> length_Cons plus_1_eq_Suc size_bin_to_bl)
  finally have "sbl_to_bin (bin_to_bl n w) = w mod (2 ^ n) - (int o of_bool) a * 2 ^ n"
    by auto
  hence "sbl_to_bin (bin_to_bl n w) mod 2 ^ n = (w mod 2 ^ n - (int o of_bool) a * 2 ^ n) mod 2 ^ n"
    by auto
  also have "... = (w - (int \<circ> of_bool) a * 2 ^ n) mod 2 ^ n"
    using pull_mods(6)[where a="w" and c="2 ^ n" and b="(int o of_bool) a * 2 ^ n"] by auto
  also have "... = w mod 2 ^ n"
    by simp
  finally show ?thesis
    by auto
qed

lemma butlast_pow_rest_bl2bin:
  "bl_to_bin ((butlast ^^ n) bl) = (bin_rest ^^ n) (bl_to_bin bl)"
  by (simp add: bin_rest_bl_to_bin fn_comm_power')

lemma take_rest_bl2bin:
  "bl_to_bin (take (length bl - n) bl) = (bin_rest ^^ n) (bl_to_bin bl)"
  by (metis butlast_pow_rest_bl2bin butlast_power)

lemma bin_rest_compow:
  "(bin_rest ^^ m) n = (n div 2 ^ m)"
  using bin_rest_shiftr shiftr_int_def by (induct m) auto

lemma bin_rest_sbl_to_bin:
  assumes "1 < length bs"
  shows "bin_rest (sbl_to_bin bs) = sbl_to_bin (butlast bs)"
proof -
  have "sbl_to_bin bs = bl_to_bin bs - (int o of_bool) (hd bs) * 2 ^ (length bs)"
    using assms  by (metis (full_types) list.size(3) not_less_zero sbl_to_bin.elims)
  hence "bin_rest (sbl_to_bin bs) = bin_rest (bl_to_bin bs + - (int o of_bool) (hd bs) * 2 ^ length bs)"
    by auto
  also have "... = bin_rest (bl_to_bin bs) - bin_rest ((int o of_bool) (hd bs) * 2 ^ length bs)"
  proof -
    have "2 dvd - (int \<circ> of_bool) (hd bs) * 2 ^ length bs"
      using assms by auto
    thus ?thesis
      unfolding bin_rest_def  using div_plus_div_distrib_dvd_right
      by (smt dvd_neg_div mult_minus_left)
  qed
  also have "... = bl_to_bin (butlast bs) - (int o of_bool) (hd bs) * 2 ^ (length bs - 1)"
    unfolding bin_rest_bl_to_bin bin_rest_def
    by (smt BIT_special_simps(3) assms bin_rest_BIT bin_rest_bl_to_bin bin_rest_def
    mult_BIT_simps(1) mult_cancel_left2 mult_cancel_right2 not_less_zero o_apply of_bool_eq(1)
    of_bool_eq(2) of_nat_1 power_eq_if semiring_1_class.of_nat_0)
  also have "... = bl_to_bin (butlast bs) - (int o of_bool) (hd (butlast bs)) * 2 ^ (length (butlast bs))"
    using assms hd_butlast by auto
  also have "... = sbl_to_bin (butlast bs)"
    by (metis assms length_butlast length_greater_0_conv sbl_to_bin.elims zero_less_diff)
  finally show ?thesis
    by auto
qed

lemma butlast_pow_rest_sbl2bin:
  assumes "n < length bl"
  shows   "sbl_to_bin ((butlast ^^ n) bl) = (bin_rest ^^ n) (sbl_to_bin bl)"
proof -
  let ?bs = "(butlast ^^ n) bl"
  have "(butlast ^^ n) bl \<noteq> []"
    using assms unfolding butlast_power by auto
  hence "sbl_to_bin ?bs = bl_to_bin ?bs - (int o of_bool) (hd ?bs) * 2 ^ (length ?bs)"
    by (metis sbl_to_bin.elims)
  moreover have "hd ?bs = hd bl"
    unfolding butlast_power  by (simp add: assms)
  moreover have "length ?bs = length bl - n"
    unfolding butlast_power by simp
  ultimately have "sbl_to_bin ?bs = bl_to_bin ?bs - (int o of_bool) (hd bl) * 2 ^ (length bl - n)"
    by auto
  also have "... = (bin_rest ^^ n) (bl_to_bin bl) - (int o of_bool) (hd bl) * 2 ^ (length bl - n)"
    unfolding butlast_pow_rest_bl2bin by auto
  also have "... = (bin_rest ^^ n) (bl_to_bin bl) + (- (int o of_bool) (hd bl) * 2 ^ length bl) div 2 ^ n"
  proof -
    have "(2::int) ^ (length bl - n) = 2 ^ length bl div 2 ^ n"
      using power_diff[OF _ less_imp_le[OF assms], of "2::int"] by auto
    hence "(int o of_bool) (hd bl) * 2 ^ (length bl - n) = (int o of_bool) (hd bl) * 2 ^ length bl div 2 ^ n"
      by auto
    thus ?thesis
      by (smt add_diff_inverse_nat assms dvd_neg_div dvd_triv_left linorder_not_less
      mult_cancel_right2 mult_minus_left o_apply of_bool_eq(1) of_bool_eq(2) of_nat_1
      order_less_imp_le power_add semiring_1_class.of_nat_0)
  qed
  also have "... = (bin_rest ^^ n) (bl_to_bin bl) + (bin_rest ^^ n) (- (int o of_bool) (hd bl) * 2 ^ length bl)"
    unfolding bin_rest_compow by auto
  also have "... = (bin_rest ^^ n) (bl_to_bin bl - (int o of_bool) (hd bl) * 2 ^ length bl)"
  proof -
    have "2 ^ n dvd (- (int \<circ> of_bool) (hd bl) * 2 ^ length bl)"
      using assms  dvd_triv_right order_less_imp_le power_le_dvd by blast
    thus ?thesis
      unfolding bin_rest_compow
      by (metis add.inverse_inverse diff_minus_eq_add div_plus_div_distrib_dvd_right
          mult_minus_left)
  qed
  also have "... = (bin_rest ^^ n) (sbl_to_bin bl)"
    by (metis (full_types) assms length_0_conv less_imp_diff_less less_not_refl2 sbl_to_bin.elims
    zero_less_diff)
  finally show ?thesis
    by auto
qed

lemma take_rest_sbl2bin:
  assumes "n < length bl"
  shows   "sbl_to_bin (take (length bl - n) bl) = (bin_rest ^^ n) (sbl_to_bin bl)"
  using butlast_pow_rest_sbl2bin[OF assms] by (simp add: butlast_power)

lemma bl_to_bin_replicate_T:
  "bl_to_bin (replicate n True) = 2 ^ n - 1"
proof -
  have "bl_to_bin (replicate n True) = (\<Sum>i = 0..<n. (int \<circ> of_bool) ((replicate n True) ! i) * 2 ^ i)"
    unfolding bl_to_bin_correctness by auto
  also have "... = 2 ^ n - 1"
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    have " (\<Sum>i = 0..<Suc n. (int \<circ> of_bool) (replicate (Suc n) True ! i) * 2 ^ i) =
           (\<Sum>i = 0..<n. (int \<circ> of_bool) (replicate (Suc n) True ! i) * 2 ^ i) + 2 ^ n"
      by (metis (no_types, lifting) One_nat_def add_Suc add_diff_cancel_left' lessI nth_replicate
      o_apply of_bool_eq(2) of_nat_1 plus_1_eq_Suc power_0 power_add sum.atLeast0_lessThan_Suc)
    also have "... = (\<Sum>i = 0..<n. (int \<circ> of_bool) (replicate n True ! i) * 2 ^ i) + 2 ^ n"
      by (metis (no_types, lifting) Diff_cancel atLeastLessThan_iff empty_iff finite_atLeastLessThan
      inf.idem less_Suc_eq nth_replicate sum.mono_neutral_cong)
    also have "... = 2 ^ n - 1 + 2 ^ n"
      using Suc by auto
    also have "... = 2 ^ Suc n - 1"
      by auto
    finally show ?case by auto
  qed
  finally show ?thesis
    by auto
qed

lemma sbl_to_bin_replicate_app:
  assumes "0 < length bl"
  shows "sbl_to_bin (replicate n (hd bl) @ bl) = sbl_to_bin bl"
proof (cases "hd bl")
  case False
  hence "sbl_to_bin (replicate n (hd bl) @ bl) = sbl_to_bin (replicate n False @ bl)"
    by auto
  also have "... = bl_to_bin (replicate n False @ bl)"
    using sbl_to_bin.simps assms
    by (smt False append_is_Nil_conv comp_apply hd_append hd_replicate length_greater_0_conv
    mult_cancel_left of_bool_eq(1) power2_eq_square replicate_empty sbl_to_bin.elims
    semiring_1_class.of_nat_0 zero_power2)
  also have "... = bl_to_bin bl"
    by (simp add: bl_to_bin_rep_F)
  also have "... = sbl_to_bin bl"
    using False sbl_to_bin.simps
    by (smt assms comp_apply length_greater_0_conv mult_cancel_left of_bool_eq(1) power2_eq_square
        sbl_to_bin.elims semiring_1_class.of_nat_0 zero_power2)
  finally show ?thesis
    by auto
next
  case True
  hence "sbl_to_bin (replicate n (hd bl) @ bl) = sbl_to_bin (replicate n True @ bl)"
    by auto
  also have "... = bl_to_bin (replicate n True @ bl) - 2 ^ (length bl + n)"
    by (smt True add.commute assms comp_apply hd_append hd_replicate length_append
    length_greater_0_conv length_replicate mult_cancel_right2 of_bool_eq(2) of_nat_1 replicate_empty
    sbl_to_bin.elims)
  also have "... = bl_to_bin_aux bl (bl_to_bin (replicate n True)) - 2 ^ (length bl + n)"
    unfolding bl_to_bin_append by auto
  also have "... = bl_to_bin_aux bl (2 ^ n - 1) - 2 ^ (length bl + n)"
    unfolding bl_to_bin_replicate_T by auto
  also have "... = (2 ^ n - 1) * 2 ^ length bl + (\<Sum>i = 0..<length bl. (int \<circ> of_bool) (rev bl ! i) * 2 ^ i) - 2 ^ (length bl + n)"
    unfolding bl_to_bin_aux_correctness by auto
  also have "... = (2 ^ (length bl + n) - 2 ^ length bl) + (\<Sum>i = 0..<length bl. (int \<circ> of_bool) (rev bl ! i) * 2 ^ i) - 2 ^ (length bl + n)"
    by (simp add: mult.commute power_add right_diff_distrib)
  also have "... = (\<Sum>i = 0..<length bl. (int \<circ> of_bool) (rev bl ! i) * 2 ^ i) - 2 ^ length bl"
    by auto
  also have "... = bl_to_bin bl - 2 ^ length bl"
    unfolding bl_to_bin_correctness by auto
  also have "... = bl_to_bin bl - (int o of_bool) (hd bl) * 2 ^ length bl"
    using True by simp
  also have "... = sbl_to_bin bl"
    by (metis assms length_greater_0_conv sbl_to_bin.elims)
  finally show ?thesis
    by auto
qed

text \<open>Equivalence between @{term "sbl_to_bin"} and @{term "sbintrunc"} + @{term "bl_to_bin"}\<close>

lemma sbl_to_bin_alt_def:
  "sbl_to_bin bs = sbintrunc (length bs - 1) (bl_to_bin bs)"
proof (induction bs)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
  have " sbl_to_bin (a # bs) =  bl_to_bin (a # bs) - (int \<circ> of_bool) a * 2 ^ (length (bs) + 1)"
    unfolding sbl_to_bin.simps by auto
  have "a = True \<or> a = False"
    by auto
  moreover
  { assume "a = False"
    hence *: "bl_to_bin (a # bs) - (int o of_bool) a * 2 ^ (length bs + 1) =  bl_to_bin (a # bs)"
      by auto
    have "bl_to_bin (a # bs) + 2 ^ length bs < 2 ^ (length bs + 1)"
      using `a = False` bl_to_bin_False by (auto simp add: bl_to_bin_lt2p)
    hence "bl_to_bin (a # bs) = sbintrunc (length (a # bs) - 1) (bl_to_bin (a # bs))"
      unfolding sbintrunc_mod2p  by (simp add: bl_to_bin_ge0)
    hence ?case
      using * by auto }
  moreover
  { assume "a = True"
    hence *: "bl_to_bin (a # bs) = 2 ^ length bs + bl_to_bin bs"
      using bl_to_bin_correctness  sbl_to_bin_correctness by auto
    hence "bl_to_bin (a # bs) - (int \<circ> of_bool) a * 2 ^ (length (bs) + 1) =   bl_to_bin bs - 2 ^ length bs "
      using `a = True` by auto
    also have "... = sbintrunc (length bs) (bl_to_bin (a # bs))"
      unfolding sbintrunc_mod2p * 
      by (smt "*" \<open>a = True\<close> add.commute bl_to_bin_ge0 bl_to_bin_lt2p calculation int_mod_eq'
      minus_mod_self2 mult_cancel_right2 o_apply of_bool_eq(2) of_nat_1 plus_1_eq_Suc)
    finally have ?case
      by simp }
  ultimately show ?case by auto
qed

lemma
  "bl_to_bin (map Not bs) + 1 = 2 ^ length bs - bl_to_bin bs"
proof -
  have "bl_to_bin (map Not bs) = (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (\<not> (rev bs ! i)) * 2 ^ i)"
    unfolding bl_to_bin_correctness rev_map using nth_map[of _ "rev bs" "Not"] by auto
  moreover have "bl_to_bin bs = (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)"
    unfolding bl_to_bin_correctness by auto
  ultimately have "bl_to_bin (map Not bs) + bl_to_bin bs = (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (\<not> (rev bs ! i)) * 2 ^ i) +  (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)"
    by auto
  also have "... = (\<Sum>x = 0..<length bs. (int \<circ> of_bool) (\<not> rev bs ! x) * 2 ^ x + (int \<circ> of_bool) (rev bs ! x) * 2 ^ x)"
    unfolding sum.distrib[symmetric] by auto
  also have "... = (\<Sum>x = 0..<length bs. ((int \<circ> of_bool) (\<not> rev bs ! x) + (int o of_bool) (rev bs ! x)) * 2 ^ x)"
    by (auto simp add: field_simps)
  also have "... = (\<Sum>x = 0..<length bs. 2 ^ x)"
    by (smt comp_apply mult_cancel_right2 of_bool_eq(1) of_bool_eq(2) of_nat_1 semiring_1_class.of_nat_0 sum.cong)
  also have "... = bl_to_bin (replicate (length bs) True) "
    unfolding bl_to_bin_correctness by auto
  also have "... = 2 ^ length bs - 1"
    using bl_to_bin_replicate_T by auto
  finally show ?thesis
    by auto
qed

lemma uminus_alt':
  "sbl_to_bin (map Not (a # bs)) + 1 = - sbl_to_bin (a # bs)"
proof -
  have "sbl_to_bin (map Not (a # bs)) = sbl_to_bin (Not a # map Not bs)"
    by auto
  also have "... = - (int \<circ> of_bool) (\<not> a) * 2 ^ length bs + (\<Sum>i = 0..<length bs. (int \<circ> of_bool) ( \<not> (rev bs ! i)) * 2 ^ i)" (is "_ = ?init_not + ?sbl_not")
    unfolding sbl_to_bin_correctness rev_map using nth_map[of _ "rev bs" "Not"] by auto
  finally have "sbl_to_bin (map Not (a # bs)) = ?init_not + ?sbl_not"
    by auto
  have "sbl_to_bin (a # bs) = - (int \<circ> of_bool) a * 2 ^ length bs + (\<Sum>i = 0..<length bs. (int \<circ> of_bool) (rev bs ! i) * 2 ^ i)" (is "_ = ?init_def + ?sbl_def")
    unfolding sbl_to_bin_correctness by auto
  hence "sbl_to_bin (map Not (a # bs)) + sbl_to_bin (a # bs) = ?init_not + ?init_def + ?sbl_not + ?sbl_def"
    using `sbl_to_bin (map Not (a # bs)) = ?init_not + ?sbl_not` by auto
  also have "... = - (2 ^ length bs) + (?sbl_not + ?sbl_def)"
    by auto
  also have "... = - (2 ^ length bs) + (\<Sum>x = 0..<length bs. (int \<circ> of_bool) (\<not> rev bs ! x) * 2 ^ x + (int \<circ> of_bool) (rev bs ! x) * 2 ^ x)"
    unfolding sum.distrib[symmetric] by auto
  also have "... = - (2 ^ length bs) + (\<Sum>x = 0..<length bs. ((int \<circ> of_bool) (\<not> rev bs ! x) + (int o of_bool) (rev bs ! x)) * 2 ^ x)"
    by (auto simp add: field_simps)
  also have "... = - (2 ^ length bs) + (\<Sum>x = 0..<length bs. 2 ^ x)"
    by (smt comp_apply mult_cancel_right2 of_bool_eq(1) of_bool_eq(2) of_nat_1 semiring_1_class.of_nat_0 sum.cong)
  also have "... = - (2 ^ length bs) + bl_to_bin (replicate (length bs) True)"
    unfolding bl_to_bin_correctness by auto
  also have "... = - (2 ^ length bs) + 2 ^ length bs - 1"
    using bl_to_bin_replicate_T by auto
  also have "... = -1"
    by auto
  finally show ?thesis
    by auto
qed

lemma uminus_alt:
  "0 < length bs \<Longrightarrow> sbl_to_bin (map Not bs) + 1 = - sbl_to_bin bs"
  using uminus_alt'  by (metis list_exhaust_size_gt0)

lemma sbin_bl_bin_sbintruc:
  "0 < n \<Longrightarrow> sbl_to_bin (bin_to_bl n w) = sbintrunc (n - 1) w"
  using bin_bl_bin sbl_to_bin_alt_def size_bin_to_bl by auto

lemma sbl_to_bin_alt_def2:
  "0 < n \<Longrightarrow> sbl_to_bin bs = sbintrunc (length bs - 1) (sbl_to_bin bs)"
  by (simp add: sbl_to_bin_alt_def)
(* proof (induction bs)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
  have " sbl_to_bin (a # bs) =  bl_to_bin (a # bs) - (int \<circ> of_bool) a * 2 ^ (length (bs) + 1)"
    unfolding sbl_to_bin.simps by auto
  have "a = True \<or> a = False"
    by auto
  moreover
  { assume "a = False"
    hence *: "bl_to_bin (a # bs) - (int o of_bool) a * 2 ^ (length bs + 1) =  bl_to_bin (a # bs)"
      by auto
    have "bl_to_bin (a # bs) + 2 ^ length bs < 2 ^ (length bs + 1)"
      using `a = False` bl_to_bin_False by (auto simp add: bl_to_bin_lt2p)
    hence "bl_to_bin (a # bs) = sbintrunc (length (a # bs) - 1) (bl_to_bin (a # bs))"
      unfolding sbintrunc_mod2p  by (simp add: bl_to_bin_ge0)
    hence ?case
      using * by auto }
  moreover
  { assume "a = True"
    hence *: "bl_to_bin (a # bs) = 2 ^ length bs + bl_to_bin bs"
      using bl_to_bin_correctness  sbl_to_bin_correctness by auto
    hence "bl_to_bin (a # bs) - (int \<circ> of_bool) a * 2 ^ (length (bs) + 1) =   bl_to_bin bs - 2 ^ length bs "
      using `a = True` by auto
    also have "... = sbintrunc (length bs) (bl_to_bin (a # bs))"
      unfolding sbintrunc_mod2p * 
      by (smt "*" \<open>a = True\<close> add.commute bl_to_bin_ge0 bl_to_bin_lt2p calculation int_mod_eq'
      minus_mod_self2 mult_cancel_right2 o_apply of_bool_eq(2) of_nat_1 plus_1_eq_Suc)
    finally have ?case
      by simp }
  ultimately show ?case by auto
qed *)

end