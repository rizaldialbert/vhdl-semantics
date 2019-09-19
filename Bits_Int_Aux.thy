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
    Main "HOL-Word.Word"
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

end