(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Fixed_Point
  imports Bits_Int_Aux Complex_Main "HOL-Decision_Procs.Approximation"
begin

instantiation sum :: (len0, len0) len0
begin

definition
  len_sum [simp] : "len_of (x :: ('a, 'b) sum itself) = LENGTH('a) + LENGTH('b)"

instance ..

end

instance sum :: (len0, len) len
  by (intro_classes, simp)
 

typedef (overloaded) ('a::len0, 'b::len0) fixed = "UNIV :: ('a + 'b) word set" 
  morphisms word_of_fixed Fixed ..                                     

setup_lifting  type_definition_fixed

text \<open>Interpreting fixed-point numbers\<close>

instantiation fixed :: (len0, len0) "{group_add}"
begin

lift_definition zero_fixed :: "('a, 'b) fixed" is "0" .

lift_definition plus_fixed :: "('a, 'b) fixed \<Rightarrow> ('a, 'b) fixed \<Rightarrow> ('a, 'b) fixed" is "(+)" .

lift_definition minus_fixed :: "('a, 'b) fixed \<Rightarrow> ('a, 'b) fixed \<Rightarrow> ('a, 'b) fixed" is "(-)" .

lift_definition uminus_fixed :: "('a, 'b) fixed \<Rightarrow> ('a, 'b) fixed " is "uminus" .

instance by standard (transfer, simp add: algebra_simps)+
end

instantiation fixed :: (len0, len) times
begin

lift_definition times_fixed :: "('a, 'b) fixed \<Rightarrow> ('a, 'b) fixed \<Rightarrow> ('a , 'b) fixed" is 
  "\<lambda>x y. word_of_int ((sint x * sint y) div (2 ^ LENGTH ('b)))" .

instance ..

end

abbreviation "uint_of_fixed \<equiv> uint o word_of_fixed" 
abbreviation "sint_of_fixed \<equiv> sint o word_of_fixed"

definition ureal_of_fixed :: "('a::len0, 'b::len0) fixed \<Rightarrow> real" where
  "ureal_of_fixed w = uint_of_fixed w / 2 ^ LENGTH('b)"

definition sreal_of_fixed :: "('a::len0, 'b::len) fixed \<Rightarrow> real" where
  "sreal_of_fixed w = sint_of_fixed w / 2 ^ LENGTH('b)"

text \<open>Compare the following two with the correctness theorem in @{thm Word.uint_plus_if'}. We cannot
have correctness theorem similar to @{thm  Word.uint_word_ariths(1)} since modulo operator is not
defined for reals.\<close>

lemma ureal_of_fixed_add_no_overflow:
  fixes x y :: "('a::len0, 'b::len0) fixed"
  assumes "uint_of_fixed x + uint_of_fixed y < 2 ^ (LENGTH('a) + LENGTH('b)) "
  shows "ureal_of_fixed (x + y) = ureal_of_fixed x + ureal_of_fixed y"
proof -
  have "ureal_of_fixed (x + y) = uint (word_of_fixed x + word_of_fixed y) / 2 ^ LENGTH('b)"
    unfolding ureal_of_fixed_def by transfer auto
  also have " ... = (uint (word_of_fixed x) + uint (word_of_fixed y)) / 2 ^ LENGTH('b)"
    unfolding uint_word_ariths(1) using uint_add_lem assms by auto
  also have "... = uint (word_of_fixed x) / 2 ^ LENGTH('b) + uint (word_of_fixed y) / 2 ^ LENGTH('b)"
    by (auto simp add: divide_simps)
  also have "... = ureal_of_fixed x + ureal_of_fixed y"
    unfolding ureal_of_fixed_def by auto
  finally show ?thesis
    by auto
qed

lemma ureal_of_fixed_add_overflow:
  fixes x y :: "('a::len0, 'b::len0) fixed"
  assumes "uint_of_fixed x + uint_of_fixed y \<ge> 2 ^ (LENGTH('a) + LENGTH('b)) "
  shows "ureal_of_fixed (x + y) = ureal_of_fixed x + ureal_of_fixed y  - 2 ^ LENGTH('a)"
proof -
  have "ureal_of_fixed (x + y) = uint (word_of_fixed x + word_of_fixed y) / 2 ^ LENGTH('b)" (is "?lhs0 = _")
    unfolding ureal_of_fixed_def by transfer auto
  moreover have "uint (word_of_fixed x + word_of_fixed y) = uint (word_of_fixed x) + uint (word_of_fixed y) - 2 ^ LENGTH('a + 'b)" (is "_ = ?rhs1")
    unfolding uint_plus_if' using assms by simp
  ultimately have "?lhs0 = ?rhs1 / 2 ^ LENGTH('b)"
    by auto
  also have "... = ureal_of_fixed x + ureal_of_fixed y  - 2 ^ LENGTH('a)"
    unfolding ureal_of_fixed_def by (auto simp add: divide_simps power_add)
  finally show ?thesis
    by auto
qed

text \<open>The following three lemmas correspond to the formula specified by Randall E Bryant :
  Computer System --- A Programmer's Perspective Equation 2.14. \<close>

lemma sreal_of_fixed_add_no_overflow:
  fixes x y :: "('a::len0, 'b::len) fixed"
  assumes " - (2 ^ (LENGTH('a) + LENGTH('b) - 1)) \<le> sint_of_fixed x + sint_of_fixed y"
  assumes "sint_of_fixed x + sint_of_fixed y < 2 ^ (LENGTH('a) + LENGTH('b) - 1)"
  shows "sreal_of_fixed (x + y) = sreal_of_fixed x + sreal_of_fixed y"
proof -
  have "sreal_of_fixed (x + y) = sint (word_of_fixed x + word_of_fixed y) / 2 ^ LENGTH('b)"
    unfolding sreal_of_fixed_def by transfer auto
  also have "... = (sbintrunc (LENGTH('a + 'b) - 1) (sint (word_of_fixed x) + sint (word_of_fixed y))) / 2 ^ LENGTH('b)"
    unfolding sint_word_ariths(1) by auto
  also have "... = real_of_int ((sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ (LENGTH('a + 'b) - 1)) mod 2 ^ Suc (LENGTH('a + 'b) - 1) - 2 ^ (LENGTH('a + 'b) - 1)) / 2 ^ LENGTH('b) "
    unfolding sbintrunc_mod2p by auto
  also have "... = real_of_int (sint (word_of_fixed x) + sint (word_of_fixed y)) / 2 ^ LENGTH('b) "
  proof -
    have "(sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ (LENGTH('a + 'b) - 1)) mod 2 ^ Suc (LENGTH('a + 'b) - 1) = 
           sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ (LENGTH('a + 'b) - 1)"
      using int_mod_eq' assms unfolding comp_def
      by (smt Bit_B1_2t One_nat_def assms(1) int_mod_eq' len_sum o_apply power_BIT)
    thus ?thesis
      by auto
  qed
  finally show ?thesis
    unfolding sreal_of_fixed_def by (auto simp add: divide_simps)
qed

lemma sreal_of_fixed_add_positive_overflow:
  fixes x y :: "('a::len0, 'b::len) fixed"
  assumes "sint_of_fixed x + sint_of_fixed y \<ge>  2 ^ (LENGTH('a) + LENGTH('b) - 1)"
  shows "sreal_of_fixed (x + y) = sreal_of_fixed x + sreal_of_fixed y - 2 ^ LENGTH('a)"
proof -
  have "sreal_of_fixed (x + y) = sint (word_of_fixed x + word_of_fixed y) / 2 ^ LENGTH('b)"
    unfolding sreal_of_fixed_def by transfer auto
  also have "... = (sbintrunc (LENGTH('a + 'b) - 1) (sint (word_of_fixed x) + sint (word_of_fixed y))) / 2 ^ LENGTH('b)"
    unfolding sint_word_ariths(1) by auto
  also have "... = real_of_int ((sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ (LENGTH('a + 'b) - 1)) mod 2 ^ Suc (LENGTH('a + 'b) - 1) - 2 ^ (LENGTH('a + 'b) - 1)) / 2 ^ LENGTH('b) "
    unfolding sbintrunc_mod2p by auto
  also have "... = real_of_int (sint (word_of_fixed x) + sint (word_of_fixed y) - 2 ^ LENGTH('a + 'b)) / 2 ^ LENGTH('b) "
  proof -
    have 0: "(0 :: int) < 2 ^ Suc (LENGTH('a + 'b) - 1)"
      by (auto)
    have 1: "sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ (LENGTH('a + 'b) - 1) \<ge> 2 ^ Suc (LENGTH('a + 'b) - 1)"
      using assms unfolding comp_def 
      by (smt int_mod_eq' len_sum sbintrunc_mod2p sint_lt sint_word_ariths(1))
    thus ?thesis
      using mod_pos_geq[OF 0 1]
      by (smt Euclidean_Division.pos_mod_bound One_nat_def Suc_pred int_mod_eq' len_gt_0 word_sint.norm_Rep zero_less_power)
  qed
  finally show ?thesis
    unfolding sreal_of_fixed_def comp_def by (auto simp add: divide_simps power_add)
qed


lemma sreal_of_fixed_add_negative_overflow:
  fixes x y :: "('a::len0, 'b::len) fixed"
  assumes "sint_of_fixed x + sint_of_fixed y <  - (2 ^ (LENGTH('a) + LENGTH('b) - 1))"
  shows   "sreal_of_fixed (x + y) = sreal_of_fixed x + sreal_of_fixed y + 2 ^ LENGTH('a)"
proof -
  have "sreal_of_fixed (x + y) = sint (word_of_fixed x + word_of_fixed y) / 2 ^ LENGTH('b)"
    unfolding sreal_of_fixed_def by transfer auto
  also have "... = (sbintrunc (LENGTH('a + 'b) - 1) (sint (word_of_fixed x) + sint (word_of_fixed y))) / 2 ^ LENGTH('b)"
    unfolding sint_word_ariths(1) by auto
  also have "... = real_of_int ((sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ (LENGTH('a + 'b) - 1)) mod 2 ^ Suc (LENGTH('a + 'b) - 1) - 2 ^ (LENGTH('a + 'b) - 1)) / 2 ^ LENGTH('b) "
    unfolding sbintrunc_mod2p by auto
  also have "... = real_of_int (sint (word_of_fixed x) + sint (word_of_fixed y) + 2 ^ LENGTH('a + 'b)) / 2 ^ LENGTH('b) "
    by (smt Bit_B1_2t One_nat_def Suc_pred assms int_mod_eq' len_gt_0 len_sum mod_add_self2 o_apply power_BIT sint_ge)
  finally show ?thesis
    unfolding sreal_of_fixed_def comp_def by (auto simp add: divide_simps power_add)
qed

definition frac :: "bool \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "frac neg prec x = x - (if neg then round_up (-int prec) x else round_down (- int prec) x)"

definition smf :: "('a::len, 'b::len) fixed \<Rightarrow> ('a::len, 'b::len) fixed \<Rightarrow> bool" where
  "smf x y = bin_nth (sint_of_fixed x * sint_of_fixed y) (LENGTH('a + 'b + 'b) - 1)"

lemma not_smf_floor:
  fixes x y :: "('a::len, 'b::len) fixed"         
  assumes "\<not> smf x y"
  shows   " \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b)) + (1/2)\<rfloor> = 
            \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b))\<rfloor>"
proof -
  have " (sint (word_of_fixed x) * sint (word_of_fixed y) -
          sint (word_of_fixed x) * sint (word_of_fixed y) div 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b)) * 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b)))
    <  (2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1))" (is "?lhs0 < ?rhs0")
  proof -
    have "sint (word_of_fixed x) * sint (word_of_fixed y) mod 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b)) = 
          sint (word_of_fixed x) * sint (word_of_fixed y) mod (2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) * 2)"
      by (metis One_nat_def Suc_pred add_gr_0 len_gt_0 mult.commute power.simps(2))
    also have "... = 
2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) * (sint (word_of_fixed x) * sint (word_of_fixed y) div 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) mod 2) +
sint (word_of_fixed x) * sint (word_of_fixed y) mod 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1)"
      using zmod_zmult2_eq[of "2" "sint (word_of_fixed x) * sint (word_of_fixed y)" "2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1)"]
      by auto
    also have "... = sint (word_of_fixed x) * sint (word_of_fixed y) mod 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1)"
      using assms unfolding smf_def bin_nth_eq_mod odd_iff_mod_2_eq_one  by (simp add: Groups.add_ac(2) add.left_commute)
    also have "... < (2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1))"
      by auto
    finally show ?thesis
      unfolding approximation_preproc_int(13)[symmetric]  by auto
  qed
  have "take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y)) / real_of_int (2 ^ LENGTH('b)) < 
         real_of_int (2 ^ (LENGTH('a) + LENGTH('b) - 1))"
  proof -
    have "real_of_int ?lhs0 < real_of_int ?rhs0"
      using `?lhs0 < ?rhs0` approximation_preproc_int(16) by auto
    hence "real_of_int ?lhs0 / 2 ^ LENGTH('b) < real_of_int ?rhs0 / 2 ^ LENGTH('b)"
      using divide_strict_right_mono[where c="2^LENGTH('b)"] by auto
    also have "... = 2 ^ (LENGTH('a) + LENGTH('b) - 1)"
    proof -
      have f1: "\<And>n. (0::nat) < 1 + n"
        by force
      have f2: "\<And>n. 0 < len_of (TYPE('a)::'a itself) + n"
        by simp
      have "2 ^ len_of (TYPE('b)::'b itself) \<noteq> (0::real)"
        by simp
      then show ?thesis
        using f2 f1 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_pred
        add_diff_cancel_left' diff_add_0 diff_is_0_eq nonzero_eq_divide_eq of_int_numeral
        of_int_power power_add)
    qed      
    finally show ?thesis
      unfolding take_bit_eq_mod  approximation_preproc_int(13) by auto
  qed
  hence "real_of_int (drop_bit LENGTH('b) (take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y)))) <  real_of_int (2 ^ (LENGTH('a) + LENGTH('b) - 1))"
    unfolding drop_bit_eq_div using real_of_int_div4[of "take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y))" "2 ^ LENGTH('b)"]
    by linarith    
  hence "real_of_int (drop_bit LENGTH('b) (take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y)))) <  real_of_int (2 ^ (LENGTH('a) + LENGTH('b)) div 2)"
    using power_diff[of "2"] 
    by (smt One_nat_def Suc_pred add_gr_0 le_numeral_extra(4) len_gt_0 neq0_conv order_less_imp_le power_one_right zero_less_diff)
  hence "real_of_int (drop_bit LENGTH('b) (take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y)))) * 2 < 2 ^ (LENGTH('a) + LENGTH('b))"
    using real_of_int_div4[of " 2 ^ (LENGTH('a) + LENGTH('b))" "2"] by auto
  hence " real_of_int (sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) mod 2 ^ LENGTH('a + 'b)) / real_of_int (2 ^ LENGTH('a + 'b)) < 1/2"
    unfolding take_bit_eq_mod[symmetric] drop_bit_eq_div[symmetric]  take_bit_drop_bit by auto
  hence "Archimedean_Field.frac (real_of_int (sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / real_of_int (2 ^ LENGTH('a + 'b))) < 1 / 2"
    unfolding Archimedean_Field.frac_def  approximation_preproc_int(7)[symmetric]
    using real_of_int_div_aux[of "(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b))" "(2 ^ LENGTH('a + 'b))"]
    by auto
  hence "\<not> 1 / 2 \<le> Archimedean_Field.frac (real_of_int (sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b))"
    unfolding not_le by auto
  thus ?thesis
    unfolding round_def[symmetric] round_altdef by auto
qed

lemma smf_ceiling:
  fixes x y :: "('a::len, 'b::len) fixed"         
  assumes " smf x y"
  shows   " \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b)) + (1/2)\<rfloor> = 
            \<lceil>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b))\<rceil>"
proof -
  have " (sint (word_of_fixed x) * sint (word_of_fixed y) -
          sint (word_of_fixed x) * sint (word_of_fixed y) div 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b)) * 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b)))
    \<ge>  (2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1))" (is "?lhs0 \<ge> ?rhs0")
  proof -
    have "sint (word_of_fixed x) * sint (word_of_fixed y) mod 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b)) = 
          sint (word_of_fixed x) * sint (word_of_fixed y) mod (2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) * 2)"
      by (metis One_nat_def Suc_pred add_gr_0 len_gt_0 mult.commute power.simps(2))
    also have "... = 
2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) * (sint (word_of_fixed x) * sint (word_of_fixed y) div 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) mod 2) +
sint (word_of_fixed x) * sint (word_of_fixed y) mod 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1)"
      using zmod_zmult2_eq[of "2" "sint (word_of_fixed x) * sint (word_of_fixed y)" "2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1)"]
      by auto
    also have "... = 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1) + sint (word_of_fixed x) * sint (word_of_fixed y) mod 2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1)"
      using assms unfolding smf_def bin_nth_eq_mod odd_iff_mod_2_eq_one  by (simp add: Groups.add_ac(2) add.left_commute)
    also have "... \<ge> (2 ^ (LENGTH('a) + LENGTH('b) + LENGTH('b) - 1))"
      by auto
    finally show ?thesis
      unfolding approximation_preproc_int(13)[symmetric]  by auto
  qed
  have " (2 ^ (LENGTH('a) + LENGTH('b) - 1)) \<le> 
        take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y)) div (2 ^ LENGTH('b))"
  proof -
    have "?rhs0 div 2 ^ LENGTH('b) \<le> ?lhs0 div 2 ^ LENGTH('b)"
      using zdiv_mono1[OF `?rhs0 \<le> ?lhs0`, of "2 ^ LENGTH('b)"] by auto
    moreover have "real_of_int ?rhs0 / 2 ^ LENGTH('b) = 2 ^ (LENGTH('a) + LENGTH('b) - 1)"
    proof -
      have f1: "\<And>n. (0::nat) < 1 + n"
        by force
      have f2: "\<And>n. 0 < len_of (TYPE('a)::'a itself) + n"
        by simp
      have "2 ^ len_of (TYPE('b)::'b itself) \<noteq> (0::real)"
        by simp
      then show ?thesis
        using f2 f1 by (metis (no_types) Nat.add_diff_assoc2 One_nat_def Suc_pred
        add_diff_cancel_left' diff_add_0 diff_is_0_eq nonzero_eq_divide_eq of_int_numeral
        of_int_power power_add)
    qed 
    ultimately show ?thesis
      unfolding take_bit_eq_mod  approximation_preproc_int(13)  using approximation_preproc_int(7) by auto
  qed
  hence "real_of_int (2 ^ (LENGTH('a) + LENGTH('b) - 1)) \<le> 
         real_of_int (drop_bit LENGTH('b) (take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y))))"
    unfolding drop_bit_eq_div by auto
  hence "real_of_int (2 ^ (LENGTH('a) + LENGTH('b)) div 2) \<le> real_of_int (drop_bit LENGTH('b) (take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y))))"
    using power_diff[of "2"] 
    by (metis (no_types) diff_self_eq_0 div_le_dividend le_numeral_extra(3) of_int_0 one_div_two_eq_zero power_0 power_diff power_one_right take_bit_0 take_bit_drop_bit zero_neq_numeral)
  hence "real_of_int (2 ^ (LENGTH('a) + LENGTH('b))) \<le>  
        (drop_bit LENGTH('b) (take_bit (LENGTH('a) + LENGTH('b) + LENGTH('b)) (sint (word_of_fixed x) * sint (word_of_fixed y)))) * 2"
      using real_of_int_div[of "2" "2 ^ (LENGTH('a) + LENGTH('b))"] by (auto)
  hence " 1/2 \<le> real_of_int (sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) mod 2 ^ LENGTH('a + 'b)) / real_of_int (2 ^ LENGTH('a + 'b))"
    unfolding take_bit_eq_mod[symmetric] drop_bit_eq_div[symmetric]  take_bit_drop_bit by auto
  hence " 1 / 2 \<le> Archimedean_Field.frac (real_of_int (sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b))"
    unfolding Archimedean_Field.frac_def 
    by (metis (no_types, hide_lams) add_diff_cancel_left' floor_divide_of_int_eq of_int_eq_numeral_power_cancel_iff real_of_int_div_aux) 
  thus ?thesis
    unfolding round_def[symmetric] round_altdef by auto
qed


lemma
  fixes x y :: "('a::len, 'b::len) fixed"         
  shows "sreal_of_fixed (x * y) = (let m   = sreal_of_fixed x * sreal_of_fixed y;
                                       m'  = round_down LENGTH('b) m 
                                   in  frac (smf x y) LENGTH('a) m') "    
proof -
  let ?m  = "(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('b)"
  let ?m' = " sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) + 2 ^ (LENGTH('a + 'b) - 1)"
  let ?unified1 = "round_down LENGTH('b) (sreal_of_fixed x * sreal_of_fixed y)"
  have zero_leq: "(0::int) \<le> (2::int) ^ LENGTH('b)"
    by simp
    
  have "sreal_of_fixed (x * y) = (sbintrunc (LENGTH('a + 'b) - 1) (sint_of_fixed x * sint_of_fixed y div (2 ^ LENGTH ('b)))) / 2 ^ LENGTH('b)"
    unfolding sreal_of_fixed_def  by transfer' (auto simp add: comp_def sint_sbintrunc')
  also have "... = ((sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) + 2 ^ (LENGTH('a + 'b) - 1)) mod 2 ^ Suc (LENGTH('a + 'b) - 1) - 2 ^ (LENGTH('a + 'b) - 1)) / 2 ^ LENGTH('b)"
    unfolding sbintrunc_mod2p by auto
  also have "... = (sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)  - ?m' div 2 ^ LENGTH('a + 'b) * 2 ^ LENGTH('a + 'b))  / 2 ^ LENGTH('b)"
    unfolding  approximation_preproc_int(13) by auto 
  also have "... = ?m  - (?m' div 2 ^ LENGTH('a + 'b) * 2 ^ LENGTH('a + 'b)) / 2 ^ LENGTH('b)"
    by (auto simp add: divide_simps)
  finally have "sreal_of_fixed (x * y) = ?m  - (?m' div 2 ^ LENGTH('a + 'b) * 2 ^ LENGTH('a + 'b)) / 2 ^ LENGTH('b)"
    by auto
  also have "... = ?m  - (?m' div 2 ^ LENGTH('a + 'b) * 2 ^ LENGTH('a))"
    by (auto simp add: power_add)
  also have "... = ?m - \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) + 2 ^ (LENGTH('a + 'b) - 1)) / (2 ^ LENGTH('a + 'b))\<rfloor> * 2 ^ LENGTH('a)"
    using approximation_preproc_int(7) by auto
  finally have temp: "sreal_of_fixed (x * y) = ?m - \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) + 2 ^ (LENGTH('a + 'b) - 1)) / (2 ^ LENGTH('a + 'b))\<rfloor> * 2 ^ LENGTH('a)"
    by auto
  have "  real_of_int \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) + 2 ^ (LENGTH('a + 'b) - 1)) / real_of_int (2 ^ LENGTH('a + 'b))\<rfloor> = 
          real_of_int \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / real_of_int (2 ^ LENGTH('a + 'b)) + (real_of_int (2 ^ (LENGTH('a + 'b) - 1)) / real_of_int (2 ^ LENGTH('a + 'b))) \<rfloor>"
    by (auto simp add: divide_simps)
  also have "... =  \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b)) + 1/2\<rfloor>"
  proof -
    have "real_of_int (2 ^ (LENGTH('a + 'b) - 1)) / real_of_int (2 ^ LENGTH('a + 'b)) = 1/2"
      by (smt One_nat_def Suc_pred div_self divide_divide_eq_left len_gt_0 of_int_1 of_int_add of_int_power power_Suc power_commutes zero_less_power)
    thus ?thesis
      by auto
  qed
  finally have last: "sreal_of_fixed (x * y) = ?m - \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b)) + (1/2)\<rfloor> * 2 ^ LENGTH('a)"
    using temp by auto

  have "smf x y \<or> \<not>  smf x y" by auto
  moreover
  { assume "\<not> smf x y"
    have "sreal_of_fixed (x * y) = ?m - \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b))\<rfloor> * 2 ^ LENGTH('a)"
      using last unfolding not_smf_floor[OF `\<not> smf x y`] by auto
    also have "... = ?unified1 - round_down (- int (LENGTH('a))) ?unified1"
    proof -
      have "?unified1 = 
            \<lfloor>real_of_int (sint (word_of_fixed x)) / 2 ^ LENGTH('b) * (real_of_int (sint (word_of_fixed y)) / 2 ^ LENGTH('b)) * 2 powr real_of_int (int LENGTH('b))\<rfloor> * 2 powr - real_of_int (int LENGTH('b))"
        unfolding round_down_def sreal_of_fixed_def comp_def by auto
      also have "... = 
            \<lfloor>real_of_int (sint (word_of_fixed x)) / 2 ^ LENGTH('b) * (real_of_int (sint (word_of_fixed y))) / 2 ^ LENGTH('b) * 2 powr real_of_int (int LENGTH('b))\<rfloor> * 2 powr - real_of_int (int LENGTH('b))"
        by auto
      also have "... =  \<lfloor>real_of_int (sint (word_of_fixed x)) / 2 ^ LENGTH('b) * (real_of_int (sint (word_of_fixed y)))\<rfloor> * 2 powr - real_of_int (int LENGTH('b))"
        using Transcendental.powr_real_of_int[of "2" "int LENGTH('b)"] by auto
      also have "... =  \<lfloor>real_of_int (sint (word_of_fixed x) * sint (word_of_fixed y)) / real_of_int (2 ^ LENGTH('b))\<rfloor> / 2 ^ LENGTH('b)"
        using powr_minus_divide[of "2" "real_of_int (int LENGTH('b))"] Transcendental.powr_real_of_int[of "2" "int LENGTH('b)"]
        by (auto simp add: field_simps)
      also have "... = ((sint (word_of_fixed x) * sint (word_of_fixed y)) div 2 ^ LENGTH('b)) / 2 ^ LENGTH('b)"
        using Approximation.approximation_preproc_int(7) by auto
      also have "... = ?m"
        unfolding comp_def by auto  
      finally have "?unified1 = ?m"
        by auto

      hence "round_down (-int(LENGTH('a))) ?unified1 = round_down (-int(LENGTH('a))) ?m"
        by auto
      also have "... =  \<lfloor>sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) / 2 ^ LENGTH('b) * 2 powr real_of_int (- int LENGTH('a))\<rfloor>  * 2 powr - real_of_int (- int LENGTH('a))"
        unfolding round_down_def by auto
      also have "... =  \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('b) / 2 ^ LENGTH('a)\<rfloor> * 2 powr real_of_int (int LENGTH('a))"
        using  powr_minus_divide[of "2" "real_of_int (int LENGTH('a))"] Transcendental.powr_real_of_int[of "2" "int LENGTH('a)"] 
        by auto
      also have "... =  \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b)\<rfloor>  * 2 powr real_of_int (int LENGTH('a))"
        by (auto simp add: power_add field_simps)
      also have "... =  \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b)\<rfloor>  * 2 ^ LENGTH('a)"
        using Transcendental.powr_real_of_int[of "2" "int LENGTH('a)"] by auto
      finally have "round_down (-int(LENGTH('a))) ?unified1 = \<lfloor>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b)\<rfloor>  * 2 ^ LENGTH('a)"
        by auto
      thus ?thesis
        using `?unified1 = ?m` by auto
    qed
    finally have ?thesis
      using `\<not> smf x y` unfolding Let_def Fixed_Point.frac_def by auto }
  moreover
  { assume "smf x y"
    have "sreal_of_fixed (x * y) = ?m - \<lceil>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / (2 ^ LENGTH('a + 'b))\<rceil> * 2 ^ LENGTH('a)"
      using last unfolding smf_ceiling[OF `smf x y`] by auto
    also have "... = ?unified1 - round_up (-int (LENGTH('a))) ?unified1"
    proof -
      have "?unified1 = 
            \<lfloor>real_of_int (sint (word_of_fixed x)) / 2 ^ LENGTH('b) * (real_of_int (sint (word_of_fixed y)) / 2 ^ LENGTH('b)) * 2 powr real_of_int (int LENGTH('b))\<rfloor> * 2 powr - real_of_int (int LENGTH('b))"
        unfolding round_down_def sreal_of_fixed_def comp_def by auto
      also have "... = 
            \<lfloor>real_of_int (sint (word_of_fixed x)) / 2 ^ LENGTH('b) * (real_of_int (sint (word_of_fixed y))) / 2 ^ LENGTH('b) * 2 powr real_of_int (int LENGTH('b))\<rfloor> * 2 powr - real_of_int (int LENGTH('b))"
        by auto
      also have "... =  \<lfloor>real_of_int (sint (word_of_fixed x)) / 2 ^ LENGTH('b) * (real_of_int (sint (word_of_fixed y)))\<rfloor> * 2 powr - real_of_int (int LENGTH('b))"
        using Transcendental.powr_real_of_int[of "2" "int LENGTH('b)"] by auto
      also have "... =  \<lfloor>real_of_int (sint (word_of_fixed x) * sint (word_of_fixed y)) / real_of_int (2 ^ LENGTH('b))\<rfloor> / 2 ^ LENGTH('b)"
        using powr_minus_divide[of "2" "real_of_int (int LENGTH('b))"] Transcendental.powr_real_of_int[of "2" "int LENGTH('b)"]
        by (auto simp add: field_simps)
      also have "... = ((sint (word_of_fixed x) * sint (word_of_fixed y)) div 2 ^ LENGTH('b)) / 2 ^ LENGTH('b)"
        using Approximation.approximation_preproc_int(7) by auto
      also have "... = ?m"
        unfolding comp_def by auto  
      finally have "?unified1 = ?m"
        by auto
      hence "round_up (-int(LENGTH('a))) ?unified1 = round_up (-int(LENGTH('a))) ?m"
        by auto
      also have "... =  \<lceil>sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b) / 2 ^ LENGTH('b) * 2 powr real_of_int (- int LENGTH('a))\<rceil>  * 2 powr - real_of_int (- int LENGTH('a))"
        unfolding round_up_def by auto
      also have "... =  \<lceil>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('b) / 2 ^ LENGTH('a)\<rceil> * 2 powr real_of_int (int LENGTH('a))"
        using  powr_minus_divide[of "2" "real_of_int (int LENGTH('a))"] Transcendental.powr_real_of_int[of "2" "int LENGTH('a)"] 
        by auto
      also have "... =  \<lceil>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b)\<rceil>  * 2 powr real_of_int (int LENGTH('a))"
        by (auto simp add: power_add field_simps)
      also have "... =  \<lceil>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b)\<rceil>  * 2 ^ LENGTH('a)"
        using Transcendental.powr_real_of_int[of "2" "int LENGTH('a)"] by auto
      finally have "round_up (-int(LENGTH('a))) ?unified1 = \<lceil>(sint_of_fixed x * sint_of_fixed y div 2 ^ LENGTH('b)) / 2 ^ LENGTH('a + 'b)\<rceil>  * 2 ^ LENGTH('a)"
        by auto
      thus ?thesis
        using `?unified1 = ?m` by auto
    qed
    finally have ?thesis
      using `smf x y` unfolding Let_def Fixed_Point.frac_def by auto }
  ultimately show ?thesis
    by blast
qed

definition square_fixed :: "('a::len0, 'b::len) fixed \<Rightarrow> ('a, 'b) fixed" where
  "square_fixed fi = fi * fi"
  
end
