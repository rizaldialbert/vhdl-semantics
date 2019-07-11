(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Dflipflop
  imports VHDL_Hoare_Complete
begin

text \<open>datatype for all signals\<close>

datatype sig = D | CLK | OUT

definition dflipflop :: "sig conc_stmt" where
  "dflipflop \<equiv> process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull"

abbreviation is_posedge :: "'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_posedge w s j i \<equiv> (j \<le> i \<and> \<not> w s (j - 1) \<and> w s j \<comment> \<open>change of signal from low to high at j\<close>
                         \<and> (\<forall>j' \<le> i. \<not> w s (j' - 1) \<and> w s j' \<longrightarrow> j' \<le> j) \<comment> \<open>largest of positive edge\<close>)"

lemma is_posedge_strictly_positive:
  "is_posedge w s j i \<Longrightarrow> 0 < j"
  using gr_zeroI by force

lemma is_posedge_unique:
  assumes "is_posedge w s j1 i" and "is_posedge w s j2 i"
  shows "j1 = j2"
  using assms by (simp add: dual_order.antisym)

definition inv :: "sig assn2" where
  "inv tw \<equiv> (\<forall>i < fst tw.                            \<comment> \<open>at all ``times''\<close>
            (\<forall>j \<le> i. is_posedge (snd tw) CLK j i \<longrightarrow> \<comment> \<open>if there is positive edge namely j\<close>
                snd tw OUT (i + 1) \<longleftrightarrow> snd tw D j)   \<comment> \<open>the output at i + 1 equals to D at j\<close>)"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> disjnt {CLK} (event_of tw) \<or> \<not> snd tw CLK (fst tw) \<longrightarrow> \<comment> \<open>if there is no positive edge in CLK\<close>
             (\<forall>i \<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw)) \<comment> \<open>the value stays the same\<close>"

lemma inv_time_seq_next_time:
  assumes "inv tw" and "\<not> disjnt {CLK} (event_of tw)" and "beval_world_raw2 tw (Bsig CLK)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig D)]"
  shows "inv (next_time_world tw', snd tw')"
  unfolding inv_def
proof (rule allI, rule impI, rule allI, rule impI, rule impI)
  fix i j
  assume "i < fst (next_time_world tw', snd tw')"
  hence "i < next_time_world tw'"
    by auto
  assume "j \<le> i"
  assume "is_posedge (snd (next_time_world tw', snd tw')) CLK j i "
  hence "is_posedge (snd tw') CLK j i"
    by auto
  have "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
    using \<open>i < next_time_world tw'\<close> by linarith
  moreover
  { assume "i < fst tw"
    hence "is_posedge (snd tw) CLK j i" 
      using \<open>is_posedge (snd tw') CLK j i\<close> by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    have "snd tw' OUT (i + 1) = snd tw OUT (i + 1)" 
      by (simp add: \<open>i < get_time tw\<close> tw'_def worldline_upd2_before_dly)
    also have "... = snd tw D j"
      using \<open>j \<le> i\<close> \<open>is_posedge (snd tw') CLK j i\<close> assms(1) \<open>i < fst tw\<close> \<open>is_posedge (snd tw) CLK j i\<close>
      unfolding inv_def by auto
    also have "... = snd tw' D j"
      by (metis (no_types, lifting) One_nat_def \<open>i < get_time tw\<close> \<open>j \<le> i\<close> add.right_neutral
      add_Suc_right add_mono1 le_imp_less_Suc less_trans tw'_def worldline_upd2_before_dly)
    finally have "snd tw' OUT (i + 1) = snd tw' D j"
      by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
    hence "is_posedge (snd tw) CLK j i" 
      using \<open>is_posedge (snd tw') CLK j i\<close> by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    have "snd tw' OUT (i + 1) = snd tw' OUT (fst tw + 1)"
      by (metis (mono_tags, lifting) One_nat_def \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close>
      add.right_neutral add_Suc_right fst_conv le_Suc_eq le_add1 le_less_trans less_diff_conv
      tw'_def unchanged_until_next_time_world worldline_upd2_def)
    also have "... = snd tw D (fst tw)"
      unfolding tw'_def  by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
    also have "... = snd tw D j"    
    proof -
      have "snd tw CLK (fst tw) \<noteq> snd tw CLK (fst tw - 1)"
        using assms(2) unfolding event_of_alt_def 
        by (smt \<open>i < next_time_world tw'\<close> \<open>is_posedge (snd tw') CLK j i\<close> \<open>j \<le> i\<close> diff_is_0_eq'
        diff_le_self disjnt_iff fst_conv le_less_trans mem_Collect_eq singletonD tw'_def
        unchanged_until_next_time_world worldline_upd2_def)
      hence "\<not> snd tw CLK (fst tw - 1)" and "snd tw CLK (fst tw)"
        using assms(3)  by (simp add: beval_world_raw2_Bsig)+
      moreover have "\<forall>j' \<le> i. \<not> snd tw CLK (j' - 1) \<and> snd tw CLK j' \<longrightarrow> j' \<le> fst tw"
        by (smt Suc_pred \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>i < next_time_world tw'\<close>
        \<open>is_posedge (snd tw') CLK j i\<close> \<open>is_posedge (snd tw) CLK j i\<close> \<open>j \<le> i\<close> add_diff_cancel_left'
        calculation(1) calculation(2) diff_is_0_eq' diff_le_self dual_order.strict_trans fst_conv
        le_Suc_eq le_less plus_1_eq_Suc tw'_def unchanged_until_next_time_world worldline_upd2_def)
      ultimately have "fst tw = j"
        using \<open>is_posedge (snd tw) CLK j i\<close> 
        by (simp add: \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>j \<le> i\<close> dual_order.antisym)
      thus ?thesis
        using \<open>is_posedge (snd tw) CLK j i\<close> by blast
    qed
    also have "... = snd tw' D j"
      by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    finally have "snd tw' OUT (i + 1) = snd tw' D j"
      by auto }
  moreover
  { assume "i = next_time_world tw' - 1"
    hence "is_posedge (snd tw) CLK j i" 
      using \<open>is_posedge (snd tw') CLK j i\<close> by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    have "snd tw' OUT (i + 1) = snd tw' OUT (next_time_world tw')"
      by (metis Suc_diff_1 Suc_eq_plus1 \<open>i < next_time_world tw'\<close> \<open>i = next_time_world tw' - 1\<close>
      add.right_neutral le_add2 nat_less_le not_le)
    also have "... = snd tw' OUT (fst tw + 1)"
      unfolding tw'_def 
      by (metis One_nat_def add.right_neutral add_Suc_right fst_conv less_Suc_eq_le
      next_time_world_at_least not_less snd_conv worldline_upd2_at_dly worldline_upd2_def
      worldline_upd_def)
    also have "... = snd tw D (fst tw)"
      unfolding tw'_def  by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
    also have "... = snd tw D j"    
    proof -
      have "snd tw CLK (fst tw) \<noteq> snd tw CLK (fst tw - 1)"
        using assms(2) unfolding event_of_alt_def 
        by (smt \<open>i < next_time_world tw'\<close> \<open>is_posedge (snd tw') CLK j i\<close> \<open>j \<le> i\<close> diff_is_0_eq'
        diff_le_self disjnt_iff fst_conv le_less_trans mem_Collect_eq singletonD tw'_def
        unchanged_until_next_time_world worldline_upd2_def)
      hence "\<not> snd tw CLK (fst tw - 1)" and "snd tw CLK (fst tw)"
        using assms(3)  by (simp add: beval_world_raw2_Bsig)+
      moreover have "\<forall>j' \<le> i. \<not> snd tw CLK (j' - 1) \<and> snd tw CLK j' \<longrightarrow> j' \<le> fst tw"
        by (smt One_nat_def Suc_pred \<open>i < next_time_world tw'\<close> eq_iff fst_conv le_0_eq le_Suc_eq
        le_cases le_less_trans not_less sig.distinct(5) snd_conv tw'_def
        unchanged_until_next_time_world worldline_upd2_def worldline_upd_def)
      ultimately have "fst tw = j"
        using \<open>is_posedge (snd tw) CLK j i\<close> 
        by (metis One_nat_def Suc_leI Suc_pred \<open>i = next_time_world tw' - 1\<close> \<open>j \<le> i\<close>
        add.right_neutral fst_swap le_add2 le_less next_time_world_at_least not_le snd_conv
        swap_simp tw'_def worldline_upd2_def)
      thus ?thesis
        using \<open>is_posedge (snd tw) CLK j i\<close> by blast
    qed
    also have "... = snd tw' D j"
      by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    finally have "snd tw' OUT (i + 1) = snd tw' D j"
      by auto }
  ultimately have "snd tw' OUT (i + 1) = snd tw' D j"
    by auto
  thus "snd (next_time_world tw', snd tw') OUT (i + 1) = snd (next_time_world tw', snd tw') D j"
    by auto
qed

lemma dflipflop_seq_inv:
  "\<turnstile> [\<lambda>tw. ((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK)] 
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_time_seq_next_time by auto

lemma inv2_seq_next_time:
  assumes "inv tw" and "inv2 tw" and "\<not> disjnt {CLK} (event_of tw)" and "beval_world_raw2 tw (Bsig CLK)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig D)]"
  shows "inv2 (next_time_world tw', snd tw')"
  unfolding inv2_def
proof (rule impI, rule allI, rule impI)
  fix i
  assume "   disjnt {CLK} (event_of (next_time_world tw', snd tw')) 
         \<or> \<not> snd (next_time_world tw', snd tw') CLK (get_time (next_time_world tw', snd tw'))"
  hence "disjnt {CLK} (event_of (next_time_world tw', snd tw')) \<or> \<not> snd tw' CLK (next_time_world tw')"
    by auto
  assume "get_time (next_time_world tw', snd tw') \<le> i"
  hence "next_time_world tw' \<le> i"
    by auto
  moreover have "fst tw < next_time_world tw'"
    using next_time_world_at_least  by (metis fst_conv tw'_def worldline_upd2_def)
  ultimately have "fst tw < i"
    by auto
  have "snd tw' OUT (i + 1) = snd tw' OUT (next_time_world tw')"
    unfolding tw'_def using \<open>fst tw < next_time_world tw'\<close> \<open>fst tw < i\<close>
    by (metis diff_is_0_eq' discrete less_numeral_extra(3) less_or_eq_imp_le snd_conv tw'_def worldline_upd2_def worldline_upd_def zero_less_diff)
  thus " snd (next_time_world tw', snd tw') OUT (i + 1) = snd (next_time_world tw', snd tw') OUT (get_time (next_time_world tw', snd tw'))"
    by auto
qed

lemma dflipflop_seq_inv2:
  "\<turnstile> [\<lambda>tw. ((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK)] 
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_seq_next_time by auto

lemma dflipflop_inv_if:
  "\<turnstile> [\<lambda>tw.((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK)] 
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv2 (next_time_world tw, snd tw)]"
  apply (rule Conj)
  apply (rule dflipflop_seq_inv)
  apply (rule dflipflop_seq_inv2)
  done

lemma inv_next_time_null:
  assumes "inv tw" and "inv2 tw" and "\<not> disjnt {CLK} (event_of tw)" and "\<not> beval_world_raw2 tw (Bsig CLK)"
  shows "inv (next_time_world tw, snd tw)"
  unfolding inv_def
proof (rule, rule, rule, rule, rule)
  fix i j :: nat
  assume "j \<le> i"
  assume "is_posedge (snd (next_time_world tw, snd tw)) CLK j i"
  hence "is_posedge (snd tw) CLK j i"
    by auto
  hence "0 < j"
    using is_posedge_strictly_positive by metis
  have *: "\<forall>i\<ge>get_time tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw)"
    using assms(2) assms(4) unfolding inv2_def by (simp add: beval_world_raw2_Bsig)
  assume "i < fst (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
    by linarith
  moreover
  { assume "i < fst tw"
    hence "snd tw OUT (i + 1) = snd tw D j"
      using Dflipflop.inv_def \<open>is_posedge (snd (next_time_world tw, snd tw)) CLK j i\<close> \<open>j \<le> i\<close>
      assms(1) by auto }
  moreover
  { assume "fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
    hence "snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw)"
      using \<open>inv2 tw\<close> assms(3-4) unfolding inv2_def 
      by (simp add: beval_world_raw2_Bsig)
    have "fst tw = 0 \<or> 0 < fst tw"
      by auto
    moreover
    { assume "0 < fst tw"
      hence "fst tw - 1 < fst tw"
        by auto
      have "j \<noteq> fst tw"
      proof (rule ccontr)
        assume "\<not> j \<noteq> fst tw"
        hence "j = fst tw"
          by auto
        hence "snd tw CLK j"
          using `is_posedge (snd tw) CLK j i` by auto
        with \<open>\<not> beval_world_raw2 tw (Bsig CLK)\<close> show False
          by (simp add: \<open>j = get_time tw\<close> beval_world_raw2_Bsig)
      qed
      hence "j < fst tw \<or> j > fst tw"
        by auto
      moreover have "j > fst tw \<Longrightarrow> False"
      proof -
        assume "j > fst tw"
        have "j < next_time_world tw - 1"
          using \<open>j \<le> i\<close> `fst tw \<le> i \<and> i \<le> next_time_world tw - 1` 
          by (meson \<open>get_time tw < j\<close> \<open>i < next_time_world tw\<close> \<open>is_posedge (snd tw) CLK j i\<close>
          assms(4) beval_world_raw2_Bsig le_less_trans less_imp_le_nat
          unchanged_until_next_time_world)
        hence "snd tw CLK (j - 1) = snd tw CLK j"
          using `fst tw < j` unchanged_until_next_time_world 
          by (metis Suc_diff_1 cancel_comm_monoid_add_class.diff_cancel less_Suc_eq_le
          less_imp_diff_less less_imp_le_nat next_time_world_at_least)
        with \<open>is_posedge (snd tw) CLK j i\<close> show False
          by blast
      qed
      ultimately have "j \<le> fst tw - 1"
        by auto
      moreover have "is_posedge (snd tw) CLK j (fst tw - 1)"
        using \<open>get_time tw \<le> i \<and> i \<le> next_time_world tw - 1\<close> \<open>is_posedge (snd tw) CLK j i\<close>
        less_imp_diff_less  using calculation by auto
      ultimately have "snd tw OUT (fst tw)= snd tw D j"
        using \<open>inv tw\<close> `fst tw - 1 < fst tw` unfolding inv_def  by auto
      with \<open>snd tw OUT (i + 1) = snd tw OUT (fst tw)\<close> have "snd tw OUT (i + 1) = snd tw D j"
        by auto }
    moreover
    { assume "fst tw = 0"
      with `inv2 tw` have "snd tw OUT (i + 1) = snd tw OUT (fst tw)"
        unfolding inv2_def  using \<open>\<not> beval_world_raw2 tw (Bsig CLK)\<close> 
        \<open>snd tw OUT (i + 1) = snd tw OUT (get_time tw)\<close> by blast
      have "is_posedge (snd tw) CLK j (fst tw)"
        using \<open>get_time tw = 0\<close> \<open>is_posedge (snd tw) CLK j i\<close> 
        by (metis (no_types, lifting) \<open>0 < j\<close> \<open>i < next_time_world tw\<close> assms(4)
        beval_world_raw2_Bsig le_less_trans less_imp_le_nat unchanged_until_next_time_world)
      hence "snd tw CLK (fst tw - 1) \<noteq> snd tw CLK (fst tw)"
        by (metis (no_types, hide_lams) \<open>get_time tw = 0\<close> \<open>i < next_time_world tw\<close> \<open>j \<le> i\<close> assms(4)
        beval_world_raw2_Bsig dual_order.strict_trans le_less unchanged_until_next_time_world
        zero_le)
      with \<open>fst tw = 0\<close> have "False"
        by simp
      hence "snd tw OUT (i + 1) = snd tw D j"
        by auto }
    ultimately have "snd tw OUT (i + 1) = snd tw D j"
      by auto }
  ultimately have "snd tw OUT (i + 1) = snd tw D j"
    by auto
  thus "snd (next_time_world tw, snd tw) OUT (i + 1) = snd (next_time_world tw, snd tw) D j"
    by auto
qed

lemma inv2_next_time_null:
  assumes "inv tw" and "inv2 tw" and "\<not> disjnt {CLK} (event_of tw)" and "\<not> beval_world_raw2 tw (Bsig CLK)"
  shows "inv2 (next_time_world tw, snd tw)"
  unfolding inv2_def
proof (rule, rule, rule)
  fix i
  assume "   disjnt {CLK} (event_of (next_time_world tw, snd tw)) 
         \<or> \<not> snd (next_time_world tw, snd tw) CLK (get_time (next_time_world tw, snd tw))"
  assume " get_time (next_time_world tw, snd tw) \<le> i"
  hence "next_time_world tw \<le> i"
    by auto
  hence "fst tw \<le> i"
    using next_time_world_at_least dual_order.strict_trans less_Suc_eq_le by blast
  moreover have "\<forall>i \<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw)"
    using assms(2) assms(4) unfolding inv2_def  by (simp add: beval_world_raw2_Bsig)
  ultimately have "snd tw OUT (i + 1) = snd tw OUT (fst tw)"
    by auto
  also have "... = snd tw OUT (next_time_world tw - 1)"
    using unchanged_until_next_time_world
    by (smt diff_is_0_eq' diff_le_self diff_less dual_order.strict_iff_order le_0_eq le_Suc_eq
    linordered_semidom_class.add_diff_inverse next_time_world_at_least plus_1_eq_Suc zero_less_one)
  also have "... = snd tw OUT (next_time_world tw)"
    using assms(3) unfolding event_of_alt_def 
    by (smt Suc_eq_plus1 \<open>\<forall>i\<ge>get_time tw. snd tw OUT (i + 1) = snd tw OUT (get_time tw)\<close> \<open>snd tw OUT
    (get_time tw) = snd tw OUT (next_time_world tw - 1)\<close> diff_add_zero le_Suc_eq le_add1
    le_add_diff_inverse le_less next_time_world_at_least plus_1_eq_Suc)
  finally have "snd tw OUT (i + 1) = snd tw OUT (next_time_world tw)"
    by auto
  thus "snd (next_time_world tw, snd tw) OUT (i + 1) = 
        snd (next_time_world tw, snd tw) OUT (get_time (next_time_world tw, snd tw))"
    by auto
qed
  
lemma dflipflop_inv_else:
  "\<turnstile> [\<lambda>tw. ((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> \<not> beval_world_raw2 tw (Bsig CLK)] 
        Bnull
     [\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv2 (next_time_world tw, snd tw)", rotated 1])
    apply (rule Null2)
   apply simp
  using inv_next_time_null inv2_next_time_null by auto
    
lemma dflipflop_seq_both_inv:
  "\<turnstile> [\<lambda>tw. (inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)] \<comment> \<open>precondition\<close>
        Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull \<comment> \<open>program\<close>
     [\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv2 (next_time_world tw, snd tw)]" \<comment> \<open>postcondition\<close>
  apply (rule If2) 
  apply (rule dflipflop_inv_if)
  apply (rule dflipflop_inv_else)
  done

lemma inv_next_time_disjnt:
  assumes "inv tw" and "inv2 tw" and "disjnt {CLK} (event_of tw)"
  shows "inv (next_time_world tw, snd tw)"
  unfolding inv_def
proof (rule, rule, rule, rule, rule)
  fix i j :: nat
  assume "j \<le> i"
  assume "is_posedge (snd (next_time_world tw, snd tw)) CLK j i"
  hence "is_posedge (snd tw) CLK j i"
    by auto
  hence "0 < j"
    using is_posedge_strictly_positive by metis
  have *: "\<forall>i\<ge>get_time tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw)"
    using assms(2) assms(3) unfolding inv2_def by auto
  assume "i < fst (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
    by linarith
  moreover
  { assume "i < fst tw"
    hence "snd tw OUT (i + 1) = snd tw D j"
      using Dflipflop.inv_def \<open>is_posedge (snd (next_time_world tw, snd tw)) CLK j i\<close> \<open>j \<le> i\<close>
      assms(1) by auto }
  moreover
  { assume "fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
    have "fst tw = 0 \<or> 0 < fst tw"
      by auto
    moreover
    { assume "0 < fst tw"
      hence "fst tw - 1 < fst tw"
        by auto
      have "j \<noteq> fst tw"
      proof (rule ccontr)
        assume "\<not> j \<noteq> fst tw"
        hence "j = fst tw"
          by auto
        hence "snd tw CLK (fst tw - 1) \<noteq> snd tw CLK (fst tw)"
          using \<open>is_posedge (snd tw) CLK j i\<close> by blast
        hence "\<not> disjnt {CLK} (event_of tw)"
          unfolding event_of_alt_def using \<open>0 < fst tw\<close>  by auto
        with \<open>disjnt {CLK} (event_of tw)\<close> show False
          by auto
      qed
      hence "j < fst tw \<or> j > fst tw"
        by auto
      moreover have "j > fst tw \<Longrightarrow> False"
      proof -
        assume "j > fst tw"
        have "j < next_time_world tw - 1"
          using \<open>j \<le> i\<close> `fst tw \<le> i \<and> i \<le> next_time_world tw - 1` 
          by (metis (no_types, lifting) Suc_diff_1 \<open>0 < j\<close> \<open>get_time tw < j\<close> \<open>is_posedge (snd tw)
          CLK j i\<close> diff_le_self less_Suc_eq_le order.strict_iff_order order_trans
          unchanged_until_next_time_world)
        hence "snd tw CLK (j - 1) = snd tw CLK j"
          using `fst tw < j` unchanged_until_next_time_world 
          by (metis Suc_diff_1 cancel_comm_monoid_add_class.diff_cancel less_Suc_eq_le
          less_imp_diff_less less_imp_le_nat next_time_world_at_least)
        with \<open>is_posedge (snd tw) CLK j i\<close> show False
          by blast
      qed
      ultimately have "j \<le> fst tw - 1"
        by auto
      moreover have "is_posedge (snd tw) CLK j (fst tw - 1)"
        using \<open>get_time tw \<le> i \<and> i \<le> next_time_world tw - 1\<close> \<open>is_posedge (snd tw) CLK j i\<close>
        less_imp_diff_less  using calculation by auto
      ultimately have "snd tw OUT (fst tw)= snd tw D j"
        using \<open>inv tw\<close> `fst tw - 1 < fst tw` unfolding inv_def  by auto
      with * have "snd tw OUT (i + 1) = snd tw D j"
        using \<open>get_time tw \<le> i \<and> i \<le> next_time_world tw - 1\<close> by blast }
    moreover
    { assume "fst tw = 0"
      have "snd tw OUT (i + 1) = snd tw OUT (fst tw)"
        using *  by (simp add: \<open>get_time tw = 0\<close>)
      have "is_posedge (snd tw) CLK j (fst tw)"
        using \<open>get_time tw = 0\<close> \<open>is_posedge (snd tw) CLK j i\<close> 
        by (metis \<open>i < next_time_world tw\<close> diff_le_self le_less_trans
        unchanged_until_next_time_world zero_le)
      hence "snd tw CLK (fst tw - 1) \<noteq> snd tw CLK (fst tw)"
        by (metis (no_types, hide_lams) \<open>get_time tw = 0\<close> \<open>get_time tw \<le> i \<and> i \<le> next_time_world tw
        - 1\<close> \<open>i < next_time_world tw\<close> \<open>is_posedge (snd (next_time_world tw, snd tw)) CLK j i\<close>
        \<open>is_posedge (snd tw) CLK j i\<close> \<open>j \<le> i\<close> cancel_comm_monoid_add_class.diff_cancel diff_le_self
        dual_order.antisym le_less less_imp_diff_less less_imp_le_nat order.trans
        unchanged_until_next_time_world zero_le)
      with \<open>fst tw = 0\<close> have "False"
        by simp
      hence "snd tw OUT (i + 1) = snd tw D j"
        by auto }
    ultimately have "snd tw OUT (i + 1) = snd tw D j"
      by auto }
  ultimately have "snd tw OUT (i + 1) = snd tw D j"
    by auto
  thus "snd (next_time_world tw, snd tw) OUT (i + 1) = snd (next_time_world tw, snd tw) D j"
    by auto
qed

lemma inv2_next_time_disjnt:
  assumes "inv tw" and "inv2 tw" and "disjnt {CLK} (event_of tw)"
  shows "inv2 (next_time_world tw, snd tw)"
  unfolding inv2_def
proof (rule, rule, rule)
  fix i
  assume "   disjnt {CLK} (event_of (next_time_world tw, snd tw)) 
         \<or> \<not> snd (next_time_world tw, snd tw) CLK (get_time (next_time_world tw, snd tw))"
  assume " get_time (next_time_world tw, snd tw) \<le> i"
  hence "next_time_world tw \<le> i"
    by auto
  hence "fst tw \<le> i"
    using next_time_world_at_least dual_order.strict_trans less_Suc_eq_le by blast
  moreover have "\<forall>i \<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw)"
    using assms(2-3) unfolding inv2_def  by (simp add: beval_world_raw2_Bsig)
  ultimately have "snd tw OUT (i + 1) = snd tw OUT (fst tw)"
    by auto
  also have "... = snd tw OUT (next_time_world tw - 1)"
    using unchanged_until_next_time_world
    by (smt diff_is_0_eq' diff_le_self diff_less dual_order.strict_iff_order le_0_eq le_Suc_eq
    linordered_semidom_class.add_diff_inverse next_time_world_at_least plus_1_eq_Suc zero_less_one)
  also have "... = snd tw OUT (next_time_world tw)"
    using assms(3) unfolding event_of_alt_def 
    by (smt Suc_eq_plus1 \<open>\<forall>i\<ge>get_time tw. snd tw OUT (i + 1) = snd tw OUT (get_time tw)\<close> \<open>snd tw OUT
    (get_time tw) = snd tw OUT (next_time_world tw - 1)\<close> diff_add_zero le_Suc_eq le_add1
    le_add_diff_inverse le_less next_time_world_at_least plus_1_eq_Suc)
  finally have "snd tw OUT (i + 1) = snd tw OUT (next_time_world tw)"
    by auto
  thus "snd (next_time_world tw, snd tw) OUT (i + 1) = 
        snd (next_time_world tw, snd tw) OUT (get_time (next_time_world tw, snd tw))"
    by auto
qed

lemma dflipflop_conc_both_inv:
  "\<turnstile> \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>  \<comment> \<open>precondition\<close>
        process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull \<comment> \<open>program\<close>
     \<lbrace>\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv2 (next_time_world tw, snd tw)\<rbrace>" \<comment> \<open>postcondition\<close>
  apply (rule Single)
  apply (rule dflipflop_seq_both_inv)
  using inv_next_time_disjnt inv2_next_time_disjnt by auto

theorem simulation_comb:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> dflipflop \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>"
  unfolding dflipflop_def
  apply (rule While)
  apply (rule dflipflop_conc_both_inv)
  done

corollary simulation_inv:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> dflipflop \<lbrace>\<lambda>tw. inv tw\<rbrace>"
  using simulation_comb  Conseq_sim by blast

subsection \<open>Initialisation satisfies @{term "inv"} and @{term "inv2"}\<close>

lemma [simp]:
  "inv (0, w)"
  unfolding inv_def by auto

lemma inv_time_seq_next_time0:
  assumes "fst tw = 0"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig D)]"
  shows "inv (next_time_world tw', snd tw')"
  unfolding inv_def
proof (rule, rule, rule, rule, rule)
  fix i j
  assume "i < get_time (next_time_world tw', snd tw')"
  hence "i < next_time_world tw'"
    by auto
  assume "j \<le> i"
  hence "j < next_time_world tw'"
    using `i < next_time_world tw'` by auto
  assume "is_posedge (snd (next_time_world tw', snd tw')) CLK j i"
  hence "is_posedge (snd tw') CLK j i"
    by auto
  hence "snd tw' CLK (j - 1) \<noteq> snd tw' CLK j"
    by blast
  moreover have "(\<forall>s. snd tw' s j = snd tw' s (fst tw'))"
    using unchanged_until_next_time_world `fst tw = 0` `j < next_time_world tw'` 
    by (metis fst_conv less_eq_nat.simps(1) tw'_def worldline_upd2_def)
  ultimately have "False"
    by (metis \<open>j < next_time_world tw'\<close> assms(1) diff_le_self fst_conv le_less_trans
    less_eq_nat.simps(1) tw'_def unchanged_until_next_time_world worldline_upd2_def)
  thus "snd (next_time_world tw', snd tw') OUT (i + 1) = snd (next_time_world tw', snd tw') D j"
    by auto
qed
  
lemma init0:
  "\<turnstile> [\<lambda>tw. get_time tw = 0 \<and> beval_world_raw2 tw (Bsig CLK)] 
        Bassign_trans OUT (Bsig D) 1 
     [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_time_seq_next_time0 by auto

lemma inv_time_seq_next_time0':
  assumes "fst tw = 0"
  shows   "inv (next_time_world tw, snd tw)"
  unfolding inv_def
proof (rule, rule, rule, rule, rule)
  fix i j
  assume "i < fst (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  assume "j \<le> i"
  hence "j < next_time_world tw"
    using `i < next_time_world tw` by auto
  assume " is_posedge (snd (next_time_world tw, snd tw)) CLK j i"
  hence "is_posedge (snd tw) CLK j i"
    by auto
  hence "snd tw CLK (j - 1) \<noteq> snd tw CLK j"
    by blast
  moreover have "(\<forall>s. snd tw s j = snd tw s (fst tw))"
    using unchanged_until_next_time_world `fst tw = 0` `j < next_time_world tw` 
    by (metis less_eq_nat.simps(1))
  ultimately have "False"
    by (metis \<open>j < next_time_world tw\<close> assms(1) diff_le_self le_less_trans
    less_eq_nat.simps(1) unchanged_until_next_time_world)
  thus "snd (next_time_world tw, snd tw) OUT (i + 1) = snd (next_time_world tw, snd tw) D j"
    by auto
qed

lemma init1:
  "\<turnstile> [\<lambda>tw. get_time tw = 0 \<and> \<not> beval_world_raw2 tw (Bsig CLK)] 
        Bnull 
     [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv (next_time_world tw, snd tw)", rotated 1])
    apply (rule Null2)
   apply simp
  using inv_time_seq_next_time0' by auto

lemma init2:
  " \<turnstile> [\<lambda>tw. get_time tw = 0] 
        Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull 
      [\<lambda>tw. Dflipflop.inv (next_time_world tw, snd tw)]"
  apply (rule If2)
   apply (rule init0)
  apply (rule init1)
  done

lemma init3:
  "init_sim_hoare (\<lambda>tw. get_time tw = 0) dflipflop inv"
  unfolding dflipflop_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule init2)
  done

lemma inv2_holds_initially_assigned:
  assumes "fst tw = 0"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig D)]"
  shows "inv2 (next_time_world tw', snd tw')"
  unfolding inv2_def
proof (rule, rule, rule)
  fix i
  assume *: "disjnt {CLK} (event_of (next_time_world tw', snd tw')) 
         \<or> \<not> snd (next_time_world tw', snd tw') CLK (get_time (next_time_world tw', snd tw'))"
  assume "get_time (next_time_world tw', snd tw') \<le> i"
  hence "next_time_world tw' \<le> i"
    by auto
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least by metis
  hence "0 < next_time_world tw'"
    by linarith
  have "snd tw' OUT (i + 1) = snd tw D (fst tw)"
    unfolding tw'_def 
    by (simp add: assms(1) beval_world_raw2_Bsig worldline_upd2_def worldline_upd_def)
  also have "... = snd tw' OUT (fst tw + 1)"
    unfolding tw'_def  by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
  also have "... = snd tw' OUT (fst tw' + 1)"
    by (simp add: tw'_def worldline_upd2_def)
  finally have **: "snd tw' OUT (i + 1) = snd tw' OUT (fst tw' + 1)"
    by auto
  have "disjnt {CLK} (event_of (next_time_world tw', snd tw'))  \<or> \<not> snd tw' CLK (next_time_world tw')"
    using * by auto
  hence "snd tw' OUT (fst tw' + 1) = snd tw' OUT (next_time_world tw')"
    by (metis One_nat_def Suc_eq_plus1 \<open>0 < next_time_world tw'\<close> assms(1) fst_conv less_one
    nat_neq_iff snd_conv tw'_def worldline_upd2_def worldline_upd_def)
  hence "snd tw' OUT (i + 1) = snd tw' OUT (next_time_world tw')"
    using ** by auto
  thus "snd (next_time_world tw', snd tw') OUT (i + 1) = 
        snd (next_time_world tw', snd tw') OUT (get_time (next_time_world tw', snd tw'))"
    by auto
qed
  
lemma init4:
  " \<turnstile> [\<lambda>tw. (get_time tw = 0 \<and> (\<forall>i. snd tw OUT i = snd tw OUT (get_time tw))) \<and> beval_world_raw2 tw (Bsig CLK)] 
        Bassign_trans OUT (Bsig D) 1 
      [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_holds_initially_assigned by auto

lemma inv2_holds_initially:
  assumes "fst tw = 0" and "(\<forall>i. snd tw OUT i = snd tw OUT (get_time tw))" and "\<not> beval_world_raw2 tw (Bsig CLK)"
  shows "inv2 (next_time_world tw, snd tw)"
proof -
  have "inv tw"
    using assms(1) unfolding inv_def by auto
  moreover have "inv2 tw"
    using assms(2)  using inv2_def by blast
  ultimately show ?thesis
    using inv2_next_time_disjnt inv2_next_time_null assms(3) 
    by blast
qed

lemma init5:
  " \<turnstile> [\<lambda>tw. (get_time tw = 0 \<and> (\<forall>i. snd tw OUT i = snd tw OUT (get_time tw))) \<and> \<not> beval_world_raw2 tw (Bsig CLK)] 
        Bnull 
      [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv2 (next_time_world tw, snd tw)", rotated 1])
    apply (rule Null2)
   apply simp
  using inv2_holds_initially by auto

lemma init6:
  "\<turnstile> [\<lambda>tw. get_time tw = 0 \<and> (\<forall>i. snd tw OUT i = snd tw OUT (get_time tw))] 
        Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull 
     [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule If2)
   apply (rule init4)
  apply (rule init5)
  done
  
lemma init7:
  "init_sim_hoare (\<lambda>tw. get_time tw = 0 \<and> (\<forall>i. snd tw OUT i = snd tw OUT (get_time tw))) dflipflop inv2"
  unfolding dflipflop_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule init6)
  done

theorem init8:
  "init_sim_hoare 
    (\<lambda>tw. fst tw = 0 \<comment> \<open>initially the time is zero\<close> 
        \<and> (\<forall>i. snd tw OUT i = snd tw OUT (fst tw))) \<comment> \<open>initially no signal shall be posted in the internal signal\<close>
      dflipflop 
    (\<lambda>tw. inv tw \<and> inv2 tw)"
  apply (rule ConjI_sim)
   apply (rule ConseqI_sim[where Q="inv" and P="\<lambda>tw. fst tw = 0"])
     apply simp
    apply (rule init3)
   apply simp
  apply (rule init7)
  done

lemma 
  assumes "sim_fin w (i + 1) dflipflop tw'"
  assumes "\<forall>i. w OUT i = w OUT 0"
  shows "(\<forall>j \<le> i. is_posedge (snd tw') CLK j i \<longrightarrow>  snd tw' OUT (i + 1) \<longleftrightarrow> snd tw' D j)"
proof -
  obtain tw where "init_sim (0, w) dflipflop = tw" and  "tw, i + 1, dflipflop \<Rightarrow>\<^sub>S tw'" 
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf dflipflop"
    unfolding conc_stmt_wf_def dflipflop_def by auto
  moreover have "nonneg_delay_conc dflipflop"
    unfolding dflipflop_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> (\<forall>i. snd tw OUT i = snd tw OUT (fst tw))) dflipflop (\<lambda>tw. inv tw \<and> inv2 tw)"
    using init_sim_hoare_soundness[OF init8] by auto
  hence "inv tw \<and> inv2 tw"
    using \<open>init_sim (0, w) dflipflop = tw\<close> fst_conv assms(2) unfolding init_sim_valid_def 
    by (metis snd_conv)    
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> dflipflop \<lbrace>inv\<rbrace>"
    using conc_sim_soundness[OF simulation_inv] \<open>conc_stmt_wf dflipflop\<close> \<open>nonneg_delay_conc dflipflop\<close>
    by auto                               
  ultimately have "inv tw'"
    using \<open>tw, i + 1, dflipflop \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i<get_time tw'. \<forall>j\<le>i. is_posedge (snd tw') CLK j i \<longrightarrow> snd tw' OUT (i + 1) = snd tw' D j"
    unfolding inv_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed


  



end 