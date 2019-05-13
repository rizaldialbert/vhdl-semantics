(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Hoare
  imports VHDL_Hoare_Complete NAND_Femto
begin

text \<open>Invariant for NAND: at all times @{term "i"} less than @{term "fst tw :: nat"}, the signal 
@{term "C :: sig"} at @{term "i + 1"} should be the NAND value of @{term "A :: sig"} and 
@{term "B :: sig"} at time @{term "i"}.\<close>

definition nand_inv :: "sig assn2" where
  "nand_inv \<equiv> (\<lambda>tw. \<forall>i < fst tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. C \<in> event_of tw \<longrightarrow> (\<forall>i> fst tw. snd tw C i = snd tw C (fst tw)))"

definition nand_inv3 :: "sig assn2" where
  "nand_inv3 \<equiv> (\<lambda>tw. event_of tw = {} \<longrightarrow> (snd tw C (fst tw + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw)))
                                       \<and>  (\<forall>i> fst tw + 1. snd tw C i = snd tw C (fst tw + 1)))"

lemma nand_seq_hoare:
  "\<turnstile> [nand_inv] (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) [nand_inv]"
  by (rule Conseq2[where Q="nand_inv", rotated 1], rule Assign2)
     (auto simp add :worldline_upd2_def worldline_upd_def nand_inv_def)

lemma nand_inv_next_time:
  assumes "nand_inv tw"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))]"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have "\<forall>i < next_time_world tw'. snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw'"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
      using \<open>fst tw < next_time_world tw'\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using assms(1) unfolding nand_inv_def by auto
      hence "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>) }
    moreover
    { assume " fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "snd tw' C (i + 1) \<longleftrightarrow> snd tw' C (fst tw + 1)"
        using unchanged_until_next_time_world 
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      moreover have "snd tw' A i \<longleftrightarrow> snd tw' A (fst tw)" and "snd tw' B i \<longleftrightarrow> snd tw' B (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (simp add: unchanged_until_next_time_world \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "snd tw' C (fst tw + 1) \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
        unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def beval_world_raw_def
        state_of_world_def beh_of_world_raw_def by auto
      ultimately have "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "snd tw' C (i + 1) = snd tw' C (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by auto
      also have "... = snd tw' C (fst tw + 1)"
        using \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def 
        worldline_upd_def by auto
      finally have "snd tw' C (i + 1) \<longleftrightarrow> snd tw' C (fst tw + 1)"
        by auto
      also have "... \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
        unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def beval_world_raw_def
        state_of_world_def beh_of_world_raw_def by auto
      also have "... \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        by (metis \<open>get_time tw = get_time tw'\<close> 
                  \<open>i < get_time tw \<Longrightarrow> snd tw' C (i + 1) = (\<not> (snd tw' A i \<and> snd tw' B i))\<close> 
                  \<open>i < next_time_world tw'\<close> calculation not_le unchanged_until_next_time_world)
      finally have "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        by auto }
    ultimately show "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
      by auto 
  qed
  thus ?thesis
    unfolding nand_inv_def by auto 
qed

lemma nand_seq_hoare_next_time:
  "\<turnstile> [nand_inv] (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using nand_inv_next_time by auto

lemma nand_inv2_next_time:
  fixes tw
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))]"
  shows   "nand_inv2 (next_time_world tw', snd tw')"
  unfolding nand_inv2_def
proof (rule impI)
  assume "C \<in> event_of (next_time_world tw', snd tw')"
  have "0 < next_time_world tw"
    using next_time_world_at_least gr_implies_not_zero by blast
  hence "event_of (next_time_world tw', snd tw') = {s. snd tw' s (next_time_world tw') \<noteq> snd tw' s (next_time_world tw' - 1)}"
    unfolding event_of_alt_def by (metis fst_conv next_time_world_at_least not_less0 snd_conv)
  hence "snd tw' C (next_time_world tw') \<noteq> snd tw' C (next_time_world tw' - 1)"
    using \<open>C \<in> event_of (next_time_world tw', snd tw')\<close> by auto
  have "next_time_world tw' = fst tw + 1"
  proof (rule ccontr)
    assume "next_time_world tw' \<noteq> fst tw + 1"
    hence "next_time_world tw' < fst tw + 1 \<or> next_time_world tw' > fst tw + 1" 
      by auto
    moreover
    { assume "next_time_world tw' < fst tw + 1"
      hence "False"
        using next_time_world_at_least 
        by (metis assms(1) discrete fstI leD worldline_upd2_def) }
    moreover
    { assume "fst tw + 1 < next_time_world tw'"
      hence False
        by (smt One_nat_def Suc_diff_1 Suc_eq_plus1 \<open>snd tw' C (next_time_world tw') \<noteq> snd tw' C
        (next_time_world tw' - 1)\<close> assms(1) calculation(2) discrete dual_order.strict_trans leD
        le_add2 snd_conv worldline_upd2_def worldline_upd_def) }
    ultimately show False 
      by auto
  qed
  have "nand_inv2 (fst tw + 1, snd tw')"
    using assms(1) unfolding tw'_def nand_inv2_def
    by (simp add: worldline_upd2_def worldline_upd_def)
  thus "\<forall>i>get_time (next_time_world tw', snd tw'). snd (next_time_world tw', snd tw') C i = 
                      snd (next_time_world tw', snd tw') C (get_time (next_time_world tw', snd tw'))"
    unfolding nand_inv2_def 
    using \<open>C \<in> event_of (next_time_world tw', snd tw')\<close> \<open>next_time_world tw' = get_time tw + 1\<close> 
    by auto
qed

lemma nand_seq_hoare_next_time2:
  "\<turnstile> [\<lambda>tw. True] (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using nand_inv2_next_time by auto

lemma nand_inv3_next_time:
  fixes tw
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))]"
  shows   "nand_inv3 (next_time_world tw', snd tw')"
  unfolding nand_inv3_def
proof (rule impI)
  assume "event_of (next_time_world tw', snd tw') = {}"
  have "0 < next_time_world tw"
    using next_time_world_at_least gr_implies_not_zero by blast
  hence "event_of (next_time_world tw', snd tw') = {s. snd tw' s (next_time_world tw') \<noteq> snd tw' s (next_time_world tw' - 1)}"
    unfolding event_of_alt_def by (metis fst_conv next_time_world_at_least not_less0 snd_conv)
  hence "\<And>s. snd tw' s (next_time_world tw') = snd tw' s (next_time_world tw' - 1)"
    using \<open>event_of (next_time_world tw', snd tw') = {}\<close> by auto
  hence *: "\<And>s. snd tw' s (next_time_world tw') = snd tw' s (fst tw')"
    using unchanged_until_next_time_world 
    by (smt diff_less discrete le_add2 le_less_trans less_diff_conv less_one next_time_world_at_least not_less)
  have "next_time_world tw' = fst tw' + 1"
  proof -
    have "\<exists>n\<ge>get_time tw'. (\<lambda>s. snd tw' s (get_time tw')) \<noteq> (\<lambda>s. snd tw' s n) \<or> 
          \<not> (\<exists>n\<ge>get_time tw'. (\<lambda>s. snd tw' s (get_time tw')) \<noteq> (\<lambda>s. snd tw' s n))"
      by auto
    moreover
    { assume "\<not> (\<exists>n\<ge>get_time tw'. (\<lambda>s. snd tw' s (get_time tw')) \<noteq> (\<lambda>s. snd tw' s n))"
      hence ?thesis
        unfolding next_time_world_alt_def Let_def by auto }
    moreover
    { assume **: "\<exists>n\<ge>get_time tw'. (\<lambda>s. snd tw' s (get_time tw')) \<noteq> (\<lambda>s. snd tw' s n)"
      hence "next_time_world tw' = (LEAST n. get_time tw' \<le> n \<and> (\<lambda>s. snd tw' s (get_time tw')) \<noteq> (\<lambda>s. snd tw' s n))"
        unfolding next_time_world_alt_def Let_def by auto
      hence "(\<lambda>s. snd tw' s (fst tw')) \<noteq> (\<lambda>s. snd tw' s (next_time_world tw'))"
        using LeastI_ex[OF **] by auto
      hence "\<exists>s. snd tw' s (fst tw') \<noteq> snd tw' s (next_time_world tw')"
        by auto
      with * have False by simp
      hence ?thesis
        by auto }
    ultimately show ?thesis
      by auto
  qed
  also have "... = fst tw + 1"
    unfolding tw'_def  by (simp add: worldline_upd2_def)
  finally have "next_time_world tw' = fst tw + 1"
    by auto
  have "snd tw' C (fst tw + 2) \<longleftrightarrow> \<not> (snd tw' A (fst tw + 1) \<and> snd tw' B (fst tw + 1))"
  proof -
    have "snd tw' C (fst tw + 2) \<longleftrightarrow> snd tw' C (fst tw + 1)"
      unfolding tw'_def 
      by (metis (no_types, hide_lams) BitM_plus_one Suc_eq_plus1 add_2_eq_Suc'
      dual_order.strict_trans exp2_def lessI less_not_refl3 nat_less_le snd_conv worldline_upd2_def
      worldline_upd_def)
    have "snd tw' A (fst tw + 1) = snd tw' A (fst tw')" and  "snd tw' B (fst tw + 1) = snd tw' B (fst tw')"
      using * unfolding \<open>next_time_world tw' = fst tw + 1\<close> by auto
    moreover have "fst tw' = fst tw"
      unfolding tw'_def by (simp add: worldline_upd2_def)
    ultimately have "snd tw' A (fst tw + 1) = snd tw' A (fst tw)" and "snd tw' B (fst tw + 1) = snd tw' B (fst tw)"
      by auto
    have "snd tw' C (fst tw + 1) \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
      unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def beval_world_raw_def
      state_of_world_def beh_of_world_raw_def 
      by auto
    thus ?thesis
      using \<open>snd tw' A (get_time tw + 1) = snd tw' A (get_time tw)\<close> \<open>snd tw' B (get_time tw + 1) =
      snd tw' B (get_time tw)\<close> \<open>snd tw' C (get_time tw + 2) = snd tw' C (get_time tw + 1)\<close> by blast
  qed
  moreover have "\<forall>i> fst tw + 2. snd tw' C i = snd tw' C (fst tw + 2)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately show "snd (next_time_world tw', snd tw') C (get_time (next_time_world tw', snd tw') + 1) =
    (\<not> (snd (next_time_world tw', snd tw') A (get_time (next_time_world tw', snd tw')) \<and>
         snd (next_time_world tw', snd tw') B (get_time (next_time_world tw', snd tw')))) \<and>
    (\<forall>i>get_time (next_time_world tw', snd tw') + 1.
        snd (next_time_world tw', snd tw') C i = snd (next_time_world tw', snd tw') C (get_time (next_time_world tw', snd tw') + 1))"
    by (simp add: \<open>next_time_world tw' = get_time tw + 1\<close>)
qed

lemma nand_seq_hoare_next_time3:
  "\<turnstile> [\<lambda>tw. True] (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv3 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv3 (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using nand_inv3_next_time by auto

lemma disjnt_AB_eq:
  "disjnt {A, B} s \<longleftrightarrow> (s = {} \<or> s = {C})"
  by (rule, metis Diff_UNIV Diff_insert0 Diff_single_insert UNIV_sig disjnt_insert1 empty_subsetI
  subset_singleton_iff) auto

lemma nand_inv_next_time_disjnt1:
  assumes "nand_inv tw" and "nand_inv2 tw"
  assumes "event_of tw = {C}"
  shows   "nand_inv (next_time_world tw, snd tw)"
proof (cases "fst tw = 0")
  case False
  have "fst tw < next_time_world tw"
    using next_time_world_at_least  using nat_less_le by blast
  have *: "(\<forall>i> fst tw. snd tw C i = snd tw C (fst tw))"
    using assms(2-3) unfolding nand_inv2_def by auto
  have "\<forall>i < next_time_world tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
      using \<open>fst tw < next_time_world tw\<close> by linarith  
    moreover
    { assume "i < fst tw"
      hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using assms(1) unfolding nand_inv_def by auto }
    moreover
    { assume " fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
      hence "snd tw C (i + 1) \<longleftrightarrow> snd tw C (fst tw + 1)"
        using unchanged_until_next_time_world "*" by force
      also have "... \<longleftrightarrow> snd tw C (fst tw)"
        using * by auto
      also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw - 1) \<and> snd tw B (fst tw - 1))"
        using assms(1) False unfolding nand_inv_def 
        by (metis Suc_eq_plus1 add.commute add_diff_inverse_nat lessI less_one)
      finally have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw - 1) \<and> snd tw B (fst tw - 1))"
        by auto
      moreover have "snd tw A i \<longleftrightarrow> snd tw A (fst tw)" and "snd tw B i \<longleftrightarrow> snd tw B (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i \<le> next_time_world tw - 1\<close>
        by (simp add: unchanged_until_next_time_world \<open>i < next_time_world tw\<close>)+
      moreover have "(snd tw A (fst tw) \<longleftrightarrow> snd tw A (fst tw - 1)) \<and> (snd tw B (fst tw) \<longleftrightarrow> snd tw B (fst tw - 1))"
      proof -
        have "event_of tw = {s. snd tw s (fst tw) \<noteq> snd tw s (fst tw - 1)}"
          using False unfolding event_of_alt_def by auto
        with \<open>event_of tw = {C}\<close> have "snd tw A (fst tw) = snd tw A (fst tw - 1)" and 
                                      "snd tw B (fst tw) = snd tw B (fst tw - 1)"
          by auto
        thus ?thesis
          by auto
      qed
      ultimately have "snd tw A i \<longleftrightarrow> snd tw A (fst tw - 1)" and "snd tw B i \<longleftrightarrow> snd tw B (fst tw - 1)"
        by auto
      hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using \<open>snd tw C (i + 1) = (\<not> (snd tw A (get_time tw - 1) \<and> snd tw B (get_time tw - 1)))\<close> by
        blast }
    ultimately show "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      by blast
  qed
  thus ?thesis
    by (simp add: nand_inv_def)
next
  case True
  hence *: "(\<forall>i. snd tw C i = snd tw C (fst tw))"
    using assms(2-3) unfolding nand_inv2_def by (metis neq0_conv singletonI)  
  have "0 < next_time_world tw"
    using True next_time_world_at_least nat_less_le  by metis
  have "\<forall>i < next_time_world tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw"
    hence "snd tw C (i + 1) \<longleftrightarrow> snd tw C 1"
      using unchanged_until_next_time_world "*" by blast
    also have "... \<longleftrightarrow> snd tw C 0"
      using * by auto
    also have "... \<longleftrightarrow> \<not> (snd tw A 0 \<and> snd tw B 0)"
    proof -
      have "event_of tw = {s. snd tw s 0 \<noteq> False}"
        unfolding event_of_alt_def True by auto
      with \<open>event_of tw ={C}\<close> have "snd tw C 0 = True" and "snd tw A 0 = False" and "snd tw B 0 = False"
        by auto
      thus ?thesis
        by auto
    qed
    finally have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A 0 \<and> snd tw B 0)"
      by auto
    moreover have "snd tw A i \<longleftrightarrow> snd tw A 0" and "snd tw B i \<longleftrightarrow> snd tw B 0"
      using unchanged_until_next_time_world 
      by (simp add: unchanged_until_next_time_world True \<open>i < next_time_world tw\<close>)+
    hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      using calculation by blast
    ultimately show "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      by blast
  qed
  thus ?thesis
    by (simp add: nand_inv_def)
qed

lemma nand_inv_next_time_disjnt2:
  assumes "nand_inv tw" and "nand_inv3 tw"
  assumes "event_of tw = {}"
  shows   "nand_inv (next_time_world tw, snd tw)"
proof (cases "fst tw = 0")
  case False
  have "fst tw < next_time_world tw"
    using next_time_world_at_least  using nat_less_le by blast
  have **: "snd tw C (fst tw + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
    using assms(2-3) unfolding nand_inv3_def by auto
  have *: "\<forall>i> fst tw + 1. snd tw C i = snd tw C (fst tw + 1)"
    using assms(2-3) unfolding nand_inv3_def by auto
  have "\<forall>i < next_time_world tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
      using \<open>fst tw < next_time_world tw\<close> by linarith  
    moreover
    { assume "i < fst tw"
      hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using assms(1) unfolding nand_inv_def by auto }
    moreover
    { assume " fst tw \<le> i \<and> i \<le> next_time_world tw - 1"
      hence "snd tw C (i + 1) \<longleftrightarrow> snd tw C (fst tw + 1)"
        using unchanged_until_next_time_world "*"  using nat_less_le by auto
      moreover have "snd tw A i \<longleftrightarrow> snd tw A (fst tw)" and "snd tw B i \<longleftrightarrow> snd tw B (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i \<le> next_time_world tw - 1\<close>
        by (simp add: unchanged_until_next_time_world \<open>i < next_time_world tw\<close>)+
      ultimately have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using ** by auto }
    ultimately show "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      by blast
  qed
  thus ?thesis
    by (simp add: nand_inv_def)  
next
  case True
  have **: "snd tw C (fst tw + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
    using assms(2-3) True unfolding nand_inv3_def by auto
  have "\<forall>i> fst tw + 1. snd tw C i = snd tw C (fst tw + 1)"
    using assms(2-3) unfolding nand_inv3_def by auto
  hence *: "\<forall>i>1. snd tw C i = snd tw C 1"
    using True by auto
  have "0 < next_time_world tw"
    using True next_time_world_at_least nat_less_le  by metis
  have "\<forall>i < next_time_world tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw"
    hence "snd tw C (i + 1) \<longleftrightarrow> snd tw C 1"
      using "*"   by (metis One_nat_def Suc_eq_plus1 less_add_same_cancel2 neq0_conv)
    also have "... \<longleftrightarrow> \<not> (snd tw A 0 \<and> snd tw B 0)"
      using "**" True by auto
    finally have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A 0 \<and> snd tw B 0)"
      by auto
    moreover have "snd tw A i \<longleftrightarrow> snd tw A 0" and "snd tw B i \<longleftrightarrow> snd tw B 0"
      using unchanged_until_next_time_world 
      by (simp add: unchanged_until_next_time_world True \<open>i < next_time_world tw\<close>)+
    hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      using calculation by blast
    ultimately show "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      by blast
  qed
  thus ?thesis
    by (simp add: nand_inv_def)
qed

lemma nand_inv_123_next_time:
  "\<forall>tw. (nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw) \<and> disjnt {A, B} (event_of tw) \<longrightarrow>
         nand_inv (next_time_world tw, snd tw) \<and> nand_inv2 (next_time_world tw, snd tw) \<and> nand_inv3 (next_time_world tw, snd tw)"
proof (rule allI, rule impI)
  fix tw
  assume "(nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw) \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "nand_inv3 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence "event_of tw = {} \<or> event_of tw = {C}"
    unfolding disjnt_AB_eq by auto
  moreover
  { assume "event_of tw = {C}"
    with \<open>nand_inv tw\<close> and \<open>nand_inv2 tw\<close> have "nand_inv (next_time_world tw, snd tw)"
      using nand_inv_next_time_disjnt1 by auto
    moreover have "nand_inv2 (next_time_world tw, snd tw)"
      using \<open>nand_inv2 tw\<close> next_time_world_at_least \<open>event_of tw ={C}\<close>
      unfolding nand_inv2_def  by (metis dual_order.strict_trans fst_eqD singletonI snd_eqD)
    moreover have "nand_inv3 (next_time_world tw, snd tw)"
    proof -
      { assume " event_of (next_time_world tw, snd tw) = {}"
        hence "snd tw A (next_time_world tw) = snd tw A (next_time_world tw - 1)" and 
              "snd tw B (next_time_world tw) = snd tw B (next_time_world tw - 1)"
          unfolding event_of_alt_def
          by (smt \<open>event_of (next_time_world tw, snd tw) = {}\<close> empty_Collect_eq event_of_alt_def
                  fst_conv next_time_world_at_least not_less0 snd_conv)+
        moreover have "snd tw C (next_time_world tw + 1) = snd tw C (next_time_world tw)"
          by (metis (mono_tags, hide_lams) \<open>event_of tw = {C}\<close> \<open>nand_inv2 tw\<close> discrete insertI1
              nand_inv2_def nat_less_le next_time_world_at_least not_less)
        moreover have "snd tw C (next_time_world tw) \<longleftrightarrow> 
                    \<not> (snd tw A (next_time_world tw - 1) \<and> snd tw B (next_time_world tw - 1))"
          using \<open>nand_inv (next_time_world tw, snd tw)\<close> unfolding nand_inv_def
          by (metis Suc_diff_1 diff_is_0_eq' diff_less fst_conv le_add_diff_inverse2 nat_less_le
              next_time_world_at_least not_less not_less0 snd_conv zero_less_one)
        ultimately have "snd tw C (next_time_world tw + 1) \<longleftrightarrow> 
                        \<not> (snd tw A (next_time_world tw) \<and> snd tw B (next_time_world tw))" (is "?po1")
          by blast
        have "\<forall>i>next_time_world tw + 1. snd tw C i = snd tw C (next_time_world tw + 1)" (is "?po2")
          using \<open>nand_inv2 (next_time_world tw, snd tw)\<close> \<open>event_of tw ={C}\<close> unfolding nand_inv2_def
          by (metis (no_types, hide_lams) \<open>nand_inv2 tw\<close> dual_order.strict_trans insertI1 less_add_one
          nand_inv2_def next_time_world_at_least)
        with \<open>?po1\<close> have "?po1 \<and> ?po2"
          by auto }
      thus ?thesis
        unfolding nand_inv3_def by auto
    qed
    ultimately have "nand_inv (next_time_world tw, snd tw) \<and> nand_inv2 (next_time_world tw, snd tw)
                    \<and> nand_inv3 (next_time_world tw, snd tw)"
      by auto }
  moreover
  { assume "event_of tw = {}"
    with \<open>nand_inv tw\<close> and \<open>nand_inv3 tw\<close> have "nand_inv (next_time_world tw, snd tw)"
      using nand_inv_next_time_disjnt2 by auto
    moreover have "nand_inv2 (next_time_world tw, snd tw)"
    proof -
      { assume " C \<in> event_of (next_time_world tw, snd tw)"
        have "(\<forall>i>get_time tw + 1. snd tw C i = snd tw C (get_time tw + 1))"
          using \<open>nand_inv3 tw\<close> \<open>event_of tw = {}\<close>  unfolding nand_inv3_def
          by auto
        hence "\<forall>i>next_time_world tw. snd tw C i = snd tw C (next_time_world tw)"
          using next_time_world_at_least 
          by (smt discrete le_neq_implies_less less_imp_le less_le_trans) }
      thus ?thesis
        unfolding nand_inv2_def by auto
    qed
    moreover have "nand_inv3 (next_time_world tw, snd tw)"
    proof -
      { assume "event_of (next_time_world tw, snd tw) = {}"
        with \<open>event_of tw = {}\<close> have "next_time_world tw = fst tw + 1" (is "?ntime")
          using successive_empty_event  by blast
        hence "snd tw C (fst tw + 2) \<longleftrightarrow> snd tw C (fst tw + 1)"
          using \<open>event_of (next_time_world tw, snd tw) = {}\<close> unfolding event_of_alt_def
          by (metis (no_types, lifting) Suc_eq_plus1 \<open>event_of tw = {}\<close> \<open>nand_inv3 tw\<close> add_Suc_right
          lessI nand_inv3_def one_add_one)
        have "snd tw C (fst tw + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
          using \<open>nand_inv (next_time_world tw, snd tw)\<close> unfolding \<open>next_time_world tw = fst tw + 1\<close>
          nand_inv_def by auto
        moreover have "snd tw A (fst tw) = snd tw A (fst tw + 1)" and "snd tw B (fst tw) = snd tw B (fst tw + 1)"
          using \<open>event_of (next_time_world tw, snd tw) = {}\<close> \<open>next_time_world tw = get_time tw + 1\<close> event_of_alt_def 
          by fastforce+
        ultimately have "snd tw C (fst tw + 2) \<longleftrightarrow> \<not> (snd tw A (fst tw + 1) \<and> snd tw B (fst tw + 1))" (is "?po1")
          using \<open>snd tw C (get_time tw + 2) = snd tw C (get_time tw + 1)\<close> by blast
        have "\<forall>i>next_time_world tw + 1. snd tw C i = snd tw C (next_time_world tw+ 1)" (is "?po2")
          using \<open>nand_inv3 tw\<close> \<open>event_of tw = {}\<close> 
          unfolding \<open>next_time_world tw = fst tw + 1\<close>  nand_inv3_def by auto
        with \<open>?po1\<close> \<open>?ntime\<close> have "?po1 \<and> ?po2 \<and> ?ntime"
          by auto }
      thus ?thesis
        unfolding nand_inv3_def by auto
    qed
    ultimately have "nand_inv (next_time_world tw, snd tw) \<and> nand_inv2 (next_time_world tw, snd tw)
                    \<and> nand_inv3 (next_time_world tw, snd tw)"
      by auto }
  ultimately show "nand_inv (next_time_world tw, snd tw) \<and> nand_inv2 (next_time_world tw, snd tw)
                    \<and> nand_inv3 (next_time_world tw, snd tw)"
    by auto
qed

lemma nand_conc_hoare:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv  (next_time_world tw, snd tw) \<and> 
                                                                  nand_inv2 (next_time_world tw, snd tw) \<and> 
                                                                  nand_inv3 (next_time_world tw, snd tw)\<rbrace>"
  unfolding nand3_def
  apply (rule Single)
   apply (rule compositional_conj)
    apply (rule strengthen_precondition)
    apply(rule nand_seq_hoare_next_time)
   apply(rule Conj)
    apply(rule Conseq2[where P="\<lambda>tw. True"])
      apply simp
     apply(rule nand_seq_hoare_next_time2)
    apply simp
   apply(rule Conseq2[where P="\<lambda>tw. True"])
     apply simp
     apply(rule nand_seq_hoare_next_time3)
   apply simp
  apply (rule nand_inv_123_next_time)
  done

lemma nand_conc_sim:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw\<rbrace>"
  apply (rule While)
  apply (rule nand_conc_hoare)
  done

lemma nand_conc_sim2:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw\<rbrace> nand3 \<lbrace>nand_inv\<rbrace>"
  by (rule Conseq_sim[where Q="\<lambda>tw. nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw" and 
                            P="\<lambda>tw. nand_inv tw \<and> nand_inv2 tw \<and> nand_inv3 tw"])
     (simp_all add: nand_conc_sim)
                
end