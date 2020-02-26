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

subsection \<open>Proving @{term "nand3"}: NAND with transport delay \<close>

lemma beval_world_raw2_type:
  assumes "wityping \<Gamma>' (snd tw)"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v"
  shows   "type_of v = \<Gamma>' A"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
    using assms(2) unfolding beval_world_raw2_def by auto
  then obtain \<sigma> \<gamma> \<theta> where "\<sigma> = state_of_world (snd tw) (fst tw)" and
                          "\<gamma> = event_of_world (snd tw) (fst tw)" and
                          "\<theta> = derivative_hist_raw (snd tw) (fst tw)" and
                          "fst tw, \<sigma>, \<gamma>, \<theta>, (fst (snd tw)) \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b v"
    using beval_world_raw_cases by force
  have "styping \<Gamma>' \<sigma>"
    using wityping_ensure_styping
    by (simp add: wityping_ensure_styping \<open>\<sigma> = state_of_world (snd tw) (get_time tw)\<close> assms(1))
  moreover have "ttyping \<Gamma>' \<theta>"
    using wityping_ensure_ttyping
    by (simp add: wityping_ensure_ttyping \<open>\<theta> = derivative_hist_raw (snd tw) (get_time tw)\<close> assms(1))
  moreover have "styping \<Gamma>' (fst (snd tw))"
    using assms(1) unfolding wityping_def by blast
  moreover have "\<Gamma>' A = \<Gamma>' B"
    apply(rule beval_cases(9)[OF `fst tw, \<sigma>, \<gamma>, \<theta>, (fst (snd tw)) \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b v`])
    apply (metis beval_raw_preserve_well_typedness bexp_wt.intros(3) calculation(1) calculation(2) calculation(3) type_of.simps(1))
    by (metis (full_types) beval_cases(1) calculation(1) styping_def type_of.simps(2))
  moreover have "bexp_wt \<Gamma>' (Bnand (Bsig A) (Bsig B)) (\<Gamma>' A)"
    by (metis bexp_wt.intros(3) bexp_wt.intros(9) calculation(4))
  ultimately show ?thesis
    using beval_raw_preserve_well_typedness
    by (metis \<open>get_time tw , \<sigma> , \<gamma> , \<theta>, get_time (snd tw) \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b v\<close>)
qed

lemma beval_world_raw2_typeB:
  assumes "wityping \<Gamma>' (snd tw)"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v"
  shows   "type_of v = \<Gamma>' B"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
    using assms(2) unfolding beval_world_raw2_def by auto
  then obtain \<sigma> \<gamma> \<theta> where "\<sigma> = state_of_world (snd tw) (fst tw)" and
                          "\<gamma> = event_of_world (snd tw) (fst tw)" and
                          "\<theta> = derivative_hist_raw (snd tw) (fst tw)" and
                          "fst tw, \<sigma>, \<gamma>, \<theta>, (fst (snd tw)) \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b v"
    using beval_world_raw_cases by force
  have "styping \<Gamma>' \<sigma>"
    using wityping_ensure_styping
    by (simp add: wityping_ensure_styping \<open>\<sigma> = state_of_world (snd tw) (get_time tw)\<close> assms(1))
  moreover have "ttyping \<Gamma>' \<theta>"
    using wityping_ensure_ttyping
    by (simp add: wityping_ensure_ttyping \<open>\<theta> = derivative_hist_raw (snd tw) (get_time tw)\<close> assms(1))
  moreover have "styping \<Gamma>' (fst (snd tw))"
    using assms(1) unfolding wityping_def by blast
  moreover have "\<Gamma>' A = \<Gamma>' B"
    apply(rule beval_cases(9)[OF `fst tw, \<sigma>, \<gamma>, \<theta>, (fst (snd tw)) \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b v`])
    apply (metis beval_raw_preserve_well_typedness bexp_wt.intros(3) calculation(1) calculation(2) calculation(3) type_of.simps(1))
    by (metis (full_types) beval_cases(1) calculation(1) styping_def type_of.simps(2))
  moreover have "bexp_wt \<Gamma>' (Bnand (Bsig A) (Bsig B)) (\<Gamma>' B)"
    by (metis bexp_wt.intros(3) bexp_wt.intros(9) calculation(4))
  ultimately show ?thesis
    using beval_raw_preserve_well_typedness
    by (metis \<open>get_time tw , \<sigma> , \<gamma> , \<theta>, get_time (snd tw) \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b v\<close>)
qed

abbreviation "bval_of_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

locale scalar_type_nand3 =
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> A = Bty" and "\<Gamma> B = Bty" and "\<Gamma> C = Bty"
begin

text \<open>Invariant for NAND: at all times @{term "i"} less than @{term "fst tw :: nat"}, the signal
@{term "C :: sig"} at @{term "i + 1"} should be the NAND value of @{term "A :: sig"} and
@{term "B :: sig"} at time @{term "i"}.\<close>

definition nand_inv :: "sig assn2" where
  "nand_inv \<equiv> (\<lambda>tw. \<forall>i < fst tw. bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i\<ge>fst tw. bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))))"

lemma nand_inv_next_time:
  assumes "nand_inv tw"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have "\<forall>i < next_time_world tw'. bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw'"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
      using \<open>fst tw < next_time_world tw'\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
        using assms(1) unfolding nand_inv_def by auto
      hence "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>) }
    moreover
    { assume " fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of_wline tw' C (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      moreover have "bval_of_wline tw' A i \<longleftrightarrow> bval_of_wline tw' A (fst tw)" and "bval_of_wline tw' B i \<longleftrightarrow> bval_of_wline tw' B (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "bval_of_wline tw' C (fst tw + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
      proof -
        have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig A) (Bsig B)) v"
          using assms(2) unfolding beval_world_raw2_def by auto
        have "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        also have "... = Bv (\<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw)))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using assms by auto
        also have "... = Bv (\<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw)))"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by simp
        finally show ?thesis
          by simp
      qed
      ultimately have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "bval_of_wline tw' C (i + 1) = bval_of_wline tw' C (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by auto
      also have "... = bval_of_wline tw' C (fst tw + 1)"
        using \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def
        worldline_upd_def by auto
      finally have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of_wline tw' C (fst tw + 1)"
        by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
      proof -
        have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig A) (Bsig B)) v"
          using assms(2) unfolding beval_world_raw2_def by auto
        have "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        also have "... = Bv (\<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw)))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using assms by auto
        also have "... = Bv (\<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw)))"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by simp
        finally show ?thesis
          by simp
      qed
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> bval_of_wline tw' C (i + 1) = (\<not>
        (bval_of_wline tw' A i \<and> bval_of_wline tw' B i))\<close> \<open>i < next_time_world tw'\<close> calculation
        le_less_linear unchanged_until_next_time_world)
      finally have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by auto }
    ultimately show "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
      by auto
  qed
  thus ?thesis
    unfolding nand_inv_def by auto
qed

lemma pre_nand_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] 
        (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) 
     [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, simp)
  using nand_inv_next_time beval_world_raw2_type worldline_upd_preserve_wityping
  by (metis scalar_type_nand3_axioms scalar_type_nand3_def snd_conv worldline_upd2_def)

lemma nand_seq_hoare_next_time_aux:
  assumes "nand_inv (next_time_world tw, snd tw)"
  shows   "\<And>i. fst tw < i \<Longrightarrow> i \<le> next_time_world tw \<Longrightarrow> nand_inv (i, snd tw)"
  using assms unfolding nand_inv_def by simp

lemma nand_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] 
        (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) 
     [\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw)) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[rotated])
  apply (rule pre_nand_seq_hoare_next_time)
  by (simp add: nand_seq_hoare_next_time_aux) auto

lemma pre_nand_seq_hoare_next_time0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] 
        Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 
      [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where P="\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)"])
  using pre_nand_seq_hoare_next_time unfolding nand_inv_def  using gr_implies_not_zero
  by auto

lemma nand_seq_hoare_next_time0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] 
          Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 
      [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[rotated])
    apply (rule pre_nand_seq_hoare_next_time0)
  by (simp add: nand_seq_hoare_next_time_aux) auto
 
lemma disjnt_AB_eq:
  "disjnt {A, B} s \<longleftrightarrow> (s = {} \<or> s = {C})"
  by (rule, metis Diff_UNIV Diff_insert0 Diff_single_insert UNIV_sig disjnt_insert1 empty_subsetI
  subset_singleton_iff) auto

lemma pre_nand_conc_hoare':
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence *: "\<forall>i < fst tw. bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
    unfolding nand_inv_def by auto
  have **: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. bval_of_wline tw s i = bval_of_wline tw s (fst tw))"
    using unchanged_until_next_time_world by metis
  have ***: "(\<forall>i\<ge> fst tw. bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and>  bval_of_wline tw B (fst tw)))"
    using \<open>nand_inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding nand_inv2_def by auto

  \<comment> \<open>obtain the value of A and B at time fst tw\<close>
  have "bval_of_wline tw A (fst tw) = bval_of_wline tw A (fst tw - 1)" and
        "bval_of_wline tw B (fst tw) = bval_of_wline tw B (fst tw - 1)"
    using \<open>disjnt {A, B} (event_of tw)\<close> unfolding event_of_alt_def
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
 { fix i
    assume "i < next_time_world tw"
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
        using * by auto }
    moreover
    { assume "fst tw \<le> i"
      hence "bval_of_wline tw C (i + 1) \<longleftrightarrow> bval_of_wline tw C (fst tw + 1)"
        using *** by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
        using *** \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
        using ** \<open>i < next_time_world tw\<close> \<open>fst tw \<le> i\<close> less_imp_le_nat by blast
      finally have "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
        by auto }
    ultimately have "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
      by auto }
  hence "\<And>i. i < next_time_world tw \<Longrightarrow> bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
    by auto
  thus "nand_inv (next_time_world tw, snd tw)"
    unfolding nand_inv_def by auto
qed

lemma nand_conc_hoare':
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j\<in> {fst tw <.. next_time_world tw}. nand_inv (j, snd tw)"
  using pre_nand_conc_hoare' nand_seq_hoare_next_time_aux 
  using greaterThanAtMost_iff by blast

lemma nand_conc_hoare2:
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. nand_inv2 (j, snd tw)"
proof (rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j :: nat
  assume "j \<in> {fst tw <.. next_time_world tw}"
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence 0: "(\<forall>i\<ge>fst tw. bval_of_wline tw C (i + 1) = (\<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))))"
    unfolding nand_inv2_def by auto
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. bval_of_wline tw s i = bval_of_wline tw s (fst tw))"
    using unchanged_until_next_time_world by metis
  { assume "disjnt {A, B} (event_of (j, snd tw))"
    hence *: "bval_of_wline tw A j = bval_of_wline tw A (j - 1)" and **: "bval_of_wline tw B j = bval_of_wline tw B (j - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "j \<le> i"
      hence "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
        using 0 \<open>j \<in> {get_time tw<..next_time_world tw}\<close> by auto
      moreover have "bval_of_wline tw A (fst tw) = bval_of_wline tw A (j - 1)" and "bval_of_wline tw B (fst tw) = bval_of_wline tw B (j - 1)"
        using 1
        by (metis (no_types, lifting) Suc_leI \<open>j \<in> {get_time tw<..next_time_world tw}\<close> diff_less
        dual_order.strict_trans1 greaterThanAtMost_iff le_add1 less_one
        linordered_semidom_class.add_diff_inverse not_le plus_1_eq_Suc)+
      ultimately have "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A j \<and> bval_of_wline tw B j)"
        using * ** by auto
    }
    hence "(\<forall>i\<ge>j. bval_of_wline tw C (i + 1) = (\<not> (bval_of_wline tw A j \<and> bval_of_wline tw B j)))"
      by auto }
  thus "nand_inv2 (j, snd tw)"
    unfolding nand_inv2_def by auto
qed

lemma nand_inv2_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "\<forall>i \<in> {fst tw <.. next_time_world tw'}. nand_inv2 (i, snd tw')"
proof (rule)
  fix i 
  assume "i \<in> {fst tw <.. next_time_world tw'}"
  { assume "disjnt {A, B} (event_of (i, snd tw'))"
    have "fst tw < i"
      using \<open>i \<in> {fst tw <.. next_time_world tw'}\<close> by auto
    have *: "\<And>s. s \<in> {A, B} \<Longrightarrow> bval_of_wline tw' s i \<longleftrightarrow> bval_of_wline tw s (fst tw)"
    proof -
      fix s
      assume "s \<in> {A, B}"
      hence "bval_of_wline tw' s i \<longleftrightarrow> bval_of_wline tw s i"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> bval_of_wline tw s (i - 1)"
        using \<open>disjnt {A, B} (event_of (i, snd tw'))\<close> \<open>fst tw < i\<close>
        unfolding event_of_alt_def
        by (smt \<open>s \<in> {A, B}\<close> comp_apply disjnt_iff fst_conv gr_implies_not_zero insert_iff
        mem_Collect_eq sig.simps(4) sig.simps(6) singletonD snd_conv tw'_def worldline_upd2_def
        worldline_upd_def)
      also have "... \<longleftrightarrow> bval_of_wline tw s (fst tw)"
      proof -
        have "fst tw' \<le> i - 1" and "i - 1 < i"
          using \<open>fst tw < i\<close> 
          by (simp add: Suc_leI tw'_def worldline_upd2_def)+
        hence "bval_of_wline tw' s (i - 1) = bval_of_wline tw' s (fst tw')"
          using unchanged_until_next_time_world[where tw="tw'"]
          by (metis (no_types, lifting) \<open>i \<in> {get_time tw<..next_time_world tw'}\<close>
          dual_order.strict_trans1 greaterThanAtMost_iff)
        moreover have "bval_of_wline tw' s (i - 1) = bval_of_wline tw s (i - 1)"
          unfolding tw'_def worldline_upd2_def worldline_upd_def using  \<open>s \<in> {A, B}\<close> by auto
        moreover have "bval_of_wline tw' s (fst tw') = bval_of_wline tw s (fst tw')"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        ultimately show ?thesis
          by (simp add: tw'_def worldline_upd2_def)
      qed
      finally show "bval_of_wline tw' s i \<longleftrightarrow> bval_of_wline tw s (fst tw)"
        by auto
    qed
    have "\<And>j. i \<le> j \<Longrightarrow> bval_of_wline tw' C (j + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
    proof -
      fix j
      have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
        using assms unfolding beval_world_raw2_def by auto
      assume "i \<le> j"
      hence "bval_of_wline tw' C (j + 1) \<longleftrightarrow> bval_of v"
        using `fst tw < i`
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
        apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
        apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
        using assms(2) by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        using * by auto
      finally show "bval_of_wline tw' C (j + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by auto
    qed }
  thus "nand_inv2 (i, snd tw')"
    unfolding nand_inv2_def by auto
qed

lemma nand_seq_hoare_next_time4:
  " \<turnstile> [\<lambda>tw.  wityping \<Gamma> (snd tw) ] Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, blast)
  using nand_inv2_next_time beval_world_raw2_type
  by (metis fst_conv scalar_type_nand3_axioms scalar_type_nand3_def snd_conv worldline_upd2_def
  worldline_upd_preserve_wityping)

definition "nand_wityping \<equiv> \<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)"
definition "nand_wityping2 \<equiv> \<lambda>tw. nand_inv2 tw \<and> wityping \<Gamma> (snd tw)"

lemma pre_nand_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> 
        nand3 
     \<lbrace>\<lambda>tw. ((\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw)) \<and> wityping \<Gamma> (snd tw)) 
         \<and> ((\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw))\<rbrace>"
  unfolding nand3_def
  apply (rule Single)
  apply (rule strengthen_precondition)
   apply (rule compositional_conj)
  unfolding nand_wityping_def snd_conv  apply(rule nand_seq_hoare_next_time)
   apply(rule Conseq2[where P="\<lambda>tw. wityping \<Gamma> (snd tw)"])
     unfolding nand_wityping2_def apply simp
    unfolding nand_wityping2_def apply (rule nand_seq_hoare_next_time4)
   apply simp
  apply (rule allI)
  apply (rule impI)
    apply (rule conjI)
     apply (rule mp, rule impI, rule conjI)
      apply (erule nand_conc_hoare')
      apply simp
     apply simp
    apply (rule mp, rule impI, rule conjI)
     apply (erule nand_conc_hoare2)
     apply simp
    apply simp
    done

lemma nand_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> 
        nand3 
     \<lbrace>\<lambda>tw. \<forall>i\<in>{get_time tw<..next_time_world tw}. nand_wityping (i, snd tw) \<and> nand_wityping2 (i, snd tw)\<rbrace>"
  apply (rule Conseq'[rotated])
  apply (rule pre_nand_conc_hoare3)
  by (auto simp add: nand_wityping2_def nand_wityping_def)
  
lemma nand_conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace>"
  apply (rule While)
  apply (rule nand_conc_hoare3)
  done

lemma nand_conc_sim2':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand3 \<lbrace>nand_wityping\<rbrace>"
  by (rule Conseq_sim[where Q="\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw" and
                            P="\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw"])
     (simp_all add: nand_conc_sim')

text \<open>Initialisation preserves the invariant\<close>

lemma init_sat_nand_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 nand_wityping"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conseq2[rotated])
  unfolding nand_wityping_def snd_conv apply (rule nand_seq_hoare_next_time0)
  using greaterThanAtMost_iff next_time_world_at_least by blast+

lemma init_sat_nand_inv2:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) nand3 nand_wityping2"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conseq2[rotated])
  unfolding nand_wityping2_def snd_conv apply (rule nand_seq_hoare_next_time4)
  by (auto simp add: next_time_world_at_least)

lemma init_sat_nand_inv_comb:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_nand_inv)
  apply (rule ConseqI_sim[where P="\<lambda>tw. wityping \<Gamma> (snd tw)" and Q="nand_wityping2"])
  apply (simp, rule init_sat_nand_inv2, simp)
  done

lemma nand_correctness:
  assumes "sim_fin w (i + 1) nand3 tw'" and "wityping \<Gamma> w"
  shows "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
proof -
  obtain tw where "init_sim (0, w) nand3 tw" and  "tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf nand3"
    unfolding conc_stmt_wf_def nand3_def by auto
  moreover have "nonneg_delay_conc nand3"
    unfolding nand3_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_inv_comb] by auto
  hence "nand_wityping tw \<and> nand_wityping2 tw"
    using \<open>init_sim (0, w) nand3 tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "nand_wityping tw" and "nand_wityping2 tw"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand3 \<lbrace>nand_wityping\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'] \<open>conc_stmt_wf nand3\<close> \<open>nonneg_delay_conc nand3\<close>
    by auto
  ultimately have "nand_wityping tw'"
    using \<open>tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
    unfolding nand_wityping_def nand_inv_def by auto
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    by (metis less_add_one)
qed

subsubsection \<open>Proving @{term "nand"}: NAND with inertial delay\<close>

lemma nand_inv_next_time_inert:
  assumes "nand_inv tw"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_inert_upd2_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have "\<forall>i < next_time_world tw'. bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw'"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
      using \<open>fst tw < next_time_world tw'\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
        using assms(1) unfolding nand_inv_def by auto
      have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
      proof (cases "i + 1 < fst tw")
        case True
        hence "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of_wline tw C (i + 1)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          by auto
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
          using `bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)` by auto
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          by auto
        finally show ?thesis
          by auto
      next
        case False
        hence "i + 1 = fst tw"
          using \<open>i < get_time tw\<close> by linarith
        show "bval_of_wline tw' C (i + 1) \<longleftrightarrow>  \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
          case True
          hence "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of_wline tw C (fst tw)"
            using `i + 1 = fst tw`
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
          also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
            using `bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)` `i + 1 = fst tw` by auto
          also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
            using `i + 1 = fst tw` by auto
          finally show ?thesis
            by auto
        next
          case False
          hence "wline_of tw C (fst tw) \<noteq> v" and "wline_of tw C (fst tw + 1) = v"
            by auto
          let ?time = "GREATEST n. n \<le> fst tw + 1
                                 \<and> wline_of tw C (n - 1) \<noteq> v
                                 \<and> wline_of tw C n = v"
          have "?time = fst tw + 1"
            using False by (intro Greatest_equality) auto
          hence "wline_of tw' C (i + 1) = wline_of tw C (fst tw)"
            using False \<open>i + 1 = get_time tw\<close> unfolding tw'_def worldline_inert_upd2_def
            worldline_inert_upd_def comp_def by auto
          have "bval_of_wline tw C (fst tw)  \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)"
            using `bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A i \<and> bval_of_wline tw B i)` `i
            + 1 = fst tw` by auto
          also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
            using `i + 1 = fst tw` by auto
          finally show ?thesis
            using \<open>wline_of tw' C (i + 1) = wline_of tw C (get_time tw)\<close> by auto
        qed
      qed }
    moreover
    { assume " fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of_wline tw' C (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      moreover have "bval_of_wline tw' A i \<longleftrightarrow> bval_of_wline tw' A (fst tw)" and "bval_of_wline tw' B i \<longleftrightarrow> bval_of_wline tw' B (fst tw)"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>i <
        next_time_world tw'\<close> unchanged_until_next_time_world)+
      moreover have "bval_of_wline tw' C (fst tw + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
      proof (cases " wline_of tw C (get_time tw) = v \<or>  wline_of tw C (get_time tw + 1) \<noteq> v")
        case True
        hence "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "bval_of v \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using assms(3) by auto
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by blast
      next
        case False
        hence "wline_of tw C (get_time tw) \<noteq> v" and
              "wline_of tw C (get_time tw + 1) = v"
          by blast+
        let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
        have "?time = fst tw + 1"
          using False
          by (intro Greatest_equality) auto
        hence "wline_of tw' C (fst tw + 1) =  v"
          using False unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          comp_def by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "bval_of v \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
          unfolding beval_world_raw2_def
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using assms(3) by auto
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by auto
      qed
      ultimately have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "bval_of_wline tw' C (i + 1) = bval_of_wline tw' C (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by auto
      also have "... = bval_of_wline tw' C (fst tw + 1)"
      proof (cases "wline_of tw C (get_time tw) =  v \<or> wline_of tw C (get_time tw + 1) \<noteq>  v")
        case True
        hence "wline_of tw' C (next_time_world tw') = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def comp_def
          using `fst tw < next_time_world tw'`
          by (smt add.commute fst_conv less_SucE next_time_world_at_least order.asym plus_1_eq_Suc
          snd_conv)
        also have "... = wline_of tw' C (fst tw + 1)"
          by (smt True dual_order.strict_iff_order not_add_less1 o_apply snd_conv tw'_def
          worldline_inert_upd2_def worldline_inert_upd_def)
        finally show ?thesis
          by auto
      next
        case False
        let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
        have "?time = fst tw + 1"
          using False by (intro Greatest_equality) auto
        hence "wline_of tw' C (next_time_world tw') = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def comp_def
          by (smt add.commute fst_conv less_SucE next_time_world_at_least order.asym plus_1_eq_Suc
          snd_conv)
        also have "... = wline_of tw' C (fst tw + 1)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def comp_def
          using `fst tw < next_time_world tw'` `?time = fst tw + 1` by auto
        finally show ?thesis
          by auto
      qed
      finally have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of_wline tw' C (fst tw + 1)"
        by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
      proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
        case True
        hence "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def comp_def
          by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using assms(3) by auto
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by auto
      next
        case False
        let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
        have "?time = fst tw + 1"
          using False by (intro Greatest_equality) auto
        hence "wline_of tw' C (fst tw + 1) =  v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def comp_def by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using assms(3) by auto
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A (fst tw) \<and> bval_of_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by blast
      qed
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> bval_of_wline tw' C (i + 1) = (\<not> (bval_of_wline tw' A
        i \<and> bval_of_wline tw' B i))\<close> \<open>i < next_time_world tw'\<close> calculation not_le
        unchanged_until_next_time_world)
      finally have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
        by auto }
    ultimately show "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
      by auto
  qed
  thus ?thesis
    unfolding nand_inv_def by auto
qed

lemma nand_inv_next_time0_inert:
  assumes "fst tw = 0"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "nand_inv tw"
    using assms(1) unfolding nand_inv_def by auto
  from nand_inv_next_time_inert[OF this] show ?thesis
    unfolding tw'_def using assms by blast
qed

lemma nand_seq_hoare_next_time_inert:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule AssignI2, blast)
  using nand_inv_next_time_inert beval_world_raw2_type
  using scalar_type_nand3_axioms scalar_type_nand3_def by auto

lemma seq_wt_nand3:
  "seq_wt \<Gamma> (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  by (metis bexp_wt.intros(3) bexp_wt.intros(9) scalar_type_nand3_axioms scalar_type_nand3_def seq_wt.intros(5))

lemma pre_nand_seq_hoare_wityping:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule nand_seq_hoare_next_time_inert)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule seq_wt_nand3)
  done

lemma nand_seq_hoare_wityping:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[rotated])
  apply (rule pre_nand_seq_hoare_wityping)
  apply (auto simp add: nand_seq_hoare_next_time_aux)
  done

lemma nand_seq_hoare_next_time0_inert:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule AssignI2)
  using nand_inv_next_time0_inert beval_world_raw2_type scalar_type_nand3_axioms scalar_type_nand3_def
  by auto

lemma nand_seq_hoare_wityping0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule nand_seq_hoare_next_time0_inert)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule seq_wt_nand3)
  done

lemma nand_inv2_next_time_inert:
  fixes tw
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. nand_inv2 (j, snd tw')"
  unfolding nand_inv2_def
proof (rule, rule impI)
  fix j
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  assume "disjnt {A, B} (event_of (j, snd tw'))"
  have "fst tw < j"
    using \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> greaterThanAtMost_iff
    by (simp add: tw'_def worldline_inert_upd2_def)
  have "wline_of tw' A j = wline_of tw A j"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... = wline_of tw A (j - 1)"
    using \<open>disjnt {A, B} (event_of (j, snd tw'))\<close> \<open>fst tw < j\<close>
    unfolding event_of_alt_def
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... = wline_of tw A (fst tw)"
  proof -
    have "fst tw' \<le> j - 1" and "j - 1 < j"
      apply (metis Suc_eq_plus1 Suc_leI \<open>get_time tw < j\<close> add_le_imp_le_diff prod.sel(1) tw'_def worldline_inert_upd2_def)
      using \<open>get_time tw < j\<close> by linarith
    hence "wline_of tw' A (j - 1) = wline_of tw' A (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] 
      by (smt \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> dual_order.strict_trans1
      greaterThanAtMost_iff o_apply prod.sel(1) prod.sel(2) sig.simps(4) tw'_def
      unchanged_until_next_time_world worldline_inert_upd2_def worldline_inert_upd_def)
    moreover have "wline_of tw' A (j - 1) = wline_of tw A (j - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "wline_of tw' A (fst tw') = wline_of tw A (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      by (simp add: tw'_def worldline_inert_upd2_def)
  qed
  finally have 0: "wline_of tw' A j = wline_of tw A (fst tw)"
    by auto
  have "wline_of tw' B j = wline_of tw B j"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... = wline_of tw B (j - 1)"
    using \<open>disjnt {A, B} (event_of (j, snd tw'))\<close> \<open>fst tw < j\<close>
    unfolding event_of_alt_def
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... = wline_of tw B (fst tw)"
  proof -
    have "fst tw' \<le> j - 1" and "j - 1 < j"
      apply (simp add: Suc_leI \<open>get_time tw < j\<close> add_le_imp_le_diff tw'_def worldline_inert_upd2_def)
      using \<open>get_time tw < j\<close> by auto
    hence "wline_of tw' B (j - 1) = wline_of tw' B (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] 
      by (smt \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> dual_order.strict_trans1
      greaterThanAtMost_iff o_apply prod.sel(1) prod.sel(2) sig.simps(6) tw'_def
      unchanged_until_next_time_world worldline_inert_upd2_def worldline_inert_upd_def)
    moreover have "wline_of tw' B (j - 1) = wline_of tw B (j - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "wline_of tw' B (fst tw') = wline_of tw B (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      by (simp add: tw'_def worldline_inert_upd2_def)
  qed
  finally have 1: "wline_of tw' B j = wline_of tw B (fst tw)"
    by auto
  { fix i
    assume "j \<le> i"
    hence "wline_of tw' C (i + 1) = v"
    proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
      case True
      thus "wline_of tw' C (i + 1) = v"
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
        using `fst tw < j` \<open>j \<le> i\<close> by auto
    next
      case False
      let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
      have "?time = fst tw + 1"
        using False by (auto intro!:Greatest_equality)
      thus ?thesis
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
        using `fst tw < j` \<open>j \<le> i\<close> by auto
    qed
    have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
      using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
      by auto
    have "bval_of v \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
      apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
      apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
      using assms(2) by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A j \<and> bval_of_wline tw' B j)"
      using 0 1 by auto
    finally have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A j \<and> bval_of_wline tw' B j)"
      using \<open>wline_of tw' C (i + 1) = v\<close> by blast }
  thus "\<forall>i\<ge>get_time (j, snd tw').
            bval_of_wline (j, snd tw') C (i + 1) = (\<not> (bval_of_wline (j, snd tw') A (get_time (j, snd tw')) \<and> bval_of_wline (j, snd tw') B (get_time (j, snd tw'))))"
    by auto
qed

lemma nand_seq_hoare_next_time4_inert:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)", rotated 1], rule AssignI2, blast)
  using nand_inv2_next_time_inert beval_world_raw2_type scalar_type_nand3_axioms scalar_type_nand3_def
  by auto

lemma nand_seq_hoare2_wityping:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule nand_seq_hoare_next_time4_inert)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule seq_wt_nand3)
  done

lemma pre_nand_conc_hoare3_inert:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand \<lbrace>\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_wityping   (i, snd tw))  
                                                          \<and> (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_wityping2  (i, snd tw))\<rbrace>"
  unfolding nand_def
  apply (rule Single)
   apply (unfold conj_assoc)
   apply (rule compositional_conj)
  unfolding nand_wityping_def snd_conv apply(rule nand_seq_hoare_wityping)
   apply (rule strengthen_precondition)
   apply(rule Conseq2[where P="\<lambda>tw. wityping \<Gamma> (snd tw)"])
     unfolding nand_wityping2_def apply simp
     unfolding nand_wityping2_def apply (rule nand_seq_hoare2_wityping)
     apply simp                                                  
  apply (rule allI)
  apply (rule impI)
     apply (rule conjI)
     using nand_conc_hoare' apply blast
     using nand_conc_hoare2 by auto

lemma nand_conc_hoare3_inert:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand \<lbrace>\<lambda>tw. \<forall>i\<in>{get_time tw<..next_time_world tw}. nand_wityping (i, snd tw) \<and> nand_wityping2 (i, snd tw)\<rbrace>"
  apply (rule Conseq'[rotated])
  apply (rule pre_nand_conc_hoare3_inert)
  by auto

lemma nand_conc_sim'_inert:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace>"
  apply (rule While)
  apply (rule nand_conc_hoare3_inert)
  done

lemma nand_conc_sim2'_inert:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand \<lbrace>nand_wityping\<rbrace>"
  by (rule Conseq_sim[where Q="\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw" and
                            P="\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw"])
     (simp_all add: nand_conc_sim'_inert)

lemma init_sat_nand_inv_inert:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand nand_wityping"
  unfolding nand_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding nand_wityping_def snd_conv apply (rule nand_seq_hoare_wityping0)
  done

lemma init_sat_nand_inv2_inert:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) nand nand_wityping2"
  unfolding nand_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conseq2[rotated])
  unfolding nand_wityping2_def snd_conv  apply (rule nand_seq_hoare2_wityping)
  apply (simp add: next_time_world_at_least)
  by auto

lemma init_sat_nand_inv_comb_inert:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand (\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_nand_inv_inert)
  apply (rule ConseqI_sim[where P="\<lambda>tw. wityping \<Gamma> (snd tw)" and Q="nand_wityping2"])
  apply (simp, rule init_sat_nand_inv2_inert, simp)
  done

lemma nand_correctness_inert:
  assumes "sim_fin w (i + 1) nand tw'" and "wityping \<Gamma> w"
  shows   "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
proof -
  obtain tw where "init_sim (0, w) nand tw" and  "tw, i + 1, nand \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf nand"
    unfolding conc_stmt_wf_def nand_def by auto
  moreover have "nonneg_delay_conc nand"
    unfolding nand_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand (\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_inv_comb_inert] by auto
  hence "nand_wityping tw \<and> nand_wityping2 tw"
    using \<open>init_sim (0, w) nand tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "nand_wityping tw" and "nand_wityping2 tw"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand \<lbrace>nand_wityping\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'_inert] \<open>conc_stmt_wf nand\<close> \<open>nonneg_delay_conc nand\<close>
    by auto
  ultimately have "nand_wityping tw'"
    using \<open>tw, i + 1, nand \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
    unfolding nand_wityping_def nand_inv_def by auto
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    by (metis less_add_one)
qed

end

subsection \<open>vector type of NAND\<close>

locale vector_type_nand3 =
  fixes len :: "nat"
  fixes ki :: signedness
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> A = Lty ki len" and "\<Gamma> B = Lty ki len" and "\<Gamma> C = Lty ki len"
begin

definition nand_inv :: "sig assn2" where
  "nand_inv \<equiv> (\<lambda>tw. \<forall>i < fst tw.
             lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. disjnt {A, B} (event_of tw) \<longrightarrow>
             (\<forall>i\<ge>fst tw. lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))))"

lemma nand_inv_next_time:
  assumes "nand_inv tw"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Lty ki len"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have "\<forall>i < next_time_world tw'. lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < next_time_world tw'"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
      using \<open>fst tw < next_time_world tw'\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
        using assms(1) unfolding nand_inv_def by auto
      hence "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>) }
    moreover
    { assume " fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      moreover have "lof_wline tw' A i = lof_wline tw' A (fst tw)" and "lof_wline tw' B i = lof_wline tw' B (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "lof_wline tw' C (fst tw + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
      proof -
        have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig A) (Bsig B)) v"
          using assms(2) unfolding beval_world_raw2_def by auto
        have "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        also have "... = Lv ki (map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw)))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
           prefer 2
           apply (metis assms(3) beval_cases(1) comp_apply state_of_world_def ty.inject type_of.simps(2) val.sel(3))
          using assms by auto
        also have "... = Lv ki (map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw)))"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by simp
        finally show ?thesis
          by simp
      qed
      ultimately have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        by simp }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "lof_wline tw' C (i + 1) = lof_wline tw' C (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by auto
      also have "... = lof_wline tw' C (fst tw + 1)"
        using \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def
        worldline_upd_def by auto
      finally have "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
        by auto
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
      proof -
        have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig A) (Bsig B)) v"
          using assms(2) unfolding beval_world_raw2_def by auto
        have "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        also have "... = Lv ki (map2 (\<lambda>x y. x \<longrightarrow> \<not> y)  (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw)))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
           prefer 2
          apply (metis assms(3) beval_cases(1) comp_apply state_of_world_def ty.inject type_of.simps(2) val.sel(3))
          using assms by auto
        also have "... = Lv ki (map2 (\<lambda>x y. x \<longrightarrow> \<not> y)  (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw)))"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by simp
        finally show ?thesis
          by simp
      qed
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        by (metis (no_types, lifting) \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> lval_of (wline_of tw' C (i + 1)) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lval_of (wline_of tw' A i)) (lval_of (wline_of tw' B i))\<close> \<open>i < next_time_world tw'\<close> \<open>lval_of (wline_of tw' C (get_time tw + 1)) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lval_of (wline_of tw' A (get_time tw))) (lval_of (wline_of tw' B (get_time tw)))\<close> \<open>lval_of (wline_of tw' C (i + 1)) = lval_of (wline_of tw' C (get_time tw + 1))\<close> le_less_linear unchanged_until_next_time_world)
      finally have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        by auto }
    ultimately show "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
      by auto
  qed
  thus ?thesis
    unfolding nand_inv_def by auto
qed

lemma pre_nand_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  using nand_inv_next_time beval_world_raw2_type worldline_upd_preserve_wityping
  by (smt Assign'_hoare2 snd_conv vector_type_nand3_axioms vector_type_nand3_def worldline_upd2_def)

lemma nand_seq_hoare_next_time_aux:
  assumes "nand_inv (next_time_world tw, snd tw)"
  shows   "\<And>i. fst tw < i \<Longrightarrow> i \<le> next_time_world tw \<Longrightarrow> nand_inv (i, snd tw)"
  using assms unfolding nand_inv_def by simp

lemma nand_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] 
        (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) 
     [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[rotated])
    apply (rule pre_nand_seq_hoare_next_time)
   apply (simp add: nand_seq_hoare_next_time_aux)
  by simp

lemma nand_seq_hoare_next_time0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] 
        Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 
      [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where P="\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)"])
  using nand_seq_hoare_next_time unfolding nand_inv_def  using gr_implies_not_zero
  by auto

lemma nand_conc_hoare':
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence *: "\<forall>i < fst tw. lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
    unfolding nand_inv_def by auto
  have **: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. lof_wline tw s i = lof_wline tw s (fst tw))"
    using unchanged_until_next_time_world by metis
  have ***: "(\<forall>i\<ge> fst tw. lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw)))"
    using \<open>nand_inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding nand_inv2_def by auto

  \<comment> \<open>obtain the value of A and B at time fst tw\<close>
  have "lof_wline tw A (fst tw) = lof_wline tw A (fst tw - 1)" and
        "lof_wline tw B (fst tw) = lof_wline tw B (fst tw - 1)"
    using \<open>disjnt {A, B} (event_of tw)\<close> unfolding event_of_alt_def
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
 { fix i
    assume "i < next_time_world tw"
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
        using * by auto }
    moreover
    { assume "fst tw \<le> i"
      hence "lof_wline tw C (i + 1) = lof_wline tw C (fst tw + 1)"
        using *** by auto
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
        using *** \<open>fst tw \<le> i\<close> by auto
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
        using ** \<open>fst tw \<le> i\<close> less_imp_le_nat  by (simp add: \<open>i < next_time_world tw\<close>)
      finally have "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
        by auto }
    ultimately have "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
      by auto }
  hence "\<And>i. i < next_time_world tw \<Longrightarrow> lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
    by auto
  thus "nand_inv (next_time_world tw, snd tw)"
    unfolding nand_inv_def by auto
qed

lemma nand_conc_hoare2:
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. nand_inv2 (j, snd tw)"
proof (rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j :: nat 
  assume " j \<in> {get_time tw<..next_time_world tw} "
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence 0: "\<forall>i \<ge> fst tw. lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
    unfolding nand_inv2_def by auto
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. lof_wline tw s i = lof_wline tw s (fst tw))"
    using unchanged_until_next_time_world by metis
  { assume "disjnt {A, B} (event_of (j, snd tw))"
    hence *: "lof_wline tw A j = lof_wline tw A (j - 1)" and **: "lof_wline tw B j = lof_wline tw B (j - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "j \<le> i"
      hence "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
        using 0 \<open>(j::nat) \<in> {get_time (tw::nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val))<..next_time_world
        tw}\<close> by auto
      moreover have "lof_wline tw A (fst tw) = lof_wline tw A (j - 1)" and "lof_wline tw B (fst tw) = lof_wline tw B (j - 1)"
        using 1 
        by (metis (no_types, lifting) Suc_diff_1 \<open>(j::nat) \<in> {get_time (tw::nat \<times> (sig \<Rightarrow> val) \<times> (sig
        \<Rightarrow> nat \<Rightarrow> val))<..next_time_world tw}\<close> greaterThanAtMost_iff le_0_eq less_Suc_eq_le not_less
        not_less_zero)+
      ultimately have "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A j) (lof_wline tw B j)"
        using * ** by auto }
    hence "(\<forall>i\<ge>j. lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A j) (lof_wline tw B j))"
      by auto }
  thus "nand_inv2 (j, snd tw)"
    unfolding nand_inv2_def by auto
qed

lemma nand_inv2_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Lty ki len"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. nand_inv2 (j, snd tw')"
proof (rule)
  fix j
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  { assume "disjnt {A, B} (event_of (j, snd tw'))"
    have "fst tw < j"
      by (metis \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> fst_conv greaterThanAtMost_iff tw'_def
      worldline_upd2_def)
    have *: "\<And>s. s \<in> {A, B} \<Longrightarrow> lof_wline tw' s j = lof_wline tw s (fst tw)"
    proof -
      fix s
      assume "s \<in> {A, B}"
      hence "lof_wline tw' s j = lof_wline tw s j"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... = lof_wline tw s (j - 1)"
        using \<open>disjnt {A, B} (event_of (j, snd tw'))\<close> \<open>fst tw < j\<close>
        unfolding event_of_alt_def 
        by (smt \<open>s \<in> {A, B}\<close> comp_apply disjnt_iff fst_conv gr_implies_not_zero insert_iff
        mem_Collect_eq sig.simps(4) sig.simps(6) singletonD snd_conv tw'_def worldline_upd2_def
        worldline_upd_def)
      also have "... = lof_wline tw s (fst tw)"
      proof -
        have "fst tw' \<le> j - 1" and "j - 1 < j"
          using \<open>fst tw < j\<close> \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> by auto
        hence "lof_wline tw' s (j - 1) = lof_wline tw' s (fst tw')"
          using unchanged_until_next_time_world[where tw="tw'"] 
          by (metis (no_types, lifting) \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close>
          dual_order.strict_trans1 greaterThanAtMost_iff)
        moreover have "lof_wline tw' s (j - 1) = lof_wline tw s (j - 1)"
          unfolding tw'_def worldline_upd2_def worldline_upd_def using  \<open>s \<in> {A, B}\<close> by auto
        moreover have "lof_wline tw' s (fst tw') = lof_wline tw s (fst tw')"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        ultimately show ?thesis
          by (simp add: tw'_def worldline_upd2_def)
      qed
      finally show "lof_wline tw' s j = lof_wline tw s (fst tw)"
        by auto
    qed
    have "\<And>i. j \<le> i \<Longrightarrow> lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A j) (lof_wline tw' B j)"
    proof -
      fix i
      have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
        using assms unfolding beval_world_raw2_def by auto
      assume "j \<le> i"
      hence "lof_wline tw' C (i + 1) = lval_of v"
        using `fst tw < j`
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
        apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
        prefer 2
        apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(3))
        using assms(2) by auto
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A j) (lof_wline tw' B j)"
        using * by auto
      finally show "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A j) (lof_wline tw' B j)"
        by auto
    qed }
  thus " nand_inv2 (j, snd tw')"
    unfolding nand_inv2_def by auto
qed

lemma nand_seq_hoare_next_time4:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) ] 
          Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 
      [\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, blast)
  using nand_inv2_next_time beval_world_raw2_type
  by (metis snd_conv vector_type_nand3_axioms vector_type_nand3_def worldline_upd2_def worldline_upd_preserve_wityping)

lemma pre_nand_conc_hoare3_without:
  "\<turnstile> \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace>
        nand3
     \<lbrace>\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw))  
         \<and> (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2  (i, snd tw))\<rbrace>"
  unfolding nand3_def
  apply (rule Single)
   apply (rule Conj)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
    apply (rule Conseq2[rotated])
      apply (rule nand_seq_hoare_next_time)
     apply simp
    apply simp
   apply (rule strengthen_precondition)           
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition2)
  apply (rule weaken_postcondition[OF nand_seq_hoare_next_time4])
  apply (rule, rule)
  using nand_conc_hoare' nand_conc_hoare2  nand_seq_hoare_next_time_aux
  using greaterThanAtMost_iff by blast

lemma nand_conc_hoare3_without:
  "\<turnstile> \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace>
        nand3
     \<lbrace>\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv   (i, snd tw) \<and> wityping \<Gamma> (snd tw))  
         \<and> (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2  (i, snd tw))\<rbrace>"
  apply (rule Conj2)
   apply (rule Conseq'[rotated])
     apply (rule pre_nand_conc_hoare3_without)
  apply (simp add: nand_seq_hoare_next_time_aux)
   apply simp
  using Conseq' pre_nand_conc_hoare3_without by fastforce
  
lemma nand3_conc_wt:
  " conc_wt \<Gamma> ( process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  apply (intro conc_wt.intros)
  apply (intro seq_wt.intros)
  apply (intro bexp_wt.intros)
  by (metis bexp_wt.intros(3) vector_type_nand3_axioms vector_type_nand3_def)+

lemma nand3_seq_wt:
  "seq_wt \<Gamma> (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  using nand3_conc_wt by blast

(* lemma nand_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace>
        nand3
     \<lbrace>\<lambda>tw. (nand_inv (next_time_world tw, snd tw)  \<and> nand_inv2  (next_time_world tw, snd tw)) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule Conj2)
   apply (rule nand_conc_hoare3_without)
  apply (rule strengthen_pre_conc_hoare)
   prefer 2
  unfolding nand3_def apply (rule single_conc_stmt_preserve_wityping_hoare)
   apply (rule nand3_seq_wt)
  apply blast
  done
 *)

lemma nand_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> 
        nand3 
     \<lbrace>\<lambda>tw. (\<forall>i\<in>{fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd (i, snd tw))) 
         \<and> (\<forall>i\<in>{fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw))\<rbrace>"
  apply (rule Conj2)
   apply (rule Conseq'[rotated])
     apply (rule nand_conc_hoare3_without)
    apply simp
   apply simp
  apply (rule Conseq'[rotated])
    apply (rule nand_conc_hoare3_without)
  by auto
  
lemma nand_conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> 
          nand3 
      \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace>"
  apply (rule While)
  apply (rule Conseq')
    prefer 2
    apply (rule nand_conc_hoare3)
   apply blast
  unfolding snd_conv apply blast
  done

lemma nand_conc_sim2':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule Conseq_sim[rotated])
  by (rule nand_conc_sim') blast+

lemma init_sat_nand_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  (* unfolding snd_conv using nand_seq_hoare_next_time0 *)
  unfolding snd_conv
  apply (rule Conseq2[rotated])
    apply (rule nand_seq_hoare_next_time0)
  using greaterThanAtMost_iff next_time_world_at_least apply blast
  by simp

lemma init_sat_nand_inv2:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. nand_inv2 tw \<and> wityping \<Gamma> (snd tw))"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv
  apply (rule Conseq2[rotated])
    apply (rule nand_seq_hoare_next_time4)
   apply (simp add: next_time_world_at_least)
  by simp

lemma init_sat_nand_inv_comb:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. (nand_inv tw \<and>  wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_nand_inv)
  apply (rule ConseqI_sim[rotated])
    apply (rule init_sat_nand_inv2)
   apply simp
  apply simp
  done

lemma nand_correctness:
  assumes "sim_fin w (i + 1) nand3 tw'" and "wityping \<Gamma> w"
  shows "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i)  (lof_wline tw' B i)"
proof -
  obtain tw where "init_sim (0, w) nand3 tw" and  "tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf nand3"
    unfolding conc_stmt_wf_def nand3_def by auto
  moreover have "nonneg_delay_conc nand3"
    unfolding nand3_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_inv_comb] by auto
  hence "(nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw"
    using \<open>init_sim (0, w) nand3 tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "nand_inv tw \<and> wityping \<Gamma> (snd tw)" and "nand_inv2 tw"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'] \<open>conc_stmt_wf nand3\<close> \<open>nonneg_delay_conc nand3\<close>
    by auto
  ultimately have "nand_inv tw' \<and> wityping \<Gamma> (snd tw)"
    using \<open>tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
    unfolding nand_inv_def by auto
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    by (metis less_add_one)
qed

lemma nand_inv_next_time_inert:
  assumes "nand_inv tw"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Lty ki len"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. nand_inv (j, snd tw')"
proof (rule)
  fix j
  assume "j \<in> {get_time tw'<..next_time_world tw'}"
  have "fst tw < j"
    by (metis \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> fst_conv greaterThanAtMost_iff tw'_def worldline_inert_upd2_def)
  have "\<forall>i < j. lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < j"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < j - 1 \<or> i = j - 1"
      using \<open>fst tw < j\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
        using assms(1) unfolding nand_inv_def by auto
      have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
      proof (cases "i + 1 < fst tw")
        case True
        hence "lof_wline tw' C (i + 1) = lof_wline tw C (i + 1)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          by auto
        also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
          using `lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)`
          by auto
        also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          by auto
        finally show ?thesis
          by auto
      next
        case False
        hence "i + 1 = fst tw"
          using \<open>i < get_time tw\<close> by linarith
        show "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
          case True
          hence "lof_wline tw' C (i + 1) = lof_wline tw C (fst tw)"
            using `i + 1 = fst tw`
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
          also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
            using `lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)`
            `i + 1 = fst tw` by auto
          also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
            using `i + 1 = fst tw` by auto
          finally show ?thesis
            by auto
        next
          case False
          hence "wline_of tw C (fst tw) \<noteq> v" and "wline_of tw C (fst tw + 1) = v"
            by auto
          let ?time = "GREATEST n. n \<le> fst tw + 1
                                 \<and> wline_of tw C (n - 1) \<noteq> v
                                 \<and> wline_of tw C n = v"
          have "?time = fst tw + 1"
            using False by (intro Greatest_equality) auto
          hence "wline_of tw' C (i + 1) = wline_of tw C (fst tw)"
            using False \<open>i + 1 = get_time tw\<close> unfolding tw'_def worldline_inert_upd2_def
            worldline_inert_upd_def comp_def by auto
          have "lof_wline tw C (fst tw) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)"
            using `lof_wline tw C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A i) (lof_wline tw B i)` `i
            + 1 = fst tw` by auto
          also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
            using `i + 1 = fst tw` by auto
          finally show ?thesis
            using \<open>wline_of tw' C (i + 1) = wline_of tw C (get_time tw)\<close> by auto
        qed
      qed }
    moreover
    { assume " fst tw \<le> i \<and> i < j - 1"
      hence "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
        using unchanged_until_next_time_world 
        by (smt \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> dual_order.strict_trans1 fst_conv
        greaterThanAtMost_iff le_add1 less_diff_conv not_le tw'_def worldline_inert_upd2_def)
      moreover have "lof_wline tw' A i = lof_wline tw' A (fst tw)" and "lof_wline tw' B i = lof_wline tw' B (fst tw)"
        by (metis (no_types, lifting) \<open>get_time tw \<le> i \<and> i < j - 1\<close> \<open>i < j\<close> \<open>j \<in> {get_time
        tw'<..next_time_world tw'}\<close> dual_order.strict_trans1 fst_conv greaterThanAtMost_iff tw'_def
        unchanged_until_next_time_world worldline_inert_upd2_def)+
      moreover have "lof_wline tw' C (fst tw + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
      proof (cases " wline_of tw C (get_time tw) = v \<or>  wline_of tw C (get_time tw + 1) \<noteq> v")
        case True
        hence "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "lval_of v = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          prefer 2
          apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(3))
          using assms(3) by auto
        also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by blast
      next
        case False
        hence "wline_of tw C (get_time tw) \<noteq> v" and
              "wline_of tw C (get_time tw + 1) = v"
          by blast+
        let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
        have "?time = fst tw + 1"
          using False
          by (intro Greatest_equality) auto
        hence "wline_of tw' C (fst tw + 1) =  v"
          using False unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          comp_def by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "lval_of v = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
          unfolding beval_world_raw2_def
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          prefer 2
          apply (metis beval_cases(1) comp_def state_of_world_def val.sel(3))
          using assms(3) by auto
        also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by auto
      qed
      ultimately have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        by auto }
    moreover
    { assume "i = j - 1"
      hence "lof_wline tw' C (i + 1) = lof_wline tw' C j"
        using \<open>i < j\<close>  by simp
      also have "... = lof_wline tw' C (fst tw + 1)"
      proof (cases "wline_of tw C (get_time tw) =  v \<or> wline_of tw C (get_time tw + 1) \<noteq>  v")
        case True
        hence "wline_of tw' C j = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def comp_def
          using `fst tw < j`
          by (smt add.commute fst_conv less_SucE next_time_world_at_least order.asym plus_1_eq_Suc
          snd_conv)
        also have "... = wline_of tw' C (fst tw + 1)"
          by (smt True dual_order.strict_iff_order not_add_less1 o_apply snd_conv tw'_def
          worldline_inert_upd2_def worldline_inert_upd_def)
        finally show ?thesis
          by auto
      next
        case False
        let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
        have "?time = fst tw + 1"
          using False by (intro Greatest_equality) auto
        hence "wline_of tw' C j = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def comp_def
          using \<open>get_time tw < j\<close> by auto
        also have "... = wline_of tw' C (fst tw + 1)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def comp_def
          using `fst tw < j` `?time = fst tw + 1` by auto
        finally show ?thesis
          by auto          
      qed
      finally have "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
        by auto
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
      proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
        case True
        hence "wline_of tw' C (fst tw + 1) = v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def comp_def
          by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "lval_of ... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
           prefer 2
          apply (metis beval_cases(1) comp_def state_of_world_def val.sel(3))
          using assms(3) by auto
        also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by auto
      next
        case False
        let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
        have "?time = fst tw + 1"
          using False by (intro Greatest_equality) auto
        hence "wline_of tw' C (fst tw + 1) =  v"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def comp_def by auto
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
          using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
          by auto
        have "lval_of ... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          prefer 2
          apply (metis beval_cases(1) comp_def state_of_world_def val.sel(3))
          using assms(3) by auto
        also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A (fst tw)) (lof_wline tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          using \<open>wline_of tw' C (get_time tw + 1) = v\<close> by blast
      qed
      also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        by (smt \<open>i < get_time tw \<Longrightarrow> lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A
        i) (lof_wline tw' B i)\<close> \<open>i < j\<close> \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> calculation
        fst_conv greaterThanAtMost_iff linordered_semidom_class.add_diff_inverse not_le
        trans_less_add1 tw'_def unchanged_until_next_time_world worldline_inert_upd2_def)
      finally have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
        by auto }
    ultimately show "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
      by auto
  qed
  thus "nand_inv (j, snd tw')"
    unfolding nand_inv_def by auto
qed

lemma nand_inv_next_time0_inert:
  assumes "fst tw = 0"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Lty ki len"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "nand_inv tw"
    using assms(1) unfolding nand_inv_def by auto
  from nand_inv_next_time_inert[OF this] show ?thesis
    unfolding tw'_def using assms 
    by (simp add: next_time_world_at_least)
qed

lemma pre_nand_seq_hoare_next_time_inert:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] 
        (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) 
     [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule AssignI2, blast)
  using nand_inv_next_time_inert beval_world_raw2_type vector_type_nand3_axioms vector_type_nand3_def
  by (metis greaterThanAtMost_iff next_time_world_at_least order_refl snd_conv
  worldline_inert_upd2_def worldline_inert_upd_preserve_wityping)

lemma nand_seq_hoare_next_time_inert:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] 
        (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) 
     [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[rotated])
    apply (rule pre_nand_seq_hoare_next_time_inert)
  apply (simp add: nand_seq_hoare_next_time_aux)
  by simp

lemma seq_wt_nand3:
  "seq_wt \<Gamma> (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  by (metis bexp_wt.intros(3) bexp_wt.intros(9) seq_wt.intros(5) vector_type_nand3_axioms vector_type_nand3_def)

lemma nand_seq_hoare_wityping:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] 
        (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) 
     [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[rotated])
    apply (rule pre_nand_seq_hoare_next_time_inert)
   apply (simp add: nand_seq_hoare_next_time_aux)
  by simp

lemma nand_seq_hoare_next_time0_inert:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule AssignI2)
  using nand_inv_next_time0_inert beval_world_raw2_type vector_type_nand3_axioms vector_type_nand3_def
  by auto

lemma nand_seq_hoare_wityping0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule nand_seq_hoare_next_time0_inert)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule seq_wt_nand3)
  done

lemma nand_inv2_next_time_inert:
  fixes tw
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Lty ki len"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. nand_inv2 (j, snd tw')"
  unfolding nand_inv2_def
proof (rule, rule)
  fix j :: nat
  assume "disjnt {A, B} (event_of (j, snd tw'))"
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  have "fst tw < j"
    using \<open>j \<in> {get_time tw' <..next_time_world tw'}\<close> greaterThanAtMost_iff 
    by (simp add: tw'_def worldline_inert_upd2_def)
  have "wline_of tw' A j = wline_of tw A j"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... = wline_of tw A (j - 1)"
    using \<open>disjnt {A, B} (event_of (j, snd tw'))\<close> \<open>fst tw < j\<close>
    unfolding event_of_alt_def
    by (auto simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... = wline_of tw A (fst tw)"
  proof -
    have "fst tw' \<le> j - 1" and "j - 1 < j"
      using \<open>fst tw < j\<close> 
      apply (metis Suc_eq_plus1 diff_add_inverse less_imp_Suc_add linordered_field_class.sign_simps(2) not_add_less1 not_le_imp_less prod.sel(1) tw'_def worldline_inert_upd2_def)
      using \<open>get_time tw < j\<close> by auto
    hence "wline_of tw' A (j - 1) = wline_of tw' A (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"]
      by (smt \<open>j \<in> {get_time tw' <..next_time_world tw'}\<close> comp_apply dual_order.strict_trans1 fst_conv
          greaterThanAtMost_iff sig.simps(4) snd_conv tw'_def unchanged_until_next_time_world
          worldline_inert_upd2_def worldline_inert_upd_def)
    moreover have "wline_of tw' A (j - 1) = wline_of tw A (j - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "wline_of tw' A (fst tw') = wline_of tw A (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      by (simp add: tw'_def worldline_inert_upd2_def)
  qed
  finally have 0: "wline_of tw' A j = wline_of tw A (fst tw)"
    by auto
  have "wline_of tw' B j = wline_of tw B j"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... = wline_of tw B (j - 1)"
    using \<open>disjnt {A, B} (event_of (j, snd tw'))\<close> \<open>fst tw < j\<close>
    unfolding event_of_alt_def
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... = wline_of tw B (fst tw)"
  proof -
    have "fst tw' \<le> j - 1" and "j - 1 < j"
      using \<open>fst tw < j\<close> 
       apply (simp add: Suc_leI tw'_def worldline_inert_upd2_def)
      using \<open>get_time tw < j\<close> by linarith
    hence "wline_of tw' B (j - 1) = wline_of tw' B (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] 
      by (smt \<open>j \<in> {get_time tw' <..next_time_world tw'}\<close> calculation comp_apply
      dual_order.strict_trans1 fst_conv greaterThanAtMost_iff less_imp_le_nat snd_conv tw'_def
      unchanged_until_next_time_world worldline_inert_upd2_def worldline_inert_upd_def)
    moreover have "wline_of tw' B (j - 1) = wline_of tw B (j - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "wline_of tw' B (fst tw') = wline_of tw B (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      by (simp add: tw'_def worldline_inert_upd2_def)
  qed
  finally have 1: "wline_of tw' B j = wline_of tw B (fst tw)"
    by auto
  { fix i
    assume "j \<le> i"
    hence "wline_of tw' C (i + 1) = v"
    proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
      case True
      thus "wline_of tw' C (i + 1) = v"
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
        using `fst tw < j`  using \<open>j \<le> i\<close> by auto
    next
      case False
      let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
      have "?time = fst tw + 1"
        using False by (auto intro!:Greatest_equality)
      thus ?thesis
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
        using `fst tw < j`  using \<open>j \<le> i\<close> by auto
    qed
    have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
      using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
      by auto
    have "lval_of v = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw A (fst tw)) (lof_wline tw B (fst tw))"
      apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
       prefer 2
      apply (metis beval_cases(1) comp_def state_of_world_def val.sel(3))
      using assms(2) by auto
    also have "... = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A j) (lof_wline tw' B j)"
      using 0 1 by auto
    finally have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A j) (lof_wline tw' B j)"
      using \<open>wline_of tw' C (i + 1) = v\<close> by blast }
  thus "\<forall>i\<ge>get_time (j, snd tw').
            lof_wline (j, snd tw') C (i + 1) =
            map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline (j, snd tw') A (get_time (j, snd tw'))) (lof_wline (j, snd tw') B (get_time (j, snd tw')))"
    by auto
qed

lemma nand_seq_hoare_next_time4_inert:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)", rotated 1], rule AssignI2, blast)
  using nand_inv2_next_time_inert beval_world_raw2_type vector_type_nand3_axioms vector_type_nand3_def
  by auto
  
lemma nand_seq_hoare2_wityping:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] 
          Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 
      [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule AssignI2, blast)
  by (metis beval_world_raw2_type nand_inv2_next_time_inert snd_conv vector_type_nand3_axioms vector_type_nand3_def worldline_inert_upd2_def worldline_inert_upd_preserve_wityping)

lemma nand_conc_hoare3_inert_without:
  "\<turnstile> \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> 
        nand 
     \<lbrace>\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv   (i, snd tw) \<and> wityping \<Gamma> (snd tw))  
         \<and> (\<forall>i \<in> {fst tw <.. next_time_world tw}. nand_inv2  (i, snd tw))\<rbrace>"
  unfolding nand_def
  apply (rule Single)
   apply (rule Conj)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
    apply (rule Conseq2[rotated])
      apply (rule nand_seq_hoare_next_time_inert)
     apply simp
    apply simp
   apply (rule strengthen_precondition)           
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition2)
   apply (rule Conseq2[rotated])
     apply(rule nand_seq_hoare_next_time4_inert)
    apply simp
   apply simp
  apply (rule, rule, rule)
  using nand_conc_hoare'  apply (simp add: nand_seq_hoare_next_time_aux)
  using nand_conc_hoare2 by simp

(* lemma nand_preserve_wityping:
  " \<turnstile> \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace> nand \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace>"
  unfolding nand_def using single_conc_stmt_preserve_wityping_hoare
  using conc_wt.intros(1) seq_wt_nand3
  by (simp add: single_conc_stmt_preserve_wityping_hoare)
*)

lemma nand_conc_hoare3_inert:
  "\<turnstile> \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. (nand_inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2  (i, snd tw)\<rbrace>"
  apply (rule Conseq'[rotated])
  apply (rule nand_conc_hoare3_inert_without)
  by auto

lemma nand_conc_sim'_inert:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace>"
  apply (rule While)
  unfolding snd_conv 
  apply (rule nand_conc_hoare3_inert)
  done

lemma nand_conc_sim2'_inert:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule Conseq_sim[rotated])
  apply (rule nand_conc_sim'_inert)
  by blast+

lemma init_sat_nand_inv_inert:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand (\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding nand_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv apply (rule nand_seq_hoare_wityping0)
  done

lemma init_sat_nand_inv2_inert:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) nand (\<lambda>tw. nand_inv2 tw \<and> wityping \<Gamma> (snd tw))"
  unfolding nand_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv   
  apply (rule Conseq2[rotated])
    apply (rule nand_seq_hoare2_wityping)
  using greaterThanAtMost_iff next_time_world_at_least apply blast
  by simp

lemma init_sat_nand_inv_comb_inert:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand (\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_nand_inv_inert)
  apply (rule ConseqI_sim[where P="\<lambda>tw. wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. nand_inv2 tw \<and> wityping \<Gamma> (snd tw)"])
  apply (simp, rule init_sat_nand_inv2_inert, simp)
  done

lemma nand_correctness_inert:
  assumes "sim_fin w (i + 1) nand tw'" and "wityping \<Gamma> w"
  shows   "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
proof -
  obtain tw where "init_sim (0, w) nand tw" and  "tw, i + 1, nand \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf nand"
    unfolding conc_stmt_wf_def nand_def by auto
  moreover have "nonneg_delay_conc nand"
    unfolding nand_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand (\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_inv_comb_inert] by auto
  hence "nand_inv tw \<and> nand_inv2 tw \<and> wityping \<Gamma> (snd tw)"
    using \<open>init_sim (0, w) nand tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "nand_inv tw" and "nand_inv2 tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (nand_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'_inert] \<open>conc_stmt_wf nand\<close> \<open>nonneg_delay_conc nand\<close>
    by auto
  ultimately have "nand_inv tw' \<and> wityping \<Gamma> (snd tw')"
    using \<open>tw, i + 1, nand \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i) (lof_wline tw' B i)"
    unfolding nand_inv_def by auto
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    by (metis less_add_one)
qed

end

lemma tyenv_possibilities_bexp_wt:
  assumes " bexp_wt \<Gamma>' (Bnand (Bsig A) (Bsig B)) (\<Gamma>' C) "
  shows "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
proof (rule bexp_wt_cases(4)[OF assms])
  assume "bexp_wt \<Gamma>' (Bsig A) (\<Gamma>' C)"
  hence "\<Gamma>' C = \<Gamma>' A"
    using bexp_wt.cases by auto
  assume "bexp_wt \<Gamma>' (Bsig B) (\<Gamma>' C)"
  hence "\<Gamma>' C = \<Gamma>' B"
    using bexp_wt.cases by auto
  obtain ki len where "\<Gamma>' C = Bty \<or> \<Gamma>' C = Lty ki len"
    using ty.exhaust by meson
  moreover
  { assume "\<Gamma>' C = Bty"
    hence "\<Gamma>' A = Bty" and "\<Gamma>' B = Bty"
      using \<open>\<Gamma>' C = \<Gamma>' A\<close> \<open>\<Gamma>' C = \<Gamma>' B\<close> by auto
    hence "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
      using \<open>\<Gamma>' C = Bty\<close> by auto }
  moreover
  { assume "\<Gamma>' C = Lty ki len"
    hence "\<Gamma>' A = Lty ki len" and "\<Gamma>' B = Lty ki len"
      using \<open>\<Gamma>' C = \<Gamma>' A\<close> \<open>\<Gamma>' C = \<Gamma>' B\<close> by auto
    hence "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
      using \<open>\<Gamma>' C = Lty ki len\<close> by auto }
  ultimately show ?thesis
    by auto
qed

lemma tyenv_possibilities_seq_wt:
  assumes "seq_wt \<Gamma>' (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  shows "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
  apply (rule seq_wt_cases(4)[OF assms])
  apply (rule tyenv_possibilities_bexp_wt)
  by simp

lemma tyenv_possibilities_conc_wt:
  assumes "conc_wt \<Gamma>' nand3"
  shows "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
  using assms unfolding nand3_def
  by (metis conc_stmt.sel(4) conc_stmt.simps(4) conc_wt.cases tyenv_possibilities_seq_wt)

theorem nand3_correctness:
  assumes "conc_wt \<Gamma>' nand3"
  assumes "sim_fin w (i + 1) nand3 tw'" and "wityping \<Gamma>' w"
  shows   " (\<Gamma>' A \<noteq> Bty \<longrightarrow> lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i)  (lof_wline tw' B i))
          \<or> (\<Gamma>' A = Bty \<longrightarrow> bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i))"
proof -
  obtain ki len where "\<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
    using tyenv_possibilities_conc_wt[OF assms(1)] by auto
  moreover
  { assume "\<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty"
    then interpret l1: scalar_type_nand3 \<Gamma>' unfolding scalar_type_nand3_def .
    have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
      using l1.nand_correctness[OF assms(2-3)] by auto
    hence ?thesis
      using \<open>\<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty\<close> by auto }
  moreover
  { assume "\<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
    then interpret l2: vector_type_nand3 len ki \<Gamma>'
      by unfold_locales auto
    have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i)  (lof_wline tw' B i)"
      using l2.nand_correctness[OF assms(2-3)] by auto
    hence ?thesis
      using \<open>\<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len\<close> by auto }
  ultimately show ?thesis
    by auto
qed

lemma tyenv_possibilities_seq_wt_inert:
  assumes "seq_wt \<Gamma>' (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  shows "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
  apply (rule seq_wt_cases(5)[OF assms])
  apply (rule tyenv_possibilities_bexp_wt)
  by simp

lemma tyenv_possibilities_conc_wt_inert:
  assumes "conc_wt \<Gamma>' nand"
  shows "\<exists>ki len. \<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
  using assms unfolding nand_def
  by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases tyenv_possibilities_seq_wt_inert)

theorem nand_correctness:
  assumes "conc_wt \<Gamma>' nand"
  assumes "sim_fin w (i + 1) nand3 tw'" and "wityping \<Gamma>' w"
  shows   " (\<Gamma>' A \<noteq> Bty \<longrightarrow> lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i)  (lof_wline tw' B i))
          \<or> (\<Gamma>' A = Bty \<longrightarrow> bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i))"
proof -
  obtain ki len where "\<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty \<or> \<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
    using tyenv_possibilities_conc_wt_inert[OF assms(1)] by auto
  moreover
  { assume "\<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty"
    then interpret l1: scalar_type_nand3 \<Gamma>' unfolding scalar_type_nand3_def .
    have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
      using l1.nand_correctness[OF assms(2-3)] by auto
    hence ?thesis
      using \<open>\<Gamma>' A = Bty \<and> \<Gamma>' B = Bty \<and> \<Gamma>' C = Bty\<close> by auto }
  moreover
  { assume "\<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len"
    then interpret l2: vector_type_nand3 len ki \<Gamma>'
      by unfold_locales auto
    have "lof_wline tw' C (i + 1) = map2 (\<lambda>x y. x \<longrightarrow> \<not> y) (lof_wline tw' A i)  (lof_wline tw' B i)"
      using l2.nand_correctness[OF assms(2-3)] by auto
    hence ?thesis
      using \<open>\<Gamma>' A = Lty ki len \<and> \<Gamma>' B = Lty ki len \<and> \<Gamma>' C = Lty ki len\<close> by auto }
  ultimately show ?thesis
    by auto
qed

end