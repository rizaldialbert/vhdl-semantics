(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Hoare3
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
  "nand_inv \<equiv> (\<lambda>tw. bval_of_wline tw C (fst tw) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw - 1) \<and> bval_of_wline tw B (fst tw - 1)))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bval_of_wline tw C i \<longleftrightarrow> bval_of_wline tw C (fst tw)))"

lemma nand_inv_next_time:
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "nand_inv (fst tw' + 1, snd tw')"
proof -
  have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig A) (Bsig B)) v"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "bval_of_wline tw' C (fst tw + 1) \<longleftrightarrow> bval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
    apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)    
    apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
    using assms by auto
  finally show ?thesis
    unfolding nand_inv_def 
    by (metis (no_types, lifting) add_diff_cancel_right' comp_apply fst_conv less_add_one snd_conv
    tw'_def worldline_upd2_before_dly worldline_upd2_def)
qed

lemma nand_inv2_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "nand_inv2 (fst tw' + 1, snd tw')"
proof -
  have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig A) (Bsig B)) v"
    using assms(1) unfolding beval_world_raw2_def by auto
  { assume "disjnt {A, B} (event_of (fst tw' + 1, snd tw'))"
    have "\<And>j. fst tw + 1 < j \<Longrightarrow> bval_of_wline tw' C j \<longleftrightarrow> bval_of_wline tw' C (fst tw + 1)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto }
  thus "nand_inv2 (fst tw' + 1, snd tw')"
    unfolding nand_inv2_def by (simp add: tw'_def worldline_upd2_def)
qed
 
lemma pre_nand_conc_hoare':
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  have "bval_of_wline tw C (fst tw + 1) \<longleftrightarrow> bval_of_wline tw C (fst tw)"
    using `nand_inv2 tw` `disjnt {A, B} (event_of tw)` unfolding nand_inv2_def 
    by (simp add: next_time_world_at_least) 
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw - 1) \<and> bval_of_wline tw B (fst tw - 1))"
    using `nand_inv tw` unfolding nand_inv_def by auto
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
    using `disjnt {A, B} (event_of tw)`  unfolding event_of_alt_def 
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "nand_inv (fst tw + 1, snd tw)"
    unfolding nand_inv_def by auto
qed

lemma nand_conc_hoare2:
  "\<And>tw. nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv2 (fst tw + 1, snd tw)"
  unfolding nand_inv2_def by auto

definition "nand_wityping \<equiv> \<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)"
definition "nand_wityping2 \<equiv> \<lambda>tw. nand_inv2 tw \<and> wityping \<Gamma> (snd tw)"

lemma conc_stmt_wf_nand3:
  "conc_stmt_wf nand3"
  unfolding nand3_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_nand3:
  "nonneg_delay_conc nand3"
  unfolding nand3_def by auto

lemma nand_conc_sim2':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp_conc nand3 (\<lambda>tw. nand_wityping  (fst tw + 1, snd tw) \<and> 
                                                   nand_wityping2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp_conc_is_pre, rule conc_stmt_wf_nand3, rule nonneg_delay_conc_nand3, simp)
  unfolding nand3_def wp_conc_single One_nat_def wp_trans[OF zero_less_Suc[of "0"]] 
proof (fold One_nat_def, rule, rule, unfold if_bool_eq_conj, rule, rule_tac[!] impI, rule_tac[2] allI, rule_tac[2] impI, rule_tac[!] conjI)
  fix tw x
  assume "(nand_wityping tw \<and> nand_wityping2 tw)"
  assume "\<not> disjnt {A, B} (event_of tw)"
  assume beval_pre: "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) x"
  have "type_of x = Bty"
    using \<open>(nand_wityping tw \<and> nand_wityping2 tw)\<close> beval_pre beval_world_raw2_type scalar_type_nand3_axioms
    unfolding nand_wityping_def scalar_type_nand3_def by fastforce
  let ?tw' = "tw [C, 1 :=\<^sub>2 x]"
  have "nand_inv (fst ?tw' + 1, snd ?tw')" and "nand_inv2 (fst ?tw' + 1, snd ?tw')"
    using nand_inv_next_time[OF beval_pre `type_of x = Bty`] nand_inv2_next_time[OF beval_pre `type_of x = Bty`]
    by auto
  thus "nand_wityping  (fst ?tw' + 1, snd ?tw')" and "nand_wityping2 (fst ?tw' + 1, snd ?tw')"
    unfolding nand_wityping_def nand_wityping2_def using worldline_upd_preserve_wityping 
    by (metis \<open>(nand_wityping tw \<and> nand_wityping2 tw)\<close> \<open>type_of x = Bty\<close>
    nand_wityping_def scalar_type_nand3_axioms scalar_type_nand3_def snd_conv worldline_upd2_def)+
next
  fix tw
  assume "(nand_wityping tw \<and> nand_wityping2 tw)"
    and  "disjnt {A, B} (event_of tw)"
  hence "nand_inv (fst tw + 1, snd tw)" and "nand_inv2 (fst tw + 1, snd tw)"
    using pre_nand_conc_hoare' nand_conc_hoare2 by (simp add: nand_wityping2_def nand_wityping_def)+
  thus "nand_wityping  (fst tw + 1, snd tw)" and  "nand_wityping2 (fst tw + 1, snd tw)"
    unfolding nand_wityping_def nand_wityping2_def using worldline_upd_preserve_wityping
    using \<open>(nand_wityping tw \<and> nand_wityping2 tw)\<close> nand_wityping_def by auto 
qed

text \<open>Initialisation preserves the invariant\<close>

lemma init_sat_nand_inv:
  "init_sim2_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 nand_wityping"
  unfolding nand3_def
  apply (rule AssignI_suc, rule SingleI, rule Conseq2[where Q="\<lambda>tw. nand_wityping (fst tw + 1, snd tw)" and P="wp (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) (\<lambda>tw. nand_wityping (fst tw + 1, snd tw))", rotated])
    apply (rule wp_is_pre, simp, simp)
  unfolding One_nat_def wp_trans[OF zero_less_Suc[of "0"]] using nand_inv_next_time 
  by (metis One_nat_def beval_world_raw2_typeB nand_wityping_def scalar_type_nand3_axioms
  scalar_type_nand3_def snd_conv worldline_upd2_def worldline_upd_preserve_wityping)

lemma init_sat_nand_inv2:
  "init_sim2_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 nand_wityping2"
  unfolding nand3_def
  apply (rule AssignI_suc, rule SingleI, rule Conseq2[where Q="\<lambda>tw. nand_wityping2 (fst tw + 1, snd tw)" and P="wp (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) (\<lambda>tw. nand_wityping2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp_is_pre, simp, simp)
  unfolding One_nat_def wp_trans[OF zero_less_Suc[of "0"]] using nand_inv2_next_time 
  by (metis (mono_tags) One_nat_def beval_world_raw2_type nand_wityping2_def
  scalar_type_nand3_axioms scalar_type_nand3_def snd_conv worldline_upd2_def
  worldline_upd_preserve_wityping)
 
lemma init_sat_nand_inv_comb:
  "init_sim2_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw)"
  by (rule ConjI_suc_sim)(rule init_sat_nand_inv, rule init_sat_nand_inv2)

lemma nand_correctness:
  assumes "sim_fin w (i + 1) nand3 tw'" and "wityping \<Gamma> w"
  shows "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
proof -
  have "sim_fin2 w (i + 1) nand3 tw'"
    using sim_fin_imp_sim_fin2[OF assms(1)] conc_stmt_wf_nand3 nonneg_delay_conc_nand3
    by auto
  obtain tw where "init_sim2 (0, w) nand3 tw" and  "tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'"
    using sim_fin2.cases[OF `sim_fin2 w (i + 1) nand3 tw'`]  by metis
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "init_sim2_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) nand3 (\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw)"
    using init_sim2_hoare_soundness[OF init_sat_nand_inv_comb] conc_stmt_wf_nand3 nonneg_delay_conc_nand3
    by auto
  hence "nand_wityping tw \<and> nand_wityping2 tw"
    using \<open>init_sim2 (0, w) nand3 tw\<close> fst_conv assms(2) unfolding init_sim2_valid_def
    by (metis snd_conv)
  hence "nand_wityping tw" and "nand_wityping2 tw"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'] conc_stmt_wf_nand3 nonneg_delay_conc_nand3
    by auto
  ultimately have "nand_wityping tw'"
    using \<open>tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  thus "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
    unfolding nand_wityping_def nand_inv_def using \<open>i + 1 = fst tw'\<close> by (metis
    add_diff_cancel_right')
qed

end