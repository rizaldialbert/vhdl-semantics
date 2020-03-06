(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Hoare_Typed
  imports VHDL_Hoare_Typed NAND_Femto
begin

subsection \<open>Proving @{term "nand3"}: NAND with transport delay \<close>

abbreviation "bval_of_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

locale scalar_type_nand3 =
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> A = Bty" and "\<Gamma> B = Bty" and "\<Gamma> C = Bty"
begin

text \<open>Invariant for NAND: at all times @{term "i"}, the signal @{term "C :: sig"} at @{term "i"} 
should be the NAND value of @{term "A :: sig"} and @{term "B :: sig"} at time @{term "i - 1"}.\<close>

definition nand_inv :: "sig assn2" where
  "nand_inv \<equiv> (\<lambda>tw. bval_of_wline tw C (fst tw) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw - 1) \<and> bval_of_wline tw B (fst tw - 1)))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bval_of_wline tw C i \<longleftrightarrow> bval_of_wline tw C (fst tw)))"

lemma nand_inv_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "nand_inv (fst tw' + 1, snd tw')"
proof -
  have bexpA: "bexp_wt \<Gamma> (Bsig A) Bty" and bexpB: "bexp_wt \<Gamma> (Bsig B) Bty" 
    using scalar_type_nand3_axioms unfolding scalar_type_nand3_def  by (metis bexp_wt.intros(3))+
  have "bval_of_wline tw' C (fst tw + 1) \<longleftrightarrow> bval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
    using eval_world_raw_bv[OF bexpA `wityping \<Gamma> (snd tw)`]  eval_world_raw_bv[OF bexpB `wityping \<Gamma> (snd tw)`] 
    unfolding v_def by (auto split:val.split)(metis val.distinct(1))+
  finally show ?thesis
    unfolding nand_inv_def  
    by (metis (no_types, lifting) add_diff_cancel_right' comp_apply fst_conv less_add_one snd_conv
    tw'_def worldline_upd2_before_dly worldline_upd2_def)
qed

lemma nand_inv2_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bnand (Bsig A) (Bsig B))" 
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "nand_inv2 (fst tw' + 1, snd tw')"
  using assms unfolding nand_inv2_def tw'_def worldline_upd2_def worldline_upd_def by auto 
 
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

lemma conc_stmt_wf_nand3:
  "conc_stmt_wf nand3"
  unfolding nand3_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_nand3:
  "nonneg_delay_conc nand3"
  unfolding nand3_def by auto

lemma nonneg_delay_conc_nand3':
  "nonneg_delay_conc ( process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  using nonneg_delay_conc_nand3 unfolding nand3_def by auto

lemma conc_wt_nand3:
  "conc_wt \<Gamma> nand3"
  unfolding nand3_def by (metis bexp_wt.intros(3) bexp_wt.intros(9) conc_wt.intros(1)
  scalar_type_nand3_axioms scalar_type_nand3_def seq_wt.intros(4))

lemma conc_wt_nand3':
  "conc_wt \<Gamma> ( process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  using conc_wt_nand3 unfolding nand3_def by auto

lemma nand_conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> nand3 (\<lambda>tw. nand_inv  (fst tw + 1, snd tw) \<and> 
                                                      nand_inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_nand3, rule nonneg_delay_conc_nand3, rule conc_wt_nand3, simp)
  unfolding nand3_def  wp3_conc_single'[OF conc_wt_nand3' nonneg_delay_conc_nand3'] wp3_fun.simps
  using nand_conc_hoare2 nand_inv2_next_time nand_inv_next_time pre_nand_conc_hoare' by presburger

text \<open>Initialisation preserves the invariant\<close>

lemma seq_wt_nand3':
  "seq_wt \<Gamma> (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  using conc_wt_nand3' by auto

lemma nonneg_delay_nand3:
  " nonneg_delay (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)"
  using nonneg_delay_conc_nand3' by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) nand3 (\<lambda>tw. nand_inv tw \<and> nand_inv2 tw)"
  unfolding nand3_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. nand_inv (fst tw + 1, snd tw) \<and> nand_inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_nand3' nonneg_delay_nand3], simp)
  unfolding wp3_fun.simps using nand_inv_next_time nand_inv2_next_time by blast

lemma nand_correctness:
  assumes "sim_fin2 w (i + 1) nand3 tw'" and "wityping \<Gamma> w"
  shows "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
  using grand_correctness[OF assms conc_stmt_wf_nand3 conc_wt_nand3 nonneg_delay_conc_nand3 nand_conc_sim2' init_sat_nand_inv_comb]
  unfolding nand_inv_def by (metis (no_types, lifting) add_diff_cancel_right' assms(1) sim_fin2.cases world_maxtime_lt_fst_tres)

end