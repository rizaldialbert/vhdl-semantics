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

text \<open>Invariant for NAND: at all times @{term "i"} less than @{term "fst tw :: nat"}, the signal 
@{term "C :: sig"} at @{term "i + 1"} should be the NAND value of @{term "A :: sig"} and 
@{term "B :: sig"} at time @{term "i"}.\<close>

definition nand_inv :: "sig assn2" where
  "nand_inv \<equiv> (\<lambda>tw. \<forall>i < fst tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i\<ge>fst tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))))"

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

lemma nand_seq_hoare_next_time0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0] Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where P="nand_inv" and Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)"])
  using nand_seq_hoare_next_time unfolding nand_inv_def by auto

lemma disjnt_AB_eq:
  "disjnt {A, B} s \<longleftrightarrow> (s = {} \<or> s = {C})"
  by (rule, metis Diff_UNIV Diff_insert0 Diff_single_insert UNIV_sig disjnt_insert1 empty_subsetI
  subset_singleton_iff) auto

lemma nand_conc_hoare':
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence *: "\<forall>i < fst tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
    unfolding nand_inv_def by auto
  have **: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. snd tw s i = snd tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  have ***: "(\<forall>i\<ge> fst tw. snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and>  snd tw B (fst tw)))"
    using \<open>nand_inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding nand_inv2_def by auto

  \<comment> \<open>obtain the value of A and B at time fst tw\<close>
  have "snd tw A (fst tw) = snd tw A (fst tw - 1)" and "snd tw B (fst tw) = snd tw B (fst tw - 1)"
    using \<open>disjnt {A, B} (event_of tw)\<close> unfolding event_of_alt_def 
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
 { fix i 
    assume "i < next_time_world tw"
    have "i < fst tw \<or> fst tw \<le> i" 
      by auto
    moreover
    { assume "i < fst tw"
      hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using * by auto }
    moreover
    { assume "fst tw \<le> i"
      hence "snd tw C (i + 1) \<longleftrightarrow> snd tw C (fst tw + 1)"
        using *** by auto
      also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
        using *** \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        using ** \<open>i < next_time_world tw\<close> \<open>fst tw \<le> i\<close> less_imp_le_nat by blast
      finally have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
        by auto }
    ultimately have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
      by auto }
  hence "\<And>i. i < next_time_world tw \<Longrightarrow> snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
    by auto
  thus "nand_inv (next_time_world tw, snd tw)"
    unfolding nand_inv_def by auto
qed

lemma nand_conc_hoare2: 
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv2 (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence 0: "(\<forall>i\<ge>fst tw. snd tw C (i + 1) = (\<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))))"
    unfolding nand_inv2_def by auto  
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. snd tw s i = snd tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  let ?t' = "next_time_world tw"
  { assume "disjnt {A, B} (event_of (next_time_world tw, snd tw))" 
    hence *: "snd tw A ?t' = snd tw A (?t' - 1)" and **: "snd tw B ?t' = snd tw B (?t' - 1)"
      unfolding event_of_alt_def  by (smt diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "?t' \<le> i"
      hence "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
        using 0 \<open>fst tw < ?t'\<close> by auto
      moreover have "snd tw A (fst tw) = snd tw A (?t' - 1)" and "snd tw B (fst tw) = snd tw B (?t' - 1)"
        using 1 
        by (metis (no_types, lifting) One_nat_def Suc_leI \<open>get_time tw < next_time_world tw\<close>
        add_le_cancel_right diff_add diff_less discrete gr_implies_not_zero neq0_conv zero_less_one)+
      ultimately have "snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A ?t' \<and> snd tw B ?t')"
        using * ** by auto
    }
    hence "(\<forall>i\<ge>?t'. snd tw C (i + 1) = (\<not> (snd tw A ?t' \<and> snd tw B ?t')))"
      by auto }
  thus "nand_inv2 (next_time_world tw, snd tw)"
    unfolding nand_inv2_def by auto
qed

lemma nand_inv2_next_time:
  fixes tw
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))]"
  shows   "nand_inv2 (next_time_world tw', snd tw')"
proof -
  { assume "disjnt {A, B} (event_of (next_time_world tw', snd tw'))"
    let ?t' = "next_time_world tw'"
    have "fst tw' < ?t'"
      using next_time_world_at_least by blast
    moreover have "fst tw = fst tw'"
      unfolding tw'_def unfolding worldline_upd2_def by auto
    ultimately have "fst tw < ?t'"
      by auto
    have *: "\<And>s. s \<in> {A, B} \<Longrightarrow> snd tw' s ?t' \<longleftrightarrow> snd tw s (fst tw)"
    proof -
      fix s
      assume "s \<in> {A, B}"    
      hence "snd tw' s ?t' \<longleftrightarrow> snd tw s ?t'"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> snd tw s (?t' - 1)"
        using \<open>disjnt {A, B} (event_of (next_time_world tw', snd tw'))\<close> \<open>fst tw < ?t'\<close>
        unfolding event_of_alt_def 
        by (smt \<open>s \<in> {A, B}\<close> disjnt_AB_eq disjnt_iff fst_conv gr_implies_not_zero mem_Collect_eq
        singletonI snd_conv tw'_def worldline_upd2_def worldline_upd_def)
      also have "... \<longleftrightarrow> snd tw s (fst tw)"
      proof -
        have "fst tw' \<le> ?t' - 1" and "?t' - 1 < ?t'"
          using \<open>fst tw' < ?t'\<close> by auto
        hence "snd tw' s (?t' - 1) = snd tw' s (fst tw')"
          using unchanged_until_next_time_world[where tw="tw'"] by blast
        moreover have "snd tw' s (?t' - 1) = snd tw s (?t' - 1)"
          unfolding tw'_def worldline_upd2_def worldline_upd_def using  \<open>s \<in> {A, B}\<close> by auto
        moreover have "snd tw' s (fst tw') = snd tw s (fst tw')"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        ultimately show ?thesis
          using \<open>fst tw = fst tw'\<close> by auto
      qed
      finally show "snd tw' s ?t' \<longleftrightarrow> snd tw s (fst tw)"
        by auto
    qed
    have "\<And>i. ?t' \<le> i \<Longrightarrow> snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A ?t' \<and> snd tw' B ?t')"
    proof -
      fix i 
      assume "?t' \<le> i"
      hence "snd tw' C (i + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
        using `fst tw < ?t'`
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
        unfolding beval_world_raw2_def beval_world_raw_def 
        by (simp add: state_of_world_def)
      also have "... \<longleftrightarrow> \<not> (snd tw' A ?t' \<and> snd tw' B ?t')"
        using * by auto
      finally show "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A ?t' \<and> snd tw' B ?t')"
        by auto
    qed }
  thus ?thesis
    unfolding nand_inv2_def by auto
qed

lemma nand_seq_hoare_next_time4:
  " \<turnstile> [\<lambda>tw. True] Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using nand_inv2_next_time by auto
  
lemma nand_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv  (next_time_world tw, snd tw)  \<and> nand_inv2  (next_time_world tw, snd tw)\<rbrace>"
  unfolding nand3_def
  apply (rule Single)
   apply (unfold conj_assoc)
   apply (rule compositional_conj)
    apply(rule nand_seq_hoare_next_time)
   apply (rule strengthen_precondition)
   apply(rule Conseq2[where P="\<lambda>tw. True"])
     apply simp
    apply (rule nand_seq_hoare_next_time4)
   apply simp
  apply (rule allI)
  apply (rule impI)
  apply (rule conjI)
   apply (erule nand_conc_hoare')
  apply (erule nand_conc_hoare2)
  done

lemma nand_conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace>"
  apply (rule While)
  apply (rule nand_conc_hoare3)
  done

lemma nand_conc_sim2':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>nand_inv\<rbrace>"
  by (rule Conseq_sim[where Q="\<lambda>tw. nand_inv tw \<and> nand_inv2 tw" and 
                            P="\<lambda>tw. nand_inv tw \<and> nand_inv2 tw"])
     (simp_all add: nand_conc_sim')  

text \<open>Initialisation preserves the invariant\<close>

lemma init_sat_nand_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) nand3 nand_inv"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule nand_seq_hoare_next_time0)
  done

lemma init_sat_nand_inv2: 
  "init_sim_hoare (\<lambda>tw. True) nand3 nand_inv2"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule nand_seq_hoare_next_time4)
  done

lemma init_sat_nand_inv_comb:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) nand3 (\<lambda>tw. nand_inv tw \<and> nand_inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_nand_inv)
  apply (rule ConseqI_sim[where P="\<lambda>tw. True" and Q="nand_inv2"])
  apply (simp, rule init_sat_nand_inv2, simp)
  done

lemma nand_correctness:
  assumes "sim_fin w (i + 1) nand3 tw'"
  shows "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
proof -
  obtain tw where "init_sim (0, w) nand3 = tw" and  "tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'" 
    using premises_sim_fin_obt[OF assms] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf nand3"
    unfolding conc_stmt_wf_def nand3_def by auto
  moreover have "nonneg_delay_conc nand3"
    unfolding nand3_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0) nand3 (\<lambda>tw. nand_inv tw \<and> nand_inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_inv_comb] by auto
  hence "nand_inv tw" and "nand_inv2 tw"
    using \<open>init_sim (0, w) nand3 = tw\<close> fst_conv unfolding init_sim_valid_def 
    by fastforce+ 
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand3 \<lbrace>nand_inv\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'] \<open>conc_stmt_wf nand3\<close> \<open>nonneg_delay_conc nand3\<close>
    by auto
  ultimately have "nand_inv tw'"
    using \<open>tw, i + 1, nand3 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
    unfolding nand_inv_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

subsection \<open>Proving @{term "nand"}: NAND with inertial delay\<close>

lemma nand_inv_next_time_inert:
  assumes "nand_inv tw"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))\<rbrakk>"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_inert_upd2_def by auto
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
      have "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
      proof (cases "i + 1 < fst tw")
        case True
        hence "snd tw' C (i + 1) \<longleftrightarrow> snd tw C (i + 1)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def 
          by auto
        also have "... \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
          using `snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)` by auto
        also have "... \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          by auto
        finally show ?thesis
          by auto 
      next
        case False
        hence "i + 1 = fst tw"
          using \<open>i < get_time tw\<close> by linarith
        show "snd tw' C (i + 1) \<longleftrightarrow>  \<not> (snd tw' A i \<and> snd tw' B i)"
        proof (cases "snd tw C (get_time tw) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) \<or> snd tw C (get_time tw + 1) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))")
          case True
          hence "snd tw' C (i + 1) \<longleftrightarrow> snd tw C (fst tw)"
            using `i + 1 = fst tw`
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
          also have "... \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
            using `snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)` `i + 1 = fst tw` by auto
          also have "... \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def 
            using `i + 1 = fst tw` by auto
          finally show ?thesis
            by auto
        next
          case False
          hence "snd tw C (fst tw) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))" and 
                "snd tw C (fst tw + 1) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
            by blast+
          let ?time = "GREATEST n. n \<le> fst tw + 1 
                                 \<and> snd tw C (n - 1) = (\<not> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))) 
                                 \<and> snd tw C n = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          have "?time = fst tw + 1"
            using False by (intro Greatest_equality) auto
          hence "snd tw' C (i + 1) \<longleftrightarrow> snd tw C (fst tw)"
            using False unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
            using \<open>i + 1 = get_time tw\<close> by auto
          also have "... \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)"
            using `snd tw C (i + 1) \<longleftrightarrow> \<not> (snd tw A i \<and> snd tw B i)` `i + 1 = fst tw` by auto
          also have "... \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
            unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def 
            using `i + 1 = fst tw` by auto
          finally show ?thesis
            by auto
        qed
      qed }
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
      proof (cases " snd tw C (get_time tw) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) \<or> snd tw C (get_time tw + 1) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))")
        case True
        hence "snd tw' C (fst tw + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
          unfolding beval_world_raw2_def  by (simp add: beval_world_raw_def state_of_world_def)
        also have "... \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          by auto
      next
        case False
        hence "snd tw C (get_time tw) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))" and 
              "snd tw C (get_time tw + 1) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          by blast+
        let ?time = "GREATEST n. n \<le> get_time tw + 1 
                               \<and> snd tw C (n - 1) = (\<not> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))) 
                               \<and> snd tw C n = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
        have "?time = fst tw + 1"
          using False
          by (intro Greatest_equality) auto
        hence "snd tw' C (fst tw + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          using False unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def
          by auto
        also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
          unfolding beval_world_raw2_def  by (simp add: beval_world_raw_def state_of_world_def)
        also have "... \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          by auto
      qed
      ultimately have "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "snd tw' C (i + 1) = snd tw' C (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by auto
      also have "... = snd tw' C (fst tw + 1)"
      proof (cases "snd tw C (get_time tw) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) \<or> snd tw C (get_time tw + 1) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))")
        case True
        hence "snd tw' C (next_time_world tw') \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def 
          using `fst tw < next_time_world tw'` 
          by (smt add.commute fst_conv less_SucE less_imp_le_nat next_time_world_at_least not_le
          plus_1_eq_Suc snd_conv)
        also have "... \<longleftrightarrow> snd tw' C (fst tw + 1)"
          by (smt True dual_order.strict_iff_order not_add_less1 snd_conv tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
        finally show ?thesis
          by auto
      next
        case False
        let ?time = "GREATEST n. n \<le> get_time tw + 1 
                               \<and> snd tw C (n - 1) = (\<not> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))) 
                               \<and> snd tw C n = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
        have "?time = fst tw + 1"
          using False by (intro Greatest_equality) auto
        hence "snd tw' C (next_time_world tw') \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def 
          by (smt add.commute fst_conv less_SucE less_imp_le_nat next_time_world_at_least not_le plus_1_eq_Suc snd_conv)
        also have "... \<longleftrightarrow> snd tw' C (fst tw + 1)"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
          using `fst tw < next_time_world tw'` `?time = fst tw + 1` by simp
        finally show ?thesis
          by auto
      qed
      finally have "snd tw' C (i + 1) \<longleftrightarrow> snd tw' C (fst tw + 1)"
        by auto
      also have "... \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
      proof (cases "snd tw C (get_time tw) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) \<or> snd tw C (get_time tw + 1) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))")
        case True
        hence "snd tw' C (fst tw + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by simp
        also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
          unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def
          by auto
        also have "... \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          by auto
      next
        case False
        let ?time = "GREATEST n. n \<le> get_time tw + 1 
                               \<and> snd tw C (n - 1) = (\<not> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))) 
                               \<and> snd tw C n = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
        have "?time = fst tw + 1"
          using False by (intro Greatest_equality) auto
        hence "snd tw' C (fst tw + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by simp
        also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
          unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def
          by auto
        also have "... \<longleftrightarrow> \<not> (snd tw' A (fst tw) \<and> snd tw' B (fst tw))"
          unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def Let_def by auto
        finally show ?thesis
          by auto
      qed
      also have "... \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> snd tw' C (i + 1) = (\<not> (snd tw' A
        i \<and> snd tw' B i))\<close> \<open>i < next_time_world tw'\<close> calculation not_le
        unchanged_until_next_time_world)
      finally have "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
        by auto }
    ultimately show "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
      by auto 
  qed
  thus ?thesis
    unfolding nand_inv_def by auto 
qed

lemma nand_inv_next_time0_inert:
  assumes "fst tw = 0"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))\<rbrakk>"
  shows   "nand_inv (next_time_world tw', snd tw')"
proof -
  have "nand_inv tw"
    using assms(1) unfolding nand_inv_def by auto
  from nand_inv_next_time_inert[OF this] show ?thesis
    unfolding tw'_def by auto
qed

lemma nand_seq_hoare_next_time_inert:
  "\<turnstile> [nand_inv] (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule AssignI2)
  using nand_inv_next_time_inert by auto

lemma nand_seq_hoare_next_time0_inert:
  " \<turnstile> [\<lambda>tw. get_time tw = 0] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule AssignI2)
  using nand_inv_next_time0_inert by auto

lemma nand_inv2_next_time_inert:
  fixes tw
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))\<rbrakk>"
  shows   "nand_inv2 (next_time_world tw', snd tw')"
  unfolding nand_inv2_def
proof (rule impI)
  assume "disjnt {A, B} (event_of (next_time_world tw', snd tw'))"
  let ?t' = "next_time_world tw'"
  have "fst tw' < ?t'"
    using next_time_world_at_least by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_inert_upd2_def by auto
  ultimately have "fst tw < ?t'"
    by auto
  have "snd tw' A ?t' \<longleftrightarrow> snd tw A ?t'"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... \<longleftrightarrow> snd tw A (?t' - 1)"
    using \<open>disjnt {A, B} (event_of (next_time_world tw', snd tw'))\<close> \<open>fst tw < ?t'\<close>
    unfolding event_of_alt_def 
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... \<longleftrightarrow> snd tw A (fst tw)"
  proof -
    have "fst tw' \<le> ?t' - 1" and "?t' - 1 < ?t'"
      using \<open>fst tw' < ?t'\<close> by auto
    hence "snd tw' A (?t' - 1) = snd tw' A (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] by blast
    moreover have "snd tw' A (?t' - 1) = snd tw A (?t' - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "snd tw' A (fst tw') = snd tw A (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally have 0: "snd tw' A ?t' \<longleftrightarrow> snd tw A (fst tw)"
    by auto
  have "snd tw' B ?t' \<longleftrightarrow> snd tw B ?t'"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... \<longleftrightarrow> snd tw B (?t' - 1)"
    using \<open>disjnt {A, B} (event_of (next_time_world tw', snd tw'))\<close> \<open>fst tw < ?t'\<close>
    unfolding event_of_alt_def 
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... \<longleftrightarrow> snd tw B (fst tw)"
  proof -
    have "fst tw' \<le> ?t' - 1" and "?t' - 1 < ?t'"
      using \<open>fst tw' < ?t'\<close> by auto
    hence "snd tw' B (?t' - 1) = snd tw' B (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] by blast
    moreover have "snd tw' B (?t' - 1) = snd tw B (?t' - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "snd tw' B (fst tw') = snd tw B (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally have 1: "snd tw' B ?t' \<longleftrightarrow> snd tw B (fst tw)"
    by auto
  { fix i 
    assume "?t' \<le> i"
    hence "snd tw' C (i + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
    proof (cases "snd tw C (get_time tw) = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) \<or> snd tw C (get_time tw + 1) \<noteq> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))")
      case True
      thus "snd tw' C (i + 1) \<longleftrightarrow> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def 
        using `fst tw < ?t'`  using \<open>next_time_world tw' \<le> i\<close> by auto
    next
      case False
      let ?time = "GREATEST n. n \<le> get_time tw + 1 
                             \<and> snd tw C (n - 1) = (\<not> beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))) 
                             \<and> snd tw C n = beval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
      have "?time = fst tw + 1"
        using False by (auto intro!:Greatest_equality)
      thus ?thesis        
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def 
        using `fst tw < ?t'`  using \<open>next_time_world tw' \<le> i\<close> by auto
    qed
    also have "... \<longleftrightarrow> \<not> (snd tw A (fst tw) \<and> snd tw B (fst tw))"
      unfolding beval_world_raw2_def beval_world_raw_def 
      by (simp add: state_of_world_def)
    also have "... \<longleftrightarrow> \<not> (snd tw' A ?t' \<and> snd tw' B ?t')"
      using 0 1 by auto
    finally have "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A ?t' \<and> snd tw' B ?t')"
      by auto } 
  thus "\<forall>i\<ge>get_time (next_time_world tw', snd tw').
       snd (next_time_world tw', snd tw') C (i + 1) =
       (\<not> (snd (next_time_world tw', snd tw') A (get_time (next_time_world tw', snd tw')) \<and>
            snd (next_time_world tw', snd tw') B (get_time (next_time_world tw', snd tw'))))"
    by auto
qed

lemma nand_seq_hoare_next_time4_inert:
  " \<turnstile> [\<lambda>tw. True] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)", rotated 1], rule AssignI2)
  using nand_inv2_next_time_inert by auto

lemma nand_conc_hoare3_inert:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_inv  (next_time_world tw, snd tw)  \<and> nand_inv2  (next_time_world tw, snd tw)\<rbrace>"
  unfolding nand_def
  apply (rule Single)
   apply (unfold conj_assoc)
   apply (rule compositional_conj)
    apply(rule nand_seq_hoare_next_time_inert)
   apply (rule strengthen_precondition)
   apply(rule Conseq2[where P="\<lambda>tw. True"])
     apply simp
    apply (rule nand_seq_hoare_next_time4_inert)
   apply simp
  apply (rule allI)
  apply (rule impI)
  apply (rule conjI)
   apply (erule nand_conc_hoare')
  apply (erule nand_conc_hoare2)
  done

lemma nand_conc_sim'_inert:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace>"
  apply (rule While)
  apply (rule nand_conc_hoare3_inert)
  done

lemma nand_conc_sim2'_inert:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand \<lbrace>nand_inv\<rbrace>"
  by (rule Conseq_sim[where Q="\<lambda>tw. nand_inv tw \<and> nand_inv2 tw" and 
                            P="\<lambda>tw. nand_inv tw \<and> nand_inv2 tw"])
     (simp_all add: nand_conc_sim'_inert)  

lemma init_sat_nand_inv_inert:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) nand nand_inv"
  unfolding nand_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule nand_seq_hoare_next_time0_inert)
  done

lemma init_sat_nand_inv2_inert: 
  "init_sim_hoare (\<lambda>tw. True) nand nand_inv2"
  unfolding nand_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule nand_seq_hoare_next_time4_inert)
  done

lemma init_sat_nand_inv_comb_inert:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) nand (\<lambda>tw. nand_inv tw \<and> nand_inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_nand_inv_inert)
  apply (rule ConseqI_sim[where P="\<lambda>tw. True" and Q="nand_inv2"])
  apply (simp, rule init_sat_nand_inv2_inert, simp)
  done

lemma nand_correctness_inert:
  assumes "sim_fin w (i + 1) nand tw'"
  shows "snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
proof -
  obtain tw where "init_sim (0, w) nand = tw" and  "tw, i + 1, nand \<Rightarrow>\<^sub>S tw'" 
    using premises_sim_fin_obt[OF assms] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf nand"
    unfolding conc_stmt_wf_def nand_def by auto
  moreover have "nonneg_delay_conc nand"
    unfolding nand_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0) nand (\<lambda>tw. nand_inv tw \<and> nand_inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_inv_comb_inert] by auto
  hence "nand_inv tw" and "nand_inv2 tw"
    using \<open>init_sim (0, w) nand = tw\<close> fst_conv unfolding init_sim_valid_def 
    by fastforce+ 
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand \<lbrace>nand_inv\<rbrace>"
    using conc_sim_soundness[OF nand_conc_sim2'_inert] \<open>conc_stmt_wf nand\<close> \<open>nonneg_delay_conc nand\<close>
    by auto                               
  ultimately have "nand_inv tw'"
    using \<open>tw, i + 1, nand \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. snd tw' C (i + 1) \<longleftrightarrow> \<not> (snd tw' A i \<and> snd tw' B i)"
    unfolding nand_inv_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed
     
end