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

text \<open>type for the signals\<close>

fun \<Gamma> :: "sig tyenv" where
  "\<Gamma> A = Bty" | "\<Gamma> B = Bty" | "\<Gamma> C = Bty"

text \<open>Invariant for NAND: at all times @{term "i"} less than @{term "fst tw :: nat"}, the signal
@{term "C :: sig"} at @{term "i + 1"} should be the NAND value of @{term "A :: sig"} and
@{term "B :: sig"} at time @{term "i"}.\<close>

abbreviation "bval_of_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"

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

lemma beval_world_raw2_type:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v"
  shows   "type_of v = Bty"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
    using assms(2) unfolding beval_world_raw2_def by auto
  then obtain \<sigma> \<gamma> \<theta> where "\<sigma> = state_of_world (snd tw) (fst tw)" and
                          "\<gamma> = event_of_world (snd tw) (fst tw)" and
                          "\<theta> = derivative_hist_raw (snd tw) (fst tw)" and
                          "fst tw, \<sigma>, \<gamma>, \<theta>, (fst (snd tw)) \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b v"
    using beval_world_raw_cases by force
  have "styping \<Gamma> \<sigma>"
    using wityping_ensure_styping
    by (simp add: wityping_ensure_styping \<open>\<sigma> = state_of_world (snd tw) (get_time tw)\<close> assms(1))
  moreover have "ttyping \<Gamma> \<theta>"
    using wityping_ensure_ttyping
    by (simp add: wityping_ensure_ttyping \<open>\<theta> = derivative_hist_raw (snd tw) (get_time tw)\<close> assms(1))
  moreover have "styping \<Gamma> (fst (snd tw))"
    using assms(1) unfolding wityping_def by blast
  moreover have "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) Bty"
    by (metis \<Gamma>.elims bexp_wt.intros(3) bexp_wt.intros(9))
  ultimately show ?thesis
    using beval_raw_preserve_well_typedness
    by (metis \<open>get_time tw , \<sigma> , \<gamma> , \<theta>, get_time (snd tw) \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b v\<close>)
qed

lemma nand_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, simp)
  using nand_inv_next_time beval_world_raw2_type worldline_upd_preserve_wityping
  by (metis \<Gamma>.simps(3) eq_snd_iff worldline_upd2_def)

lemma nand_seq_hoare_next_time0:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where P="\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)"])
  using nand_seq_hoare_next_time unfolding nand_inv_def  using gr_implies_not_zero
  by auto

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

lemma nand_conc_hoare2:
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv2 (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  hence 0: "(\<forall>i\<ge>fst tw. bval_of_wline tw C (i + 1) = (\<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))))"
    unfolding nand_inv2_def by auto
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. bval_of_wline tw s i = bval_of_wline tw s (fst tw))"
    using unchanged_until_next_time_world by metis
  let ?t' = "next_time_world tw"
  { assume "disjnt {A, B} (event_of (next_time_world tw, snd tw))"
    hence *: "bval_of_wline tw A ?t' = bval_of_wline tw A (?t' - 1)" and **: "bval_of_wline tw B ?t' = bval_of_wline tw B (?t' - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "?t' \<le> i"
      hence "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
        using 0 \<open>fst tw < ?t'\<close> by auto
      moreover have "bval_of_wline tw A (fst tw) = bval_of_wline tw A (?t' - 1)" and "bval_of_wline tw B (fst tw) = bval_of_wline tw B (?t' - 1)"
        using 1
        by (metis (no_types, lifting) One_nat_def Suc_leI \<open>get_time tw < next_time_world tw\<close>
        add_le_cancel_right diff_add diff_less discrete gr_implies_not_zero neq0_conv zero_less_one)+
      ultimately have "bval_of_wline tw C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw A ?t' \<and> bval_of_wline tw B ?t')"
        using * ** by auto
    }
    hence "(\<forall>i\<ge>?t'. bval_of_wline tw C (i + 1) = (\<not> (bval_of_wline tw A ?t' \<and> bval_of_wline tw B ?t')))"
      by auto }
  thus "nand_inv2 (next_time_world tw, snd tw)"
    unfolding nand_inv2_def by auto
qed

lemma nand_inv2_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v" and "type_of v = Bty"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
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
    have *: "\<And>s. s \<in> {A, B} \<Longrightarrow> bval_of_wline tw' s ?t' \<longleftrightarrow> bval_of_wline tw s (fst tw)"
    proof -
      fix s
      assume "s \<in> {A, B}"
      hence "bval_of_wline tw' s ?t' \<longleftrightarrow> bval_of_wline tw s ?t'"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> bval_of_wline tw s (?t' - 1)"
        using \<open>disjnt {A, B} (event_of (next_time_world tw', snd tw'))\<close> \<open>fst tw < ?t'\<close>
        unfolding event_of_alt_def
        by (smt \<open>s \<in> {A, B}\<close> comp_apply disjnt_iff fst_conv gr_implies_not_zero insert_iff
        mem_Collect_eq sig.simps(4) sig.simps(6) singletonD snd_conv tw'_def worldline_upd2_def
        worldline_upd_def)
      also have "... \<longleftrightarrow> bval_of_wline tw s (fst tw)"
      proof -
        have "fst tw' \<le> ?t' - 1" and "?t' - 1 < ?t'"
          using \<open>fst tw' < ?t'\<close> by auto
        hence "bval_of_wline tw' s (?t' - 1) = bval_of_wline tw' s (fst tw')"
          using unchanged_until_next_time_world[where tw="tw'"] by metis
        moreover have "bval_of_wline tw' s (?t' - 1) = bval_of_wline tw s (?t' - 1)"
          unfolding tw'_def worldline_upd2_def worldline_upd_def using  \<open>s \<in> {A, B}\<close> by auto
        moreover have "bval_of_wline tw' s (fst tw') = bval_of_wline tw s (fst tw')"
          unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
        ultimately show ?thesis
          using \<open>fst tw = fst tw'\<close> by auto
      qed
      finally show "bval_of_wline tw' s ?t' \<longleftrightarrow> bval_of_wline tw s (fst tw)"
        by auto
    qed
    have "\<And>i. ?t' \<le> i \<Longrightarrow> bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A ?t' \<and> bval_of_wline tw' B ?t')"
    proof -
      fix i
      have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
        using assms unfolding beval_world_raw2_def by auto
      assume "?t' \<le> i"
      hence "bval_of_wline tw' C (i + 1) \<longleftrightarrow> bval_of v"
        using `fst tw < ?t'`
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
        apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
        apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
        using assms(2) by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A ?t' \<and> bval_of_wline tw' B ?t')"
        using * by auto
      finally show "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A ?t' \<and> bval_of_wline tw' B ?t')"
        by auto
    qed }
  thus ?thesis
    unfolding nand_inv2_def by auto
qed

lemma nand_seq_hoare_next_time4:
  " \<turnstile> [\<lambda>tw.  wityping \<Gamma> (snd tw) ] Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv2 (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv2 (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, blast)
  using nand_inv2_next_time beval_world_raw2_type
  by (simp add: worldline_upd_preserve_wityping worldline_upd2_def)

definition "nand_wityping \<equiv> \<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)"
definition "nand_wityping2 \<equiv> \<lambda>tw. nand_inv2 tw \<and> wityping \<Gamma> (snd tw)"

lemma nand_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand3 \<lbrace>\<lambda>tw. nand_wityping  (next_time_world tw, snd tw)  \<and> nand_wityping2  (next_time_world tw, snd tw)\<rbrace>"
  unfolding nand3_def
  apply (rule Single)
   apply (unfold conj_assoc)
   apply (rule compositional_conj)
  unfolding nand_wityping_def snd_conv apply(rule nand_seq_hoare_next_time)
   apply (rule strengthen_precondition)
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
  unfolding nand_wityping_def snd_conv apply (rule nand_seq_hoare_next_time0)
  done

lemma init_sat_nand_inv2:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) nand3 nand_wityping2"
  unfolding nand3_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding nand_wityping2_def snd_conv
  apply (rule nand_seq_hoare_next_time4)
  done

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
  hence "i + 1 < fst tw'"
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
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

subsection \<open>Proving @{term "nand"}: NAND with inertial delay\<close>

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
  using nand_inv_next_time_inert beval_world_raw2_type by blast

lemma seq_wt_nand3:
  "seq_wt \<Gamma> (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  by (metis \<Gamma>.elims seq_wt.intros bexp_wt.intros)

lemma nand_seq_hoare_wityping:
  "\<turnstile> [\<lambda>tw. nand_inv tw \<and> wityping \<Gamma> (snd tw)] (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1) [\<lambda>tw. nand_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule nand_seq_hoare_next_time_inert)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule seq_wt_nand3)
  done

lemma nand_seq_hoare_next_time0_inert:
  " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv (next_time_world tw, snd tw)", rotated 1], rule AssignI2)
  using nand_inv_next_time0_inert beval_world_raw2_type by auto

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
  have "wline_of tw' A ?t' = wline_of tw A ?t'"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... = wline_of tw A (?t' - 1)"
    using \<open>disjnt {A, B} (event_of (next_time_world tw', snd tw'))\<close> \<open>fst tw < ?t'\<close>
    unfolding event_of_alt_def
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... = wline_of tw A (fst tw)"
  proof -
    have "fst tw' \<le> ?t' - 1" and "?t' - 1 < ?t'"
      using \<open>fst tw' < ?t'\<close> by auto
    hence "wline_of tw' A (?t' - 1) = wline_of tw' A (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] by blast
    moreover have "wline_of tw' A (?t' - 1) = wline_of tw A (?t' - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "wline_of tw' A (fst tw') = wline_of tw A (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally have 0: "wline_of tw' A ?t' = wline_of tw A (fst tw)"
    by auto
  have "wline_of tw' B ?t' = wline_of tw B ?t'"
    unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
  also have "... = wline_of tw B (?t' - 1)"
    using \<open>disjnt {A, B} (event_of (next_time_world tw', snd tw'))\<close> \<open>fst tw < ?t'\<close>
    unfolding event_of_alt_def
    by (simp add: tw'_def worldline_inert_upd2_def worldline_inert_upd_def)
  also have "... = wline_of tw B (fst tw)"
  proof -
    have "fst tw' \<le> ?t' - 1" and "?t' - 1 < ?t'"
      using \<open>fst tw' < ?t'\<close> by auto
    hence "wline_of tw' B (?t' - 1) = wline_of tw' B (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] by blast
    moreover have "wline_of tw' B (?t' - 1) = wline_of tw B (?t' - 1)"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    moreover have "wline_of tw' B (fst tw') = wline_of tw B (fst tw')"
      unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally have 1: "wline_of tw' B ?t' = wline_of tw B (fst tw)"
    by auto
  { fix i
    assume "?t' \<le> i"
    hence "wline_of tw' C (i + 1) = v"
    proof (cases "wline_of tw C (get_time tw) = v \<or> wline_of tw C (get_time tw + 1) \<noteq> v")
      case True
      thus "wline_of tw' C (i + 1) = v"
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
        using `fst tw < ?t'`  using \<open>next_time_world tw' \<le> i\<close> by auto
    next
      case False
      let ?time = "GREATEST n. n \<le> get_time tw + 1  \<and> wline_of tw C (n - 1) \<noteq> v  \<and> wline_of tw C n = v"
      have "?time = fst tw + 1"
        using False by (auto intro!:Greatest_equality)
      thus ?thesis
        unfolding tw'_def worldline_inert_upd2_def worldline_inert_upd_def
        using `fst tw < ?t'`  using \<open>next_time_world tw' \<le> i\<close> by auto
    qed
    have assms2: "beval_world_raw (snd tw) (fst tw) (Bnand (Bsig A) (Bsig B)) v"
      using \<open>beval_world_raw2 tw (Bnand (Bsig A) (Bsig B)) v\<close> unfolding beval_world_raw2_def
      by auto
    have "bval_of v \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
      apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
      apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
      using assms(2) by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw' A ?t' \<and> bval_of_wline tw' B ?t')"
      using 0 1 by auto
    finally have "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A ?t' \<and> bval_of_wline tw' B ?t')"
      using \<open>wline_of tw' C (i + 1) = v\<close> by blast }
  thus "\<forall>i\<ge>get_time (next_time_world tw', snd tw').
       bval_of_wline (next_time_world tw', snd tw') C (i + 1) =
       (\<not> (bval_of_wline (next_time_world tw', snd tw') A (get_time (next_time_world tw', snd tw')) \<and>
            bval_of_wline (next_time_world tw', snd tw') B (get_time (next_time_world tw', snd tw'))))"
    by auto
qed

lemma nand_seq_hoare_next_time4_inert:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. nand_inv2 (next_time_world tw, snd tw)", rotated 1], rule AssignI2, blast)
  using nand_inv2_next_time_inert beval_world_raw2_type by blast

lemma nand_seq_hoare2_wityping:
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 [\<lambda>tw. nand_inv2 (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule nand_seq_hoare_next_time4_inert)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule seq_wt_nand3)
  done

lemma nand_conc_hoare3_inert:
  "\<turnstile> \<lbrace>\<lambda>tw. nand_wityping tw \<and> nand_wityping2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_wityping  (next_time_world tw, snd tw)  \<and> nand_wityping2  (next_time_world tw, snd tw)\<rbrace>"
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
     apply (rule mp, rule impI, rule conjI)
      apply (erule nand_conc_hoare')
      apply simp
     apply simp
    apply (rule mp, rule impI, rule conjI)
     apply (erule nand_conc_hoare2)
     apply simp
    apply simp
  done

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
  unfolding nand_wityping2_def snd_conv  apply (rule nand_seq_hoare2_wityping)
  done

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
  hence "i + 1 < fst tw'"
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
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

end