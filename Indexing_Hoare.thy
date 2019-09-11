(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Indexing_Hoare
  imports VHDL_Hoare_Complete
begin

datatype sig = IN | OUT

definition index :: "sig conc_stmt" where
  "index \<equiv> process {IN} : Bassign_trans OUT (Bindex IN 3) 1"

abbreviation "bof_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

definition inv :: "sig assn2" where
  "inv tw \<equiv> (\<forall>i < fst tw. bof_wline tw OUT (i + 1) = (lof_wline tw IN i) ! 3)"

definition inv' :: "sig assn2" where
  "inv' tw = (disjnt {IN} (event_of tw) \<longrightarrow> (\<forall>i\<ge>fst tw. bof_wline tw OUT (i + 1) = (lof_wline tw IN (fst tw)) ! 3))"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<exists>len>3. \<Gamma> IN = Lty len \<and> \<Gamma> OUT = Bty"
proof (rule seq_wt_cases(4)[OF assms])
  assume "bexp_wt \<Gamma> (Bindex IN 3) (\<Gamma> OUT)"
  then obtain len where "bexp_wt \<Gamma> (Bsig IN) (Lty len) \<and> 3 < len \<and> \<Gamma> OUT = Bty"
    by (meson bexp_wt_cases(10))
  hence "\<Gamma> IN = Lty len" and "\<Gamma> OUT = Bty" and "3 < len"
    by (metis bexp_wt_cases(9))+
  thus ?thesis
    by blast
qed

lemma inv_next_time:
  assumes "inv tw"
  assumes "beval_world_raw2 tw (Bindex IN 3) x" and "type_of x = Bty"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 x]"
  shows   "inv (next_time_world tw', snd tw')"
  unfolding inv_def
proof (rule, rule)
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  fix i
  assume "i < fst (next_time_world tw', snd tw')"
  hence "i < next_time_world tw'"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
    by linarith
  moreover
  { assume "i < fst tw"
    hence "wline_of tw' OUT (i + 1) = wline_of tw OUT (i + 1)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    hence "bof_wline (next_time_world tw', snd tw') OUT (i + 1) =  bof_wline tw OUT (i + 1)"
      by simp
    also have "... = (lof_wline tw IN i) ! 3"
      using assms(1) \<open>i < fst tw\<close> unfolding inv_def by auto
    also have "... = (lof_wline (next_time_world tw', snd tw') IN i) ! 3"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally have "bof_wline (next_time_world tw', snd tw') OUT (i + 1) =
                 (lof_wline (next_time_world tw', snd tw') IN i) ! 3"
      by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
    hence "bof_wline tw' OUT (i + 1) = bof_wline tw' OUT (fst tw + 1)"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) One_nat_def Suc_lessI Suc_less_eq \<open>get_time tw < next_time_world
      tw'\<close> \<open>get_time tw = get_time tw'\<close> add.right_neutral add_Suc_right le_SucI le_add1
      less_diff_conv not_le)
    also have "... = bval_of x"
      using assms(4)  by (metis worldline_upd2_at_dly)
    also have "... = lof_wline tw IN (fst tw) ! 3"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Bindex IN 3) x"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "\<not> is_Bv (wline_of tw IN (fst tw))"
        apply (rule beval_world_raw_cases[OF assm2], erule beval_cases)
        by (metis beval_cases(1) comp_apply state_of_world_def val.disc(2))
      hence "state_of_world (snd tw) (fst tw) IN = Lv (lof_wline tw IN (fst tw))"
        unfolding state_of_world_def by simp
      show ?thesis
        apply (rule beval_world_raw_cases[OF assm2])
        apply (erule beval_cases)+
        using \<open>state_of_world (snd tw) (fst tw) IN = Lv (lof_wline tw IN (fst tw))\<close> by simp
    qed
    also have "... = lof_wline (next_time_world tw', snd tw') IN i ! 3"
      by (metis \<open>get_time tw = get_time tw'\<close> \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>i <
      next_time_world tw'\<close> less_add_one o_apply snd_conv tw'_def unchanged_until_next_time_world
      worldline_upd2_before_dly)
    finally have "bof_wline (next_time_world tw', snd tw') OUT (i + 1) =
                 (lof_wline (next_time_world tw', snd tw') IN i) ! 3"
      by auto }
  moreover
  { assume "i = next_time_world tw' - 1"
    hence "bof_wline tw' OUT (i + 1) = bof_wline tw' OUT (next_time_world tw')"
      using \<open>get_time tw < next_time_world tw'\<close> by auto
    also have "... = bof_wline tw' OUT (fst tw' + 1)"
      by (smt \<open>get_time tw < next_time_world tw'\<close> \<open>get_time tw = get_time tw'\<close> comp_apply discrete
      leD snd_conv tw'_def worldline_upd2_at_dly worldline_upd2_def worldline_upd_def)
    also have "... = bof_wline tw' OUT (fst tw + 1)"
      by (simp add: \<open>get_time tw = get_time tw'\<close>)
    also have "... = bval_of x"
      using assms(4)  by (metis worldline_upd2_at_dly)
    also have "... = lof_wline tw IN (fst tw) ! 3"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Bindex IN 3) x"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "\<not> is_Bv (wline_of tw IN (fst tw))"
        apply (rule beval_world_raw_cases[OF assm2], erule beval_cases)
        by (metis beval_cases(1) comp_apply state_of_world_def val.disc(2))
      hence "state_of_world (snd tw) (fst tw) IN = Lv (lof_wline tw IN (fst tw))"
        unfolding state_of_world_def by simp
      show ?thesis
        apply (rule beval_world_raw_cases[OF assm2])
        apply (erule beval_cases)+
        using \<open>state_of_world (snd tw) (fst tw) IN = Lv (lof_wline tw IN (fst tw))\<close> by simp
    qed
    also have "... = lof_wline (next_time_world tw', snd tw') IN i ! 3"
      by (metis (mono_tags, lifting) \<open>get_time tw < next_time_world tw'\<close> \<open>get_time tw = get_time
      tw'\<close> \<open>i < next_time_world tw'\<close> \<open>i = next_time_world tw' - 1\<close> add_le_imp_le_diff comp_apply
      discrete less_add_one snd_conv tw'_def unchanged_until_next_time_world
      worldline_upd2_before_dly)
    finally have "bof_wline (next_time_world tw', snd tw') OUT (i + 1) =
                 (lof_wline (next_time_world tw', snd tw') IN i) ! 3"
      by auto }
  ultimately show "bof_wline (next_time_world tw', snd tw') OUT (i + 1) = lof_wline (next_time_world tw', snd tw') IN i ! 3"
    by auto
qed

lemma type_correctness_length:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  assumes "wityping \<Gamma> (snd tw)"
  assumes "beval_world_raw2 tw (Bindex IN 3) x"
  shows   "type_of x = Bty"
proof -
  obtain len where "\<Gamma> IN = Lty len" and "3 < len"
    using potential_tyenv[OF assms(1)] by auto
  have *: "beval_world_raw (snd tw) (fst tw) (Bindex IN 3) x"
    using assms(3) unfolding beval_world_raw2_def by auto
  have "type_of (state_of_world (snd tw) (fst tw) IN) = Lty len"
    using assms(2) unfolding wityping_def
    by (simp add: \<open>\<Gamma> IN = Lty len\<close> state_of_world_def wtyping_def)
  hence **: "\<And>bs. state_of_world (snd tw) (fst tw) IN = Lv bs \<Longrightarrow> length bs = len"
    by simp
  show ?thesis
    apply (rule beval_world_raw_cases[OF *])
    apply (erule beval_cases)+
    using \<open>3 < len\<close> **  by simp
qed

lemma index_seq_hoare_next_time:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<turnstile> [\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw)] Bassign_trans OUT (Bindex IN 3) 1 [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_next_time type_correctness_length[OF assms] by blast

lemma index_seq_hoare_next_time0:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_trans OUT (Bindex IN 3) 1 [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_next_time type_correctness_length[OF assms]  Indexing_Hoare.inv_def gr_implies_not_zero
  by blast

lemma index_conc_hoare:
  "\<And>tw. inv tw \<and> inv' tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv (next_time_world tw, snd tw)"
  by (smt inv_def comp_apply inv'_def not_less prod.sel(1) snd_conv
  unchanged_until_next_time_world)

lemma index_conc_hoare2:
  "\<And>tw. inv tw \<and> inv' tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv' (next_time_world tw, snd tw)"
  unfolding inv_def inv'_def
  by (smt Suc_diff_1 comp_apply diff_less disjnt_insert1 event_of_alt_def gr_implies_not_zero
  le_Suc_eq le_less_trans mem_Collect_eq next_time_world_at_least not_less order.strict_iff_order
  prod.sel(1) snd_conv unchanged_until_next_time_world zero_less_one)

lemma inv'_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Bindex IN 3) x" and "type_of x = Bty"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 x]"
  shows   "inv' (next_time_world tw', snd tw')"
  unfolding inv'_def
proof (rule, rule, rule)
  fix i
  assume "disjnt {IN} (event_of (next_time_world tw', snd tw'))"
  hence "IN \<notin> event_of (next_time_world tw', snd tw')"
    by auto
  assume "fst (next_time_world tw', snd tw') \<le> i"
  hence "next_time_world tw' \<le> i"
    by auto
  let ?t' = "next_time_world tw'"
  have "fst tw' < ?t'"
    using next_time_world_at_least by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < ?t'"
    by auto
  have "wline_of (?t', snd tw') OUT (i + 1) = wline_of tw' OUT (i + 1)"
    by auto
  also have "... = x"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using \<open>next_time_world tw' \<le> i\<close> \<open>fst tw < ?t'\<close>
    by auto
  also have "bval_of ... = lof_wline tw IN (fst tw) ! 3"
  proof -
    have assm: "beval_world_raw (snd tw) (fst tw) (Bindex IN 3) x"
      using assms(1) unfolding beval_world_raw2_def by auto
    show ?thesis
      apply (rule beval_world_raw_cases[OF assm])
      apply (erule beval_cases)+
      by (metis comp_apply state_of_world_def val.sel(1) val.sel(2))
  qed
  also have "... = lof_wline tw IN (fst tw') ! 3"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = lof_wline tw' IN (?t') ! 3"
  proof -
    have "wline_of tw' IN ?t' = wline_of tw' IN (?t' - 1)"
      using \<open>IN \<notin> event_of (?t', snd tw')\<close> unfolding event_of_alt_def
      using \<open>get_time tw < next_time_world tw'\<close> by auto
    also have "... = wline_of tw' IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 \<open>get_time tw' < next_time_world tw'\<close> diff_less
      gr_implies_not_zero le_0_eq less_Suc_eq_le not_less zero_less_one)
    also have "... = wline_of tw' IN (fst tw)"
      by (simp add: \<open>get_time tw = get_time tw'\<close>)
    also have "... = wline_of tw IN (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by simp
    finally have "wline_of tw' IN ?t' = wline_of tw IN (fst tw)"
      by auto
    thus ?thesis
      using \<open>fst tw = fst tw'\<close> by simp
  qed
  also have "... = lof_wline (?t', snd tw') IN ?t' ! 3"
    by auto
  finally show "bof_wline (next_time_world tw', snd tw') OUT (i + 1) = lof_wline (next_time_world tw', snd tw') IN (get_time (next_time_world tw', snd tw')) ! 3"
    by simp
qed

lemma index_seq_hoare_next_time1:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_trans OUT (Bindex IN 3) 1 [\<lambda>tw. inv' (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv'_next_time type_correctness_length[OF assms] by blast

lemma index_conc_hoare3:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw\<rbrace> index \<lbrace>\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv' (next_time_world tw, snd tw)\<rbrace>"
  unfolding index_def
  apply (rule Single)
   apply (rule Conj)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
    apply(rule index_seq_hoare_next_time[OF assms])
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition2)
   apply(rule index_seq_hoare_next_time1[OF assms])
  using index_conc_hoare index_conc_hoare2 by blast

lemma index_conc_hoare4:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw\<rbrace> index \<lbrace>\<lambda>tw. (inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)) \<and> inv' (next_time_world tw, snd tw)\<rbrace>"
  apply (rule Conj2)
   apply (rule Conj2)
    apply (rule weaken_post_conc_hoare[OF _ index_conc_hoare3[OF assms]])
    apply blast
   apply (rule strengthen_pre_conc_hoare[rotated])
    apply (unfold index_def, rule single_conc_stmt_preserve_wityping_hoare[OF assms], blast)
  apply (fold index_def, rule weaken_post_conc_hoare[OF _ index_conc_hoare3[OF assms]], blast)
  done

lemma index_conc_sim':
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw\<rbrace> index \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw\<rbrace>"
  apply (rule While)
  apply (unfold snd_conv, rule index_conc_hoare4[OF assms])
  done

lemma index_conc_sim2':
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw\<rbrace> index \<lbrace>inv\<rbrace>"
  using index_conc_sim' Conseq_sim assms by smt

lemma init_sat_index_inv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) index (\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding index_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conj)
  unfolding snd_conv apply (rule index_seq_hoare_next_time0[OF assms])
  apply (rule strengthen_precondition2)
  by (metis assms seq_stmt_preserve_wityping_hoare)

lemma init_sat_index_inv2:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) index inv'"
  unfolding index_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv apply (rule index_seq_hoare_next_time1[OF assms])
  done

lemma init_sat_slicer_inv_comb:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) index (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_index_inv[OF assms])
  apply (rule ConseqI_sim[rotated])
  apply (rule init_sat_index_inv2[OF assms])
  by blast+

lemma slicer_correctness:
  assumes "sim_fin w (i + 1) index tw'" and "wityping \<Gamma> w"
  assumes "conc_wt \<Gamma> index"
  shows   "bof_wline tw' OUT (i + 1) = lof_wline tw' IN i ! 3"
proof -
  obtain tw where "init_sim (0, w) index tw" and  "tw, i + 1, index \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf index"
    unfolding conc_stmt_wf_def index_def by auto
  moreover have "nonneg_delay_conc index"
    unfolding index_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) index (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw)"
    using init_sim_hoare_soundness[OF init_sat_slicer_inv_comb]
    by (metis (no_types, lifting) assms(3) conc_wt_cases(1) init_sat_slicer_inv_comb
    init_sim_hoare_soundness index_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv' tw"
    using \<open>init_sim (0, w) index tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv' tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
    using assms(3) unfolding index_def by auto
  moreover hence "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw\<rbrace> index \<lbrace>inv\<rbrace>"
    using conc_sim_soundness[OF index_conc_sim2'] \<open>conc_stmt_wf index\<close> \<open>nonneg_delay_conc index\<close>
    by auto
  ultimately have "inv tw'"
    using \<open>tw, i + 1, index \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    unfolding inv_def by auto
qed

end
