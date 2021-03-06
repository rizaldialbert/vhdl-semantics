(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Slicing_Hoare
  imports VHDL_Hoare_Complete
begin

datatype sig = IN | OUT

definition slicer :: "sig conc_stmt" where
  "slicer = process {IN} : Bassign_trans OUT (Bslice IN 3 2) 1"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<exists>ki len. 3 < len \<and> \<Gamma> IN = Lty ki len \<and> \<Gamma> OUT = Lty ki 2"
proof (rule seq_wt_cases(4)[OF assms])
  assume "bexp_wt \<Gamma> (Bslice IN 3 2) (\<Gamma> OUT)"
  then obtain ki len where "bexp_wt \<Gamma> (Bsig IN) (Lty ki len) \<and> 3 < len \<and> \<Gamma> OUT = Lty ki 2"
    by (metis add_2_eq_Suc add_Suc add_Suc_right add_diff_cancel_right' bexp_wt_cases_slice(1)
    numeral_2_eq_2 numeral_3_eq_3)
  hence "bexp_wt \<Gamma> (Bsig IN) (Lty ki len)" and "3 < len" and "\<Gamma> OUT = Lty ki 2"
    by auto
  hence "\<Gamma> IN = Lty ki len"
    using bexp_wt_cases_slice(2)[OF \<open>bexp_wt \<Gamma> (Bsig IN) (Lty ki len)\<close>] by metis
  thus ?thesis
    using \<open>3 < len\<close> \<open>\<Gamma> OUT = Lty ki 2\<close> by blast
qed

abbreviation "lof_wline tw sig i \<equiv> lval_of (wline_of tw sig i)"

definition inv :: "sig assn2" where
  "inv tw = (\<forall>i < fst tw. let ins = lof_wline tw IN i; idx = length ins - 1 in
                                          lof_wline tw OUT (i + 1) = nths ins {idx - 3 .. idx - 2})"

definition inv' :: "sig assn2" where
  "inv' tw = (disjnt {IN} (event_of tw) \<longrightarrow>
              (\<forall>i\<ge>fst tw. let ins = lof_wline tw IN (fst tw); idx = length ins - 1 in
                                         lof_wline tw OUT (i + 1) = nths ins {idx - 3 .. idx - 2}))"

text \<open>Note that we need the assumption that @{term "type_of x = Lty ki 2"} as there is no
guarantee that @{term "beval_world_raw2 tw (Bslice IN 3 2) x"} would result in a list
of length 2.\<close>

lemma inv_next_time:
  assumes "inv tw"
  assumes "beval_world_raw2 tw (Bslice IN 3 2) x" and "type_of x = Lty ki 2"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 x]"
  shows   "inv (next_time_world tw', snd tw')"
proof -
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have "\<forall>i < next_time_world tw'. let ins = lof_wline tw' IN i; idx = length ins - 1 in
                                           lof_wline tw' OUT (i + 1) = nths ins {idx - 3 .. idx - 2}"
  proof (rule, rule)
    fix i
    let ?ins   = "lof_wline tw IN i"
    let ?ins'  = "lof_wline tw' IN i"
    let ?instw = "lof_wline tw IN (fst tw)"
    let ?idx   = "length ?ins - 1"
    let ?idx'  = "length ?ins' - 1"
    let ?idxtw = "length ?instw - 1"

    assume "i < next_time_world tw'"
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
      using \<open>fst tw < next_time_world tw'\<close> by auto
    moreover
    { assume "i < fst tw"
      have "lof_wline tw' OUT (i + 1) = lof_wline tw OUT (i + 1)"
        using \<open>i < fst tw\<close> \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def
        worldline_upd_def by (simp add: discrete)
      also have "... = nths ?ins {?idx - 3 .. ?idx - 2}"
        using assms(1) \<open>i < fst tw\<close> unfolding inv_def Let_def by auto
      also have "... = nths ?ins' {?idx' - 3 .. ?idx' - 2}"
      proof -
        have "lof_wline tw' IN i = lof_wline tw IN i"
          using \<open>i < fst tw\<close> \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def
          worldline_upd_def by (simp add: discrete)
        thus ?thesis
          by auto
      qed
      finally have "lof_wline tw' OUT (i + 1) = nths ?ins' {?idx' - 3 .. ?idx' - 2}"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      have "lof_wline tw' IN i = lof_wline tw IN (fst tw)"
        using unchanged_until_next_time_world
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>i <
        next_time_world tw'\<close> less_add_one tw'_def worldline_upd2_before_dly)
      let ?instw = "lof_wline tw IN (fst tw)"
      let ?idxtw = "length ?instw - 1"
      have "nths ?ins' {?idx' - 3 .. ?idx' - 2} = nths ?instw {?idxtw - 3 .. ?idxtw - 2}"
        using \<open>lof_wline tw' IN i = lof_wline tw IN (fst tw)\<close> by simp
      have "lof_wline tw' OUT (fst tw + 1) = lval_of x"
        using assms(4)  by (metis worldline_upd2_at_dly)
      also have "... = nths ?instw {?idxtw - 3 .. ?idxtw - 2}"
      proof -
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bslice IN 3 2) x"
          using assms(2) unfolding beval_world_raw2_def by auto
        have "\<not> is_Bv (wline_of tw IN (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          by (metis beval_cases(1) comp_apply state_of_world_def val.disc(2))
        then obtain ki where "state_of_world (snd tw) (fst tw) IN = Lv ki ?instw"
          unfolding state_of_world_def  by (metis comp_def val.collapse(2))
        show "lval_of x = nths ?instw {?idxtw - 3 .. ?idxtw - 2}"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          using \<open>state_of_world (snd tw) (fst tw) IN = Lv ki ?instw\<close> plus_1_eq_Suc by auto
      qed
      also have "... = nths ?ins' {?idx' - 3 .. ?idx' - 2}"
        using \<open>lof_wline tw' IN i = lof_wline tw IN (fst tw)\<close>
        by simp
      finally have "lof_wline tw' OUT (i + 1) = nths ?ins' {?idx' - 3 .. ?idx' - 2}"
        using \<open>lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (fst tw + 1)\<close> by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by auto
      also have "... = lof_wline tw' OUT (fst tw' + 1)"
        by (smt Suc_eq_plus1 \<open>get_time tw < next_time_world tw'\<close> \<open>get_time tw = get_time tw'\<close>
        comp_def dual_order.strict_trans1 less_Suc_eq_le less_not_refl snd_conv tw'_def
        worldline_upd2_def worldline_upd_def)
      also have "... = lof_wline tw' OUT (fst tw + 1)"
        unfolding `fst tw = fst tw'` by auto
      also have "... = lval_of x"
        using assms(4)  by (metis worldline_upd2_at_dly)
      also have "... = nths ?instw {?idxtw - 3 .. ?idxtw - 2}"
      proof -
        have assms2: "beval_world_raw (snd tw) (fst tw) (Bslice IN 3 2) x"
          using assms(2) unfolding beval_world_raw2_def by auto
        have "\<not> is_Bv (wline_of tw IN (fst tw))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          by (metis beval_cases(1) comp_apply state_of_world_def val.disc(2))
        then obtain ki where "state_of_world (snd tw) (fst tw) IN = Lv ki ?instw"
          unfolding state_of_world_def  by (metis comp_def val.collapse(2))
        show "lval_of x = nths ?instw {?idxtw - 3 .. ?idxtw - 2}"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          using \<open>state_of_world (snd tw) (fst tw) IN = Lv ki ?instw\<close> plus_1_eq_Suc by auto
      qed
      also have "... = nths ?ins' {?idx' - 3 .. ?idx' - 2}"
        by (smt \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> lof_wline tw' OUT (i + 1) = nths
        (lof_wline tw' IN i) {length (lof_wline tw' IN i) - 1 - 3..length (lof_wline tw' IN i) - 1 -
        2}\<close> \<open>i < next_time_world tw'\<close> calculation comp_def not_less sig.distinct(1) snd_conv tw'_def
        unchanged_until_next_time_world worldline_upd2_def worldline_upd_def)
      finally have "lof_wline tw' OUT (i + 1) = nths ?ins' {?idx' - 3 .. ?idx' - 2}"
        by blast }
    ultimately show "let ins = lof_wline tw' IN i; idx = length ins - 1 in lof_wline tw' OUT (i + 1) = nths ins {idx - 3..idx - 2}"
      unfolding Let_def by auto
  qed
  thus ?thesis
    unfolding inv_def by auto
qed

lemma type_correctness_length:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  assumes "wityping \<Gamma> (snd tw)"
  assumes "beval_world_raw2 tw (Bslice IN 3 2) x"
  shows   "\<exists>ki. type_of x = Lty ki 2"
proof -
  obtain ki len where "\<Gamma> IN = Lty ki len" and "3 < len"
    using potential_tyenv[OF assms(1)] by auto
  have *: "beval_world_raw (snd tw) (fst tw) (Bslice IN 3 2) x"
    using assms(3) unfolding beval_world_raw2_def by auto
  have "type_of (state_of_world (snd tw) (get_time tw) IN) = Lty ki len"
    using assms(2) unfolding wityping_def
    by (simp add: \<open>\<Gamma> IN = Lty ki len\<close> state_of_world_def wtyping_def)
  hence **: "\<And>bs. state_of_world (snd tw) (fst tw) IN = Lv ki bs \<Longrightarrow> length bs = len"
    by simp
  have ***: "\<And>bs. 3 < length bs  \<Longrightarrow> length (nths bs {length bs - Suc 3..length bs - Suc 2}) = 2"
  proof -
    fix bs :: "'a list"
    assume "3 < length bs"
    hence "length (nths bs {length bs - Suc 3..length bs - Suc 2}) =
                               card {i. i < length bs \<and> i \<in> {length bs - Suc 3..length bs - Suc 2}}"
      unfolding length_nths by auto
    have "\<And>i. i \<in> {length bs - Suc 3 .. length bs - Suc 2} \<Longrightarrow> i < length bs"
      using \<open>3 < length bs\<close> by auto
    hence "{i. i < length bs \<and> i \<in> {length bs - Suc 3 .. length bs - Suc 2}} =
           {i. i \<in> {length bs - Suc 3 .. length bs - Suc 2}}" (is "?lhs = ?rhs")
      by auto
    hence "card ?lhs = card ?rhs"
      by auto
    also have "... = 2"
      using \<open>3 < length bs\<close>
      by (metis Collect_mem_eq One_nat_def Suc_diff_Suc Suc_numeral add_diff_cancel_left'
      add_diff_cancel_right' card_atLeastAtMost diff_less_Suc numeral_2_eq_2 plus_1_eq_Suc
      semiring_norm(5))
    finally have "card ?lhs = 2"
      by auto
    thus "length (nths bs {length bs - Suc 3..length bs - Suc 2}) = 2 "
      using \<open>length (nths bs {length bs - Suc 3..length bs - Suc 2}) = card {i. i < length bs \<and> i \<in>
      {length bs - Suc 3..length bs - Suc 2}}\<close> by linarith
  qed
  show ?thesis
    apply (rule beval_world_raw_cases[OF *])
    apply (erule beval_cases)+
    using \<open>3 < len\<close> ** ***
    by (metis \<open>type_of (state_of_world (snd tw) (get_time tw) IN) = Lty ki len\<close> ty.inject
    type_of.simps(2))
qed

lemma slicer_seq_hoare_next_time:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<turnstile> [\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw)]  Bassign_trans OUT (Bslice IN 3 2) 1 [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_next_time type_correctness_length[OF assms] by blast

lemma aux:
  "\<And>tw. inv (next_time_world tw, snd tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw)"
  unfolding inv_def Let_def by simp

lemma slicer_seq_hoare_next_time_post:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<turnstile> [\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw)]  
              Bassign_trans OUT (Bslice IN 3 2) 1 
           [\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw)]"
  apply (rule Conseq2[rotated])
    apply (rule slicer_seq_hoare_next_time[OF assms])
  by (auto simp add: aux)

lemma slicer_seq_hoare_next_time0:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)] Bassign_trans OUT (Bslice IN 3 2) 1 [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_next_time type_correctness_length[OF assms] inv_def gr_implies_not0 by metis

lemma slicer_conc_hoare:
  "\<And>tw. inv tw \<and> inv' tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv (next_time_world tw, snd tw)"
  by (smt Slicing_Hoare.inv_def comp_apply inv'_def not_less prod.sel(1) snd_conv
  unchanged_until_next_time_world)

lemma slicer_conc_hoare2:
  "\<And>tw. inv tw \<and> inv' tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. inv' (j, snd tw)"
  unfolding inv_def inv'_def
  by (smt Suc_diff_1 comp_apply diff_less disjnt_insert1 dual_order.strict_trans1 event_of_alt_def
  fst_conv gr_implies_not_zero greaterThanAtMost_iff le_Suc_eq mem_Collect_eq nat_neq_iff
  order.strict_iff_order snd_conv unchanged_until_next_time_world zero_less_one)

lemma inv'_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Bslice IN 3 2) x" and "type_of x = Lty ki 2"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 x]"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. inv' (j, snd tw')"
  unfolding inv'_def
proof (rule, rule, rule, rule)
  fix i j
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  assume "disjnt {IN} (event_of (j, snd tw'))"
  hence "IN \<notin> event_of (j, snd tw')"
    by auto
  assume "fst (j, snd tw') \<le> i"
  hence "j \<le> i"
    by auto
  let ?ins = "lof_wline (j, snd tw') IN j"
  let ?idx = "length ?ins - 1"

  have "fst tw' < j"
    using \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> by auto
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < j"
    by auto
  have "wline_of tw' IN j = wline_of tw IN (fst tw)"
  proof -
    have "wline_of tw' IN j = wline_of tw' IN (j - 1)"
      using \<open>IN \<notin> event_of (j, snd tw')\<close> unfolding event_of_alt_def
      using \<open>get_time tw < j\<close> by auto
    also have "... = wline_of tw' IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close>
      gr_implies_not_zero greaterThanAtMost_iff le_0_eq less_Suc_eq_le not_less)
    also have "... = wline_of tw' IN (fst tw)"
      by (simp add: \<open>get_time tw = get_time tw'\<close>)
    also have "... = wline_of tw IN (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by simp
    finally show "wline_of tw' IN j = wline_of tw IN (fst tw)"
      by auto
  qed
  moreover have "?ins = lof_wline tw' IN j"
    by auto
  ultimately have "?ins = lof_wline tw IN (fst tw)"
    by auto
  have "\<And>i. j \<le> i \<Longrightarrow> lof_wline tw' OUT (i + 1) = nths ?ins {?idx - 3 .. ?idx - 2}"
  proof -
    fix i
    have assms2: "beval_world_raw (snd tw) (fst tw) (Bslice IN 3 2) x"
      using assms unfolding beval_world_raw2_def by auto
    assume "j \<le> i"
    hence "lof_wline tw' OUT (i + 1) = lval_of x"
      using `fst tw < j`
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    have "\<not> is_Bv (wline_of tw IN (fst tw))"
      by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
         (metis beval_cases(1) comp_apply state_of_world_def val.disc(2))
    then obtain ki where "state_of_world (snd tw) (fst tw) IN = Lv ki ?ins"
      unfolding \<open>?ins = lof_wline tw IN (fst tw)\<close>state_of_world_def
      by (metis comp_def val.collapse(2))
    have "lval_of x = nths ?ins {?idx - 3 .. ?idx - 2}"
      apply (rule beval_world_raw_cases[OF assms2])
      apply (erule beval_cases)+
      using \<open>state_of_world (snd tw) (fst tw) IN = Lv ki ?ins\<close>
      by (metis diff_Suc_eq_diff_pred val.sel(3))
    thus "lof_wline tw' OUT (i + 1) = nths ?ins {?idx - 3 .. ?idx - 2}"
      using \<open>lof_wline tw' OUT (i + 1) = lval_of x\<close> by auto
  qed
  thus "let ins = lof_wline (j, snd tw') IN (get_time (j, snd tw')); idx = length ins - 1 in lof_wline (j, snd tw') OUT (i + 1) = nths ins {idx - 3..idx - 2}"
    by (simp add: \<open>j \<le> i\<close>)
qed

lemma slicer_seq_hoare_next_time1:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] 
              Bassign_trans OUT (Bslice IN 3 2) 1 
           [\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. inv' (j, snd tw)]"
  apply (rule Assign2_altI)
  using inv'_next_time type_correctness_length[OF assms] by blast

lemma slicer_conc_hoare3:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> 
              slicer 
           \<lbrace>\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw) \<and> inv' (j, snd tw)\<rbrace>"
  unfolding slicer_def
  apply (rule Single)
   apply (rule Conj_univ_qtfd)
  apply (rule Conseq2[rotated])
      apply (rule slicer_seq_hoare_next_time_post[OF assms], simp, simp)
   apply (rule Conseq2[rotated])
     apply (rule slicer_seq_hoare_next_time1[OF assms], simp, simp)
  using slicer_conc_hoare aux slicer_conc_hoare2 by blast

lemma slicer_conc_hoare4:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> 
                slicer 
           \<lbrace>\<lambda>tw. \<forall>i\<in>{get_time tw<..next_time_world tw}. (Slicing_Hoare.inv (i, snd tw) \<and> inv' (i, snd tw)) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule Conj2_univ_qtfd[where R="\<lambda>tw. wityping \<Gamma> (snd tw)", unfolded snd_conv])
   apply (rule slicer_conc_hoare3[OF assms])
  apply (rule strengthen_pre_conc_hoare[rotated])
  apply (rule weaken_post_conc_hoare[rotated])
    apply (unfold slicer_def, rule single_conc_stmt_preserve_wityping_hoare[OF assms], blast)
  by auto

lemma slicer_conc_sim':
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows   "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> 
                  slicer 
              \<lbrace>\<lambda>tw. (inv tw \<and> inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule While)    
  apply (unfold snd_conv, rule slicer_conc_hoare4[OF assms])
  done

lemma slicer_conc_sim2':
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows   "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> slicer \<lbrace>inv\<rbrace>"
  using slicer_conc_sim' Conseq_sim assms by smt

lemma init_sat_slicer_inv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows   "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) slicer (\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding slicer_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conj)
  unfolding snd_conv apply (rule slicer_seq_hoare_next_time0[OF assms])
  apply (rule strengthen_precondition2)
  by (metis assms seq_stmt_preserve_wityping_hoare)

lemma init_sat_slicer_inv2:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) slicer inv'"
  unfolding slicer_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conseq2[rotated])
    apply (rule slicer_seq_hoare_next_time1[OF assms])
  by (auto simp add: next_time_world_at_least)
  
lemma init_sat_slicer_inv_comb:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows   "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) slicer (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_slicer_inv[OF assms])
  apply (rule ConseqI_sim[rotated])
  apply (rule init_sat_slicer_inv2[OF assms])
  by blast+

lemma slicer_correctness:
  assumes "sim_fin w (i + 1) slicer tw'" and "wityping \<Gamma> w"
  assumes "conc_wt \<Gamma> slicer"
  shows   "let ins = lof_wline tw' IN i; idx = length ins - 1 in
                                          lof_wline tw' OUT (i + 1) = nths ins {idx - 3 .. idx - 2}"
proof -
  obtain tw where "init_sim (0, w) slicer tw" and  "tw, i + 1, slicer \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf slicer"
    unfolding conc_stmt_wf_def slicer_def by auto
  moreover have "nonneg_delay_conc slicer"
    unfolding slicer_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) slicer (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv' tw)"
    using init_sim_hoare_soundness[OF init_sat_slicer_inv_comb]
    by (metis (no_types, lifting) assms(3) conc_wt_cases(1) init_sat_slicer_inv_comb
    init_sim_hoare_soundness slicer_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv' tw"
    using \<open>init_sim (0, w) slicer tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv' tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
    using assms(3) unfolding slicer_def by auto
  moreover hence "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (Slicing_Hoare.inv tw \<and> inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> slicer \<lbrace>Slicing_Hoare.inv\<rbrace>"
    using conc_sim_soundness[OF slicer_conc_sim2'] \<open>conc_stmt_wf slicer\<close> \<open>nonneg_delay_conc slicer\<close>
    by auto
  ultimately have "inv tw'"
    using \<open>tw, i + 1, slicer \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    unfolding inv_def by (metis less_add_one)
qed

end