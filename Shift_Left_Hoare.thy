(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Shift_Left_Hoare
  imports VHDL_Hoare_Complete Bits_Int_Aux
begin

datatype sig = IN | OUT

definition shiftl :: "nat \<Rightarrow> sig conc_stmt" where
  "shiftl n \<equiv> process {IN} : Bassign_trans OUT (Bshiftl (Bsig IN) n) 1"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bshiftl (Bsig IN) n) 1)"
  shows "\<exists>len>0. \<Gamma> IN = Lty Uns len \<and> \<Gamma> OUT = Lty Uns len \<or> \<Gamma> IN = Lty Sig len \<and> \<Gamma> OUT = Lty Sig len"
  by (rule seq_wt_cases(4)[OF assms])
     (metis bexp_wt_cases(14) bexp_wt_cases(9))

locale unsigned_shift_left =
  fixes \<Gamma> :: "sig tyenv"
  fixes len :: nat
  fixes amount :: nat
  assumes "0 < len"
  assumes "\<Gamma> IN = Lty Uns len \<and> \<Gamma> OUT = Lty Uns len \<or>
           \<Gamma> IN = Lty Sig len \<and> \<Gamma> OUT = Lty Sig len"
begin

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans OUT (Bshiftl (Bsig IN) n) 1)"
  by (rule seq_wt.intros(4))
     (smt bexp_wt.intros(21) bexp_wt.intros(22) bexp_wt.intros(3) unsigned_shift_left_axioms
     unsigned_shift_left_def)

abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

text \<open>Here we factor out common expression in both inv1 and inv2. It is parametrised by the index
we are interested with for C (first argument) and A (the second argument). Note that the index
we are interested with for A should be the same as the index for B.\<close>

definition property :: "nat \<Rightarrow> nat \<Rightarrow> sig assn2" where
  "property idxc idx =
      (\<lambda>tw. lof_wline tw OUT idxc = drop amount (lof_wline tw IN idx @ replicate amount False))"

definition inv :: "sig assn2" where
  "inv tw \<equiv> (\<forall>i < fst tw. property (i + 1) i tw)"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> (disjnt {IN} (event_of tw) \<longrightarrow> (\<forall>i \<ge> fst tw. property (i + 1) (fst tw) tw))"

abbreviation "next_world tw \<equiv> (next_time_world tw, snd tw)"

lemma inv_next_time_uns:
  assumes "inv tw"
  assumes "beval_world_raw2 tw (Bshiftl (Bsig IN) amount) v" and "type_of v = Lty Uns len"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv (next_time_world tw', snd tw')"
  unfolding inv_def
proof (rule, rule)
  fix i
  assume "i < fst (next_world tw')"
  hence "i < next_time_world tw'"
    by auto
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
    using \<open>i < next_time_world tw'\<close> by linarith
  moreover
  { assume "i < fst tw"
    have "lof_wline tw' OUT (i + 1) = lof_wline tw OUT (i + 1)"
      by (metis \<open>i < get_time tw\<close> add_mono1 tw'_def worldline_upd2_before_dly)
    also have "... = drop amount (lof_wline tw IN i @ replicate amount False)"
      using assms(1) \<open>i < fst tw\<close> unfolding inv_def property_def by auto
    also have "... = drop amount (lof_wline tw' IN i @ replicate amount False)"
      by (metis \<open>i < get_time tw\<close> add.commute trans_less_add2 tw'_def worldline_upd2_before_dly)
    finally have "property (i + 1) i (next_time_world tw', snd tw')"
      unfolding property_def by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
    hence "fst tw \<le> i" and "i < next_time_world tw' - 1"
      by auto
    hence "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (fst tw + 1)"
      using unchanged_until_next_time_world
      by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
          le_less_trans less_diff_conv)
    moreover have "lof_wline tw' IN i = lof_wline tw' IN (fst tw)"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw = get_time tw'\<close> \<open>get_time tw \<le> i\<close> \<open>i < next_time_world tw'\<close> worldline_upd2_before_dly)
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' OUT (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Uns (drop amount (lof_wline tw IN (fst tw) @ replicate amount False))"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule beval_cases)+
        unfolding state_of_world_def
        apply (metis comp_apply drop_append drop_replicate val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Uns (drop amount (lof_wline tw' IN (fst tw) @ replicate amount False))"
        by (metis less_add_one tw'_def worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    ultimately have "property (i + 1) i (next_world tw')"
      unfolding property_def by auto }
  moreover
  { assume "i = next_time_world tw' - 1"
    hence "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (next_time_world tw')"
      using \<open>i < next_time_world tw'\<close> by force
    also have "... = lof_wline tw' OUT (fst tw + 1)"
      using \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def
      worldline_upd_def by auto
    finally have "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (fst tw + 1)"
      by auto
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' OUT (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Uns (drop amount (lof_wline tw IN (fst tw) @ replicate amount False))"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule beval_cases)+
        unfolding state_of_world_def
        apply (metis comp_apply drop_append drop_replicate val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Uns (drop amount (lof_wline tw' IN (fst tw) @ replicate amount False))"
        by (metis less_add_one tw'_def worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    moreover have "lof_wline tw' IN i = lof_wline tw' IN (fst tw)"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw < next_time_world tw'\<close> \<open>get_time tw = get_time tw'\<close> \<open>i <
      next_time_world tw'\<close> \<open>i = next_time_world tw' - 1\<close> add_le_imp_le_diff discrete)+
    ultimately have "property (i + 1) i (next_world tw')"
      unfolding property_def by auto }
  ultimately show "property (i + 1) i (next_world tw')"
    by auto
qed

lemma inv_next_time_sig:
  assumes "inv tw"
  assumes "beval_world_raw2 tw (Bshiftl (Bsig IN) amount) v" and "type_of v = Lty Sig len"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv (next_time_world tw', snd tw')"
  unfolding inv_def
proof (rule, rule)
  fix i
  assume "i < fst (next_world tw')"
  hence "i < next_time_world tw'"
    by auto
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
    using \<open>i < next_time_world tw'\<close> by linarith
  moreover
  { assume "i < fst tw"
    have "lof_wline tw' OUT (i + 1) = lof_wline tw OUT (i + 1)"
      by (metis \<open>i < get_time tw\<close> add_mono1 tw'_def worldline_upd2_before_dly)
    also have "... = drop amount (lof_wline tw IN i @ replicate amount False)"
      using assms(1) \<open>i < fst tw\<close> unfolding inv_def property_def by auto
    also have "... = drop amount (lof_wline tw' IN i @ replicate amount False)"
      by (metis \<open>i < get_time tw\<close> add.commute trans_less_add2 tw'_def worldline_upd2_before_dly)
    finally have "property (i + 1) i (next_time_world tw', snd tw')"
      unfolding property_def by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
    hence "fst tw \<le> i" and "i < next_time_world tw' - 1"
      by auto
    hence "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (fst tw + 1)"
      using unchanged_until_next_time_world
      by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
          le_less_trans less_diff_conv)
    moreover have "lof_wline tw' IN i = lof_wline tw' IN (fst tw)"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw = get_time tw'\<close> \<open>get_time tw \<le> i\<close> \<open>i < next_time_world tw'\<close> worldline_upd2_before_dly)
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' OUT (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Sig (drop amount (lof_wline tw IN (fst tw) @ replicate amount False))"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule_tac[!] beval_cases)+
         prefer 2
        unfolding state_of_world_def
        apply (metis comp_apply drop_append drop_replicate val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Sig (drop amount (lof_wline tw' IN (fst tw) @ replicate amount False))"
        by (metis less_add_one tw'_def worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    ultimately have "property (i + 1) i (next_world tw')"
      unfolding property_def by auto }
  moreover
  { assume "i = next_time_world tw' - 1"
    hence "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (next_time_world tw')"
      using \<open>i < next_time_world tw'\<close> by force
    also have "... = lof_wline tw' OUT (fst tw + 1)"
      using \<open>fst tw < next_time_world tw'\<close> unfolding tw'_def worldline_upd2_def
      worldline_upd_def by auto
    finally have "lof_wline tw' OUT (i + 1) = lof_wline tw' OUT (fst tw + 1)"
      by auto
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' OUT (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Sig (drop amount (lof_wline tw IN (fst tw) @ replicate amount False))"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule_tac[!] beval_cases)+
        prefer 2
        unfolding state_of_world_def
        apply (metis comp_apply drop_append drop_replicate val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Sig (drop amount (lof_wline tw' IN (fst tw) @ replicate amount False))"
        by (metis less_add_one tw'_def worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    moreover have "lof_wline tw' IN i = lof_wline tw' IN (fst tw)"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw < next_time_world tw'\<close> \<open>get_time tw = get_time tw'\<close> \<open>i <
      next_time_world tw'\<close> \<open>i = next_time_world tw' - 1\<close> add_le_imp_le_diff discrete)+
    ultimately have "property (i + 1) i (next_world tw')"
      unfolding property_def by auto }
  ultimately show "property (i + 1) i (next_world tw')"
    by auto
qed

lemma type_correctness_length:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "beval_world_raw2 tw (Bshiftl (Bsig IN) amount) v"
  shows   "type_of v = Lty Uns len \<or> type_of v = Lty Sig len"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
    using assms(2) unfolding beval_world_raw2_def by auto
  have *: "type_of (state_of_world (snd tw) (fst tw) IN) = Lty Uns len
       \<or> type_of (state_of_world (snd tw) (fst tw) IN) = Lty Sig len"
    using assms(1) unfolding wityping_def
    by (metis (full_types) state_of_world_def unsigned_shift_left_axioms unsigned_shift_left_def wtyping_def)
  show ?thesis
    apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v\<close>])
    apply (erule beval_cases)+
    apply (metis *
        add.left_neutral add_diff_cancel_left' diff_is_0_eq' le_add_diff_inverse2 length_append
        length_drop length_replicate nat_le_linear rev_min_pm1 type_of.simps(2))
    apply (erule beval_cases)+
    apply (metis "*" add_left_imp_eq diff_le_self le_add_diff_inverse length_append length_drop
        length_replicate min_pm1 rev_min_pm1 type_of.simps(2))
    done
qed

lemma seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1
     [\<lambda>tw. inv (next_world tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv (next_world tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, simp)
  using inv_next_time_sig inv_next_time_uns type_correctness_length
  by (metis BassignE_hoare2 seq_stmt_preserve_wityping_hoare well_typed)

lemma seq_hoare_next_time0:
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1
     [\<lambda>tw. inv (next_world tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv (next_world tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, simp)
  using inv_next_time_sig inv_next_time_uns type_correctness_length unfolding inv_def
  by (metis BassignE_hoare2 gr_implies_not_zero seq_stmt_preserve_wityping_hoare well_typed)

lemma conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv (next_world tw)"
proof -
  fix tw
  assume "inv tw \<and> inv2 tw \<and> disjnt {IN} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {IN} (event_of tw)"
    by auto
  { fix i
    assume "i < next_time_world tw"
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "property (i + 1) i tw"
        using \<open>inv tw\<close> unfolding inv_def by auto
      hence "property (i + 1) i (next_world tw)"
        unfolding property_def by simp }
    moreover
    { assume "fst tw \<le> i"
      moreover have "\<forall>i \<ge> fst tw. property (i + 1) (fst tw) tw"
        using \<open>inv2 tw\<close> \<open>disjnt {IN} (event_of tw)\<close> unfolding inv2_def
        by auto
      ultimately have "property (i + 1) (fst tw) tw"
        by auto
      hence "property (i + 1) i tw"
        unfolding property_def
        by (metis \<open>get_time tw \<le> i\<close> \<open>i < next_time_world tw\<close> unchanged_until_next_time_world)
      hence "property (i + 1) i (next_world tw)"
        unfolding property_def by auto }
    ultimately have "property (i + 1) i (next_world tw)"
      by auto }
  thus "inv (next_world tw)"
    unfolding inv_def by auto
qed

lemma conc_hoare2:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv2 (next_world tw)"
proof -
  fix tw
  assume "inv tw \<and> inv2 tw \<and> disjnt {IN} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {IN} (event_of tw)"
    by auto
  let ?t' = "next_time_world tw"
  { assume "disjnt {IN} (event_of (next_world tw))"
    hence *: "lof_wline tw IN ?t' = lof_wline tw IN (?t' - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)
    have "fst tw < ?t'"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "?t' \<le> i"
      have "property (i + 1) (fst tw) tw"
        using \<open>inv2 tw\<close> \<open>disjnt {IN} (event_of tw)\<close> unfolding inv2_def
        using \<open>get_time tw < next_time_world tw\<close> \<open>next_time_world tw \<le> i\<close> by auto
      moreover have "lof_wline tw IN (fst tw) = lof_wline tw IN (?t' - 1)"
        by (metis \<open>get_time tw < next_time_world tw\<close> add_le_imp_le_diff diff_less discrete
        gr_implies_not0 not_less_iff_gr_or_eq unchanged_until_next_time_world zero_less_one)
      ultimately have "property (i + 1) ?t' (next_world tw)"
        unfolding property_def using *  by auto }
    hence "\<forall>i\<ge>?t'. property (i + 1) ?t' (next_world tw)"
      by auto }
  thus "inv2 (next_world tw)"
    unfolding inv2_def by auto
qed

lemma inv2_next_time_uns:
  fixes tw
  assumes "beval_world_raw2 tw (Bshiftl (Bsig IN) amount) v" and "type_of v = Lty Uns len"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv2 (next_time_world tw', snd tw')"
  unfolding inv2_def
proof (rule, rule, rule)
  fix i
  assume "disjnt {IN} (event_of (next_world tw'))"
  hence "IN \<notin> event_of (next_world tw')"
    by auto
  assume "fst (next_world tw') \<le> i"
  hence "next_time_world tw' \<le> i"
    by auto
  let ?t' = "next_time_world tw'"
  have "fst tw' < ?t'"
    using next_time_world_at_least by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < ?t'"
    by auto
  have 0: "wline_of (next_world tw') IN ?t' = wline_of tw IN (fst tw)"
  proof -
    have "wline_of tw' IN ?t' = wline_of tw' IN (?t' - 1)"
      using \<open>IN \<notin> event_of (next_world tw')\<close> unfolding event_of_alt_def
      using \<open>get_time tw' < next_time_world tw'\<close> by auto
    also have " ... = wline_of tw' IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 \<open>get_time tw' < next_time_world tw'\<close> diff_less
      gr_implies_not_zero le_0_eq less_Suc_eq_le not_less zero_less_one)
    also have "... = wline_of tw' IN (fst tw)"
      by (simp add: \<open>get_time tw = get_time tw'\<close>)
    also have "... = wline_of tw IN (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally show "wline_of (next_world tw') IN ?t' = wline_of tw IN (fst tw)"
      by auto
  qed
  have assm2: "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "wline_of (next_world tw') OUT (i + 1) = v"
  proof -
    have "wline_of tw' OUT (i + 1) = v"
      using `fst tw < ?t'` \<open>?t' \<le> i\<close>
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    thus ?thesis
      by auto
  qed
  also have "lval_of ... = drop amount (lof_wline tw IN (fst tw) @ replicate amount False)"
    apply (rule beval_world_raw_cases[OF assm2])
    apply (erule beval_cases)+
    apply (metis comp_def drop_append drop_replicate state_of_world_def val.sel(3))
    using assms(2) by auto
  finally have "property (i + 1) ?t' (next_world tw')"
    unfolding property_def using 0  by auto
  thus "property (i + 1) (get_time (next_time_world tw', snd tw')) (next_time_world tw', snd tw')"
    by auto
qed

lemma inv2_next_time_sig:
  fixes tw
  assumes "beval_world_raw2 tw (Bshiftl (Bsig IN) amount) v" and "type_of v = Lty Sig len"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv2 (next_time_world tw', snd tw')"
  unfolding inv2_def
proof (rule, rule, rule)
  fix i
  assume "disjnt {IN} (event_of (next_world tw'))"
  hence "IN \<notin> event_of (next_world tw')"
    by auto
  assume "fst (next_world tw') \<le> i"
  hence "next_time_world tw' \<le> i"
    by auto
  let ?t' = "next_time_world tw'"
  have "fst tw' < ?t'"
    using next_time_world_at_least by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < ?t'"
    by auto
  have 0: "wline_of (next_world tw') IN ?t' = wline_of tw IN (fst tw)"
  proof -
    have "wline_of tw' IN ?t' = wline_of tw' IN (?t' - 1)"
      using \<open>IN \<notin> event_of (next_world tw')\<close> unfolding event_of_alt_def
      using \<open>get_time tw' < next_time_world tw'\<close> by auto
    also have " ... = wline_of tw' IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 \<open>get_time tw' < next_time_world tw'\<close> diff_less
      gr_implies_not_zero le_0_eq less_Suc_eq_le not_less zero_less_one)
    also have "... = wline_of tw' IN (fst tw)"
      by (simp add: \<open>get_time tw = get_time tw'\<close>)
    also have "... = wline_of tw IN (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally show "wline_of (next_world tw') IN ?t' = wline_of tw IN (fst tw)"
      by auto
  qed
  have assm2: "beval_world_raw (snd tw) (fst tw) (Bshiftl (Bsig IN) amount) v"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "wline_of (next_world tw') OUT (i + 1) = v"
  proof -
    have "wline_of tw' OUT (i + 1) = v"
      using `fst tw < ?t'` \<open>?t' \<le> i\<close>
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    thus ?thesis
      by auto
  qed
  also have "lval_of ... = drop amount (lof_wline tw IN (fst tw) @ replicate amount False)"
    apply (rule beval_world_raw_cases[OF assm2])
    apply (erule_tac[!] beval_cases)+
    apply (metis comp_def drop_append drop_replicate state_of_world_def val.sel(3))
    by (metis comp_def drop_append drop_replicate state_of_world_def val.sel(3))
  finally have "property (i + 1) ?t' (next_world tw')"
    unfolding property_def using 0  by auto
  thus "property (i + 1) (get_time (next_time_world tw', snd tw')) (next_time_world tw', snd tw')"
    by auto
qed

lemma seq_hoare_next_time1:
  shows "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1 [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_next_time_sig inv2_next_time_uns type_correctness_length by blast

lemma conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> shiftl amount \<lbrace>\<lambda>tw. inv (next_time_world tw, snd tw) \<and> inv2 (next_time_world tw, snd tw)\<rbrace>"
  unfolding shiftl_def
  apply (rule Single)
   apply (rule Conj)
    apply (rule strengthen_precondition)
  apply (rule strengthen_precondition)
    apply (rule seq_hoare_next_time)
  apply (rule strengthen_precondition)
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition2)
   apply (rule seq_hoare_next_time1)
  using conc_hoare conc_hoare2 by blast

lemma seq_wt_sub:
  "seq_wt \<Gamma> (Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1)"
  using well_typed by blast

lemma conc_hoare4:
  "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> shiftl amount \<lbrace>\<lambda>tw. (inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)) \<and> inv2 (next_time_world tw, snd tw)\<rbrace>"
  apply (rule Conj2)
   apply (rule Conj2)
    apply (rule weaken_post_conc_hoare[OF _ conc_hoare3], blast)
   apply (rule strengthen_pre_conc_hoare[rotated])
    apply (unfold shiftl_def, rule single_conc_stmt_preserve_wityping_hoare)
    apply (rule seq_wt_sub)
   apply blast
  apply (fold shiftl_def, rule weaken_post_conc_hoare[OF _ conc_hoare3], blast)
  done

lemma conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> shiftl amount \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace>"
  apply (rule While)
  apply (unfold snd_conv, rule conc_hoare4)
  done

lemma conc_sim2:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> shiftl amount \<lbrace>inv\<rbrace>"
  using conc_sim' Conseq_sim by blast

lemma init_sat_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) (shiftl amount) (\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding shiftl_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conj)
  unfolding snd_conv apply(rule seq_hoare_next_time0)
  apply (rule strengthen_precondition2)
  by (metis seq_stmt_preserve_wityping_hoare well_typed)

lemma init_sat_inv2:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) (shiftl amount) inv2"
  unfolding shiftl_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv apply (rule seq_hoare_next_time1)
  done

lemma init_sat_inv_comb:
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) (shiftl amount)  (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_inv)
  apply (rule ConseqI_sim[rotated])
  apply (rule init_sat_inv2)
  by blast+

lemma correctness:
  assumes "sim_fin w (i + 1) (shiftl amount) tw'" and "wityping \<Gamma> w"
  shows   "property (i + 1) i tw'"
proof -
  obtain tw where "init_sim (0, w) (shiftl amount) tw" and  "tw, i + 1, shiftl amount \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf (shiftl amount)"
    unfolding conc_stmt_wf_def shiftl_def by auto
  moreover have "nonneg_delay_conc (shiftl amount)"
    unfolding shiftl_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) (shiftl amount) (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_inv_comb]
    by (metis (no_types, lifting) conc_wt_cases(1) init_sat_inv_comb
    init_sim_hoare_soundness sub_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv2 tw"
    using \<open>init_sim (0, w) (shiftl amount) tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv2 tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> shiftl amount \<lbrace>inv\<rbrace>"
    using conc_sim_soundness[OF conc_sim2] \<open>conc_stmt_wf (shiftl amount)\<close> \<open>nonneg_delay_conc (shiftl amount)\<close>
    by auto
  ultimately have "inv tw'"
    using \<open>tw, i + 1, shiftl amount \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    unfolding inv_def by auto
qed

lemma correctness_wityping:
  assumes "sim_fin w (i + 1) (shiftl amount) tw'" and "wityping \<Gamma> w"
  shows   "wityping \<Gamma> (snd tw')"
proof -
  obtain tw where "init_sim (0, w) (shiftl amount) tw" and  "tw, i + 1, (shiftl amount) \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf (shiftl amount)"
    unfolding conc_stmt_wf_def shiftl_def by auto
  moreover have "nonneg_delay_conc (shiftl amount)"
    unfolding shiftl_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) (shiftl amount) (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_inv_comb]
    by (metis (no_types, lifting) conc_wt_cases(1) init_sat_inv_comb
    init_sim_hoare_soundness sub_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv2 tw"
    using \<open>init_sim (0, w) (shiftl amount) tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv2 tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> (shiftl amount) \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace>"
    using conc_sim_soundness[OF conc_sim'] \<open>conc_stmt_wf (shiftl amount)\<close> \<open>nonneg_delay_conc (shiftl amount)\<close>
    by (metis (no_types, lifting) sim_hoare_valid_def)
  ultimately show "wityping \<Gamma> (snd tw')"
    using \<open>tw, i + 1, (shiftl amount) \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
qed

corollary correctness2:
  assumes "sim_fin w (i + 1) (shiftl amount) tw'" and "wityping \<Gamma> w"
  defines "bsIN  \<equiv> lof_wline tw' IN i"
  defines "bsOUT \<equiv> lof_wline tw' OUT (i + 1)"
  shows   "(\<Sum>i = 0..<length bsOUT. (int \<circ> of_bool) (rev bsOUT ! i) * 2 ^ i) =
          ((\<Sum>i = 0..<length bsIN. (int \<circ> of_bool) (rev bsIN  ! i) * 2 ^ i) * 2 ^ amount) mod 2 ^ len "
proof -
  have "property (i + 1) i tw'" and "wityping \<Gamma> (snd tw')"
    using correctness[OF assms(1-2)] correctness_wityping[OF assms(1-2)] by auto
  hence "lof_wline tw' OUT (i + 1) = drop amount (lof_wline tw' IN i @ replicate amount False)"
    unfolding property_def by auto
  hence "bsOUT = drop amount (bsIN @ replicate amount False)" (is "_ = ?rhs")
    unfolding bsIN_def bsOUT_def by auto
  hence "bl_to_bin bsOUT = bl_to_bin ?rhs"
    by auto
  also have "... = bintrunc (length bsIN) (bl_to_bin (bsIN @ replicate amount False))"
    unfolding bl2bin_drop by auto
  also have "... = bl_to_bin (bsIN @ replicate amount False) mod 2 ^ length bsIN"
    unfolding bintrunc_mod2p by auto
  finally have "bl_to_bin bsOUT = bl_to_bin (bsIN @ replicate amount False) mod 2 ^ length bsIN"
    by auto
  moreover have "bl_to_bin (bsIN @ replicate amount False) = bl_to_bin bsIN * 2 ^ amount"
    by (simp add: bin_cat_num bl_to_bin_app_cat bl_to_bin_rep_False)
  moreover have "len = length bsIN"
    by (smt \<open>wityping \<Gamma> (snd tw')\<close> assms(3) comp_apply ty.distinct(1) ty.inject type_of.elims
    unsigned_shift_left_axioms unsigned_shift_left_def val.sel(3) wityping_def wtyping_def)
  ultimately have "bl_to_bin bsOUT = (bl_to_bin bsIN * 2 ^ amount) mod 2 ^ len"
    by auto
  thus ?thesis
    unfolding bl_to_bin_correctness by auto
qed

end

end

