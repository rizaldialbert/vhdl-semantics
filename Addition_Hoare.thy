(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Addition_Hoare
  imports VHDL_Hoare_Complete Bits_Int_Aux
begin

datatype sig = A | B | C

definition add :: "sig conc_stmt" where
  "add \<equiv> process {A, B} : Bassign_trans C (Badd (Bsig A) (Bsig B)) 1"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  shows "\<exists>len1>0. \<exists>len2>0. \<Gamma> A = Lty Uns len1 \<and> \<Gamma> B = Lty Uns len2 \<and> \<Gamma> C = Lty Uns (max len1 len2)
                         \<or> \<Gamma> A = Lty Sig len1 \<and> \<Gamma> B = Lty Sig len2 \<and> \<Gamma> C = Lty Sig (max len1 len2)"
proof (rule seq_wt_cases(4)[OF assms])
  assume "bexp_wt \<Gamma> (Badd (Bsig A) (Bsig B)) (\<Gamma> C)"
  obtain len1 len2 where " \<Gamma> A = Lty Uns len1 \<and> \<Gamma> B = Lty Uns len2 \<and> \<Gamma> C = Lty Uns (max len1 len2)
                              \<or> \<Gamma> A = Lty Sig len1 \<and> \<Gamma> B = Lty Sig len2 \<and> \<Gamma> C = Lty Sig (max len1 len2)"
          and "0 < len1" and "0 < len2"
    by (rule bexp_wt_cases(11)[OF \<open>bexp_wt \<Gamma> (Badd (Bsig A) (Bsig B)) (\<Gamma> C)\<close>])
       (metis bexp_wt_cases(9))+
  thus ?thesis
    by auto
qed

locale unsigned_addition =
  fixes \<Gamma> :: "sig tyenv"
  fixes len len1 len2 :: nat
  assumes len_def: "len = max len1 len2"
  assumes atype: "\<Gamma> A = Lty Uns len1" and btype: "\<Gamma> B = Lty Uns len2" and ctype: "\<Gamma> C = Lty Uns len"
  assumes len1: "0 < len1" and len2: "0 < len2"
begin

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  apply (rule seq_wt.intros(4))
  unfolding ctype len_def apply (rule bexp_wt.intros(15))
  unfolding atype[THEN sym] btype[THEN sym]
     apply (rule bexp_wt.intros(3))+
   apply (rule len1)
  apply (rule len2)
  done

abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

term "bin_to_bl len (bl_to_bin bs1 + bl_to_bin bs2)"

text \<open>Here we factor out common expression in both inv1 and inv2. It is parametrised by the index
we are interested with for C (first argument) and A (the second argument). Note that the index
we are interested with for A should be the same as the index for B.\<close>

definition property :: "nat \<Rightarrow> nat \<Rightarrow> sig assn2" where
  "property idxc idx =
      (\<lambda>tw. lof_wline tw C idxc =
                  bin_to_bl len (bl_to_bin (lof_wline tw A idx) + bl_to_bin (lof_wline tw B idx)))"

definition inv :: "sig assn2" where
  "inv tw \<equiv> (\<forall>i < fst tw. property (i + 1) i tw)"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> (disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i \<ge> fst tw. property (i + 1) (fst tw) tw))"

abbreviation "next_world tw \<equiv> (next_time_world tw, snd tw)"

lemma inv_next_time:
  assumes "inv tw"
  assumes "beval_world_raw2 tw (Badd (Bsig A) (Bsig B)) v" and "type_of v = Lty Uns len"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. inv (j, snd tw')"
  unfolding inv_def
proof (rule, rule, rule)
  fix i j
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  assume "i < fst (j, snd tw')"
  hence "i < j"
    by auto
  have "fst tw < j"
    by (metis \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> greaterThanAtMost_iff snd_conv snd_swap
    swap_simp tw'_def worldline_upd2_def)
  hence "i < fst tw \<or> fst tw \<le> i \<and> i < j - 1 \<or> i = j - 1"
    using \<open>i < j\<close> by linarith
  moreover
  { assume "i < fst tw"
    have "lof_wline tw' C (i + 1) = lof_wline tw C (i + 1)"
      by (metis \<open>i < get_time tw\<close> add_mono1 tw'_def worldline_upd2_before_dly)
    also have "... = bin_to_bl len (bl_to_bin (lof_wline tw A i) + bl_to_bin (lof_wline tw B i))"
      using assms(1) \<open>i < fst tw\<close> unfolding inv_def property_def by auto
    also have "... = bin_to_bl len (bl_to_bin (lof_wline tw' A i) + bl_to_bin (lof_wline tw' B i))"
      by (metis \<open>i < get_time tw\<close> add.commute trans_less_add2 tw'_def worldline_upd2_before_dly)
    finally have "property (i + 1) i (j, snd tw')"
      unfolding property_def by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < j - 1"
    hence "fst tw \<le> i" and "i < j - 1"
      by auto
    hence "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
      using unchanged_until_next_time_world
      by (smt \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> dual_order.strict_trans1
      greaterThanAtMost_iff le_add1 less_diff_conv not_less prod.exhaust_sel prod.inject tw'_def
      worldline_upd2_def)
    moreover have "lof_wline tw' A i = lof_wline tw' A (fst tw)" and "lof_wline tw' B i = lof_wline tw' B (fst tw)"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Pair_inject \<open>get_time tw \<le> i\<close> \<open>i < j\<close> \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> dual_order.strict_trans1 greaterThanAtMost_iff prod.exhaust_sel tw'_def worldline_upd2_def)+
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' C (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Uns (bin_to_bl_aux len (bl_to_bin (lof_wline tw A (fst tw)) + bl_to_bin (lof_wline tw B (fst tw))) [])"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule beval_cases)+
        unfolding state_of_world_def using atype btype
        apply (metis assms(3) bin_to_bl_def comp_def size_bin_to_bl ty.inject type_of.simps(2) val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Uns (bin_to_bl_aux len (bl_to_bin (lof_wline tw' A (fst tw)) + bl_to_bin (lof_wline tw' B (fst tw))) [])"
        by (metis Suc_eq_plus1 \<open>lval_of (wline_of tw' A i) = lval_of (wline_of tw' A (get_time tw))\<close>
        \<open>lval_of (wline_of tw' B i) = lval_of (wline_of tw' B (get_time tw))\<close> lessI tw'_def
        worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    ultimately have "property (i + 1) i (j, snd tw')"
      unfolding property_def by auto }
  moreover
  { assume "i = j - 1"
    hence "lof_wline tw' C (i + 1) = lof_wline tw' C (next_time_world tw')"
      using \<open>i < j\<close>
      by (smt \<open>get_time tw < j\<close> add_diff_cancel_left' comp_apply discrete
      dual_order.order_iff_strict fst_conv leD le_add1 less_imp_Suc_add next_time_world_at_least
      plus_1_eq_Suc snd_conv tw'_def worldline_upd2_def worldline_upd_def)
    also have "... = lof_wline tw' C (fst tw + 1)"
      using \<open>fst tw < j\<close> unfolding tw'_def worldline_upd2_def
      worldline_upd_def 
      by (smt Suc_lessI add.commute comp_apply fst_conv next_time_world_at_least order.asym
      plus_1_eq_Suc snd_conv)
    finally have "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
      by auto
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' C (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Uns (bin_to_bl_aux len (bl_to_bin (lof_wline tw A (fst tw)) + bl_to_bin (lof_wline tw B (fst tw))) [])"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule beval_cases)+
        unfolding state_of_world_def using atype btype
        apply (metis assms(3) bin_to_bl_def comp_def size_bin_to_bl ty.inject type_of.simps(2) val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Uns (bin_to_bl_aux len (bl_to_bin (lof_wline tw' A (fst tw)) + bl_to_bin (lof_wline tw' B (fst tw))) [])"
        by (metis less_add_one tw'_def worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    moreover have "lof_wline tw' A i = lof_wline tw' A (fst tw)" and "lof_wline tw' B i = lof_wline tw' B (fst tw)"
      using unchanged_until_next_time_world
      by (smt Pair_inject Suc_eq_plus1 Suc_lessI \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in> {get_time
      tw'<..next_time_world tw'}\<close> dual_order.strict_trans1 greaterThanAtMost_iff less_diff_conv
      less_or_eq_imp_le not_le prod.exhaust_sel tw'_def worldline_upd2_def)+
    ultimately have "property (i + 1) i (j, snd tw')"
      unfolding property_def by auto }
  ultimately show "property (i + 1) i (j, snd tw')"
    by auto
qed

lemma type_correctness_length:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "beval_world_raw2 tw (Badd (Bsig A) (Bsig B)) v"
  shows   "type_of v = Lty Uns len"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
    using assms(2) unfolding beval_world_raw2_def by auto
  have "type_of (state_of_world (snd tw) (fst tw) A) = Lty Uns len1" and
       "type_of (state_of_world (snd tw) (fst tw) B) = Lty Uns len2"
    using assms(1) unfolding wityping_def
    by (simp add: atype btype state_of_world_def wtyping_def)+
  show ?thesis
    apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v\<close>])
    apply (erule beval_cases)
    apply (metis (no_types, lifting) \<open>type_of (state_of_world (snd tw) (get_time tw) A) = Lty Uns len1\<close> \<open>type_of (state_of_world (snd tw) (get_time tw) B) = Lty Uns len2\<close> add.right_neutral beval_cases(1) len_def list.size(3) size_bin_to_bl_aux ty.inject type_of.simps(2))
    apply (metis (no_types, lifting) \<open>type_of (state_of_world (snd tw) (get_time tw) A) = Lty Uns len1\<close> beval_cases(1) signedness.distinct(5) ty.inject type_of.simps(2))
    done
qed

lemma add_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans C (Badd (Bsig A) (Bsig B)) 1
     [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, simp)
  using inv_next_time type_correctness_length
  by (metis ctype snd_conv worldline_upd2_def worldline_upd_preserve_wityping)

lemma add_seq_hoare_next_time0:
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans C (Badd (Bsig A) (Bsig B)) 1
     [\<lambda>tw. inv (next_world tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2)
  using next_time_world_at_least apply fastforce
  using inv_next_time type_correctness_length unfolding inv_def
  by (metis ctype gr_implies_not0 snd_conv worldline_upd2_def worldline_upd_preserve_wityping)

lemma add_conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw)"
proof (rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j
  assume "j \<in> {fst tw <.. next_time_world tw}"
  assume "inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  { fix i
    assume "i < j"
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "property (i + 1) i tw"
        using \<open>inv tw\<close> unfolding inv_def by auto
      hence "property (i + 1) i (j, snd tw)"
        unfolding property_def by simp }
    moreover
    { assume "fst tw \<le> i"
      moreover have "\<forall>i \<ge> fst tw. property (i + 1) (fst tw) tw"
        using \<open>inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding inv2_def
        by auto
      ultimately have "property (i + 1) (fst tw) tw"
        by auto
      hence "property (i + 1) i tw"
        unfolding property_def
        by (smt \<open>get_time tw \<le> i\<close> \<open>i < j\<close> \<open>j \<in> {get_time tw<..next_time_world tw}\<close>
        dual_order.strict_trans1 greaterThanAtMost_iff unchanged_until_next_time_world)
      hence "property (i + 1) i (j, snd tw)"
        unfolding property_def by auto }
    ultimately have "property (i + 1) i (j, snd tw)"
      by auto }
  thus "inv (j, snd tw)"
    unfolding inv_def by auto
qed


lemma add_conc_hoare2:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. inv2 (j, snd tw)"
proof (rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j :: nat
  assume "j \<in> {fst tw <.. next_time_world tw}"
  assume "inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  { assume "disjnt {A, B} (event_of (j, snd tw))"
    hence *: "lof_wline tw A j = lof_wline tw A (j - 1)" and **: "lof_wline tw B j = lof_wline tw B (j - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < j"
      using \<open>j \<in> {get_time tw<..next_time_world tw}\<close> greaterThanAtMost_iff by blast
    { fix i
      assume "j \<le> i"
      have "property (i + 1) (fst tw) tw"
        using \<open>inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding inv2_def
        using \<open>fst tw < j\<close> \<open>j \<le> i\<close> by auto
      moreover have "lof_wline tw A (fst tw) = lof_wline tw A (j - 1)" and
                    "lof_wline tw B (fst tw) = lof_wline tw B (j - 1)"
        by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 \<open>j \<in> {get_time tw<..next_time_world
        tw}\<close> add_le_imp_le_diff diff_add discrete gr_implies_not0 greaterThanAtMost_iff
        not_less_iff_gr_or_eq unchanged_until_next_time_world)+
      ultimately have "property (i + 1) j (j, snd tw)"
        unfolding property_def using * **  by auto }
    hence "\<forall>i\<ge>j. property (i + 1) j (j, snd tw)"
      by auto }
  thus "inv2 (j, snd tw)"
    unfolding inv2_def by auto
qed

lemma inv2_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Badd (Bsig A) (Bsig B)) v" and "type_of v = Lty Uns len"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. inv2 (j, snd tw')"
  unfolding inv2_def
proof (rule)+
  fix j i
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  assume "disjnt {A, B} (event_of (j, snd tw'))"
  hence "A \<notin> event_of (j, snd tw')" and "B \<notin> event_of (j, snd tw')"
    by auto
  assume "fst (j, snd tw') \<le> i"
  hence "j \<le> i"
    by auto
  have "fst tw < j"
    by (metis \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> greaterThanAtMost_iff prod.exhaust_sel
    prod.inject tw'_def worldline_upd2_def)
  have 0: "wline_of (j, snd tw') A j = wline_of tw A (fst tw)"
  proof -
    have "wline_of tw' A j = wline_of tw' A (j - 1)"
      using \<open>A \<notin> event_of (j, snd tw')\<close> unfolding event_of_alt_def
      using \<open>fst tw < j\<close> by auto
    also have " ... = wline_of tw' A (fst tw')"
      using unchanged_until_next_time_world
      by (metis (mono_tags, lifting) Suc_diff_1 \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close>
      gr_implies_not_zero greaterThanAtMost_iff le_0_eq less_Suc_eq_le not_less)
    also have "... = wline_of tw' A (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = wline_of tw A (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally show "wline_of (j, snd tw') A j = wline_of tw A (fst tw)"
      by auto
  qed
  have 1: "wline_of (j, snd tw') B j = wline_of tw B (fst tw)"
  proof -
    have "wline_of tw' B j = wline_of tw' B (j - 1)"
      using \<open>B \<notin> event_of (j, snd tw')\<close> unfolding event_of_alt_def
      using \<open>fst tw < j\<close> by auto
    also have " ... = wline_of tw' B (fst tw')"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close>
      dual_order.order_iff_strict greaterThanAtMost_iff le_0_eq less_Suc_eq_le not_less)
    also have "... = wline_of tw' B (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = wline_of tw B (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally show "wline_of (j, snd tw') B j = wline_of tw B (fst tw)"
      by auto
  qed
  have assm2: "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "wline_of (next_world tw') C (i + 1) = v"
  proof -
    have "wline_of tw' C (i + 1) = v"
      using `fst tw < j` \<open>j \<le> i\<close>
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    thus ?thesis
      by auto
  qed
  also have "lval_of ... = bin_to_bl len (bl_to_bin (lof_wline tw A (fst tw)) + bl_to_bin (lof_wline tw B (fst tw)))"
    apply (rule beval_world_raw_cases[OF assm2])
    apply (erule beval_cases)+
    apply (metis assms(2) beval_raw.intros(1) beval_world_raw.simps beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic bin_to_bl_def size_bin_to_bl ty.inject type_of.simps(2) val.sel(3))
    using assms(2) by auto
  finally have "property (i + 1) j (j, snd tw')"
    unfolding property_def using 0 1  by auto
  thus "property (i + 1) (get_time (j, snd tw')) (j, snd tw')"
    by auto
qed

lemma add_seq_hoare_next_time1:
  "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_trans C (Badd (Bsig A) (Bsig B)) 1 [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv2 (i, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_next_time type_correctness_length by blast

lemma seq_wt_add:
  "seq_wt \<Gamma> (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  using well_typed by blast

lemma add_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw) \<and> inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule Conj2)
  unfolding add_def
   apply (rule Single)
    apply(rule Conj_univ_qtfd[where Q="inv" and R="inv2"])
     apply (rule strengthen_precondition)
     apply (rule strengthen_precondition)
     apply (rule add_seq_hoare_next_time)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition2)
    apply (rule add_seq_hoare_next_time1)
  using add_conc_hoare add_conc_hoare2 apply blast
  apply (rule strengthen_pre_conc_hoare[rotated])
  apply (rule single_conc_stmt_preserve_wityping_hoare)
   apply (rule seq_wt_add)
  by simp

lemma add_conc_hoare4:
  "\<turnstile> \<lbrace>\<lambda>tw. (local.inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add
       \<lbrace>\<lambda>tw. \<forall>i\<in>{get_time tw<..next_time_world tw}. (local.inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)) \<and> inv2 (i, snd tw)\<rbrace>"
  apply (rule Conseq'[rotated])
  apply (rule add_conc_hoare3)
  by auto

lemma add_conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace>"
  apply (rule While)
  unfolding snd_conv
  apply (rule add_conc_hoare4)
  done

lemma add_conc_sim2:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>inv\<rbrace>"
  using add_conc_sim' Conseq_sim by blast

lemma init_sat_add_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add (\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding add_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conj)
  unfolding snd_conv apply(rule add_seq_hoare_next_time0)
  apply (rule strengthen_precondition2)
  by (metis seq_stmt_preserve_wityping_hoare well_typed)

lemma init_sat_add_inv2:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) add inv2"
  unfolding add_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv 
  apply (rule Conseq2[rotated])
    apply (rule add_seq_hoare_next_time1)
   apply (simp add: next_time_world_at_least)
  by auto

lemma init_sat_add_inv_comb:
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add  (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_add_inv)
  apply (rule ConseqI_sim[rotated])
  apply (rule init_sat_add_inv2)
  by blast+

lemma add_correctness:
  assumes "sim_fin w (i + 1) add tw'" and "wityping \<Gamma> w"
  shows   "property (i + 1) i tw'"
proof -
  obtain tw where "init_sim (0, w) add tw" and  "tw, i + 1, add \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf add"
    unfolding conc_stmt_wf_def add_def by auto
  moreover have "nonneg_delay_conc add"
    unfolding add_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_add_inv_comb]
    by (metis (no_types, lifting) conc_wt_cases(1) init_sat_add_inv_comb
    init_sim_hoare_soundness add_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv2 tw"
    using \<open>init_sim (0, w) add tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv2 tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>inv\<rbrace>"
    using conc_sim_soundness[OF add_conc_sim2] \<open>conc_stmt_wf add\<close> \<open>nonneg_delay_conc add\<close>
    by auto
  ultimately have "inv tw'"
    using \<open>tw, i + 1, add \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    unfolding inv_def  by (metis less_add_one)
qed

corollary add_correctness2:
  assumes "sim_fin w (i + 1) add tw'" and "wityping \<Gamma> w"
  defines "bsA \<equiv> lof_wline tw' A i"
  defines "bsB \<equiv> lof_wline tw' B i"
  defines "bsC \<equiv> lof_wline tw' C (i + 1)"
  shows   "(\<Sum>i = 0..<length bsC. (int \<circ> of_bool) (rev bsC ! i) * 2 ^ i) =
          ((\<Sum>i = 0..<length bsA. (int \<circ> of_bool) (rev bsA ! i) * 2 ^ i) +
           (\<Sum>i = 0..<length bsB. (int \<circ> of_bool) (rev bsB ! i) * 2 ^ i) ) mod 2 ^ len "
proof -
  have "property (i + 1) i tw'"
    using add_correctness[OF assms(1-2)] by auto
  hence "lof_wline tw' C (i + 1) =
                  bin_to_bl len (bl_to_bin (lof_wline tw' A i) + bl_to_bin (lof_wline tw' B i))"
    unfolding property_def by auto
  hence "bsC = bin_to_bl len (bl_to_bin bsA + bl_to_bin bsB)" (is "_ = ?rhs")
    unfolding bsA_def bsB_def bsC_def by auto
  hence "bl_to_bin bsC = bl_to_bin ?rhs"
    by auto
  also have "... = bintrunc len (bl_to_bin bsA + bl_to_bin bsB)"
    unfolding bin_bl_bin by auto
  also have "... = (bl_to_bin bsA + bl_to_bin bsB) mod 2 ^ len"
    unfolding bintrunc_mod2p by auto
  finally have "bl_to_bin bsC = (bl_to_bin bsA + bl_to_bin bsB) mod 2 ^ len"
    by auto
  thus ?thesis
    unfolding bl_to_bin_correctness by auto
qed

end

locale signed_addition =
  fixes \<Gamma> :: "sig tyenv"
  fixes len len1 len2 :: nat
  assumes len_def: "len = max len1 len2"
  assumes atype: "\<Gamma> A = Lty Sig len1" and btype: "\<Gamma> B = Lty Sig len2" and ctype: "\<Gamma> C = Lty Sig len"
  assumes len1 : "0 < len1" and len2: "0 < len2"
begin

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  apply (rule seq_wt.intros(4))
  apply (metis atype bexp_wt.intros(16) bexp_wt.intros(3) btype ctype len_def len1 len2)
  done

abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

text \<open>Here we factor out common expression in both inv1 and inv2. It is parametrised by the index
we are interested with for C (first argument) and A (the second argument). Note that the index
we are interested with for A should be the same as the index for B.\<close>

definition property :: "nat \<Rightarrow> nat \<Rightarrow> sig assn2" where
  "property idxc idx =
      (\<lambda>tw. lof_wline tw C idxc =
                  bin_to_bl len (sbl_to_bin (lof_wline tw A idx) + sbl_to_bin (lof_wline tw B idx)))"

definition inv :: "sig assn2" where
  "inv tw \<equiv> (\<forall>i < fst tw. property (i + 1) i tw)"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> (disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i \<ge> fst tw. property (i + 1) (fst tw) tw))"

abbreviation "next_world tw \<equiv> (next_time_world tw, snd tw)"

lemma inv_next_time:
  assumes "inv tw"
  assumes "beval_world_raw2 tw (Badd (Bsig A) (Bsig B)) v" and "type_of v = Lty Sig len"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. inv (j, snd tw')"
  unfolding inv_def
proof (rule, rule, rule)
  fix i j
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  assume "i < fst (j, snd tw')"
  hence "i < j"
    by auto
  have "fst tw < j"
    by (metis \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> greaterThanAtMost_iff snd_conv snd_swap
    swap_simp tw'_def worldline_upd2_def)
  hence "i < fst tw \<or> fst tw \<le> i \<and> i < j - 1 \<or> i = j - 1"
    using \<open>i < j\<close> by linarith
  moreover
  { assume "i < fst tw"
    have "lof_wline tw' C (i + 1) = lof_wline tw C (i + 1)"
      by (metis \<open>i < get_time tw\<close> add_mono1 tw'_def worldline_upd2_before_dly)
    also have "... = bin_to_bl len (sbl_to_bin (lof_wline tw A i) + sbl_to_bin (lof_wline tw B i))"
      using assms(1) \<open>i < fst tw\<close> unfolding inv_def property_def by auto
    also have "... = bin_to_bl len (sbl_to_bin (lof_wline tw' A i) + sbl_to_bin (lof_wline tw' B i))"
      by (metis \<open>i < get_time tw\<close> add.commute trans_less_add2 tw'_def worldline_upd2_before_dly)
    finally have "property (i + 1) i (j, snd tw')"
      unfolding property_def by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < j - 1"
    hence "fst tw \<le> i" and "i < j - 1"
      by auto
    hence "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
      using unchanged_until_next_time_world
      by (smt Pair_inject \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> dual_order.strict_trans1
      greaterThanAtMost_iff le_add1 less_diff_conv not_less prod.exhaust_sel tw'_def
      worldline_upd2_def)
    moreover have "lof_wline tw' A i = lof_wline tw' A (fst tw)" and "lof_wline tw' B i = lof_wline tw' B (fst tw)"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Pair_inject \<open>get_time tw \<le> i\<close> \<open>i < j\<close> \<open>j \<in> {get_time
      tw'<..next_time_world tw'}\<close> dual_order.strict_trans1 greaterThanAtMost_iff prod.exhaust_sel
      tw'_def worldline_upd2_def)+
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' C (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Sig (bin_to_bl_aux len (sbl_to_bin (lof_wline tw A (fst tw)) + sbl_to_bin (lof_wline tw B (fst tw))) [])"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule beval_cases)
        defer
        apply ( erule beval_cases)+
        unfolding state_of_world_def using atype btype
        apply (metis assms(3) bin_to_bl_def comp_apply size_bin_to_bl ty.inject type_of.simps(2) val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Sig (bin_to_bl_aux len (sbl_to_bin (lof_wline tw' A (fst tw)) + sbl_to_bin (lof_wline tw' B (fst tw))) [])"
        by (metis Suc_eq_plus1 \<open>lval_of (wline_of tw' A i) = lval_of (wline_of tw' A (get_time tw))\<close>
        \<open>lval_of (wline_of tw' B i) = lval_of (wline_of tw' B (get_time tw))\<close> lessI tw'_def
        worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    ultimately have "property (i + 1) i (j, snd tw')"
      unfolding property_def by auto }
  moreover
  { assume "i = j - 1"
    hence "lof_wline tw' C (i + 1) = lof_wline tw' C (j)"
      using \<open>i < j\<close> by force
    also have "... = lof_wline tw' C (fst tw + 1)"
      using \<open>fst tw < j\<close> unfolding tw'_def worldline_upd2_def
      worldline_upd_def by auto
    finally have "lof_wline tw' C (i + 1) = lof_wline tw' C (fst tw + 1)"
      by auto
    moreover have "property (fst tw + 1) (fst tw) tw'"
    proof -
      have assm2: "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' C (fst tw + 1) = v"
        unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... =  Lv Sig (bin_to_bl_aux len (sbl_to_bin (lof_wline tw A (fst tw)) + sbl_to_bin (lof_wline tw B (fst tw))) [])"
        apply (rule beval_world_raw_cases[OF assm2])
        apply ( erule beval_cases)
        defer
        apply ( erule beval_cases)+
        unfolding state_of_world_def using atype btype
        apply (metis assms(3) bin_to_bl_def comp_def size_bin_to_bl ty.inject type_of.simps(2) val.sel(3))
        using assms(3) by auto
      also have "... =  Lv Sig (bin_to_bl_aux len (sbl_to_bin (lof_wline tw' A (fst tw)) + sbl_to_bin (lof_wline tw' B (fst tw))) [])"
        by (metis less_add_one tw'_def worldline_upd2_before_dly)
      finally show ?thesis
        unfolding property_def bin_to_bl_def by auto
    qed
    moreover have "lof_wline tw' A i = lof_wline tw' A (fst tw)" and "lof_wline tw' B i = lof_wline tw' B (fst tw)"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessI \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in> {get_time
      tw'<..next_time_world tw'}\<close> discrete greaterThanAtMost_iff less_diff_conv less_or_eq_imp_le
      not_less prod.exhaust_sel prod.inject tw'_def worldline_upd2_def)+
    ultimately have "property (i + 1) i (j, snd tw')"
      unfolding property_def by auto }
  ultimately show "property (i + 1) i (j, snd tw')"
    by auto
qed

lemma type_correctness_length:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "beval_world_raw2 tw (Badd (Bsig A) (Bsig B)) v"
  shows   "type_of v = Lty Sig len"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
    using assms(2) unfolding beval_world_raw2_def by auto
  have "type_of (state_of_world (snd tw) (fst tw) A) = Lty Sig len1" and
       "type_of (state_of_world (snd tw) (fst tw) B) = Lty Sig len2"
    using assms(1) unfolding wityping_def
    by (simp add: atype btype state_of_world_def wtyping_def)+
  show ?thesis
    apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v\<close>])
    apply (erule beval_cases)
    apply (metis (no_types, hide_lams) \<open>type_of (state_of_world (snd tw) (get_time tw) A) = Lty Sig len1\<close> beval_cases(1) signedness.distinct(5) ty.inject type_of.simps(2))
    apply (metis \<open>type_of (state_of_world (snd tw) (get_time tw) A) = Lty Sig len1\<close> \<open>type_of (state_of_world (snd tw) (get_time tw) B) = Lty Sig len2\<close> beval_cases(1) bin_to_bl_def len_def size_bin_to_bl ty.inject type_of.simps(2) val.sel(3))
    done
qed

lemma add_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans C (Badd (Bsig A) (Bsig B)) 1
     [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2, simp)
  using inv_next_time type_correctness_length
  by (metis ctype snd_conv worldline_upd2_def worldline_upd_preserve_wityping)

lemma add_seq_hoare_next_time0:
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans C (Badd (Bsig A) (Bsig B)) 1
     [\<lambda>tw. inv (next_world tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)", rotated 1], rule Assign2)
  apply (simp add: next_time_world_at_least)
  using inv_next_time type_correctness_length unfolding inv_def
  by (metis ctype gr_implies_not0 snd_conv worldline_upd2_def worldline_upd_preserve_wityping)

lemma add_conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw)"
proof (rule+)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j  
  assume "j \<in> {fst tw <.. next_time_world tw}"
  assume "inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  { fix i
    assume "i < j"
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "property (i + 1) i tw"
        using \<open>inv tw\<close> unfolding inv_def by auto
      hence "property (i + 1) i (j, snd tw)"
        unfolding property_def by simp }
    moreover
    { assume "fst tw \<le> i"
      moreover have "\<forall>i \<ge> fst tw. property (i + 1) (fst tw) tw"
        using \<open>inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding inv2_def
        by auto
      ultimately have "property (i + 1) (fst tw) tw"
        by auto
      hence "property (i + 1) i tw"
        unfolding property_def
        by (smt \<open>get_time tw \<le> i\<close> \<open>i < j\<close> \<open>j \<in> {get_time tw<..next_time_world tw}\<close> dual_order.strict_trans1 greaterThanAtMost_iff unchanged_until_next_time_world)
      hence "property (i + 1) i (j, snd tw)"
        unfolding property_def by auto }
    ultimately have "property (i + 1) i (j, snd tw)"
      by auto }
  thus "inv (j, snd tw)"
    unfolding inv_def by auto
qed

lemma add_conc_hoare2:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. inv2 (j, snd tw)"
proof (rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j :: nat
  assume "j \<in> {fst tw <.. next_time_world tw}"
  assume "inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  { assume "disjnt {A, B} (event_of (j, snd tw))"
    hence *: "lof_wline tw A j = lof_wline tw A (j - 1)" and **: "lof_wline tw B j = lof_wline tw B (j - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < j"
      using \<open>j \<in> {get_time tw<..next_time_world tw}\<close> greaterThanAtMost_iff by blast
    { fix i
      assume "j \<le> i"
      have "property (i + 1) (fst tw) tw"
        using \<open>inv2 tw\<close> \<open>disjnt {A, B} (event_of tw)\<close> unfolding inv2_def
        using \<open>fst tw < j\<close> \<open>j \<le> i\<close> by auto
      moreover have "lof_wline tw A (fst tw) = lof_wline tw A (j - 1)" and
                    "lof_wline tw B (fst tw) = lof_wline tw B (j - 1)"
        by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 \<open>j \<in> {get_time tw<..next_time_world
        tw}\<close> add_le_imp_le_diff diff_add discrete gr_implies_not0 greaterThanAtMost_iff
        not_less_iff_gr_or_eq unchanged_until_next_time_world)+      
      ultimately have "property (i + 1) j (j, snd tw)"
        unfolding property_def using * **  by auto }
    hence "\<forall>i\<ge>j. property (i + 1) j (j, snd tw)"
      by auto }
  thus "inv2 (j, snd tw)"
    unfolding inv2_def by auto
qed

lemma inv2_next_time:
  fixes tw
  assumes "beval_world_raw2 tw (Badd (Bsig A) (Bsig B)) v" and "type_of v = Lty Sig len"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "\<forall>j \<in> {fst tw' <.. next_time_world tw'}. inv2 (j, snd tw')"
  unfolding inv2_def
proof (rule+)
  fix j i
  assume "j \<in> {fst tw' <.. next_time_world tw'}"
  assume "disjnt {A, B} (event_of (j, snd tw'))"
  hence "A \<notin> event_of (j, snd tw')" and "B \<notin> event_of (j, snd tw')"
    by auto
  assume "fst (j, snd tw') \<le> i"
  hence "j \<le> i"
    by auto
  have "fst tw < j"
    by (metis \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close> greaterThanAtMost_iff prod.exhaust_sel
    prod.inject tw'_def worldline_upd2_def)
  have 0: "wline_of (j, snd tw') A j = wline_of tw A (fst tw)"
  proof -
    have "wline_of tw' A j = wline_of tw' A (j - 1)"
      using \<open>A \<notin> event_of (j, snd tw')\<close> unfolding event_of_alt_def
      using \<open>fst tw < j\<close> by auto
    also have " ... = wline_of tw' A (fst tw')"
      using unchanged_until_next_time_world
      by (metis (mono_tags, lifting) Suc_diff_1 \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close>
      gr_implies_not_zero greaterThanAtMost_iff le_0_eq less_Suc_eq_le not_less)
    also have "... = wline_of tw' A (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = wline_of tw A (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally show "wline_of (j, snd tw') A j = wline_of tw A (fst tw)"
      by auto
  qed
  have 1: "wline_of (j, snd tw') B j = wline_of tw B (fst tw)"
  proof -
    have "wline_of tw' B j = wline_of tw' B (j - 1)"
      using \<open>B \<notin> event_of (j, snd tw')\<close> unfolding event_of_alt_def
      using \<open>fst tw < j\<close> by auto
    also have " ... = wline_of tw' B (fst tw')"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 \<open>j \<in> {get_time tw'<..next_time_world tw'}\<close>
      dual_order.order_iff_strict greaterThanAtMost_iff le_0_eq less_Suc_eq_le not_less)
    also have "... = wline_of tw' B (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = wline_of tw B (fst tw)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    finally show "wline_of (j, snd tw') B j = wline_of tw B (fst tw)"
      by auto
  qed
  have assm2: "beval_world_raw (snd tw) (fst tw) (Badd (Bsig A) (Bsig B)) v"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "wline_of (next_world tw') C (i + 1) = v"
  proof -
    have "wline_of tw' C (i + 1) = v"
      using `fst tw < j` \<open>j \<le> i\<close>
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    thus ?thesis
      by auto
  qed
  also have "lval_of ... = bin_to_bl len (sbl_to_bin (lof_wline tw A (fst tw)) + sbl_to_bin (lof_wline tw B (fst tw)))"
    apply (rule beval_world_raw_cases[OF assm2])
    apply (erule beval_cases)
    defer
    apply (metis (mono_tags, lifting) add.right_neutral assms(2) beval_cases(1) bin_to_bl_def comp_apply list.size(3) size_bin_to_bl_aux state_of_world_def ty.distinct(1) ty.inject type_of.elims val.sel(3))
    using assms(2) by auto
  finally have "property (i + 1) j (j, snd tw')"
    unfolding property_def using 0 1  by auto
  thus " property (i + 1) (get_time (j, snd tw')) (j, snd tw')"
    by auto
qed

lemma add_seq_hoare_next_time1:
  "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bassign_trans C (Badd (Bsig A) (Bsig B)) 1 [\<lambda>tw. \<forall>i \<in> {fst tw <.. next_time_world tw}. inv2 (i, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_next_time type_correctness_length by blast

lemma seq_wt_add:
  "seq_wt \<Gamma> (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  using well_typed by blast

lemma add_conc_hoare3:
  "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>\<lambda>tw. (\<forall>i \<in> {fst tw <.. next_time_world tw}. inv (i, snd tw) \<and> inv2 (i, snd tw)) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule Conj2)
  unfolding add_def
   apply (rule Single)
    apply(rule Conj_univ_qtfd[where Q="inv" and R="inv2"])
     apply (rule strengthen_precondition)
     apply (rule strengthen_precondition)
     apply (rule add_seq_hoare_next_time)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition2)
    apply (rule add_seq_hoare_next_time1)
  using add_conc_hoare add_conc_hoare2 apply blast
  apply (rule strengthen_pre_conc_hoare[rotated])
  apply (rule single_conc_stmt_preserve_wityping_hoare)
   apply (rule seq_wt_add)
  by simp

lemma add_conc_hoare4:
  "\<turnstile> \<lbrace>\<lambda>tw. (local.inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add
       \<lbrace>\<lambda>tw. \<forall>i\<in>{get_time tw<..next_time_world tw}. (local.inv (i, snd tw) \<and> wityping \<Gamma> (snd tw)) \<and> inv2 (i, snd tw)\<rbrace>"
  apply (rule Conseq'[rotated])
  apply (rule add_conc_hoare3)
  by auto

lemma add_conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace>"
  apply (rule While)
  unfolding snd_conv
  apply (rule add_conc_hoare4)
  done

lemma add_conc_sim2:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>inv\<rbrace>"
  using add_conc_sim' Conseq_sim by blast

lemma init_sat_add_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add (\<lambda>tw. inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding add_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conj)
  unfolding snd_conv apply(rule add_seq_hoare_next_time0)
  apply (rule strengthen_precondition2)
  by (metis seq_stmt_preserve_wityping_hoare well_typed)

lemma init_sat_add_inv2:
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) add inv2"
  unfolding add_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv 
  apply (rule Conseq2[rotated])
    apply (rule add_seq_hoare_next_time1)
   apply (simp add: next_time_world_at_least)
  by auto

lemma init_sat_add_inv_comb:
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add  (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_add_inv)
  apply (rule ConseqI_sim[rotated])
  apply (rule init_sat_add_inv2)
  by blast+

lemma add_correctness:
  assumes "sim_fin w (i + 1) add tw'" and "wityping \<Gamma> w"
  shows   "property (i + 1) i tw'"
proof -
  obtain tw where "init_sim (0, w) add tw" and  "tw, i + 1, add \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf add"
    unfolding conc_stmt_wf_def add_def by auto
  moreover have "nonneg_delay_conc add"
    unfolding add_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_add_inv_comb]
    by (metis (no_types, lifting) conc_wt_cases(1) init_sat_add_inv_comb
    init_sim_hoare_soundness add_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv2 tw"
    using \<open>init_sim (0, w) add tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv2 tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>inv\<rbrace>"
    using conc_sim_soundness[OF add_conc_sim2] \<open>conc_stmt_wf add\<close> \<open>nonneg_delay_conc add\<close>
    by auto
  ultimately have "inv tw'"
    using \<open>tw, i + 1, add \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    unfolding inv_def by (metis less_add_one)
qed

lemma add_correctness2:
  assumes "sim_fin w (i + 1) add tw'" and "wityping \<Gamma> w"
  shows   "wityping \<Gamma> (snd tw')"
proof -
  obtain tw where "init_sim (0, w) add tw" and  "tw, i + 1, add \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf add"
    unfolding conc_stmt_wf_def add_def by auto
  moreover have "nonneg_delay_conc add"
    unfolding add_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) add (\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw)"
    using init_sim_hoare_soundness[OF init_sat_add_inv_comb]
    by (metis (no_types, lifting) conc_wt_cases(1) init_sat_add_inv_comb
    init_sim_hoare_soundness add_def strengthen_precondition_init_sim_hoare)
  hence "inv tw \<and> wityping \<Gamma> (snd tw) \<and> inv2 tw"
    using \<open>init_sim (0, w) add tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "inv tw" and "inv2 tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> wityping \<Gamma> (snd tw)) \<and> inv2 tw\<rbrace> add \<lbrace>\<lambda>tw. wityping \<Gamma> (snd tw)\<rbrace>"
    using conc_sim_soundness[OF add_conc_sim'] \<open>conc_stmt_wf add\<close> \<open>nonneg_delay_conc add\<close>
    by (metis (no_types, lifting) sim_hoare_valid_def)
  ultimately show "wityping \<Gamma> (snd tw')"
    using \<open>tw, i + 1, add \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
qed

corollary add_correctness3:
  assumes "sim_fin w (i + 1) add tw'" and "wityping \<Gamma> w"
  defines "bsA \<equiv> lof_wline tw' A i"
  defines "bsB \<equiv> lof_wline tw' B i"
  defines "bsC \<equiv> lof_wline tw' C (i + 1)"
  assumes "0 < len1" and "0 < len2" \<comment> \<open>bit length of less than two is senseless for signed number\<close>
  shows   "sbl_to_bin bsC mod 2 ^  len = (sbl_to_bin bsA + sbl_to_bin bsB) mod 2 ^ len" and
          "length bsC = len" and "0 < length bsB" and  "length bsA = len1"
proof -
  have "property (i + 1) i tw'" and "wityping \<Gamma> (snd tw')"
    using add_correctness[OF assms(1-2)] add_correctness2[OF assms(1-2)] by auto
  hence "length bsA = len1" and "length bsB = len2"
    by (smt assms(3-4) atype btype o_apply ty.distinct(1) ty.inject type_of.elims val.sel(3)
    wityping_def wtyping_def)+
  hence "0 < length bsA" and "0 < length bsB"
    using assms by blast+
  hence "0 < len"
    using assms unfolding len_def by auto
  have "lof_wline tw' C (i + 1) =
                  bin_to_bl len (sbl_to_bin (lof_wline tw' A i) + sbl_to_bin (lof_wline tw' B i))"
    using \<open>property (i + 1) i tw'\<close> unfolding property_def by auto
  hence "bsC = bin_to_bl len (sbl_to_bin bsA + sbl_to_bin bsB)" (is "_ = ?rhs")
    unfolding bsA_def bsB_def bsC_def by auto
  hence "sbl_to_bin bsC = sbl_to_bin ?rhs"
    by auto
  hence "sbl_to_bin bsC mod 2 ^ len = sbl_to_bin ?rhs mod 2 ^ len"
    by auto
  also have "... = (sbl_to_bin bsA + sbl_to_bin bsB) mod 2 ^ len"
    using sbin_bl_bin' \<open>0 < len\<close> by auto
  finally show "sbl_to_bin bsC mod 2 ^ len = (sbl_to_bin bsA + sbl_to_bin bsB) mod 2 ^ len"
    by auto
  show "length bsC = len" and "0 < length bsB" and "length bsA = len1"
    using \<open>bsC = bin_to_bl len (sbl_to_bin bsA + sbl_to_bin bsB)\<close> size_bin_to_bl \<open>0 < length bsB\<close>
    \<open>length bsA = len1\<close> by blast+
qed

corollary add_correctness4:
  assumes "sim_fin w (i + 1) add tw'" and "wityping \<Gamma> w"
  defines "bsA \<equiv> lof_wline tw' A i"
  defines "bsB \<equiv> lof_wline tw' B i"
  defines "bsC \<equiv> lof_wline tw' C (i + 1)"
  assumes "0 < len1" and "0 < len2" \<comment> \<open>bit length of less than two is senseless for signed number\<close>
  defines "repA \<equiv> - (int \<circ> of_bool) (hd bsA) * 2 ^ (length bsA - 1) + (\<Sum>i = 0..<length bsA - 1. (int \<circ> of_bool) (rev (tl bsA) ! i) * 2 ^ i)"
  defines "repB \<equiv> - (int \<circ> of_bool) (hd bsB) * 2 ^ (length bsB - 1) + (\<Sum>i = 0..<length bsB - 1. (int \<circ> of_bool) (rev (tl bsB) ! i) * 2 ^ i)"
  defines "repC \<equiv> - (int \<circ> of_bool) (hd bsC) * 2 ^ (length bsC - 1) + (\<Sum>i = 0..<length bsC - 1. (int \<circ> of_bool) (rev (tl bsC) ! i) * 2 ^ i)"
  shows   "repC mod 2 ^ len = (repA + repB) mod 2 ^ len"
proof -
  have "sbl_to_bin bsC mod 2 ^ len =
       (sbl_to_bin bsA + sbl_to_bin bsB) mod 2 ^ len" and  "length bsC = len" and "0 < length bsB" and "length bsA = len1"
    using add_correctness3 assms by auto
  hence "0 < length bsC"
    unfolding len_def using \<open>0 < len1\<close> \<open>0 < len2\<close> by auto
  then obtain c bsC' where "bsC = c # bsC'" and "hd bsC = c" and "tl bsC = bsC'"
    using list.exhaust_sel by auto
  hence sC: "sbl_to_bin bsC = - (int \<circ> of_bool) (hd bsC) * 2 ^ (length bsC - 1) + (\<Sum>i = 0..<length bsC - 1. (int \<circ> of_bool) (rev (tl bsC) ! i) * 2 ^ i)"
    using sbl_to_bin_correctness by simp
  obtain b bsB' a bsA' where "bsA = a # bsA'" and "bsB = b # bsB'" and "hd bsA = a" and "tl bsA = bsA'"
    and "hd bsB = b" and "tl bsB = bsB'"
    by (metis \<open>0 < length bsB\<close> \<open>length bsA = len1\<close> assms(6) list.sel(1) list.sel(3)  list_exhaust_size_gt0 )
  hence sA: "sbl_to_bin bsA = - (int \<circ> of_bool) (hd bsA) * 2 ^ (length bsA - 1) + (\<Sum>i = 0..<length bsA - 1. (int \<circ> of_bool) (rev (tl bsA) ! i) * 2 ^ i)"
    and sB: "sbl_to_bin bsB = - (int \<circ> of_bool) (hd bsB) * 2 ^ (length bsB - 1) + (\<Sum>i = 0..<length bsB - 1. (int \<circ> of_bool) (rev (tl bsB) ! i) * 2 ^ i)"
    using sbl_to_bin_correctness by simp+
  show ?thesis
    using \<open>sbl_to_bin bsC mod 2 ^ len =
       (sbl_to_bin bsA + sbl_to_bin bsB) mod 2 ^ len\<close> unfolding sA sB sC repA_def repB_def repC_def
    by  metis
qed

end
