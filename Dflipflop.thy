(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Dflipflop
  imports VHDL_Hoare_Complete
begin

text \<open>datatype for all signals\<close>

datatype sig = D | CLK | OUT

definition dflipflop :: "sig conc_stmt" where
  "dflipflop \<equiv> process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull"

text \<open>The following positive edge is only defined for a scalar signal.\<close>

abbreviation is_posedge :: "'signal worldline \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_posedge w s j i \<equiv> (  j \<le> i \<and> w s (j - 1)  = Bv False \<and> w s j = Bv True \<comment> \<open>change of signal from low to high at j\<close>
                      \<and> (\<forall>j' \<le> i.  w s (j' - 1) = Bv False \<and> w s j' = Bv True \<longrightarrow> j' \<le> j) \<comment> \<open>largest of positive edge\<close>)"

lemma is_posedge_strictly_positive:
  "is_posedge w s j i \<Longrightarrow> 0 < j"
  using gr_zeroI  by force

lemma is_posedge_unique:
  assumes "is_posedge w s j1 i" and "is_posedge w s j2 i"
  shows "j1 = j2"
  using assms by (simp add: dual_order.antisym)

definition inv :: "sig assn2" where
  "inv tw \<equiv> (\<forall>i < fst tw.                                   \<comment> \<open>at all ``times''\<close>
            (\<forall>j \<le> i. is_posedge (wline_of tw) CLK j i \<longrightarrow>   \<comment> \<open>if there is positive edge namely j\<close>
                wline_of tw OUT (i + 1) = wline_of tw D j)  \<comment> \<open>the output at i + 1 equals to D at j\<close>)"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) = (Bv False) \<longrightarrow> \<comment> \<open>if there is no positive edge in CLK\<close>
             (\<forall>i \<ge> fst tw. wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)) \<comment> \<open>the value stays the same\<close>"

lemma wline_of_diff:
  assumes "wline_of tw sig t \<noteq> wline_of tw sig (t - 1)"
  assumes "wline_of tw sig t = (Bv bool)"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "wline_of tw sig (t - 1) = (Bv (\<not> bool))"
proof -
  have "type_of (wline_of tw sig t) = Bty"
    using assms(2) by auto
  hence "type_of (wline_of tw sig (t - 1)) = Bty"
    using assms(3) unfolding wityping_def wtyping_def by auto
  thus ?thesis
    using assms(1-2)  by (metis (mono_tags) ty.distinct(1) type_of.elims val.inject(1))
qed

lemma inv_time_seq_next_time:
  assumes "inv tw" and "\<not> disjnt {CLK} (event_of tw)" and "beval_world_raw2 tw (Bsig CLK) (Bv True)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 wline_of tw D (fst tw)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "\<forall>k \<in> {fst tw' <.. next_time_world tw'}. inv (k, snd tw')"
  unfolding inv_def
proof (rule)+
  fix i j k
  assume "k \<in> {fst tw' <.. next_time_world tw'}"
  assume "i < fst (k, snd tw')"
  hence "i < k"
    by auto
  assume "j \<le> i"
  assume "is_posedge (wline_of (k, snd tw')) CLK j i "
  hence  "is_posedge (wline_of tw') CLK j i"
    by auto
  have "i < fst tw \<or> fst tw \<le> i \<and> i < k - 1 \<or> i = k - 1"
    using \<open>i < k\<close> by linarith
  moreover
  { assume "i < fst tw"
    hence "is_posedge (wline_of tw) CLK j i"
      using \<open>is_posedge (wline_of tw') CLK j i\<close> by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    have "wline_of tw' OUT (i + 1) = wline_of tw OUT (i + 1)"
      by (metis \<open>i < get_time tw\<close> add_mono1 tw'_def worldline_upd2_before_dly)
    also have "... = wline_of tw D j"
      using \<open>j \<le> i\<close> \<open>is_posedge (wline_of tw') CLK j i\<close> assms(1) \<open>i < fst tw\<close> \<open>is_posedge (wline_of tw) CLK j i\<close>
      unfolding inv_def by auto
    also have "... = wline_of tw' D j"
      by (metis (no_types, lifting) One_nat_def \<open>i < get_time tw\<close> \<open>j \<le> i\<close> add.right_neutral
      add_Suc_right add_mono1 le_imp_less_Suc less_trans tw'_def worldline_upd2_before_dly)
    finally have "wline_of tw' OUT (i + 1) = wline_of tw' D j"
      by auto }
  moreover
  { assume "fst tw \<le> i \<and> i < k - 1"
    hence "is_posedge (wline_of tw) CLK j i"
      using \<open>is_posedge (wline_of tw') CLK j i\<close> 
      by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    have "wline_of tw' OUT (i + 1) = wline_of tw' OUT (fst tw + 1)"
      by (smt \<open>get_time tw \<le> i \<and> i < k - 1\<close> add_diff_cancel_right' comp_def less_diff_conv not_le
      sndI tw'_def worldline_upd2_at_dly worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw D (fst tw)"
      unfolding tw'_def  by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
    also have "... = wline_of tw D j"
    proof -
      have "0 < j"
        using is_posedge_strictly_positive \<open>is_posedge (wline_of tw') CLK j i\<close>  by fastforce
      hence "0 < i"
        using \<open>j \<le> i\<close> by auto
      hence "0 < fst tw"
        by (smt \<open>i < k\<close> \<open>is_posedge (wline_of tw') CLK j i\<close> \<open>k \<in> {get_time tw'<..next_time_world
        tw'}\<close> assms(4) diff_le_self fst_conv gr0I greaterThanAtMost_iff le_less_trans
        less_imp_le_nat less_le_trans unchanged_until_next_time_world val.inject(1)
        worldline_upd2_def)
      have "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
        using assms(2) \<open>0 < fst tw\<close> unfolding event_of_alt_def
        by simp
      hence "wline_of tw CLK (fst tw) = Bv True"
        using assms(3) by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
      have "wline_of tw CLK (fst tw - 1) = Bv False"
      proof -
        have "type_of (wline_of tw CLK (fst tw)) = Bty"
          using \<open>wline_of tw CLK (fst tw) = Bv True\<close> by auto
        hence "type_of (wline_of tw CLK (fst tw - 1)) = Bty"
          using \<open>wityping \<Gamma> (snd tw)\<close> unfolding wityping_def wtyping_def  by auto
        hence "wline_of tw CLK (fst tw - 1) = (Bv False) \<or> wline_of tw CLK (fst tw - 1) = (Bv True)"
          by (metis ty.distinct(1) type_of.elims)
        thus ?thesis
          using \<open>wline_of tw CLK (get_time tw) = Bv True\<close> \<open>wline_of tw CLK (get_time tw) \<noteq> wline_of tw CLK (get_time tw - 1)\<close> by auto
      qed
      moreover have "\<forall>j' \<le> i. wline_of tw CLK (j' - 1) = (Bv False) \<and> wline_of tw CLK j' = (Bv True) \<longrightarrow> j' \<le> fst tw"
        by (smt Suc_diff_1 \<open>0 < j\<close> \<open>get_time tw \<le> i \<and> i < k - 1\<close> \<open>is_posedge (wline_of tw') CLK j i\<close>
        \<open>is_posedge (wline_of tw) CLK j i\<close> \<open>k \<in> {get_time tw'<..next_time_world tw'}\<close> \<open>wline_of tw
        CLK (get_time tw) = Bv True\<close> \<open>wline_of tw CLK (get_time tw) \<noteq> wline_of tw CLK (get_time tw -
        1)\<close> calculation diff_le_self dual_order.strict_trans1 fst_conv greaterThanAtMost_iff
        le_less_trans less_Suc_eq_le not_le_imp_less tw'_def unchanged_until_next_time_world
        worldline_upd2_def)
      ultimately have "fst tw = j"
        using \<open>is_posedge (wline_of tw) CLK j i\<close>
        by (meson \<open>get_time tw \<le> i \<and> i < k - 1\<close> \<open>wline_of tw CLK (get_time tw) = Bv True\<close> eq_iff)
      thus ?thesis
        using \<open>is_posedge (wline_of tw) CLK j i\<close> by blast
    qed
    also have "... = wline_of tw' D j"
      by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    finally have "wline_of tw' OUT (i + 1) = wline_of tw' D j"
      by auto }
  moreover
  { assume "i = k - 1"
    hence "is_posedge (wline_of tw) CLK j i"
      using \<open>is_posedge (wline_of tw') CLK j i\<close> by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    have "wline_of tw' OUT (i + 1) = wline_of tw' OUT (k)"
      by (metis Suc_diff_1 Suc_eq_plus1 \<open>i < k\<close> \<open>i = k - 1\<close>
      add.right_neutral le_add2 nat_less_le not_le)
    also have "... = wline_of tw' OUT (fst tw + 1)"
      unfolding tw'_def
      by (smt Suc_eq_plus1 Suc_leI \<open>k \<in> {get_time tw'<..next_time_world tw'}\<close> comp_apply fst_conv
      greaterThanAtMost_iff nat_less_le not_less_iff_gr_or_eq sndI tw'_def worldline_upd2_def
      worldline_upd_def)
    also have "... = wline_of tw D (fst tw)"
      unfolding tw'_def  by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
    also have "... = wline_of tw D j"
    proof -
      have *: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
        using assms(2) unfolding event_of_alt_def
        by (smt \<open>i < k\<close> \<open>is_posedge (wline_of tw') CLK j i\<close> \<open>k \<in> {get_time tw'<..next_time_world
        tw'}\<close> diff_is_0_eq' diff_le_self disjnt_iff fst_conv greaterThanAtMost_iff le_less_trans
        mem_Collect_eq not_less singletonD tw'_def unchanged_until_next_time_world val.inject(1)
        worldline_upd2_def)
      have "wline_of tw CLK (fst tw) = Bv True"
        by (metis assms(3) beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
      hence "wline_of tw CLK (fst tw - 1) = Bv False"
        using wline_of_diff[OF * _ assms(5)] by auto
      moreover have "\<forall>j' \<le> i. wline_of tw CLK (j' - 1) = Bv False \<and> wline_of tw CLK j' = Bv True \<longrightarrow> j' \<le> fst tw"
        by (smt "*" One_nat_def \<open>i = k - 1\<close> \<open>is_posedge (wline_of tw') CLK j i\<close> \<open>is_posedge
        (wline_of tw) CLK j i\<close> \<open>k \<in> {get_time tw'<..next_time_world tw'}\<close> \<open>wline_of tw CLK (get_time
        tw) = Bv True\<close> calculation dual_order.strict_trans1 fst_conv greaterThanAtMost_iff le_Suc_eq
        le_imp_less_Suc le_zero_eq less_imp_le_nat linordered_semidom_class.add_diff_inverse
        not_less_iff_gr_or_eq plus_1_eq_Suc tw'_def unchanged_until_next_time_world
        worldline_upd2_def)
      ultimately have "fst tw = j"
        using \<open>is_posedge (wline_of tw) CLK j i\<close>
        by (metis One_nat_def \<open>i = k - 1\<close> \<open>k \<in> {get_time tw'<..next_time_world tw'}\<close> \<open>wline_of tw
        CLK (get_time tw) = Bv True\<close> dual_order.antisym fstI gr_implies_not_zero
        greaterThanAtMost_iff less_Suc0 less_Suc_eq_le linordered_semidom_class.add_diff_inverse
        plus_1_eq_Suc tw'_def worldline_upd2_def)
      thus ?thesis
        using \<open>is_posedge (wline_of tw) CLK j i\<close> by blast
    qed
    also have "... = wline_of tw' D j"
      by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
    finally have "wline_of tw' OUT (i + 1) = wline_of tw' D j"
      by auto }
  ultimately have "wline_of tw' OUT (i + 1) = wline_of tw' D j"
    by auto
  thus "wline_of (k, snd tw') OUT (i + 1) = wline_of (k, snd tw') D j"
    by auto
qed

lemma dflipflop_seq_inv:
  "\<turnstile> [\<lambda>tw. (((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK) (Bv True)) \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. \<forall>k \<in> {fst tw <.. next_time_world tw}. inv (k, snd tw)]"
  apply (rule Assign2_altI)
  using inv_time_seq_next_time
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

lemma inv2_seq_next_time:
  assumes "inv tw" and "inv2 tw" and "\<not> disjnt {CLK} (event_of tw)" and "beval_world_raw2 tw (Bsig CLK) (Bv True)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 wline_of tw D (fst tw)]"
  shows "\<forall>k \<in> {fst tw' <.. next_time_world tw'}. inv2 (k, snd tw')"
  unfolding inv2_def
proof (rule)+
  fix i k
  assume "k \<in> {fst tw' <.. next_time_world tw'}"
  assume "   disjnt {CLK} (event_of (k, snd tw'))  \<or> wline_of (k, snd tw') CLK (get_time (k, snd tw')) = (Bv False)"
  hence  "   disjnt {CLK} (event_of (k, snd tw'))  \<or> wline_of tw' CLK (k) = (Bv False)"
    by auto
  assume "get_time (k, snd tw') \<le> i"
  hence "k \<le> i"
    by auto
  moreover have "fst tw < k"
    using next_time_world_at_least
    by (metis Pair_inject \<open>k \<in> {get_time tw'<..next_time_world tw'}\<close> greaterThanAtMost_iff
    prod.collapse tw'_def worldline_upd2_def)
  ultimately have "fst tw < i"
    by auto
  have "wline_of tw' OUT (i + 1) = wline_of tw' OUT (k)"
    unfolding tw'_def using \<open>fst tw < k\<close> \<open>fst tw < i\<close>
    by (smt Suc_eq_plus1 Suc_leI add_diff_cancel_right' comp_apply diff_is_0_eq' less_diff_conv
    not_less_iff_gr_or_eq snd_conv tw'_def worldline_upd2_def worldline_upd_def zero_less_diff)
  thus " wline_of (k, snd tw') OUT (i + 1) =
         wline_of (k, snd tw') OUT (get_time (k, snd tw'))"
    by auto
qed

lemma dflipflop_seq_inv2:
  "\<turnstile> [\<lambda>tw. ((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK) (Bv True)]
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. \<forall>k \<in> {fst tw <.. next_time_world tw}. inv2 (k, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_seq_next_time
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

lemma dflipflop_inv_if:
  "\<turnstile> [\<lambda>tw. (((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK) (Bv True)) \<and> wityping \<Gamma> (snd tw)]
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. \<forall>k \<in> {fst tw <.. next_time_world tw}. inv (k, snd tw) \<and> inv2 (k, snd tw)]"
  apply (rule Conj_univ_qtfd)
   apply (rule dflipflop_seq_inv)
  apply (rule strengthen_precondition)
  apply (rule dflipflop_seq_inv2)
  done

lemma inv_next_time_null:
  assumes "inv tw" and "inv2 tw" and "\<not> disjnt {CLK} (event_of tw)" and "beval_world_raw2 tw (Bsig CLK) (Bv False)"
  shows "\<forall>k \<in> {fst tw <.. next_time_world tw}. inv (k, snd tw)"
  unfolding inv_def
proof (rule)+
  fix i j k :: nat
  assume "j \<le> i"
  assume "k \<in> {fst tw <.. next_time_world tw}"
  assume "is_posedge (wline_of (k, snd tw)) CLK j i"
  hence  "is_posedge (wline_of tw) CLK j i"
    by auto
  hence "0 < j"
    using is_posedge_strictly_positive by metis
  have *: "\<forall>i\<ge>get_time tw. wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
    using assms(2) assms(4) unfolding inv2_def
    by (metis Suc_eq_plus1 beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
  assume "i < fst (k, snd tw)"
  hence "i < k"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i \<le> k - 1"
    by linarith
  moreover
  { assume "i < fst tw"
    hence "wline_of tw OUT (i + 1) = wline_of tw D j"
      using Dflipflop.inv_def \<open>is_posedge (wline_of (k, snd tw)) CLK j i\<close> \<open>j \<le> i\<close>
      assms(1) by auto }
  moreover
  { assume "fst tw \<le> i \<and> i \<le> k - 1"
    hence "wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
      using \<open>inv2 tw\<close> assms(3-4) * unfolding inv2_def by blast
    have "fst tw = 0 \<or> 0 < fst tw"
      by auto
    moreover
    { assume "0 < fst tw"
      hence "fst tw - 1 < fst tw"
        by auto
      have "j \<noteq> fst tw"
      proof (rule ccontr)
        assume "\<not> j \<noteq> fst tw"
        hence "j = fst tw"
          by auto
        hence "wline_of tw CLK j = Bv True"
          using `is_posedge (wline_of tw) CLK j i` by auto
        with \<open>beval_world_raw2 tw (Bsig CLK) (Bv False)\<close> show False
          by (smt \<open>j = get_time tw\<close> beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic val.inject(1))
      qed
      hence "j < fst tw \<or> j > fst tw"
        by auto
      moreover have "j > fst tw \<Longrightarrow> False"
      proof -
        assume "j > fst tw"
        have "j < next_time_world tw - 1"
          using \<open>j \<le> i\<close> `fst tw \<le> i \<and> i \<le> k - 1`
          by (smt Suc_diff_1 \<open>get_time tw < j\<close> \<open>i < k\<close> \<open>is_posedge (wline_of tw) CLK j i\<close> \<open>k \<in>
          {get_time tw<..next_time_world tw}\<close> diff_is_0_eq' greaterThanAtMost_iff le_less_trans
          less_SucE less_imp_diff_less less_imp_le_nat less_le_trans unchanged_until_next_time_world
          val.inject(1))
        hence "wline_of tw CLK (j - 1) = wline_of tw CLK j"
          using `fst tw < j` unchanged_until_next_time_world
          by (metis Suc_diff_1 cancel_comm_monoid_add_class.diff_cancel less_Suc_eq_le
          less_imp_diff_less less_imp_le_nat next_time_world_at_least)
        with \<open>is_posedge (wline_of tw) CLK j i\<close> show False
          by simp
      qed
      ultimately have "j \<le> fst tw - 1"
        by auto
      moreover have "is_posedge (wline_of tw) CLK j (fst tw - 1)"
        using \<open>get_time tw \<le> i \<and> i \<le> k - 1\<close> \<open>is_posedge (wline_of tw) CLK j i\<close>
        less_imp_diff_less  using calculation by auto
      ultimately have "wline_of tw OUT (fst tw)= wline_of tw D j"
        using \<open>inv tw\<close> `fst tw - 1 < fst tw` unfolding inv_def  by auto
      with \<open>wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)\<close> have "wline_of tw OUT (i + 1) = wline_of tw D j"
        by auto }
    moreover
    { assume "fst tw = 0"
      with `inv2 tw` have "wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
        unfolding inv2_def  using \<open>beval_world_raw2 tw (Bsig CLK) (Bv False)\<close>
        \<open>wline_of tw OUT (i + 1) = wline_of tw OUT (get_time tw)\<close> by blast
      have "is_posedge (wline_of tw) CLK j (fst tw)"
        using \<open>get_time tw = 0\<close> \<open>is_posedge (wline_of tw) CLK j i\<close>
        by (metis (no_types, lifting) \<open>i < k\<close> \<open>k \<in> {get_time tw<..next_time_world tw}\<close> diff_le_self
        dual_order.strict_trans1 greaterThanAtMost_iff le0 le_less_trans
        unchanged_until_next_time_world val.inject(1))
      hence "wline_of tw CLK (fst tw - 1) \<noteq> wline_of tw CLK (fst tw)"
        using \<open>get_time tw = 0\<close> by auto
      with \<open>fst tw = 0\<close> have "False"
        by simp
      hence "wline_of tw OUT (i + 1) = wline_of tw D j"
        by auto }
    ultimately have "wline_of tw OUT (i + 1) = wline_of tw D j"
      by auto }
  ultimately have "wline_of tw OUT (i + 1) = wline_of tw D j"
    by auto
  thus "wline_of (k, snd tw) OUT (i + 1) = wline_of (k, snd tw) D j"
    by auto
qed

lemma inv2_next_time_null:
  assumes "inv tw" and "inv2 tw" and "\<not> disjnt {CLK} (event_of tw)" and "beval_world_raw2 tw (Bsig CLK) (Bv False)"
  shows "\<forall>k \<in> {fst tw <.. next_time_world tw}. inv2 (k, snd tw)"
  unfolding inv2_def
proof (rule)+
  fix i k
  assume "k \<in> {fst tw <.. next_time_world tw}"
  assume "   disjnt {CLK} (event_of (k, snd tw))
         \<or>   wline_of (k, snd tw) CLK (get_time (k, snd tw)) = Bv False"
  assume " get_time (k, snd tw) \<le> i"
  hence "k \<le> i"
    by auto
  hence "fst tw \<le> i"
    using next_time_world_at_least dual_order.strict_trans less_Suc_eq_le 
    using \<open>k \<in> {get_time tw<..next_time_world tw}\<close> by auto
  moreover have "\<forall>i \<ge> fst tw. wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
    using assms(2) assms(4) unfolding inv2_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
  ultimately have "wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
    by auto
  also have "... = wline_of tw OUT (k - 1)"
    using unchanged_until_next_time_world
    by (smt Suc_diff_1 \<open>k \<in> {get_time tw<..next_time_world tw}\<close> diff_is_0_eq' diff_le_self diff_less
    dual_order.strict_iff_order greaterThanAtMost_iff le_Suc_eq less_le_trans zero_less_one)
  also have "... = wline_of tw OUT (k)"
    using assms(3) unfolding event_of_alt_def
    by (smt \<open>\<forall>i\<ge>get_time tw. wline_of tw OUT (i + 1) = wline_of tw OUT (get_time tw)\<close> \<open>k \<in> {get_time
    tw<..next_time_world tw}\<close> add_diff_cancel_left' diff_add diff_add_zero greaterThanAtMost_iff
    le_Suc_eq le_add1 le_add_diff_inverse less_le plus_1_eq_Suc)
  finally have "wline_of tw OUT (i + 1) = wline_of tw OUT (k)"
    by auto
  thus "wline_of (k, snd tw) OUT (i + 1) =
        wline_of (k, snd tw) OUT (get_time (k, snd tw))"
    by auto
qed

lemma dflipflop_inv_else:
  "\<turnstile> [\<lambda>tw. ((inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw)) \<and> beval_world_raw2 tw (Bsig CLK) (Bv False)]
        Bnull
     [\<lambda>tw. \<forall>k \<in> {fst tw <.. next_time_world tw}. inv (k, snd tw) \<and> inv2 (k, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. \<forall>k \<in> {fst tw <.. next_time_world tw}. inv (k, snd tw) \<and> inv2 (k, snd tw)", rotated 1])
    apply (rule Null2)
   apply simp
  using inv_next_time_null inv2_next_time_null by auto

lemma dflipflop_seq_both_inv:
  "\<turnstile> [\<lambda>tw. (inv tw \<and> inv2 tw) \<and> \<not> disjnt {CLK} (event_of tw) \<and> wityping \<Gamma> (snd tw)] \<comment> \<open>precondition\<close>
        Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull \<comment> \<open>program\<close>
     [\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw) \<and> inv2 (j, snd tw)]" \<comment> \<open>postcondition\<close>
  apply (rule If2)
   apply (rule Conseq2)
     prefer 2          
     apply (rule dflipflop_inv_if)
    apply blast+
  apply (rule Conseq2)
    prefer 2
    apply (rule dflipflop_inv_else)
   apply blast+
  done
 
lemma inv_next_time_disjnt:
  assumes "inv tw" and "inv2 tw" and "disjnt {CLK} (event_of tw)"
  shows "\<forall>k \<in> {fst tw <.. next_time_world tw}. inv (k, snd tw)"
  unfolding inv_def
proof (rule)+
  fix i j k :: nat
  assume "k \<in> {fst tw <.. next_time_world tw}"
  assume "j \<le> i"
  assume "is_posedge (wline_of (k, snd tw)) CLK j i"
  hence "is_posedge (wline_of tw) CLK j i"
    by auto
  hence "0 < j"
    using is_posedge_strictly_positive by metis
  have *: "\<forall>i\<ge>get_time tw. wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
    using assms(2) assms(3) unfolding inv2_def by auto
  assume "i < fst (k, snd tw)"
  hence "i < k"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i \<and> i \<le> k - 1"
    by linarith
  moreover
  { assume "i < fst tw"
    hence "wline_of tw OUT (i + 1) = wline_of tw D j"
      using Dflipflop.inv_def \<open>is_posedge (wline_of (k, snd tw)) CLK j i\<close> \<open>j \<le> i\<close>
      assms(1) by auto }
  moreover
  { assume "fst tw \<le> i \<and> i \<le> k - 1"
    have "fst tw = 0 \<or> 0 < fst tw"
      by auto
    moreover
    { assume "0 < fst tw"
      hence "fst tw - 1 < fst tw"
        by auto
      have "j \<noteq> fst tw"
      proof (rule ccontr)
        assume "\<not> j \<noteq> fst tw"
        hence "j = fst tw"
          by auto
        hence "wline_of tw CLK (fst tw - 1) \<noteq> wline_of tw CLK (fst tw)"
          using \<open>is_posedge (wline_of tw) CLK j i\<close> by simp
        hence "\<not> disjnt {CLK} (event_of tw)"
          unfolding event_of_alt_def using \<open>0 < fst tw\<close>  by auto
        with \<open>disjnt {CLK} (event_of tw)\<close> show False
          by auto
      qed
      hence "j < fst tw \<or> j > fst tw"
        by auto
      moreover have "j > fst tw \<Longrightarrow> False"
      proof -
        assume "j > fst tw"
        have "j < next_time_world tw - 1"
          using \<open>j \<le> i\<close> `fst tw \<le> i \<and> i \<le> k - 1`
          by (smt \<open>get_time tw < j\<close> \<open>is_posedge (wline_of tw) CLK j i\<close> \<open>k \<in> {get_time
          tw<..next_time_world tw}\<close> diff_is_0_eq' diff_less_Suc greaterThanAtMost_iff less_SucE
          less_imp_le_nat less_le_trans linordered_semidom_class.add_diff_inverse not_less
          plus_1_eq_Suc unchanged_until_next_time_world val.inject(1))
        hence "wline_of tw CLK (j - 1) = wline_of tw CLK j"
          using `fst tw < j` unchanged_until_next_time_world
          by (smt add_le_imp_le_diff diff_le_self discrete dual_order.strict_trans1
          le_eq_less_or_eq)
        with \<open>is_posedge (wline_of tw) CLK j i\<close> show False
          by simp
      qed
      ultimately have "j \<le> fst tw - 1"
        by auto
      moreover have "is_posedge (wline_of tw) CLK j (fst tw - 1)"
        using  \<open>is_posedge (wline_of tw) CLK j i\<close>
        less_imp_diff_less calculation \<open>get_time tw \<le> i \<and> i \<le> k - 1\<close> by auto
      ultimately have "wline_of tw OUT (fst tw)= wline_of tw D j"
        using \<open>inv tw\<close> `fst tw - 1 < fst tw` unfolding inv_def  by auto
      with * have "wline_of tw OUT (i + 1) = wline_of tw D j"
        using \<open>get_time tw \<le> i \<and> i \<le> k - 1\<close>  by simp }
    moreover
    { assume "fst tw = 0"
      have "wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
        using *  by (simp add: \<open>get_time tw = 0\<close>)
      have "is_posedge (wline_of tw) CLK j (fst tw)"
        using \<open>get_time tw = 0\<close> \<open>is_posedge (wline_of tw) CLK j i\<close>
        by (metis (no_types, lifting) \<open>i < get_time (k, snd tw)\<close> \<open>k \<in> {get_time tw<..next_time_world
        tw}\<close> diff_le_self dual_order.strict_trans1 fst_conv greaterThanAtMost_iff le0 le_less_trans
        unchanged_until_next_time_world val.inject(1))
      hence "wline_of tw CLK (fst tw - 1) \<noteq> wline_of tw CLK (fst tw)"
        using \<open>get_time tw = 0\<close> by auto
      with \<open>fst tw = 0\<close> have "False"
        by simp
      hence "wline_of tw OUT (i + 1) = wline_of tw D j"
        by auto }
    ultimately have "wline_of tw OUT (i + 1) = wline_of tw D j"
      by auto }
  ultimately have "wline_of tw OUT (i + 1) = wline_of tw D j"
    by auto
  thus "wline_of (k, snd tw) OUT (i + 1) = wline_of (k, snd tw) D j"
    by auto
qed

lemma inv2_next_time_disjnt:
  assumes "inv tw" and "inv2 tw" and "disjnt {CLK} (event_of tw)"
  shows "\<forall>k \<in> {fst tw <.. next_time_world tw}. inv2 (k, snd tw)"
  unfolding inv2_def
proof rule+
  fix i k
  assume "k \<in> {get_time tw<..next_time_world tw}"
  assume "   disjnt {CLK} (event_of (k, snd tw))
         \<or>   wline_of (k, snd tw) CLK (get_time (k, snd tw)) = Bv False"
  assume " get_time (k, snd tw) \<le> i"
  hence "k \<le> i"
    by auto
  hence "fst tw \<le> i"
    using next_time_world_at_least dual_order.strict_trans less_Suc_eq_le 
    using \<open>k \<in> {get_time tw<..next_time_world tw}\<close> by auto
  moreover have "\<forall>i \<ge> fst tw. wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
    using assms(2-3) unfolding inv2_def  by (simp add: beval_world_raw2_Bsig)
  ultimately have "wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw)"
    by auto
  also have "... = wline_of tw OUT (k - 1)"
    using unchanged_until_next_time_world
    by (smt Suc_diff_1 \<open>k \<in> {get_time tw<..next_time_world tw}\<close> diff_is_0_eq' diff_le_self diff_less
    dual_order.strict_iff_order greaterThanAtMost_iff le_Suc_eq less_le_trans zero_less_one)
  also have "... = wline_of tw OUT (k)"
    using assms(3) unfolding event_of_alt_def
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 \<open>\<forall>i\<ge>get_time tw. wline_of tw OUT (i + 1)
    = wline_of tw OUT (get_time tw)\<close> \<open>k \<in> {get_time tw<..next_time_world tw}\<close> \<open>wline_of tw OUT
    (get_time tw) = wline_of tw OUT (k - 1)\<close> gr_implies_not0 greaterThanAtMost_iff le_Suc_eq
    less_Suc0 less_or_eq_imp_le linordered_semidom_class.add_diff_inverse plus_1_eq_Suc)
  finally have "wline_of tw OUT (i + 1) = wline_of tw OUT (k)"
    by auto
  thus "wline_of (k, snd tw) OUT (i + 1) =
        wline_of (k, snd tw) OUT (get_time (k, snd tw))"
    by auto
qed

lemma dflipflop_conc_both_inv:
  "\<turnstile> \<lbrace>\<lambda>tw. (inv tw \<and> inv2 tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>  \<comment> \<open>precondition\<close>
        process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull \<comment> \<open>program\<close>
     \<lbrace>\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. inv (j, snd tw) \<and> inv2 (j, snd tw)\<rbrace>" \<comment> \<open>postcondition\<close>
  apply (rule Single)
   apply (rule Conseq2)
     prefer 2
     apply (rule dflipflop_seq_both_inv)
    apply blast+
  using inv_next_time_disjnt inv2_next_time_disjnt 
  by auto

theorem simulation_comb:
  assumes "conc_wt \<Gamma> dflipflop"
  shows "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv tw \<and> inv2 tw) \<and>  wityping \<Gamma> (snd tw)\<rbrace> dflipflop \<lbrace>\<lambda>tw. (inv tw \<and> inv2 tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  unfolding dflipflop_def
  apply (rule While)
  apply (rule Conj2_univ_qtfd)
   apply (rule dflipflop_conc_both_inv)
  apply (rule Conseq'[rotated])
    apply (rule single_conc_stmt_preserve_wityping_hoare[where \<Gamma>="\<Gamma>"])
    apply (metis assms conc_wt_cases(1) dflipflop_def)
  by auto

corollary simulation_inv:
  assumes "conc_wt \<Gamma> dflipflop"
  shows "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw \<and> wityping \<Gamma> (snd tw)\<rbrace> dflipflop \<lbrace>\<lambda>tw. inv tw\<rbrace>"
  using simulation_comb[OF assms]  Conseq_sim   by fastforce

subsection \<open>Initialisation satisfies @{term "inv"} and @{term "inv2"}\<close>

lemma [simp]:
  "inv (0, w)"
  unfolding inv_def by auto

lemma inv_time_seq_next_time0:
  assumes "fst tw = 0"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 wline_of tw D (fst tw)]"
  shows "inv (next_time_world tw', snd tw')"
  unfolding inv_def
proof (rule, rule, rule, rule, rule)
  fix i j
  assume "i < get_time (next_time_world tw', snd tw')"
  hence "i < next_time_world tw'"
    by auto
  assume "j \<le> i"
  hence "j < next_time_world tw'"
    using `i < next_time_world tw'` by auto
  assume "is_posedge (wline_of (next_time_world tw', snd tw')) CLK j i"
  hence "is_posedge (wline_of tw') CLK j i"
    by auto
  hence "wline_of tw' CLK (j - 1) \<noteq> wline_of tw' CLK j"
    by simp
  moreover have "(\<forall>s. wline_of tw' s j = wline_of tw' s (fst tw'))"
    using unchanged_until_next_time_world `fst tw = 0` `j < next_time_world tw'`
    by (metis fst_conv less_eq_nat.simps(1) tw'_def worldline_upd2_def)
  ultimately have "False"
    by (metis \<open>j < next_time_world tw'\<close> assms(1) fst_conv less_imp_diff_less tw'_def
    unchanged_until_next_time_world worldline_upd2_def zero_le)
  thus "wline_of (next_time_world tw', snd tw') OUT (i + 1) = wline_of (next_time_world tw', snd tw') D j"
    by auto
qed

lemma init0:
  "\<turnstile> [\<lambda>tw. get_time tw = 0 \<and> beval_world_raw2 tw (Bsig CLK) (Bv True)]
        Bassign_trans OUT (Bsig D) 1
     [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv_time_seq_next_time0
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

lemma inv_time_seq_next_time0':
  assumes "fst tw = 0"
  shows   "inv (next_time_world tw, snd tw)"
  unfolding inv_def
proof (rule, rule, rule, rule, rule)
  fix i j
  assume "i < fst (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  assume "j \<le> i"
  hence "j < next_time_world tw"
    using `i < next_time_world tw` by auto
  assume " is_posedge (wline_of (next_time_world tw, snd tw)) CLK j i"
  hence "is_posedge (wline_of tw) CLK j i"
    by auto
  hence "wline_of tw CLK (j - 1) \<noteq> wline_of tw CLK j"
    by simp
  moreover have "(\<forall>s. wline_of tw s j = wline_of tw s (fst tw))"
    using unchanged_until_next_time_world `fst tw = 0` `j < next_time_world tw`
    by (metis less_eq_nat.simps(1))
  ultimately have "False"
    by (metis \<open>j < next_time_world tw\<close> assms le0 less_imp_diff_less unchanged_until_next_time_world)
  thus "wline_of (next_time_world tw, snd tw) OUT (i + 1) = wline_of (next_time_world tw, snd tw) D j"
    by auto
qed

lemma init1:
  "\<turnstile> [\<lambda>tw. get_time tw = 0 \<and> beval_world_raw2 tw (Bsig CLK) (Bv False)]
        Bnull
     [\<lambda>tw. inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv (next_time_world tw, snd tw)", rotated 1])
    apply (rule Null2)
   apply simp
  using inv_time_seq_next_time0' by auto

lemma init2:
  " \<turnstile> [\<lambda>tw. get_time tw = 0]
        Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull
      [\<lambda>tw. Dflipflop.inv (next_time_world tw, snd tw)]"
  apply (rule If2)
   apply (rule init0)
  apply (rule init1)
  done

lemma init3:
  "init_sim_hoare (\<lambda>tw. get_time tw = 0) dflipflop inv"
  unfolding dflipflop_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule init2)
  done

lemma inv2_holds_initially_assigned:
  assumes "fst tw = 0"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 wline_of tw D (fst tw)]"
  shows "inv2 (next_time_world tw', snd tw')"
  unfolding inv2_def
proof (rule, rule, rule)
  fix i
  assume *: "disjnt {CLK} (event_of (next_time_world tw', snd tw'))
         \<or>  wline_of (next_time_world tw', snd tw') CLK (get_time (next_time_world tw', snd tw')) = Bv False"
  assume "get_time (next_time_world tw', snd tw') \<le> i"
  hence "next_time_world tw' \<le> i"
    by auto
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least by metis
  hence "0 < next_time_world tw'"
    by linarith
  have "wline_of tw' OUT (i + 1) = wline_of tw D (fst tw)"
    unfolding tw'_def
    by (simp add: assms(1) beval_world_raw2_Bsig worldline_upd2_def worldline_upd_def)
  also have "... = wline_of tw' OUT (fst tw + 1)"
    unfolding tw'_def by (metis worldline_upd2_at_dly)
  also have "... = wline_of tw' OUT (fst tw' + 1)"
    by (simp add: tw'_def worldline_upd2_def)
  finally have **: "wline_of tw' OUT (i + 1) = wline_of tw' OUT (fst tw' + 1)"
    by auto
  have "disjnt {CLK} (event_of (next_time_world tw', snd tw'))  \<or> wline_of tw' CLK (next_time_world tw') = (Bv False)"
    using * by auto
  hence "wline_of tw' OUT (fst tw' + 1) = wline_of tw' OUT (next_time_world tw')"
    by (smt One_nat_def Suc_diff_1 Suc_eq_plus1 \<open>0 < next_time_world tw'\<close> assms(1) diff_add_zero
    less_numeral_extra(3) o_apply plus_1_eq_Suc snd_conv tw'_def worldline_upd2_def
    worldline_upd_def zero_less_diff)
  hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT (next_time_world tw')"
    using ** by auto
  thus "wline_of (next_time_world tw', snd tw') OUT (i + 1) =
        wline_of (next_time_world tw', snd tw') OUT (get_time (next_time_world tw', snd tw'))"
    by auto
qed

lemma init4:
  " \<turnstile> [\<lambda>tw. (get_time tw = 0 \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (get_time tw))) \<and> beval_world_raw2 tw (Bsig CLK) (Bv True)]
        Bassign_trans OUT (Bsig D) 1
      [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule Assign2_altI)
  using inv2_holds_initially_assigned
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

lemma inv2_holds_initially:
  assumes "fst tw = 0" and "(\<forall>i. wline_of tw OUT i = wline_of tw OUT (get_time tw))" and "beval_world_raw2 tw (Bsig CLK) (Bv False)"
  shows "inv2 (next_time_world tw, snd tw)"
proof -
  have "inv tw"
    using assms(1) unfolding inv_def by auto
  moreover have "inv2 tw"
    using assms(2)  using inv2_def by blast
  ultimately show ?thesis
    using inv2_next_time_disjnt inv2_next_time_null assms(3)
    by (meson greaterThanAtMost_iff next_time_world_at_least order_refl)
qed

lemma init5:
  " \<turnstile> [\<lambda>tw. (get_time tw = 0 \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (get_time tw))) \<and> beval_world_raw2 tw (Bsig CLK) (Bv False)]
        Bnull
      [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. inv2 (next_time_world tw, snd tw)", rotated 1])
    apply (rule Null2)
   apply simp
  using inv2_holds_initially by auto

lemma init6:
  "\<turnstile> [\<lambda>tw. get_time tw = 0 \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (get_time tw))]
        Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull
     [\<lambda>tw. inv2 (next_time_world tw, snd tw)]"
  apply (rule If2)
   apply (rule init4)
  apply (rule init5)
  done

lemma init7:
  "init_sim_hoare (\<lambda>tw. get_time tw = 0 \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (get_time tw))) dflipflop inv2"
  unfolding dflipflop_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule init6)
  done

theorem init8:
  "init_sim_hoare
    (\<lambda>tw. fst tw = 0 \<comment> \<open>initially the time is zero\<close>
        \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (fst tw))) \<comment> \<open>initially no signal shall be posted in the internal signal\<close>
      dflipflop
    (\<lambda>tw. inv tw \<and> inv2 tw)"
  apply (rule ConjI_sim)
   apply (rule ConseqI_sim[where Q="inv" and P="\<lambda>tw. fst tw = 0"])
     apply simp
    apply (rule init3)
   apply simp
  apply (rule init7)
  done

lemma init_sim_hoare_well_typed:
  assumes "conc_wt \<Gamma> dflipflop"
  shows "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) dflipflop (\<lambda>tw. wityping \<Gamma> (snd tw))"
  unfolding dflipflop_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv
  by (metis assms conc_stmt.distinct(1) conc_stmt.inject(2) conc_wt.cases dflipflop_def
      seq_stmt_preserve_wityping_hoare)

theorem init_sim_hoare_inv_and_well_typed:
  assumes "conc_wt \<Gamma> dflipflop"
  shows
  "init_sim_hoare
    (\<lambda>tw. fst tw = 0 \<comment> \<open>initially the time is zero\<close>
        \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (fst tw)) \<comment> \<open>initially no signal shall be posted in the internal signal\<close>
        \<and> wityping \<Gamma> (snd tw))
      dflipflop
    (\<lambda>tw. (inv tw \<and> inv2 tw) \<and> wityping \<Gamma> (snd tw))"
  apply (rule ConjI_sim)
   apply (rule strengthen_precondition_init_sim_hoare)
  prefer 2
    apply (rule init8)
   apply blast
  apply (rule ConseqI_sim)
  prefer 2
  apply (rule init_sim_hoare_well_typed[OF assms])
  by blast+

lemma
  assumes "sim_fin w (i + 1) dflipflop tw'"
  assumes "\<forall>i. snd w OUT i = snd w OUT 0"
  assumes " conc_wt \<Gamma> dflipflop" and "wityping \<Gamma> w"
  shows "(\<forall>j \<le> i. is_posedge (wline_of tw') CLK j i \<longrightarrow>  wline_of tw' OUT (i + 1) = wline_of tw' D j)"
proof -
  obtain tw where "init_sim (0, w) dflipflop tw" and  "tw, i + 1, dflipflop \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf dflipflop"
    unfolding conc_stmt_wf_def dflipflop_def by auto
  moreover have "nonneg_delay_conc dflipflop"
    unfolding dflipflop_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT (fst tw)) \<and> wityping \<Gamma> (snd tw)) dflipflop (\<lambda>tw. (inv tw \<and> inv2 tw) \<and> wityping \<Gamma> (snd tw))"
    using init_sim_hoare_soundness[OF init_sim_hoare_inv_and_well_typed[OF assms(3)]] by auto
  hence "(inv tw \<and> inv2 tw) \<and> wityping \<Gamma> (snd tw)"
    using \<open>init_sim (0, w) dflipflop tw\<close> fst_conv assms(2) assms(4) unfolding init_sim_valid_def
    by (metis (mono_tags) comp_apply snd_conv)
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw \<and> wityping \<Gamma> (snd tw)\<rbrace> dflipflop \<lbrace>inv\<rbrace>"
    using conc_sim_soundness[OF simulation_inv] \<open>conc_stmt_wf dflipflop\<close> \<open>nonneg_delay_conc dflipflop\<close>
    assms(3) by blast
  ultimately have "inv tw'"
    using \<open>tw, i + 1, dflipflop \<Rightarrow>\<^sub>S tw'\<close>  unfolding sim_hoare_valid_def
    by blast
  hence "\<forall>i<get_time tw'. \<forall>j\<le>i. is_posedge (wline_of tw') CLK j i \<longrightarrow> wline_of tw' OUT (i + 1) = wline_of tw' D j"
    unfolding inv_def by auto
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    by (smt less_add_one)
qed

end