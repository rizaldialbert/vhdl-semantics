(*
 * Copyright 2020, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Cosine_Imp 
  imports Cosine_Generator
begin

lemma (in cosine_locale) Inv_core_everywhere_strict:
  assumes "tw, T, architecture \<Rightarrow>\<^sub>S tw'"
  assumes "Inv tw" and "wityping \<Gamma> (snd tw)"
  shows   "\<And>n. fst tw \<le> n \<Longrightarrow> n \<le> T \<Longrightarrow> Inv_core (n, snd tw')"
proof -                                     
  fix n
  assume "fst tw \<le> n" and "n \<le> T"
  hence "n < T \<and> fst tw < n \<or> n = T \<or> fst tw = n"
    by auto
  moreover
  { assume "n < T \<and> fst tw < n" hence "fst tw < n" and "n < T" by auto
    have 0: "world_sim_fin2_alt tw T architecture tw'"
      using world_sim_fin_eq_world_sim_fin2_alt[OF conc_stmt_wf_arch nonneg_delay_conc_architecture] assms
      by auto
    obtain temp where "world_sim_fin2_alt tw n architecture temp" and "world_sim_fin2_alt temp T architecture tw'"
      using split_world_sim_fin2_alt[OF 0 `fst tw < n` `n < T`] by auto
    hence "world_sim_fin tw n architecture temp" and "world_sim_fin temp T architecture tw'"
      using world_sim_fin_eq_world_sim_fin2_alt[OF conc_stmt_wf_arch nonneg_delay_conc_architecture]
      by auto
    hence "Inv temp"
      using `Inv tw` `wityping \<Gamma> (snd tw)` inv_all_preserved_arch
      unfolding sim_hoare_valid_wt_def by blast
  
    have "fst temp = n" and "n \<le> fst temp" and "n - 1 - 1 \<le> fst temp" and "n - 1 \<le> fst temp"
      using fst_world_sim_fin2_alt[OF `world_sim_fin2_alt tw n architecture temp`] by auto
    note helpers =     world_sim_fin2_alt_unaffected_before_curr[OF `world_sim_fin2_alt temp T architecture tw'` 
      nonneg_delay_conc_architecture conc_stmt_wf_arch `n \<le> fst temp`, unfolded comp_def snd_conv fst_conv] 
      world_sim_fin2_alt_unaffected_before_curr[OF `world_sim_fin2_alt temp T architecture tw'` 
      nonneg_delay_conc_architecture conc_stmt_wf_arch `n - 1 \<le> fst temp`, unfolded comp_def snd_conv fst_conv] 
      world_sim_fin2_alt_unaffected_before_curr[OF `world_sim_fin2_alt temp T architecture tw'` 
      nonneg_delay_conc_architecture conc_stmt_wf_arch `n - 1 - 1\<le> fst temp`, unfolded comp_def snd_conv fst_conv]
    have "inv_reg (n, snd temp)" and "inv_ncommon (n, snd temp)" and "inv_sqr (n, snd temp)"
     and "inv_naccum (n, snd temp)" and "Inv_core (n, snd temp)" and "inv_nfrac (n, snd temp)"
      using `Inv temp` `fst temp = n` by auto
    hence "Inv_core (n, snd tw')"
      unfolding inv_reg_def inv_ncommon_alt_def inv_sqr_def inv_naccum_alt_def inv_term1_def
      inv_output_def inv_output_ready_def inv_nout_alt_def inv_nstate_alt_def inv_ncounter_alt_def
      inv_n0_def comp_def fst_conv snd_conv helpers inv_nfrac_alt_def by auto }
  moreover
  { assume "n = T"
    moreover have "fst tw' = T"
      using assms(1)  using world_maxtime_lt_fst_tres by blast
    ultimately have "tw' = (n, snd tw')"
      by auto
    have "Inv tw'"
      using `Inv tw` `wityping \<Gamma> (snd tw)` assms(1) inv_all_preserved_arch 
      unfolding sim_hoare_valid_wt_def by blast
    hence "Inv_core (n, snd tw')"
      using `tw' = (n, snd tw')` by auto }
  moreover
  { assume "fst tw = n"
    hence "Inv (n, snd tw)" and "n \<le> fst tw" and "n - 1 \<le> fst tw" and "n - 1 - 1 \<le> fst tw"
      using `Inv tw` by auto
    have "world_sim_fin2_alt tw T architecture tw'"
      using assms(1) world_sim_fin_eq_world_sim_fin2_alt 
      by (simp add: world_sim_fin_eq_world_sim_fin2_alt conc_stmt_wf_arch nonneg_delay_conc_architecture)
    note helpers =  world_sim_fin2_alt_unaffected_before_curr[OF `world_sim_fin2_alt tw T architecture tw'` 
      nonneg_delay_conc_architecture conc_stmt_wf_arch `n \<le> fst tw`, unfolded comp_def snd_conv fst_conv]
      world_sim_fin2_alt_unaffected_before_curr[OF `world_sim_fin2_alt tw T architecture tw'` 
      nonneg_delay_conc_architecture conc_stmt_wf_arch `n - 1\<le> fst tw`, unfolded comp_def snd_conv fst_conv]
      world_sim_fin2_alt_unaffected_before_curr[OF `world_sim_fin2_alt tw T architecture tw'` 
      nonneg_delay_conc_architecture conc_stmt_wf_arch `n - 1 - 1\<le> fst tw`, unfolded comp_def snd_conv fst_conv]
    have "Inv_core (n, snd tw')"
      using `Inv (n, snd tw)`
      unfolding inv_reg_def inv_ncommon_alt_def inv_sqr_def inv_naccum_alt_def inv_term1_def
      inv_output_def inv_output_ready_def inv_nout_alt_def inv_nstate_alt_def inv_ncounter_alt_def
      inv_n0_def comp_def fst_conv snd_conv helpers inv_nfrac_alt_def by auto }
  ultimately show "Inv_core (n, snd tw')"
    by auto
qed

lemma (in cosine_locale) registers_unchanged_no_rising_edge:
  assumes "tw, T, architecture \<Rightarrow>\<^sub>S tw'"
  assumes "Inv tw" and "wityping \<Gamma> (snd tw)" and "fst tw \<le> m" and "m \<le> n" and "n \<le> T"
  assumes "\<And>k. m \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
  assumes "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  shows   "wline_of tw' s m = wline_of tw' s n"
  using assms
proof (induction "n - m" arbitrary: n)
  case 0
  hence "m = n"
    by auto
  then show ?case 
    by auto
next
  case (Suc x)
  hence "x = (n - 1) - m"
    by (auto)
  have "m = n \<or> m < n"
    using Suc by auto
  moreover
  { assume " m = n"
    hence ?case by auto }
  moreover
  { assume " m < n"
    hence "m \<le> n - 1"
      by auto
    have "n - 1 \<le> T"
      using Suc by auto
    have *: "\<And>k. m \<le> k \<Longrightarrow> k \<le> n - 1 \<Longrightarrow> \<not> (snd (snd tw') CLK (k - 1) = Bv False \<and> snd (snd tw') CLK k = Bv True)"
      using Suc(9) by auto
    have "wline_of tw' s m = wline_of tw' s (n - 1)"
      using Suc(1)[OF `x = (n - 1) - m` `tw, T, architecture \<Rightarrow>\<^sub>S tw'` `Inv tw` `wityping \<Gamma> (snd tw)` `fst tw \<le> m` `m \<le> n - 1` `n - 1 \<le> T` * `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}`]
      by auto
    have "fst tw \<le> n" and "n \<le> T"
      using Suc.prems(5) assms(4) Suc.prems(6) dual_order.trans by blast+
    have "\<not> is_posedge2 (snd tw') CLK (n - 1)"
      using * \<open>m \<le> n - 1\<close> by blast
    moreover have "Inv_core (n, snd tw')"
      using Inv_core_everywhere_strict[OF Suc(3) `Inv tw` `wityping \<Gamma> (snd tw)` `fst tw \<le> n` `n \<le> T`]
      by auto
    ultimately have "wline_of tw' s (n - 1) = wline_of tw' s n"
      using `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}` unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    hence ?case
      using `wline_of tw' s m = wline_of tw' s (n - 1)` by auto }
  ultimately show ?case 
    by auto
qed

lemma (in cosine_locale) posedge_only_if_mod_clk_period:
  assumes "even clk_period" and "2 \<le> clk_period"
  assumes "\<forall>k < clk_period div 2. wline_of (0, w) CLK k = Bv True"
  assumes "\<forall>k \<ge> clk_period div 2. k < clk_period \<longrightarrow> wline_of (0, w) CLK k = Bv False"
  assumes "\<forall>k \<ge> clk_period. wline_of (0, w) CLK k = wline_of (0, w) CLK (k - clk_period)"
  assumes type: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
  shows   "\<And>m. m mod clk_period \<noteq> 0 \<Longrightarrow> \<not> is_posedge2 w CLK m"
proof -
  fix m
  assume "m mod clk_period \<noteq> 0"
  have "\<And>k. (wline_of (0, w) CLK k = Bv False) \<or> (wline_of (0, w) CLK k = Bv True)"
    using type type_of_bty_cases by blast
  have assms6': "\<And>k. k < clk_period \<Longrightarrow> wline_of (0, w) CLK k = Bv True \<Longrightarrow> k < clk_period div 2"
    using assms(4) \<open>\<And>k. (wline_of (0, w) CLK k = Bv False) \<or> (wline_of (0, w) CLK k = Bv True)\<close>
    using nat_less_le by force
  have assms7': "\<And>k. wline_of (0, w) CLK k = wline_of (0, w) CLK (k mod clk_period)"
    using wline_of_mod[OF assms(5)]  by (metis mod_by_0 neq0_conv)
  have "m < clk_period \<or> clk_period < m"
    using `m mod clk_period \<noteq> 0` by (metis linorder_neqE_nat mod_self)
  moreover
  { assume "m < clk_period"
    have "\<not> is_posedge2 w CLK m"
    proof (rule ccontr)
      assume "\<not> \<not> is_posedge2 w CLK m" hence "is_posedge2 w CLK m" by auto
      hence "snd w CLK (m - 1) = Bv False \<and> snd w CLK m = Bv True"
        by auto
      hence "m < clk_period div 2"
        using assms6'[OF `m < clk_period`] unfolding comp_def snd_conv by auto
      hence "wline_of (0, w) CLK (m - 1) = Bv True"
        using assms(3) less_imp_diff_less by blast
      thus False
        using \<open>\<not> \<not> (snd w CLK (m - 1) = Bv False \<and> snd w CLK m = Bv True)\<close> by auto
    qed }
  moreover
  { assume "clk_period < m"
    have "m = clk_period * (m div clk_period) + m mod clk_period"
      using mult_div_mod_eq by auto
    hence "wline_of (0, w) CLK m = wline_of (0, w) CLK (m mod clk_period)"
      using assms7' by auto
    have "\<not> is_posedge2 w CLK m"
    proof (rule ccontr)
      assume "\<not> \<not> is_posedge2 w CLK m"
      hence "is_posedge2 w CLK m" by auto
      hence "snd w CLK (m - 1) = Bv False \<and> snd w CLK m = Bv True"
        by auto
      have "m mod clk_period < clk_period"
        using `2 \<le> clk_period `  by (auto intro!: pos_mod_bound)
      moreover have "snd w CLK (m mod clk_period) = Bv True"
        using assms7'[unfolded comp_def snd_conv] \<open>snd w CLK (m - 1) = Bv False \<and> snd w CLK m = Bv True\<close> by auto
      ultimately have "m mod clk_period < clk_period div 2"
        using assms6'[unfolded comp_def snd_conv] by blast
      hence "snd w CLK (m mod clk_period - 1) = Bv True"
        using assms(3)[unfolded comp_def snd_conv] less_imp_diff_less by blast
      have "m = (m div clk_period) * clk_period + m mod clk_period"
        by auto
      hence "m - 1 = (m div clk_period) * clk_period + ((m mod clk_period) - 1)"
        using \<open>m mod clk_period \<noteq> 0\<close> by auto
      hence "snd w CLK (m - 1) = Bv True"
        using wline_of_mod2[OF assms(5)] \<open>snd w CLK (m mod clk_period - 1) = Bv True\<close>
        by (metis assms7' comp_apply mod_mult_self4 mult.commute snd_conv)
      thus False
        using \<open>\<not> \<not> (snd w CLK (m - 1) = Bv False \<and> snd w CLK m = Bv True)\<close> by auto
    qed }
  ultimately show "\<not> is_posedge2 w CLK m"
    by auto
qed

lemma (in cosine_locale) ubin_counter_atmost:
  assumes "wityping \<Gamma> (snd tw)"
  shows   "ubin_of COUNTER at_time n on tw \<le> 7"
proof -
  have *: "type_of (wline_of tw COUNTER n) = Lty Uns 3"
    using assms unfolding wityping_def wtyping_def 
    using cosine_locale_axioms unfolding cosine_locale_def comp_def snd_conv fst_conv by auto
  have "\<exists>bs. wline_of tw COUNTER n = Lv Uns bs \<and> length bs = 3"
  proof (rule ccontr)
    assume "\<not> (\<exists>bs. wline_of tw COUNTER n = Lv Uns bs \<and> length bs = 3)"
    hence "\<And>bs. wline_of tw COUNTER n = Lv Uns bs \<Longrightarrow> length bs \<noteq> 3"
      by auto
    moreover have "\<And>bs. wline_of tw COUNTER n = Lv Uns bs \<Longrightarrow> length bs = 3"
      using * by auto
    ultimately have **: "\<And>bs. wline_of tw COUNTER n = Lv Uns bs \<Longrightarrow> False"
      by auto
    obtain bs where" wline_of tw COUNTER n = Lv Uns bs"
      using type_of.elims[OF *] by fastforce
    with ** show False by auto
  qed
  then obtain bs where "wline_of tw COUNTER  n = Lv Uns bs" and "length bs = 3"
    by auto
  hence "bl_to_bin bs < 8"
    using bl_to_bin_lt2p[of "bs"] by auto
  thus ?thesis
    using \<open>wline_of tw COUNTER n = Lv Uns bs\<close> by auto
qed

fun approx_div_fact :: "nat \<Rightarrow> (1, 31) fixed" where
  "approx_div_fact 0                          = Fixed (approx_one :: (1 + 31) word)   "
| "approx_div_fact (Suc 0)                    = Fixed (approx_half :: (1 + 31) word)  "
| "approx_div_fact (Suc (Suc 0))              = Fixed (approx_fourth :: (1 + 31) word)"
| "approx_div_fact (Suc (Suc (Suc 0)))        = Fixed (approx_sixth :: (1 + 31) word) "
| "approx_div_fact (Suc (Suc (Suc (Suc 0))))  = Fixed (approx_eighth :: (1 + 31) word)"

fun fixed_of_sval :: "val \<Rightarrow> ('a::len0, 'b::len0) fixed" where
  "fixed_of_sval (Lv ki bl) = Fixed (of_bl bl :: ('a + 'b) word)"

fun nat_of_val :: "val \<Rightarrow> nat" where
  "nat_of_val (Lv ki bl) = nat (bl_to_bin bl)"

fun val_of_fixed :: "('a::len0, 'b::len0) fixed \<Rightarrow> val" where
  "val_of_fixed fi = Lv Sig (to_bl (word_of_fixed fi))"

lemma nths_from_upt_eq_drop_take [simp]: "nths l {m..<n} = drop m (take n l)"
proof (induct l rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case 
    unfolding nths_append nths_singleton by auto
qed                        
    
lemma (in cosine_locale) math_ident:
  assumes "sim_fin2 w (i + 7 * clk_period + 1) architecture tw'"
  assumes "wityping \<Gamma> w"

  \<comment>\<open>characterising clock signals\<close>
  assumes "even clk_period" and "3 < clk_period"
  assumes "\<forall>k < clk_period div 2. wline_of (0, w) CLK k = Bv True"
  assumes "\<forall>k \<ge> clk_period div 2. k < clk_period \<longrightarrow> wline_of (0, w) CLK k = Bv False"
  assumes "\<forall>k \<ge> clk_period. wline_of (0, w) CLK k = wline_of (0, w) CLK (k - clk_period)"

  \<comment>\<open>clock is in rising edge at i\<close>
  assumes posedge: "is_posedge2 (snd tw') CLK (i + 7 * clk_period)"

  \<comment> \<open>output ready signal is asserted at i + 1\<close>
  assumes ready: "wline_of tw' OUTREADY_REG (i + 7 * clk_period + 1) = Bv True"
  assumes " ubin_of COUNTER at_time (i + 1) on tw' \<noteq> 5"
  shows   "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = 
                         (foldr (\<lambda>a b. approx_div_fact a + (fixed_of_sval (wline_of tw' INPUT (i + 1 * clk_period - 1)) * fixed_of_sval (wline_of tw' INPUT (i + 1 * clk_period - 1))) * b) [0 ..< 5]  0)"
proof -
  obtain tw where "init_sim2 (0, w) architecture tw" and  0: "tw, (i + 7 * clk_period + 1), architecture \<Rightarrow>\<^sub>S tw'"
    using sim_fin2.cases[OF assms(1)]  by metis
  hence "Inv tw"
    using init_sim2_hoare_wt_soundness[OF init_sat_inv_all] `wityping \<Gamma> w` 
    unfolding init_sim2_valid_wt_def 
    by (metis conc_stmt_wf_arch cwt_arch fst_conv nonneg_delay_conc_architecture snd_conv)
  moreover have "wityping \<Gamma> (snd tw)"
    using \<open>wityping \<Gamma> w\<close> init_sim2_preserves_wityping[OF `init_sim2 (0, w) architecture tw`]
    by (simp add: conc_stmt_wf_arch nonneg_delay_conc_architecture)
  ultimately have "Inv tw'"                                                   
    using inv_all_preserved_arch 0 unfolding sim_hoare_valid_wt_def by blast

  have "wityping \<Gamma> (snd tw')"
    using world_sim_fin_preserves_wityping[OF 0] 
    using \<open>wityping \<Gamma> (snd tw)\<close> conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast

  \<comment> \<open>CLK's behaviour is the same either for twk or (0, w)\<close>
  have "CLK \<notin> set (signals_from architecture)"
    unfolding architecture_def circuit_defs by auto
  have "\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k"
    using sim_fin2_unaffected[OF assms(1)]
    using \<open>CLK \<notin> set (signals_from architecture)\<close> conc_stmt_wf_arch nonneg_delay_conc_architecture by auto

  have "wline_of tw' OUTREADY_REG (fst tw') = Bv True"
    using ready fst_world_sim_fin2_alt 0 world_sim_fin2_eq_world_sim_fin 
    by (metis world_maxtime_lt_fst_tres)
  have posedge2: "is_posedge2 (snd tw') CLK (fst tw' - 1)"
    using posedge fst_world_sim_fin2_alt 0 world_sim_fin2_eq_world_sim_fin 
    by (metis diff_add_inverse2 world_maxtime_lt_fst_tres)
  have *: "\<And>n. fst tw < n \<Longrightarrow> n < i + 7 * clk_period + 1 \<Longrightarrow> Inv_core (n, snd tw')"
    using Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto 
  have "wline_of tw' RST (fst tw' - 1) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (fst tw' - 1) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (fst tw' - 1)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (fst tw' - 1) = Bv True"
      using `wline_of tw' RST (fst tw' - 1) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' OUTREADY_REG (fst tw') = Bv False"
      using `Inv tw'` `is_posedge2 (snd tw') CLK (fst tw' - 1)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv  by simp
    with ready show False
      using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
  qed
  hence "wline_of tw' NEXT_OUTREADYREG (fst tw' - 1) = Bv True"
    using `Inv tw'` posedge2 `wline_of tw' OUTREADY_REG (fst tw') = Bv True` 
    unfolding inv_reg_alt_def by auto
  have "wline_of tw' STATE (fst tw' - 2) = V_POST"
  proof -
    have "fst tw < fst tw' - 1"
      using world_maxtime_lt_fst_tres[OF 0] fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms
      by (auto simp add: field_simps)
    hence "Inv_core (fst tw' - 1, snd tw')"
      using * world_maxtime_lt_fst_tres[OF 0] by simp
    thus ?thesis
      using \<open>wline_of tw' NEXT_OUTREADYREG (fst tw' - 1) = Bv True\<close>
      unfolding inv_nout_alt_def comp_def snd_conv fst_conv
      by (metis diff_diff_left one_add_one val.sel(1))
  qed
  have "wline_of tw' STATE (i + 7 * clk_period - 1) = V_POST"
    using world_maxtime_lt_fst_tres[OF 0] `wline_of tw' STATE (fst tw' - 2) = V_POST`
    `3 < clk_period`  by (metis add_diff_cancel_right nat_1_add_1)

  \<comment> \<open> obtaining accum\<close>
  have "wline_of tw' ACCUM (fst tw') = wline_of tw' NEXT_ACCUM (fst tw' - 1)"
    using `Inv tw'` posedge2 `wline_of tw' RST (fst tw' - 1) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  also have "... = wline_of tw' NEXT_ACCUM (i + 7 * clk_period)"
    using world_maxtime_lt_fst_tres[OF 0] `wline_of tw' STATE (fst tw' - 2) = V_POST`
    `3 < clk_period`  by (metis diff_add_inverse2)
  finally have "wline_of tw' ACCUM (fst tw') = wline_of tw' NEXT_ACCUM (i + 7 * clk_period)"
    by auto
  have  "bin_of ACCUM at_time fst tw' on tw' = sbintrunc 31 (bin_of FRAC at_time i + 7 * clk_period - 1 on tw' + 
                                                            (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})))"
  proof -
    have "Inv_core (i + 7 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    hence "bin_of NEXT_ACCUM at_time (i + 7 * clk_period) on tw' = sbintrunc 31 (bin_of FRAC at_time i + 7 * clk_period - 1 on tw' + 
                                                                                (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32}))   )"
      using `wline_of tw' STATE (i + 7 * clk_period - 1) = V_POST`
      unfolding inv_naccum_alt_def comp_def snd_conv fst_conv by auto
    thus ?thesis
      using `wline_of tw' ACCUM (fst tw') = wline_of tw' NEXT_ACCUM (i + 7 * clk_period)` by auto
  qed
  hence "(word_of_int (bin_of ACCUM at_time fst tw' on tw') :: (1 + 31) word) = word_of_int (sbintrunc 31 (bin_of FRAC at_time i + 7 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (sbintrunc (LENGTH((1 + 31)) - 1) (bin_of FRAC at_time i + 7 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})))"
    unfolding word_sbin.Abs_norm by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32}))"
    unfolding wi_hom_syms(1) by auto
  finally have "(word_of_int (bin_of ACCUM at_time fst tw' on tw') :: (1 + 31) word) = 
                 word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32}))"
    by auto
  hence "Fixed (word_of_int (bin_of ACCUM at_time fst tw' on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})))"
    unfolding plus_fixed.abs_eq by auto  
  have "Fixed (word_of_int (bin_of ACCUM at_time fst tw' on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (fst tw'))"
    (is "?lhs = ?rhs")
  proof -
    have "type_of (wline_of tw' ACCUM (fst tw')) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (get_time tw'))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "?lhs = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (get_time tw'))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (fst tw')))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (fst tw'))"
    proof -
      have "wline_of tw' ACCUM (fst tw') = Lv Sig (lval_of (wline_of tw' ACCUM (fst tw')))"
        using `type_of (wline_of tw' ACCUM (fst tw')) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  have "wline_of tw' STATE (i + 6 * clk_period + 1) = V_POST"
  proof -
    have a: "fst tw \<le> i + 6 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 6 * clk_period + 1 \<le> i + 7 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 7 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 6 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 7 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 6 * clk_period = m1 * clk_period"
        using `(i + 6 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 7 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 7 * clk_period = m2 * clk_period"
          using `(i + 7 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 7 * clk_period - (i + 6 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 6 * clk_period = m1 * clk_period` `i + 7  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 7 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 6 * clk_period + 1 \<le> n" and "n \<le> i + 7 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 6 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 7 * clk_period - 1` `i + 7 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show ?thesis
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      `wline_of tw' STATE (i + 7 * clk_period - 1) = V_POST` by auto
  qed
  moreover have "Inv_core (i + 6 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
  moreover have "is_posedge2 (snd tw') CLK (i + 6 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 7 * clk_period)"
      using assms(8) 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 7 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 6 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 6 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  moreover have "wline_of tw' RST (i + 6 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 6 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 6 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 6 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 6 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' STATE (i + 6 * clk_period + 1) = V_INIT"
      using `Inv_core (i + 6 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 6 * clk_period)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv  by auto
    with `wline_of tw' STATE (i + 6 * clk_period + 1) = V_POST` show False
      using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
  qed
  ultimately have "wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST"
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  have " wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<and> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 *clk_period - 1))"
  proof (rule ccontr)
    have "Inv_core (i + 6 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 6 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<and> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 * clk_period - 1)))"
    hence *: "(wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<Longrightarrow> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 * clk_period - 1)))"
      by auto
    let ?state = "wline_of tw' STATE (i + 6 * clk_period - 1)"
    consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      | "?state = V_PRE"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 6 * clk_period) \<noteq> V_POST"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 6 * clk_period) \<noteq> V_POST"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') INREADY (i + 6 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 6 * clk_period) \<noteq> V_POST"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 6 * clk_period) \<noteq> V_POST"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 6 * clk_period) \<noteq> V_POST"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST`
        by auto
    next
      case 6
      hence "wline_of tw' NEXT_STATE (i + 6 * clk_period) \<noteq> V_POST"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 6 * clk_period) = V_POST`
        by auto
    qed
  qed
  have "ubin_of COUNTER at_time i + 6 * clk_period - 2 on tw' = 0"
  proof -
    have "Inv_core (i + 6 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto    
    hence "ubin_of COUNTER at_time i + 6 * clk_period - 2 on tw' \<le> 0"
      using \<open>wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<and> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 *clk_period - 1))\<close>
      unfolding inv_n0_def comp_def snd_conv fst_conv  by (smt diff_diff_left nat_1_add_1)
    thus ?thesis
      using bl_to_bin_ge0 antisym by blast
  qed
  have "ubin_of COUNTER at_time i + 6 * clk_period - 1 on tw' = 0"
  proof -
    have "Inv_core (i + 6 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto   
    have "(i + 6 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 5 * clk_period < i + 6 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 6 * clk_period - 2 < i + 6 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 6 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 6 * clk_period - 2)"
      using ** by auto      
    hence "ubin_of COUNTER at_time i + 6 * clk_period - 1 on tw' = ubin_of COUNTER at_time i + 6 * clk_period - 2 on tw'"
      using `Inv_core (i + 6 * clk_period -1, snd tw')` unfolding inv_reg_alt_def comp_def snd_conv fst_conv  using diff_diff_left nat_1_add_1 by presburger
    thus ?thesis
      using `ubin_of COUNTER at_time i + 6 * clk_period - 2 on tw' = 0` by auto
  qed
  have "bin_of FRAC at_time i + 7 * clk_period - 1 on tw' = bin_of FRAC at_time i + 6 * clk_period + 1 on tw'"
  proof -
    have a: "fst tw \<le> i + 6 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 6 * clk_period + 1 \<le> i + 7 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 7 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 6 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 7 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 6 * clk_period = m1 * clk_period"
        using `(i + 6 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 7 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 7 * clk_period = m2 * clk_period"
          using `(i + 7 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 7 * clk_period - (i + 6 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 6 * clk_period = m1 * clk_period` `i + 7  * clk_period = m2 * clk_period` by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 7 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 6 * clk_period + 1 \<le> n" and "n \<le> i + 7 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 6 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 7 * clk_period - 1` `i + 7 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show ?thesis
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d] by auto
  qed
  also have "... = bin_of NEXT_FRAC at_time i + 6 * clk_period on tw'"
    using `Inv_core (i + 6 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 6 * clk_period)`
    `wline_of tw' RST (i + 6 * clk_period) = Bv False` unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  also have "... = approx_one"
  proof -
    have "Inv_core (i + 6 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nfrac (i + 6 * clk_period, snd tw')"
      by auto
    thus ?thesis
      using `ubin_of COUNTER at_time i + 6 * clk_period - 1 on tw' = 0`
      unfolding inv_nfrac_alt_def comp_def snd_conv fst_conv by auto
  qed
  finally have "bin_of FRAC at_time i + 7 * clk_period - 1 on tw' = approx_one"
    by auto
  have "bin_of TERM1 at_time (i + 7 * clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw')"
  proof -
    have "Inv_core (i + 7 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      unfolding inv_term1_def comp_def snd_conv fst_conv  by (metis diff_diff_left one_add_one)
  qed
  have "Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_one) :: (1 + 31) word)"
    using `bin_of FRAC at_time i + 7 * clk_period - 1 on tw' = approx_one` by auto
  have "((word_of_int approx_one) :: (1 + 31) word) = (approx_one :: (1 + 31) word)"
    unfolding word_uint.inverse_norm by eval
  hence "Fixed ((word_of_int approx_one) :: (1 + 31) word) = Fixed (approx_one :: (1 + 31) word)"
    by auto
  also have "... = approx_div_fact 0"
    by auto
  finally have "Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) = approx_div_fact 0"
    using `Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_one) :: (1 + 31) word)`
    by auto
  moreover have "Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) = (fixed_of_sval (wline_of tw' FRAC (i + 7 * clk_period - 1)) :: (1,31) fixed)"
  proof -
    have "type_of (wline_of tw' FRAC (i + 7 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' FRAC (i + 7 * clk_period - 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' FRAC (i + 7 * clk_period - 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' FRAC (i + 7 * clk_period - 1)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' FRAC (i + 7 * clk_period - 1))"
    proof -
      have "wline_of tw' FRAC (i + 7 * clk_period - 1) = Lv Sig (lval_of (wline_of tw' FRAC (i + 7 * clk_period - 1)))"
        using `type_of (wline_of tw' FRAC (i + 7 *clk_period - 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  ultimately have "(fixed_of_sval (wline_of tw' FRAC (i + 7 * clk_period - 1)) :: (1,31) fixed) = approx_div_fact 0"
    by auto

  have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
        word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31)"
  proof -
    have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)= 
          word_of_int
     (sbintrunc (length (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32}) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32})))"
      unfolding sbl_to_bin_alt_def by auto
    moreover have "(length (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32}) - 1) = 31"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "card {1::nat ..32} = 32"
        unfolding card_atLeastAtMost by auto 
      show ?thesis
        unfolding length_nths * 
        using card_slice[where len="64" and l=62 and r="31"] by auto
    qed
    ultimately have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                     word_of_int (sbintrunc 31 (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = (word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32})) :: (1 + 31) word) "
      unfolding word_sbin.Abs_norm by auto
    finally have "word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1+31) word)"
      by auto

    have interval: "{1 :: nat .. 32} = {1 :: nat ..< 33}"
      by auto
    have nths: "\<And>xs:: bool list. nths xs {1 :: nat .. 32} = drop 1 (take 33 xs)"
      unfolding interval  nths_from_upt_eq_drop_take[where m="1" and n="33"] by auto
    have " bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1 ..32}) = 
           bl_to_bin (drop 1 (take 33 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
      using nths[of "(lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))"] by auto
    also have "... = bintrunc (length (take 33 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))) - 1) (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
      unfolding bl2bin_drop by auto
    also have "... = bintrunc 32 (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence " length (take 33 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))) = 33"
        unfolding length_take by auto
      thus ?thesis
        by auto
    qed
    also have "... = bintrunc 32 (bl_to_bin (take (length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) - 31)  (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        by auto
    qed
    also have "... =  bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
      unfolding take_rest_bl2bin  by auto
    finally have "bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1 ..32}) = 
                      bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
      by auto


    have "(word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1 ..32})) :: (1+31) word)= 
           word_of_int (bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))"
      using \<open>bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) {1..32}) = bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))\<close> by auto
    \<comment> \<open>push bintrunc 32 inside\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (bintrunc 63 (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))"
      using bin_rest_power_trunc[where n="63" and k="31", symmetric] by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using bl2bin_drop by auto
    qed
    \<comment> \<open>pull bl_to_bin to left\<close>
    also have "... =  word_of_int (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))"
      unfolding butlast_pow_rest_bl2bin[symmetric] by auto
    \<comment> \<open>change to sbl_to_bin\<close>
    also have "... = (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... =  word_of_int (sbl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))) = 32"
        unfolding butlast_power length_take length_drop * by eval
      hence "(word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))) :: (1 + 31) word) = 
            (word_of_int (sbintrunc (length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))) :: (1 + 31) word)"
        by auto
      thus ?thesis
        using sbl_to_bin_alt_def by auto
    qed
    \<comment> \<open>push sbl_to_bin back to right\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (sbl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))" 
    proof -
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))) = 63"
        unfolding length_take length_drop * by eval
      hence **: "31 < length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)))))"
        by auto
      show ?thesis
        unfolding butlast_pow_rest_sbl2bin[OF **] by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (sbl_to_bin (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 7 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 7 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using sbl2bin_drop by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw')))"
      using `bin_of TERM1 at_time (i + 7 * clk_period - 1) on tw' = sbintrunc 63 (bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw')` 
      by auto
    also have "... =  word_of_int (sbintrunc 31 ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw')))"
    proof -
      have "(31 :: nat) \<le> 62" by auto
      show ?thesis
        unfolding bin_rest_power_strunc[OF `31 \<le> 62`]
        by auto
    qed
    also have "... =  word_of_int (sbintrunc (LENGTH(1 + 31) - 1) ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw')))"
      by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw'))"
      unfolding word_sbin.Abs_norm by auto
    also have "... = word_of_int ((bin_of COMMON at_time (i + 7 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 7 * clk_period - 2) on tw') div 2 ^ 31)"
      unfolding bin_rest_compow by auto
    also have "... = word_of_int (sbintrunc (length (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))) * 
                                  sbintrunc (length (lval_of (wline_of tw' ACCUM  (i + 7 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))) div 2 ^ 31)"
      using sbl_to_bin_alt_def2 by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))) * 
                                  sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))) div 2 ^ 31)"
    proof - 
      have "type_of (wline_of tw' COMMON (i + 7 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "type_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence **: "length (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      with * show ?thesis
        by auto
    qed
    also have "... = word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))) :: (1 + 31) word) * 
                                  sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))) :: (1 + 31) word ) div 2 ^ 31)"
      unfolding sint_sbintrunc' by auto
    finally show ?thesis
      unfolding `(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)`
      by auto
  qed
  hence "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
         Fixed (word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31))"
    by auto
  also have "... = Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2))))) * Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))))"
    using times_fixed.abs_eq[where xa="word_of_int (bin_of COMMON at_time i + 7 * clk_period - 2 on tw') :: (1 + 31) word" and 
                                    x="word_of_int (bin_of ACCUM at_time i + 7 * clk_period - 2 on tw') :: (1 + 31) word", symmetric]
    by auto
  also have "... = fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 7 * clk_period - 2))"
  proof -
    have "type_of (wline_of tw' COMMON (i + 7 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of COMMON at_time i + 7 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2))"
    proof -
      have "wline_of tw' COMMON (i + 7 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2)))"
        using `type_of (wline_of tw' COMMON (i + 7 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of COMMON at_time i + 7 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2))"
      by auto

    have "type_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of ACCUM at_time i + 7 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 7 * clk_period - 2))"
    proof -
      have "wline_of tw' ACCUM (i + 7 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 7 * clk_period - 2)))"
        using `type_of (wline_of tw' ACCUM (i + 7 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of ACCUM at_time i + 7 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 7 * clk_period - 2))"
      by auto
    thus ?thesis
      using \<open>Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 7 * clk_period - 2))))) = fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2))\<close> by auto
  qed
  finally have "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 7 * clk_period - 2))"
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 7 * clk_period - 2))"
    using `?lhs = ?rhs`
        `Fixed (word_of_int (bin_of ACCUM at_time fst tw' on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 7 * clk_period - 1)) {1 .. 32})))`
        `Fixed (word_of_int (bin_of FRAC at_time i + 7 * clk_period - 1 on tw')) = approx_div_fact 0`
    by auto

  \<comment> \<open> obtaining common and accum\<close>
  have "wline_of tw' COMMON (i + 6 * clk_period + 1) = wline_of tw' COMMON (i + 7 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 6 * clk_period + 1) = wline_of tw' ACCUM (i + 7 * clk_period - 2)"
  proof -
    have a: "fst tw \<le> i + 6 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 6 * clk_period + 1 \<le> i + 7 * clk_period - 2"
      using assms by (auto simp add: field_simps)
    have c: "i + 7 * clk_period - 2 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 6 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 7 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 6 * clk_period = m1 * clk_period"
        using `(i + 6 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 7 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 7 * clk_period = m2 * clk_period"
          using `(i + 7 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 7 * clk_period - (i + 6 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 6 * clk_period = m1 * clk_period` `i + 7  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 7 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 6 * clk_period + 1 \<le> n" and "n \<le> i + 7 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 6 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 7 * clk_period - 1` `i + 7 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' COMMON (i + 6 * clk_period + 1) = wline_of tw' COMMON (i + 7 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 6 * clk_period + 1) = wline_of tw' ACCUM (i + 7 * clk_period - 2)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  have "wline_of tw' NEXT_COMMON (i + 6 * clk_period) = wline_of tw' COMMON (i + 6 * clk_period + 1)"
    and "wline_of tw' NEXT_ACCUM  (i + 6 * clk_period) = wline_of tw' ACCUM (i + 6* clk_period + 1)"
    using `Inv_core (i + 6 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 6 * clk_period)` `wline_of tw' RST (i + 6 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  have "bin_of COMMON at_time (i + 6 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 6 * clk_period) on tw'"
  proof -
    have "Inv_core (i + 6 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<and> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 *clk_period - 1))`
      unfolding inv_ncommon_alt_def comp_def snd_conv fst_conv by auto
  qed
  have "(fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 1))"
  proof -
    have typof2: "type_of (wline_of tw' COMMON (i + 6 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs2 where " wline_of tw' COMMON (i + 6 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32"
      using type_of.elims[OF typof2] by fastforce
    have typof: "type_of (wline_of tw' COMMON (i + 7 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs1 where " wline_of tw' COMMON (i + 7 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32"
      using type_of.elims[OF typof] by fastforce
    hence "fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) = Fixed (of_bl bs1 :: (1 + 31) word)"
      using fixed_of_sval.simps by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs1) :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs1)))"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs1"] by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs1 - 1) (bl_to_bin bs1)))"
      using `wline_of tw' COMMON (i + 7 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs1))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs2))"
      using `bin_of COMMON at_time (i + 6 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 6 * clk_period) on tw'`
        `wline_of tw' COMMON (i + 6 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
        `wline_of tw' COMMON (i + 7 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` 
      using \<open>wline_of tw' COMMON (i + 6 * clk_period + 1) = wline_of tw' COMMON (i + 7 * clk_period - 2)\<close> \<open>wline_of tw' NEXT_COMMON (i + 6 * clk_period) = wline_of tw' COMMON (i + 6 * clk_period + 1)\<close> by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs2- 1) (bl_to_bin bs2)))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs2)))"
      using `wline_of tw' COMMON (i + 6 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32` by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs2) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs2"] by auto
    also have "... = Fixed (of_bl bs2 :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 1))"
      using `wline_of tw' COMMON (i + 6 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
      using fixed_of_sval.simps by auto
    finally show ?thesis
      by auto
  qed
  have "wline_of tw' COMMON (i + 6 * clk_period - 2) = wline_of tw' COMMON (i + 6 * clk_period - 1)"
  proof - 
    have "Inv_core (i + 6 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 6 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 5 * clk_period < i + 6 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 6 * clk_period - 2 < i + 6 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 6 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 6 * clk_period - 2)"
      using ** by auto
    thus ?thesis
      using `Inv_core (i + 6 * clk_period - 1, snd tw')`  unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed
    \<comment> \<open> obtaining state\<close>
  have "wline_of tw' STATE (i + 5 * clk_period + 1) = wline_of tw' STATE (i + 6 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 5 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 5 * clk_period + 1 \<le> i + 6 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 6 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 5 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 6 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 5 * clk_period = m1 * clk_period"
        using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 6 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 6 * clk_period = m2 * clk_period"
          using `(i + 6 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 6 * clk_period - (i + 5 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 5 * clk_period = m1 * clk_period` `i + 6  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 6 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 5 * clk_period + 1 \<le> n" and "n \<le> i + 6 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 5 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 6 * clk_period - 1` `i + 6 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' STATE (i + 5 * clk_period + 1) = wline_of tw' STATE (i + 6 * clk_period - 1)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  hence "wline_of tw' STATE (i + 5 * clk_period + 1) = V_PROC"
    using `wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<and> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 *clk_period - 1))`
    by auto
  have "wline_of tw' FRAC (i + 5 * clk_period + 1) = wline_of tw' FRAC (i + 6 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 5 * clk_period + 1) = wline_of tw' COUNTER (i + 6 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 5 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 5 * clk_period + 1 \<le> i + 6 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 6 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 5 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 6 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 5 * clk_period = m1 * clk_period"
        using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 6 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 6 * clk_period = m2 * clk_period"
          using `(i + 6 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 6 * clk_period - (i + 5 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 5 * clk_period = m1 * clk_period` `i + 6  * clk_period = m2 * clk_period` by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 6 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 5 * clk_period + 1 \<le> n" and "n \<le> i + 6 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 5 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 6 * clk_period - 1` `i + 6 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' FRAC (i + 5 * clk_period + 1) = wline_of tw' FRAC (i + 6 * clk_period - 1)"
     and "wline_of tw' COUNTER (i + 5 * clk_period + 1) = wline_of tw' COUNTER (i + 6 * clk_period - 1)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d] by auto
  qed
  have "wline_of tw' NEXT_FRAC (i + 5 * clk_period) = wline_of tw' FRAC (i + 5 * clk_period + 1)"
   and "wline_of tw' NEXT_STATE (i + 5 * clk_period) = wline_of tw' STATE (i + 5 * clk_period + 1)"
   and "wline_of tw' NEXT_COUNTER (i + 5 * clk_period) = wline_of tw' COUNTER (i + 5 * clk_period + 1)"
  proof -
    have "Inv_core (i + 5 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto  
    moreover have "is_posedge2 (snd tw') CLK (i + 5 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 6 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 6 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 6 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 5 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 5 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have "wline_of tw' RST (i + 5 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "wline_of tw' RST (i + 5 * clk_period) \<noteq> Bv False" 
      have "wityping \<Gamma> (snd tw')"
        using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
      hence "type_of (wline_of tw' RST (i + 5 * clk_period)) = Bty"
        unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence "wline_of tw' RST (i + 5 * clk_period) = Bv True"
        using `wline_of tw' RST (i + 5 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 5 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 5 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 5 * clk_period)` unfolding inv_reg_alt_def
        comp_def snd_conv fst_conv  by auto
      with `wline_of tw' STATE (i + 5 * clk_period + 1) = V_PROC` show False
        using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
    qed
    ultimately show "wline_of tw' NEXT_FRAC (i + 5 * clk_period) = wline_of tw' FRAC (i + 5 * clk_period + 1)"
      and "wline_of tw' NEXT_STATE (i + 5 * clk_period) = wline_of tw' STATE (i + 5 * clk_period + 1)"
      and "wline_of tw' NEXT_COUNTER (i + 5 * clk_period) = wline_of tw' COUNTER (i + 5 * clk_period + 1)"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "wline_of tw' NEXT_STATE (i + 5 * clk_period) = V_PROC" and "ubin_of NEXT_COUNTER at_time i + 5 * clk_period on tw' = 0"
    using `wline_of tw' STATE (i + 5 * clk_period + 1) = V_PROC` `ubin_of COUNTER at_time i + 6 * clk_period - 1 on tw' = 0` 
    using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 6 * clk_period - 1))) = 0\<close> \<open>wline_of tw' COUNTER (i + 5 * clk_period + 1) = wline_of tw' COUNTER (i + 6 * clk_period - 1)\<close> \<open>wline_of tw' NEXT_COUNTER (i + 5 * clk_period) = wline_of tw' COUNTER (i + 5 * clk_period + 1)\<close> 
    by auto
  have "wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 5 * clk_period - 1) = V_PRE"
  proof (rule ccontr)
    have "Inv_core (i + 5 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 5 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 5 * clk_period - 1) = V_PRE)"
    hence *: "(wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<Longrightarrow> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1)))" and 
      **: "wline_of tw' STATE (i + 5 * clk_period - 1) \<noteq> V_PRE" (is "?state \<noteq> _")by auto
    then consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 5 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 5 * clk_period) = V_PROC`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 5 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') INREADY (i + 5 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 5 * clk_period) = V_PROC`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 5 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 5 * clk_period) = V_PROC`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 5 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 5 * clk_period) = V_PROC`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 5 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 5 * clk_period) = V_PROC`
        by auto
    qed
  qed
  moreover have "wline_of tw' STATE (i + 5 * clk_period - 1) \<noteq> V_PRE"
  proof (rule ccontr)
    assume "\<not> wline_of tw' STATE (i + 5 * clk_period - 1) \<noteq> V_PRE"
    hence "wline_of tw' STATE (i + 5 * clk_period - 1) = V_PRE"
      by auto
    have "Inv_core (i + 5 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "bintrunc 3 (bl_to_bin (lval_of (wline_of (i + 5 * clk_period, snd tw') COUNTER (get_time (i + 5 * clk_period, snd tw') - 1))) - 1) = 0"
      using `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PRE` `ubin_of NEXT_COUNTER at_time (i + 5 * clk_period) on tw' = 0`
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
    hence "bintrunc 3 (ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1) = 0"
      unfolding fst_conv comp_def snd_conv by auto
    have "is_posedge2 (snd tw') CLK (i + 5 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 6 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 6 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 6 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 5 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 5 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 5 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> `is_posedge2 (snd tw') CLK (i + 5 * clk_period)` by blast
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto  
    have fd: "\<And>k. i + 4 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 5 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 4 * clk_period = m1 * clk_period"
        using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 5 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 5 * clk_period = m2 * clk_period"
          using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 6 * clk_period - (i + 5 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 4 * clk_period = m1 * clk_period` `i + 5  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 5 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 4 * clk_period + 1 \<le> n" and "n \<le> i + 5 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 4 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 5 * clk_period - 1` `i + 5 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    have c: "wline_of tw' STATE (i + 4 * clk_period + 1) = V_PRE"
    proof -
      have fa: "fst tw \<le> i + 4 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have fb: "i + 4 * clk_period + 1 \<le> i + 5 * clk_period - 1"
        using assms by (auto simp add: field_simps)
      have fc: "i + 5 * clk_period - 1 \<le> i + 7 * clk_period + 1"
        by auto
      show ?thesis
        using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` fa fb fc fd]
        `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PRE` by auto
    qed
    moreover have b: "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 5 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 5 * clk_period)` 
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv]  by auto
      hence "is_posedge2 w CLK (i + 5 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 4 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have a: "Inv_core (i + 4 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    moreover have d: "wline_of tw' RST (i + 4 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "\<not> wline_of tw' RST (i + 4 * clk_period) = Bv False"
      moreover have "type_of (wline_of tw' RST (i + 4 * clk_period)) = Bty"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      ultimately have "wline_of tw' RST (i + 4 * clk_period) = Bv True"
        using type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 4 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 4 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 4 * clk_period)`
        unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
      with `wline_of tw' STATE (i + 4 * clk_period + 1) = V_PRE`
      show False by auto
    qed
    ultimately have "wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PRE"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nstate (i + 4 * clk_period, snd tw')"
      by auto
    have "wline_of tw' STATE (i + 4 * clk_period - 1) = V_WAIT"
    proof (rule ccontr)
      assume "\<not> wline_of tw' STATE (i + 4 * clk_period - 1) = V_WAIT" (is "\<not> ?state = V_WAIT")
      then consider "?state = V_INIT" | "?state = V_PRE" | "?state = V_PROC" | "?state = V_POST" 
        | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
        by auto
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) \<noteq> V_PRE"
      proof (cases)
        case 1
        then show ?thesis 
          using `inv_nstate (i + 4 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 2
        then show ?thesis 
          using `inv_nstate (i + 4 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 3
        then show ?thesis 
          using `inv_nstate (i + 4 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          apply (cases "bval_of (wline_of (i + 4 * clk_period, snd tw') CTR_NEQ_0 (get_time (i + 4 * clk_period, snd tw') - 1))")
          by auto
      next
        case 4
        then show ?thesis 
          using `inv_nstate (i + 4 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 5
        then show ?thesis 
          using `inv_nstate (i + 4 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by (auto)
      qed
      thus False
        using \<open>wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PRE\<close> by blast
    qed
    moreover have "bval_of (wline_of tw' INREADY (i + 4 * clk_period - 1))"
    proof (rule ccontr)
      assume "\<not> bval_of (wline_of tw' INREADY (i + 4 * clk_period - 1))"
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_WAIT"
        using `Inv_core (i + 4 * clk_period, snd tw')` `wline_of tw' STATE (i + 4 * clk_period - 1) = V_WAIT`
        unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      thus False
        using `wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PRE` by auto
    qed
    ultimately have "ubin_of NEXT_COUNTER at_time i + 4 * clk_period on tw' = 4"
      using `Inv_core (i + 4 * clk_period, snd tw')` 
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
    hence "ubin_of COUNTER at_time i + 4 * clk_period + 1 on tw' = 4"
      using a b d unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    hence "ubin_of COUNTER at_time i + 5 * clk_period - 1 on tw' = 4"
    proof -
      have *: "get_time tw \<le> i + 4 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have **: "i + 4 * clk_period + 1 \<le> i + 5 * clk_period - 1"
        using assms by auto
      have "wline_of tw' COUNTER (i + 4 * clk_period + 1) = wline_of tw' COUNTER (i + 5 * clk_period - 1)"
        using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` * ** _ fd]
        using assms by (auto)
      thus ?thesis
        using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 4 * clk_period + 1))) = 4\<close> by auto
    qed        
    with `bintrunc 3 (ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1) = 0`
    show False
      by auto
  qed
  ultimately have "wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1))"
    by auto

  \<comment> \<open>obtaining counter value\<close>
  have "bintrunc 3 (ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1) = 0"
  proof -
    have "Inv_core (i + 5 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      using `ubin_of NEXT_COUNTER at_time (i + 5 * clk_period) on tw' = 0`
      `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1))`
      unfolding inv_ncounter_alt_def fst_conv comp_def snd_conv by auto
  qed
  hence "(ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1) mod 8 = 0" 
    unfolding bintrunc_mod2p by auto
  have "0 < ubin_of COUNTER at_time i + 5 * clk_period - 2 on tw'"
  proof -
    have "Inv_core (i + 5 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    hence "inv_n0 (i + 5 * clk_period - 1, snd tw')"
      by auto
    hence "0 < bl_to_bin (lval_of (snd (snd tw') COUNTER (i + 5 * clk_period - 1 - 1)))"
      using `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1))`
      unfolding inv_n0_def comp_def snd_conv fst_conv by auto
    thus ?thesis
      unfolding comp_def snd_conv fst_conv
      by (metis diff_diff_left nat_1_add_1)
  qed
  moreover have "ubin_of COUNTER at_time i + 5 * clk_period - 2 on tw' = ubin_of COUNTER at_time i + 5 * clk_period - 1 on tw'"
  proof -
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 5 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 4 * clk_period < i + 5 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 5 * clk_period - 2 < i + 5 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 5 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 5 * clk_period - 2)"
      using ** by auto
    moreover have "Inv_core (i + 5 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    ultimately show ?thesis
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed
  ultimately have "0 < ubin_of COUNTER at_time i + 5 * clk_period - 1 on tw'"
    by auto
  moreover have "ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' \<le> 7"
    using ubin_counter_atmost[OF `wityping \<Gamma> (snd tw')`] by auto
  ultimately have "(ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1) mod 8 = ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1"
    by (auto intro!: int_mod_eq')
  hence "ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' = 1"  
    using `(ubin_of COUNTER at_time (i + 5 * clk_period - 1) on tw' - 1) mod 8 = 0` by auto

  \<comment> \<open> obtaining frac \<close>
  have "bin_of NEXT_FRAC at_time (i + 5 * clk_period) on tw' = approx_half"
  proof -
    have "Inv_core (i + 5 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nfrac (i + 5 * clk_period, snd tw')"
      by auto
    thus ?thesis
      using `ubin_of COUNTER at_time i + 5 * clk_period - 1 on tw' = 1`
      unfolding inv_nfrac_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of FRAC at_time (i + 6 * clk_period - 1) on tw' = approx_half"
    using \<open>wline_of tw' FRAC (i + 5 * clk_period + 1) = wline_of tw' FRAC (i + 6 * clk_period - 1)\<close>
    \<open>wline_of tw' NEXT_FRAC (i + 5 * clk_period) = wline_of tw' FRAC (i + 5 * clk_period + 1)\<close> by
    auto

  have "bin_of TERM1 at_time (i + 6 * clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw')"
  proof -
    have "Inv_core (i + 6 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      unfolding inv_term1_def comp_def snd_conv fst_conv  by (metis diff_diff_left one_add_one)
  qed

  have "Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_half) :: (1 + 31) word)"
    using `bin_of FRAC at_time i + 6 * clk_period - 1 on tw' = approx_half` by auto
  have "((word_of_int approx_half) :: (1 + 31) word) = (approx_half :: (1 + 31) word)"
    unfolding word_uint.inverse_norm by eval
  hence "Fixed ((word_of_int approx_half) :: (1 + 31) word) = Fixed (approx_half :: (1 + 31) word)"
    by auto
  also have "... = approx_div_fact 1"
    by auto
  finally have "Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) = approx_div_fact 1"
    using `Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_half) :: (1 + 31) word)`
    by auto
  moreover have "Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) = (fixed_of_sval (wline_of tw' FRAC (i + 6 * clk_period - 1)) :: (1,31) fixed)"
  proof -
    have "type_of (wline_of tw' FRAC (i + 6 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' FRAC (i + 6 * clk_period - 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' FRAC (i + 6 * clk_period - 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' FRAC (i + 6 * clk_period - 1)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' FRAC (i + 6 * clk_period - 1))"
    proof -
      have "wline_of tw' FRAC (i + 6 * clk_period - 1) = Lv Sig (lval_of (wline_of tw' FRAC (i + 6 * clk_period - 1)))"
        using `type_of (wline_of tw' FRAC (i + 6 *clk_period - 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  ultimately have "(fixed_of_sval (wline_of tw' FRAC (i + 6 * clk_period - 1)) :: (1,31) fixed) = approx_div_fact 1"
    by auto

  \<comment> \<open> obtaining accum\<close>
  have  "bin_of NEXT_ACCUM at_time (i + 6 * clk_period) on tw' = 
            sbintrunc 31 (bin_of FRAC at_time i + 6 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})))"
  proof -
    have "Inv_core (i + 6 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 6 * clk_period - 1) = V_PROC \<and> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 6 *clk_period - 1))`
      unfolding inv_naccum_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of ACCUM at_time (i + 6 * clk_period + 1) on tw' = 
        sbintrunc 31 (bin_of FRAC at_time i + 6 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})))"
    using `wline_of tw' NEXT_ACCUM  (i + 6 * clk_period) = wline_of tw' ACCUM (i + 6* clk_period + 1)` 
    by auto
  hence "(word_of_int (bin_of ACCUM at_time i + 6 * clk_period + 1 on tw') :: (1 + 31) word) =  word_of_int (sbintrunc 31 (bin_of FRAC at_time i + 6 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (sbintrunc (LENGTH((1 + 31)) - 1) (bin_of FRAC at_time i + 6 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})))"
    unfolding word_sbin.Abs_norm by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32}))"
    unfolding wi_hom_syms(1) by auto
  finally have "(word_of_int (bin_of ACCUM at_time i + 6 * clk_period + 1 on tw') :: (1 + 31) word) = 
                 word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32}))"
    by auto
  hence "Fixed (word_of_int (bin_of ACCUM at_time i + 6 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})))"
    unfolding plus_fixed.abs_eq by auto
  have "Fixed (word_of_int (bin_of ACCUM at_time i + 6 * clk_period + 1 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period + 1))"
    (is "?lhs2 = ?rhs2")
  proof -
    have "type_of (wline_of tw' ACCUM (i + 6 * clk_period + 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 6 * clk_period + 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "?lhs2 = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period + 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period + 1)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period + 1))"
    proof -
      have "wline_of tw' ACCUM (i + 6 * clk_period + 1) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 6 * clk_period + 1)))"
        using `type_of (wline_of tw' ACCUM (i + 6 * clk_period + 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed

  have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
        word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31)"
  proof -
    have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)= 
          word_of_int
     (sbintrunc (length (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32}) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32})))"
      unfolding sbl_to_bin_alt_def by auto
    moreover have "(length (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32}) - 1) = 31"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "card {1::nat ..32} = 32"
        unfolding card_atLeastAtMost by auto 
      show ?thesis
        unfolding length_nths * 
        using card_slice[where len="64" and l=62 and r="31"] by auto
    qed
    ultimately have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                     word_of_int (sbintrunc 31 (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = (word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32})) :: (1 + 31) word) "
      unfolding word_sbin.Abs_norm by auto
    finally have "word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1+31) word)"
      by auto

    have interval: "{1 :: nat .. 32} = {1 :: nat ..< 33}"
      by auto
    have nths: "\<And>xs:: bool list. nths xs {1 :: nat .. 32} = drop 1 (take 33 xs)"
      unfolding interval  nths_from_upt_eq_drop_take[where m="1" and n="33"] by auto
    have " bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1 ..32}) = 
           bl_to_bin (drop 1 (take 33 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
      using nths[of "(lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))"] by auto
    also have "... = bintrunc (length (take 33 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))) - 1) (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
      unfolding bl2bin_drop by auto
    also have "... = bintrunc 32 (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence " length (take 33 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))) = 33"
        unfolding length_take by auto
      thus ?thesis
        by auto
    qed
    also have "... = bintrunc 32 (bl_to_bin (take (length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) - 31)  (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        by auto
    qed
    also have "... =  bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
      unfolding take_rest_bl2bin  by auto
    finally have "bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1 ..32}) = 
                      bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
      by auto


    have "(word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1 ..32})) :: (1+31) word)= 
           word_of_int (bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))"
      using \<open>bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) {1..32}) = bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))\<close> by auto
    \<comment> \<open>push bintrunc 32 inside\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (bintrunc 63 (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))"
      using bin_rest_power_trunc[where n="63" and k="31", symmetric] by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using bl2bin_drop by auto
    qed
    \<comment> \<open>pull bl_to_bin to left\<close>
    also have "... =  word_of_int (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))"
      unfolding butlast_pow_rest_bl2bin[symmetric] by auto
    \<comment> \<open>change to sbl_to_bin\<close>
    also have "... = (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... =  word_of_int (sbl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))) = 32"
        unfolding butlast_power length_take length_drop * by eval
      hence "(word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))) :: (1 + 31) word) = 
            (word_of_int (sbintrunc (length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))) :: (1 + 31) word)"
        by auto
      thus ?thesis
        using sbl_to_bin_alt_def by auto
    qed
    \<comment> \<open>push sbl_to_bin back to right\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (sbl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))" 
    proof -
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))) = 63"
        unfolding length_take length_drop * by eval
      hence **: "31 < length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)))))"
        by auto
      show ?thesis
        unfolding butlast_pow_rest_sbl2bin[OF **] by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (sbl_to_bin (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 6 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 6 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using sbl2bin_drop by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw')))"
      using `bin_of TERM1 at_time (i + 6 * clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw')` 
      by auto
    also have "... =  word_of_int (sbintrunc 31 ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw')))"
    proof -
      have "(31 :: nat) \<le> 62" by auto
      show ?thesis
        unfolding bin_rest_power_strunc[OF `31 \<le> 62`]
        by auto
    qed
    also have "... =  word_of_int (sbintrunc (LENGTH(1 + 31) - 1) ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw')))"
      by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw'))"
      unfolding word_sbin.Abs_norm by auto
    also have "... = word_of_int ((bin_of COMMON at_time (i + 6 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 6 * clk_period - 2) on tw') div 2 ^ 31)"
      unfolding bin_rest_compow by auto
    also have "... = word_of_int (sbintrunc (length (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))) * 
                                  sbintrunc (length (lval_of (wline_of tw' ACCUM  (i + 6 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))) div 2 ^ 31)"
      using sbl_to_bin_alt_def2 by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))) * 
                                  sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))) div 2 ^ 31)"
    proof - 
      have "type_of (wline_of tw' COMMON (i + 6 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "type_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence **: "length (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      with * show ?thesis
        by auto
    qed
    also have "... = word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))) :: (1 + 31) word) * 
                                  sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))) :: (1 + 31) word ) div 2 ^ 31)"
      unfolding sint_sbintrunc' by auto
    finally show ?thesis
      unfolding `(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)`
      by auto
  qed
  hence "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
         Fixed (word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31))"
    by auto
  also have "... = Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2))))) * Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))))"
    using times_fixed.abs_eq[where xa="word_of_int (bin_of COMMON at_time i + 6 * clk_period - 2 on tw') :: (1 + 31) word" and 
                                    x="word_of_int (bin_of ACCUM at_time i + 6 * clk_period - 2 on tw') :: (1 + 31) word", symmetric]
    by auto
  also have "... = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2))"
  proof -
    have "type_of (wline_of tw' COMMON (i + 6 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of COMMON at_time i + 6 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2))"
    proof -
      have "wline_of tw' COMMON (i + 6 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2)))"
        using `type_of (wline_of tw' COMMON (i + 6 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of COMMON at_time i + 6 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2))"
      by auto

    have "type_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of ACCUM at_time i + 6 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2))"
    proof -
      have "wline_of tw' ACCUM (i + 6 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 6 * clk_period - 2)))"
        using `type_of (wline_of tw' ACCUM (i + 6 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of ACCUM at_time i + 6 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2))"
      by auto
    thus ?thesis
      using \<open>Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 6 * clk_period - 2))))) = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2))\<close> by auto
  qed  
  finally have "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2))"
    by auto  
  hence "fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period + 1)) = 
          approx_div_fact 1 + fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2))"
    using `?lhs2 = ?rhs2`
        `Fixed (word_of_int (bin_of ACCUM at_time i + 6 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 6 * clk_period - 1)) {1 .. 32})))`
        `Fixed (word_of_int (bin_of FRAC at_time i + 6 * clk_period - 1 on tw')) = approx_div_fact 1`
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 1)) * (approx_div_fact 1 + fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2)))"
    using `fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) *  fixed_of_sval (wline_of tw' ACCUM (i + 7 * clk_period - 2))`
          `(fixed_of_sval (wline_of tw' COMMON (i + 7 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 1))`
    using \<open>wline_of tw' ACCUM (i + 6 * clk_period + 1) = wline_of tw' ACCUM (i + 7 * clk_period - 2)\<close> by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * (approx_div_fact 1 + fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2)))"
    using `wline_of tw' COMMON (i + 6 * clk_period - 2) = wline_of tw' COMMON (i + 6 * clk_period - 1)`
    by auto

  \<comment> \<open> obtaining common and accum\<close>
  have "wline_of tw' COMMON (i + 5 * clk_period + 1) = wline_of tw' COMMON (i + 6 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 5 * clk_period + 1) = wline_of tw' ACCUM (i + 6 * clk_period - 2)"
  proof -
    have a: "fst tw \<le> i + 5 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 5 * clk_period + 1 \<le> i + 6 * clk_period - 2"
      using assms by (auto simp add: field_simps)
    have c: "i + 6 * clk_period - 2 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 6 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 5 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 6 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 5 * clk_period = m1 * clk_period"
        using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 6 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 6 * clk_period = m2 * clk_period"
          using `(i + 6 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 7 * clk_period - (i + 6 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 5 * clk_period = m1 * clk_period` `i + 6  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 6 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 5 * clk_period + 1 \<le> n" and "n \<le> i + 6 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 5 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 6 * clk_period - 1` `i + 6 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' COMMON (i + 5 * clk_period + 1) = wline_of tw' COMMON (i + 6 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 5 * clk_period + 1) = wline_of tw' ACCUM (i + 6 * clk_period - 2)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  have "Inv_core (i + 5 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
    by auto
  have "is_posedge2 (snd tw') CLK (i + 5 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 7 * clk_period)"
      using `is_posedge2 (snd tw') CLK (i + 7 * clk_period)` 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 6 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 5 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 5 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  have "wline_of tw' RST (i + 5 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 5 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
      using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 5 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 5 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 5 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' STATE (i + 5 * clk_period + 1) = V_INIT"
      using  `Inv_core ((i + 5 * clk_period + 1, snd tw'))` `is_posedge2 (snd tw') CLK (i + 5 * clk_period)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv by auto
    with `wline_of tw' STATE (i + 5 * clk_period + 1) = V_PROC` show False
      by auto
  qed
  have "wline_of tw' NEXT_COMMON (i + 5 * clk_period) = wline_of tw' COMMON (i + 5 * clk_period + 1)"
    and "wline_of tw' NEXT_ACCUM  (i + 5 * clk_period) = wline_of tw' ACCUM (i + 5 * clk_period + 1)"
    using `Inv_core (i + 5 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 5 * clk_period)` `wline_of tw' RST (i + 5 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  have "bin_of COMMON at_time (i + 5 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 5 * clk_period) on tw'"
  proof -
    have "Inv_core (i + 5 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1))`
      unfolding inv_ncommon_alt_def comp_def snd_conv fst_conv by auto
  qed
  have "(fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 1))"
  proof -
    have typof2: "type_of (wline_of tw' COMMON (i + 5 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs2 where " wline_of tw' COMMON (i + 5 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32"
      using type_of.elims[OF typof2] by fastforce
    have typof: "type_of (wline_of tw' COMMON (i + 6 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs1 where " wline_of tw' COMMON (i + 6 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32"
      using type_of.elims[OF typof] by fastforce
    hence "fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) = Fixed (of_bl bs1 :: (1 + 31) word)"
      using fixed_of_sval.simps by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs1) :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs1)))"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs1"] by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs1 - 1) (bl_to_bin bs1)))"
      using `wline_of tw' COMMON (i + 6 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs1))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs2))"
      using `bin_of COMMON at_time (i + 5 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 5 * clk_period) on tw'`
        `wline_of tw' COMMON (i + 5 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
        `wline_of tw' COMMON (i + 6 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` 
      using \<open>wline_of tw' COMMON (i + 5 * clk_period + 1) = wline_of tw' COMMON (i + 6 * clk_period - 2)\<close> \<open>wline_of tw' NEXT_COMMON (i + 5 * clk_period) = wline_of tw' COMMON (i + 5 * clk_period + 1)\<close> by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs2- 1) (bl_to_bin bs2)))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs2)))"
      using `wline_of tw' COMMON (i + 5 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32` by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs2) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs2"] by auto
    also have "... = Fixed (of_bl bs2 :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 1))"
      using `wline_of tw' COMMON (i + 5 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
      using fixed_of_sval.simps by auto
    finally show ?thesis
      by auto
  qed
  have "wline_of tw' COMMON (i + 5 * clk_period - 2) = wline_of tw' COMMON (i + 5 * clk_period - 1)"
  proof - 
    have "Inv_core (i + 5 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 5 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 4 * clk_period < i + 5 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 5 * clk_period - 2 < i + 6 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 5 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 5 * clk_period - 2)"
      using ** by auto
    thus ?thesis
      using `Inv_core (i + 5 * clk_period - 1, snd tw')`  unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed
  
    \<comment> \<open> obtaining state\<close>
  have "wline_of tw' STATE (i + 4 * clk_period + 1) = wline_of tw' STATE (i + 5 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 4 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 4 * clk_period + 1 \<le> i + 5 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 5 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 4 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 5 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 4 * clk_period = m1 * clk_period"
        using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 5 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 5 * clk_period = m2 * clk_period"
          using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 5 * clk_period - (i + 4 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 4 * clk_period = m1 * clk_period` `i + 5  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 5 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 4 * clk_period + 1 \<le> n" and "n \<le> i + 5 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 4 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 5 * clk_period - 1` `i + 5 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' STATE (i + 4 * clk_period + 1) = wline_of tw' STATE (i + 5 * clk_period - 1)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  hence "wline_of tw' STATE (i + 4 * clk_period + 1) = V_PROC"
    using `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 * clk_period - 1))`
    by auto
  have "wline_of tw' FRAC (i + 4 * clk_period + 1) = wline_of tw' FRAC (i + 5 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 4 * clk_period + 1) = wline_of tw' COUNTER (i + 5 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 4 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 4 * clk_period + 1 \<le> i + 5 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 5 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 4 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 5 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 4 * clk_period = m1 * clk_period"
        using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 5 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 5 * clk_period = m2 * clk_period"
          using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 5 * clk_period - (i + 4 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 4 * clk_period = m1 * clk_period` `i + 5  * clk_period = m2 * clk_period` by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 5 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 4 * clk_period + 1 \<le> n" and "n \<le> i + 5 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 4 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 5 * clk_period - 1` `i + 5 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
  show "wline_of tw' FRAC (i + 4 * clk_period + 1) = wline_of tw' FRAC (i + 5 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 4 * clk_period + 1) = wline_of tw' COUNTER (i + 5 * clk_period - 1)"
    using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d] by auto
  qed
  have "wline_of tw' NEXT_FRAC (i + 4 * clk_period) = wline_of tw' FRAC (i + 4 * clk_period + 1)"
   and "wline_of tw' NEXT_STATE (i + 4 * clk_period) = wline_of tw' STATE (i + 4 * clk_period + 1)"
   and "wline_of tw' NEXT_COUNTER (i + 4 * clk_period) = wline_of tw' COUNTER (i + 4 * clk_period + 1)"
  proof -
    have "Inv_core (i + 4 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto  
    moreover have "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 5 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 5 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 5 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 4 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have "wline_of tw' RST (i + 4 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "wline_of tw' RST (i + 4 * clk_period) \<noteq> Bv False" 
      have "wityping \<Gamma> (snd tw')"
        using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
      hence "type_of (wline_of tw' RST (i + 4 * clk_period)) = Bty"
        unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence "wline_of tw' RST (i + 4 * clk_period) = Bv True"
        using `wline_of tw' RST (i + 4 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 4 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 4 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 4 * clk_period)` unfolding inv_reg_alt_def
        comp_def snd_conv fst_conv  by auto
      with `wline_of tw' STATE (i + 4 * clk_period + 1) = V_PROC` show False
        using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
    qed
    ultimately show "wline_of tw' NEXT_FRAC (i + 4 * clk_period) = wline_of tw' FRAC (i + 4 * clk_period + 1)"
      and "wline_of tw' NEXT_STATE (i + 4 * clk_period) = wline_of tw' STATE (i + 4 * clk_period + 1)"
      and "wline_of tw' NEXT_COUNTER (i + 4 * clk_period) = wline_of tw' COUNTER (i + 4 * clk_period + 1)"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PROC" and "ubin_of NEXT_COUNTER at_time i + 4 * clk_period on tw' = 1"
    using `wline_of tw' STATE (i + 4 * clk_period + 1) = V_PROC`  `ubin_of COUNTER at_time i + 5 * clk_period - 1 on tw' = 1` 
    using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 5 * clk_period - 1))) = 1\<close> \<open>wline_of tw' COUNTER (i + 4 * clk_period + 1) = wline_of tw' COUNTER (i + 5 * clk_period - 1)\<close> \<open>wline_of tw' NEXT_COUNTER (i + 4 * clk_period) = wline_of tw' COUNTER (i + 4 * clk_period + 1)\<close> 
    by auto
  have "wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 4 * clk_period - 1) = V_PRE"
  proof (rule ccontr)
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 4 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 4 * clk_period - 1) = V_PRE)"
    hence *: "(wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<Longrightarrow> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1)))" and 
      **: "wline_of tw' STATE (i + 4 * clk_period - 1) \<noteq> V_PRE" (is "?state \<noteq> _")by auto
    then consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PROC`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') INREADY (i + 4 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PROC`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PROC`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PROC`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 4 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 4 * clk_period) = V_PROC`
        by auto
    qed
  qed
  moreover have "wline_of tw' STATE (i + 4 * clk_period - 1) \<noteq> V_PRE"
  proof (rule ccontr)
    assume "\<not> wline_of tw' STATE (i + 4 * clk_period - 1) \<noteq> V_PRE"
    hence "wline_of tw' STATE (i + 4 * clk_period - 1) = V_PRE"
      by auto
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "bintrunc 3 (bl_to_bin (lval_of (wline_of (i + 4 * clk_period, snd tw') COUNTER (get_time (i + 4 * clk_period, snd tw') - 1))) - 1) = 1"
      using `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PRE` `ubin_of NEXT_COUNTER at_time (i + 4 * clk_period) on tw' = 1`
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
    hence "bintrunc 3 (ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1) = 1"
      unfolding fst_conv comp_def snd_conv by auto
    have "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 5 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 5 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 5 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 4 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 4 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> `is_posedge2 (snd tw') CLK (i + 4 * clk_period)` by blast
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto  
    have fd: "\<And>k. i + 3 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 4 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 3 * clk_period = m1 * clk_period"
        using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 4 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 4 * clk_period = m2 * clk_period"
          using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 4 * clk_period - (i + 3 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 3 * clk_period = m1 * clk_period` `i + 4  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 4 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 3 * clk_period + 1 \<le> n" and "n \<le> i + 4 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 3 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 4 * clk_period - 1` `i + 4 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    have c: "wline_of tw' STATE (i + 3 * clk_period + 1) = V_PRE"
    proof -
      have fa: "fst tw \<le> i + 3 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have fb: "i + 3 * clk_period + 1 \<le> i + 4 * clk_period - 1"
        using assms by (auto simp add: field_simps)
      have fc: "i + 4 * clk_period - 1 \<le> i + 7 * clk_period + 1"
        by auto
      show ?thesis
        using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` fa fb fc fd]
        `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PRE` by auto
    qed
    moreover have b: "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 4 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 4 * clk_period)` 
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv]  by auto
      hence "is_posedge2 w CLK (i + 4 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 3 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have a: "Inv_core (i + 3 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    moreover have d: "wline_of tw' RST (i + 3 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "\<not> wline_of tw' RST (i + 3 * clk_period) = Bv False"
      moreover have "type_of (wline_of tw' RST (i + 3 * clk_period)) = Bty"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      ultimately have "wline_of tw' RST (i + 3 * clk_period) = Bv True"
        using type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 3 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 3 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 3 * clk_period)`
        unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
      with `wline_of tw' STATE (i + 3 * clk_period + 1) = V_PRE`
      show False by auto
    qed
    ultimately have "wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PRE"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    have "Inv_core (i + 3 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nstate (i + 3 * clk_period, snd tw')"
      by auto
    have "wline_of tw' STATE (i + 3 * clk_period - 1) = V_WAIT"
    proof (rule ccontr)
      assume "\<not> wline_of tw' STATE (i + 3 * clk_period - 1) = V_WAIT" (is "\<not> ?state = V_WAIT")
      then consider "?state = V_INIT" | "?state = V_PRE" | "?state = V_PROC" | "?state = V_POST" 
        | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
        by auto
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) \<noteq> V_PRE"
      proof (cases)
        case 1
        then show ?thesis 
          using `inv_nstate (i + 3 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 2
        then show ?thesis 
          using `inv_nstate (i + 3 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 3
        then show ?thesis 
          using `inv_nstate (i + 3 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          apply (cases "bval_of (wline_of (i + 3 * clk_period, snd tw') CTR_NEQ_0 (get_time (i + 3 * clk_period, snd tw') - 1))")
          by auto
      next
        case 4
        then show ?thesis 
          using `inv_nstate (i + 3 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 5
        then show ?thesis 
          using `inv_nstate (i + 3 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by (auto)
      qed
      thus False
        using \<open>wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PRE\<close> by blast
    qed
    moreover have "bval_of (wline_of tw' INREADY (i + 3 * clk_period - 1))"
    proof (rule ccontr)
      assume "\<not> bval_of (wline_of tw' INREADY (i + 3 * clk_period - 1))"
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_WAIT"
        using `Inv_core (i + 3 * clk_period, snd tw')` `wline_of tw' STATE (i + 3 * clk_period - 1) = V_WAIT`
        unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      thus False
        using `wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PRE` by auto
    qed
    ultimately have "ubin_of NEXT_COUNTER at_time i + 3 * clk_period on tw' = 4"
      using `Inv_core (i + 3 * clk_period, snd tw')` 
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
    hence "ubin_of COUNTER at_time i + 3 * clk_period + 1 on tw' = 4"
      using a b d unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    hence "ubin_of COUNTER at_time i + 4 * clk_period - 1 on tw' = 4"
    proof -
      have *: "get_time tw \<le> i + 3 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have **: "i + 3 * clk_period + 1 \<le> i + 4 * clk_period - 1"
        using assms by auto
      have "wline_of tw' COUNTER (i + 3 * clk_period + 1) = wline_of tw' COUNTER (i + 4 * clk_period - 1)"
        using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` * ** _ fd]
        using assms by (auto)
      thus ?thesis
        using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 3 * clk_period + 1))) = 4\<close> by auto
    qed        
    with `bintrunc 3 (ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1) = 1`
    show False
      by auto
  qed
  ultimately have "wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1))"
    by auto  


  \<comment> \<open>obtaining counter value\<close>
  have "bintrunc 3 (ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1) = 1"
  proof -
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      using `ubin_of NEXT_COUNTER at_time (i + 4 * clk_period) on tw' = 1`
      `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1))`
      unfolding inv_ncounter_alt_def fst_conv comp_def snd_conv by auto
  qed
  hence "(ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1) mod 8 = 1" 
    unfolding bintrunc_mod2p by auto
  have "0 < ubin_of COUNTER at_time i + 4 * clk_period - 2 on tw'"
  proof -
    have "Inv_core (i + 4 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    hence "inv_n0 (i + 4 * clk_period - 1, snd tw')"
      by auto
    hence "0 < bl_to_bin (lval_of (snd (snd tw') COUNTER (i + 4 * clk_period - 1 - 1)))"
      using `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1))`
      unfolding inv_n0_def comp_def snd_conv fst_conv by auto
    thus ?thesis
      unfolding comp_def snd_conv fst_conv
      by (metis diff_diff_left nat_1_add_1)
  qed
  moreover have "ubin_of COUNTER at_time i + 4 * clk_period - 2 on tw' = ubin_of COUNTER at_time i + 4 * clk_period - 1 on tw'"
  proof -
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 4 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 3 * clk_period < i + 4 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 4 * clk_period - 2 < i + 4 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 4 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 4 * clk_period - 2)"
      using ** by auto
    moreover have "Inv_core (i + 4 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    ultimately show ?thesis
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed
  ultimately have "0 < ubin_of COUNTER at_time i + 4 * clk_period - 1 on tw'"
    by auto
  moreover have "ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' \<le> 7"
    using ubin_counter_atmost[OF `wityping \<Gamma> (snd tw')`] by auto
  ultimately have "(ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1) mod 8 = ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1"
    by (auto intro!: int_mod_eq')
  hence "ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' = 2"  
    using `(ubin_of COUNTER at_time (i + 4 * clk_period - 1) on tw' - 1) mod 8 = 1` by auto

  \<comment> \<open> obtaining frac\<close>
  have "bin_of NEXT_FRAC at_time (i + 4 * clk_period) on tw' = approx_fourth"
  proof -
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nfrac (i + 4 * clk_period, snd tw')"
      by auto
    thus ?thesis
      using `ubin_of COUNTER at_time i + 4 * clk_period - 1 on tw' = 2`
      unfolding inv_nfrac_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of FRAC at_time (i + 5 * clk_period - 1) on tw' = approx_fourth"
    using \<open>wline_of tw' FRAC (i + 4 * clk_period + 1) = wline_of tw' FRAC (i + 5 * clk_period - 1)\<close>
    \<open>wline_of tw' NEXT_FRAC (i + 4 * clk_period) = wline_of tw' FRAC (i + 4 * clk_period + 1)\<close> by
    auto

  have "bin_of TERM1 at_time (i + 5 * clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 5 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 * clk_period - 2) on tw')"
  proof -
    have "Inv_core (i + 5 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      unfolding inv_term1_def comp_def snd_conv fst_conv  by (metis diff_diff_left one_add_one)
  qed

  have "Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_fourth) :: (1 + 31) word)"
    using `bin_of FRAC at_time i + 5 * clk_period - 1 on tw' = approx_fourth` by auto
  have "((word_of_int approx_fourth) :: (1 + 31) word) = (approx_fourth :: (1 + 31) word)"
    unfolding word_uint.inverse_norm by eval
  hence "Fixed ((word_of_int approx_fourth) :: (1 + 31) word) = Fixed (approx_fourth :: (1 + 31) word)"
    by auto
  also have "... = approx_div_fact 2"
    by (simp add: numeral_2_eq_2)
  finally have "Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) = approx_div_fact 2"
    using `Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_fourth) :: (1 + 31) word)`
    by auto
  moreover have "Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) = (fixed_of_sval (wline_of tw' FRAC (i + 5 * clk_period - 1)) :: (1,31) fixed)"
  proof -
    have "type_of (wline_of tw' FRAC (i + 5 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' FRAC (i + 5 * clk_period - 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' FRAC (i + 5 * clk_period - 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' FRAC (i + 5 * clk_period - 1)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' FRAC (i + 5 * clk_period - 1))"
    proof -
      have "wline_of tw' FRAC (i + 5 * clk_period - 1) = Lv Sig (lval_of (wline_of tw' FRAC (i + 5 * clk_period - 1)))"
        using `type_of (wline_of tw' FRAC (i + 5 *clk_period - 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  ultimately have "(fixed_of_sval (wline_of tw' FRAC (i + 5 * clk_period - 1)) :: (1,31) fixed) = approx_div_fact 2"
    by auto

  \<comment> \<open> obtaining accum\<close>
  have  "bin_of NEXT_ACCUM at_time (i + 5 * clk_period) on tw' = 
            sbintrunc 31 (bin_of FRAC at_time i + 5 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})))"
  proof -
    have "Inv_core (i + 5 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 5 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 5 *clk_period - 1))`
      unfolding inv_naccum_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of ACCUM at_time (i + 5 * clk_period + 1) on tw' = 
        sbintrunc 31 (bin_of FRAC at_time i + 5 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})))"
    using `wline_of tw' NEXT_ACCUM  (i + 5 * clk_period) = wline_of tw' ACCUM (i + 5* clk_period + 1)` 
    by auto
  hence "(word_of_int (bin_of ACCUM at_time i + 5 * clk_period + 1 on tw') :: (1 + 31) word) =  word_of_int (sbintrunc 31 (bin_of FRAC at_time i + 5 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (sbintrunc (LENGTH((1 + 31)) - 1) (bin_of FRAC at_time i + 5 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})))"
    unfolding word_sbin.Abs_norm by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32}))"
    unfolding wi_hom_syms(1) by auto
  finally have "(word_of_int (bin_of ACCUM at_time i + 5 * clk_period + 1 on tw') :: (1 + 31) word) = 
                 word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32}))"
    by auto
  hence "Fixed (word_of_int (bin_of ACCUM at_time i + 5 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})))"
    unfolding plus_fixed.abs_eq by auto
  have "Fixed (word_of_int (bin_of ACCUM at_time i + 5 * clk_period + 1 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period + 1))"
    (is "?lhs3 = ?rhs3")
  proof -
    have "type_of (wline_of tw' ACCUM (i + 5 * clk_period + 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 5 * clk_period + 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "?lhs3 = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period + 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period + 1)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period + 1))"
    proof -
      have "wline_of tw' ACCUM (i + 5 * clk_period + 1) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 5 * clk_period + 1)))"
        using `type_of (wline_of tw' ACCUM (i + 5 * clk_period + 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed

  have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
        word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31)"
  proof -
    have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)= 
          word_of_int
     (sbintrunc (length (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32}) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32})))"
      unfolding sbl_to_bin_alt_def by auto
    moreover have "(length (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32}) - 1) = 31"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "card {1::nat ..32} = 32"
        unfolding card_atLeastAtMost by auto 
      show ?thesis
        unfolding length_nths * 
        using card_slice[where len="64" and l=62 and r="31"] by auto
    qed
    ultimately have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                     word_of_int (sbintrunc 31 (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = (word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32})) :: (1 + 31) word) "
      unfolding word_sbin.Abs_norm by auto
    finally have "word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1+31) word)"
      by auto

    have interval: "{1 :: nat .. 32} = {1 :: nat ..< 33}"
      by auto
    have nths: "\<And>xs:: bool list. nths xs {1 :: nat .. 32} = drop 1 (take 33 xs)"
      unfolding interval  nths_from_upt_eq_drop_take[where m="1" and n="33"] by auto
    have " bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1 ..32}) = 
           bl_to_bin (drop 1 (take 33 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
      using nths[of "(lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))"] by auto
    also have "... = bintrunc (length (take 33 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))) - 1) (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
      unfolding bl2bin_drop by auto
    also have "... = bintrunc 32 (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence " length (take 33 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))) = 33"
        unfolding length_take by auto
      thus ?thesis
        by auto
    qed
    also have "... = bintrunc 32 (bl_to_bin (take (length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) - 31)  (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        by auto
    qed
    also have "... =  bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
      unfolding take_rest_bl2bin  by auto
    finally have "bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1 ..32}) = 
                      bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
      by auto


    have "(word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1 ..32})) :: (1+31) word)= 
           word_of_int (bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))"
      using \<open>bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) {1..32}) = bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))\<close> by auto
    \<comment> \<open>push bintrunc 32 inside\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (bintrunc 63 (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))"
      using bin_rest_power_trunc[where n="63" and k="31", symmetric] by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using bl2bin_drop by auto
    qed
    \<comment> \<open>pull bl_to_bin to left\<close>
    also have "... =  word_of_int (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))"
      unfolding butlast_pow_rest_bl2bin[symmetric] by auto
    \<comment> \<open>change to sbl_to_bin\<close>
    also have "... = (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... =  word_of_int (sbl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))) = 32"
        unfolding butlast_power length_take length_drop * by eval
      hence "(word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))) :: (1 + 31) word) = 
            (word_of_int (sbintrunc (length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))) :: (1 + 31) word)"
        by auto
      thus ?thesis
        using sbl_to_bin_alt_def by auto
    qed
    \<comment> \<open>push sbl_to_bin back to right\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (sbl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))" 
    proof -
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))) = 63"
        unfolding length_take length_drop * by eval
      hence **: "31 < length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)))))"
        by auto
      show ?thesis
        unfolding butlast_pow_rest_sbl2bin[OF **] by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (sbl_to_bin (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 5 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 5 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using sbl2bin_drop by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (bin_of COMMON at_time (i + 5 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 * clk_period - 2) on tw')))"
      using `bin_of TERM1 at_time (i + 5 *clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 5 *clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 *clk_period - 2) on tw')` 
      by auto
    also have "... =  word_of_int (sbintrunc 31 ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 5 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 * clk_period - 2) on tw')))"
    proof -
      have "(31 :: nat) \<le> 62" by auto
      show ?thesis
        unfolding bin_rest_power_strunc[OF `31 \<le> 62`]
        by auto
    qed
    also have "... =  word_of_int (sbintrunc (LENGTH(1 + 31) - 1) ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 5 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 * clk_period - 2) on tw')))"
      by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 5 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 * clk_period - 2) on tw'))"
      unfolding word_sbin.Abs_norm by auto
    also have "... = word_of_int ((bin_of COMMON at_time (i + 5 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 5 * clk_period - 2) on tw') div 2 ^ 31)"
      unfolding bin_rest_compow by auto
    also have "... = word_of_int (sbintrunc (length (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))) * 
                                  sbintrunc (length (lval_of (wline_of tw' ACCUM  (i + 5 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))) div 2 ^ 31)"
      using sbl_to_bin_alt_def2 by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))) * 
                                  sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))) div 2 ^ 31)"
    proof - 
      have "type_of (wline_of tw' COMMON (i + 5 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "type_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence **: "length (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      with * show ?thesis
        by auto
    qed
    also have "... = word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))) :: (1 + 31) word) * 
                                  sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))) :: (1 + 31) word ) div 2 ^ 31)"
      unfolding sint_sbintrunc' by auto
    finally show ?thesis
      unfolding `(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)`
      by auto
  qed
  hence "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
         Fixed (word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31))"
    by auto
  also have "... = Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2))))) * Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))))"
    using times_fixed.abs_eq[where xa="word_of_int (bin_of COMMON at_time i + 5 * clk_period - 2 on tw') :: (1 + 31) word" and 
                                    x="word_of_int (bin_of ACCUM at_time i + 5 * clk_period - 2 on tw') :: (1 + 31) word", symmetric]
    by auto
  also have "... = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))"
  proof -
    have "type_of (wline_of tw' COMMON (i + 5 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of COMMON at_time i + 5 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2))"
    proof -
      have "wline_of tw' COMMON (i + 5 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2)))"
        using `type_of (wline_of tw' COMMON (i + 5 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of COMMON at_time i + 5 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2))"
      by auto

    have "type_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of ACCUM at_time i + 5 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))"
    proof -
      have "wline_of tw' ACCUM (i + 5 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 5 * clk_period - 2)))"
        using `type_of (wline_of tw' ACCUM (i + 5 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of ACCUM at_time i + 5 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))"
      by auto
    thus ?thesis
      using \<open>Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 5 * clk_period - 2))))) = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2))\<close> by auto
  qed  
  finally have "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))"
    by auto  
  hence "fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period + 1)) = 
          approx_div_fact 2 + fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))"
    using `?lhs3 = ?rhs3`
        `Fixed (word_of_int (bin_of ACCUM at_time i + 5 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 5 * clk_period - 1)) {1 .. 32})))`
        `Fixed (word_of_int (bin_of FRAC at_time i + 5 * clk_period - 1 on tw')) = approx_div_fact 2`
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))))"
    using `fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 6 * clk_period - 2)))`
        `wline_of tw' COMMON (i + 5 * clk_period - 2) = wline_of tw' COMMON (i + 5 * clk_period - 1)`
        `(fixed_of_sval (wline_of tw' COMMON (i + 6 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 1))`
        `wline_of tw' ACCUM  (i + 5 * clk_period + 1) = wline_of tw' ACCUM (i + 6 * clk_period - 2)`
    by auto

  \<comment> \<open> obtaining common and accum\<close>
  have "wline_of tw' COMMON (i + 4 * clk_period + 1) = wline_of tw' COMMON (i + 5 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 4 * clk_period + 1) = wline_of tw' ACCUM (i + 5 * clk_period - 2)"
  proof -
    have a: "fst tw \<le> i + 4 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 4 * clk_period + 1 \<le> i + 5 * clk_period - 2"
      using assms by (auto simp add: field_simps)
    have c: "i + 5 * clk_period - 2 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 5 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 4 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 5 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 4 * clk_period = m1 * clk_period"
        using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 5 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 5 * clk_period = m2 * clk_period"
          using `(i + 5 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 6 * clk_period - (i + 5 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 4 * clk_period = m1 * clk_period` `i + 5  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 5 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 4 * clk_period + 1 \<le> n" and "n \<le> i + 5 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 4 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 5 * clk_period - 1` `i + 5 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' COMMON (i + 4 * clk_period + 1) = wline_of tw' COMMON (i + 5 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 4 * clk_period + 1) = wline_of tw' ACCUM (i + 5 * clk_period - 2)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  have "Inv_core (i + 4 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
    by auto
  have "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 6 * clk_period)"
      using `is_posedge2 (snd tw') CLK (i + 6 * clk_period)` 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 5 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 4 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 4 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  have "wline_of tw' RST (i + 4 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 4 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
      using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 4 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 4 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 4 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' STATE (i + 4 * clk_period + 1) = V_INIT"
      using  `Inv_core ((i + 4 * clk_period + 1, snd tw'))` `is_posedge2 (snd tw') CLK (i + 4 * clk_period)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv by auto
    with `wline_of tw' STATE (i + 4 * clk_period + 1) = V_PROC` show False
      by auto
  qed
  have "wline_of tw' NEXT_COMMON (i + 4 * clk_period) = wline_of tw' COMMON (i + 4 * clk_period + 1)"
    and "wline_of tw' NEXT_ACCUM  (i + 4 * clk_period) = wline_of tw' ACCUM (i + 4 * clk_period + 1)"
    using `Inv_core (i + 4 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 4 * clk_period)` `wline_of tw' RST (i + 4 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  have "bin_of COMMON at_time (i + 4 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 4 * clk_period) on tw'"
  proof -
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1))`
      unfolding inv_ncommon_alt_def comp_def snd_conv fst_conv by auto
  qed
  have "(fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 1))"
  proof -
    have typof2: "type_of (wline_of tw' COMMON (i + 4 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs2 where " wline_of tw' COMMON (i + 4 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32"
      using type_of.elims[OF typof2] by fastforce
    have typof: "type_of (wline_of tw' COMMON (i + 5 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs1 where " wline_of tw' COMMON (i + 5 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32"
      using type_of.elims[OF typof] by fastforce
    hence "fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) = Fixed (of_bl bs1 :: (1 + 31) word)"
      using fixed_of_sval.simps by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs1) :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs1)))"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs1"] by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs1 - 1) (bl_to_bin bs1)))"
      using `wline_of tw' COMMON (i + 5 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs1))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs2))"
      using `bin_of COMMON at_time (i + 4 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 4 * clk_period) on tw'`
        `wline_of tw' COMMON (i + 4 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
        `wline_of tw' COMMON (i + 5 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` 
      using \<open>wline_of tw' COMMON (i + 4 * clk_period + 1) = wline_of tw' COMMON (i + 5 * clk_period - 2)\<close> \<open>wline_of tw' NEXT_COMMON (i + 4 * clk_period) = wline_of tw' COMMON (i + 4 * clk_period + 1)\<close> by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs2- 1) (bl_to_bin bs2)))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs2)))"
      using `wline_of tw' COMMON (i + 4 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32` by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs2) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs2"] by auto
    also have "... = Fixed (of_bl bs2 :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 1))"
      using `wline_of tw' COMMON (i + 4 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
      using fixed_of_sval.simps by auto
    finally show ?thesis
      by auto
  qed
  have "wline_of tw' COMMON (i + 4 * clk_period - 2) = wline_of tw' COMMON (i + 4 * clk_period - 1)"
  proof - 
    have "Inv_core (i + 4 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 4 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 3 * clk_period < i + 4 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 4 * clk_period - 2 < i + 6 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 4 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 4 * clk_period - 2)"
      using ** by auto
    thus ?thesis
      using `Inv_core (i + 4 * clk_period - 1, snd tw')`  unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed

  \<comment> \<open> obtaining state\<close>
  have "wline_of tw' STATE (i + 3 * clk_period + 1) = wline_of tw' STATE (i + 4 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 3 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 3 * clk_period + 1 \<le> i + 4 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 4 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 3 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 4 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 3 * clk_period = m1 * clk_period"
        using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 4 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 4 * clk_period = m2 * clk_period"
          using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 4 * clk_period - (i + 3 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 3 * clk_period = m1 * clk_period` `i + 4  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 4 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 3 * clk_period + 1 \<le> n" and "n \<le> i + 4 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 3 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 4 * clk_period - 1` `i + 4 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' STATE (i + 3 * clk_period + 1) = wline_of tw' STATE (i + 4 * clk_period - 1)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  hence "wline_of tw' STATE (i + 3 * clk_period + 1) = V_PROC"
    using `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 * clk_period - 1))`
    by auto
  have "wline_of tw' FRAC (i + 3 * clk_period + 1) = wline_of tw' FRAC (i + 4 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 3 * clk_period + 1) = wline_of tw' COUNTER (i + 4 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 3 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 3 * clk_period + 1 \<le> i + 4 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 4 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 3 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 4 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 3 * clk_period = m1 * clk_period"
        using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 4 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 4 * clk_period = m2 * clk_period"
          using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 4 * clk_period - (i + 3 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 3 * clk_period = m1 * clk_period` `i + 4  * clk_period = m2 * clk_period` by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 4 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 3 * clk_period + 1 \<le> n" and "n \<le> i + 4 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 3 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 4 * clk_period - 1` `i + 4 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
  show "wline_of tw' FRAC (i + 3 * clk_period + 1) = wline_of tw' FRAC (i + 4 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 3 * clk_period + 1) = wline_of tw' COUNTER (i + 4 * clk_period - 1)"
    using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d] by auto
  qed
  have "wline_of tw' NEXT_FRAC (i + 3 * clk_period) = wline_of tw' FRAC (i + 3 * clk_period + 1)"
   and "wline_of tw' NEXT_STATE (i + 3 * clk_period) = wline_of tw' STATE (i + 3 * clk_period + 1)"
   and "wline_of tw' NEXT_COUNTER (i + 3 * clk_period) = wline_of tw' COUNTER (i + 3 * clk_period + 1)"
  proof -
    have "Inv_core (i + 3 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto  
    moreover have "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 4 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 4 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 4 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 3 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have "wline_of tw' RST (i + 3 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "wline_of tw' RST (i + 3 * clk_period) \<noteq> Bv False" 
      have "wityping \<Gamma> (snd tw')"
        using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
      hence "type_of (wline_of tw' RST (i + 3 * clk_period)) = Bty"
        unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence "wline_of tw' RST (i + 3 * clk_period) = Bv True"
        using `wline_of tw' RST (i + 3 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 3 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 3 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` unfolding inv_reg_alt_def
        comp_def snd_conv fst_conv  by auto
      with `wline_of tw' STATE (i + 3 * clk_period + 1) = V_PROC` show False
        using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
    qed
    ultimately show "wline_of tw' NEXT_FRAC (i + 3 * clk_period) = wline_of tw' FRAC (i + 3 * clk_period + 1)"
      and "wline_of tw' NEXT_STATE (i + 3 * clk_period) = wline_of tw' STATE (i + 3 * clk_period + 1)"
      and "wline_of tw' NEXT_COUNTER (i + 3 * clk_period) = wline_of tw' COUNTER (i + 3 * clk_period + 1)"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PROC" and "ubin_of NEXT_COUNTER at_time i + 3 * clk_period on tw' = 2"
    using `wline_of tw' STATE (i + 3 * clk_period + 1) = V_PROC`  `ubin_of COUNTER at_time i + 4 *clk_period - 1 on tw' = 2` 
    using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 4 *clk_period - 1))) = 2\<close> \<open>wline_of tw' COUNTER (i + 3 * clk_period + 1) = wline_of tw' COUNTER (i + 4 *clk_period - 1)\<close> \<open>wline_of tw' NEXT_COUNTER (i + 3 * clk_period) = wline_of tw' COUNTER (i + 3 * clk_period + 1)\<close> 
    by auto
  have "wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 3 * clk_period - 1) = V_PRE"
  proof (rule ccontr)
    have "Inv_core (i + 3 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 3 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 3 * clk_period - 1) = V_PRE)"
    hence *: "(wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<Longrightarrow> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1)))" and 
      **: "wline_of tw' STATE (i + 3 * clk_period - 1) \<noteq> V_PRE" (is "?state \<noteq> _")by auto
    then consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PROC`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') INREADY (i + 3 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PROC`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PROC`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PROC`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 3 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 3 * clk_period) = V_PROC`
        by auto
    qed
  qed
  moreover have "wline_of tw' STATE (i + 3 * clk_period - 1) \<noteq> V_PRE"
  proof (rule ccontr)
    assume "\<not> wline_of tw' STATE (i + 3 * clk_period - 1) \<noteq> V_PRE"
    hence "wline_of tw' STATE (i + 3 * clk_period - 1) = V_PRE"
      by auto
    have "Inv_core (i + 3 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "bintrunc 3 (bl_to_bin (lval_of (wline_of (i + 3 * clk_period, snd tw') COUNTER (get_time (i + 3 * clk_period, snd tw') - 1))) - 1) = 2"
      using `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PRE` `ubin_of NEXT_COUNTER at_time (i + 3 * clk_period) on tw' = 2`
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
    hence "bintrunc 3 (ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1) = 2"
      unfolding fst_conv comp_def snd_conv by auto
    have "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 4 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 4 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 4 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 3 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 3 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` by blast
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto  
    have fd: "\<And>k. i + 2 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 3 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 2 * clk_period = m1 * clk_period"
        using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 3 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 3 * clk_period = m2 * clk_period"
          using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 3 * clk_period - (i + 2 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 2 * clk_period = m1 * clk_period` `i + 3  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 3 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 2 * clk_period + 1 \<le> n" and "n \<le> i + 3 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 2 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 3 * clk_period - 1` `i + 3 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    have c: "wline_of tw' STATE (i + 2 * clk_period + 1) = V_PRE"
    proof -
      have fa: "fst tw \<le> i + 2 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have fb: "i + 2 * clk_period + 1 \<le> i + 3 * clk_period - 1"
        using assms by (auto simp add: field_simps)
      have fc: "i + 3 * clk_period - 1 \<le> i + 7 * clk_period + 1"
        by auto
      show ?thesis
        using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` fa fb fc fd]
        `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PRE` by auto
    qed
    moreover have b: "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 3 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` 
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv]  by auto
      hence "is_posedge2 w CLK (i + 3 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 2 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have a: "Inv_core (i + 2 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    moreover have d: "wline_of tw' RST (i + 2 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "\<not> wline_of tw' RST (i + 2 * clk_period) = Bv False"
      moreover have "type_of (wline_of tw' RST (i + 2 * clk_period)) = Bty"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      ultimately have "wline_of tw' RST (i + 2 * clk_period) = Bv True"
        using type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 2 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 2 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 2 * clk_period)`
        unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
      with `wline_of tw' STATE (i + 2 * clk_period + 1) = V_PRE`
      show False by auto
    qed
    ultimately have "wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PRE"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    have "Inv_core (i + 2 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nstate (i + 2 * clk_period, snd tw')"
      by auto
    have "wline_of tw' STATE (i + 2 * clk_period - 1) = V_WAIT"
    proof (rule ccontr)
      assume "\<not> wline_of tw' STATE (i + 2 * clk_period - 1) = V_WAIT" (is "\<not> ?state = V_WAIT")
      then consider "?state = V_INIT" | "?state = V_PRE" | "?state = V_PROC" | "?state = V_POST" 
        | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
        by auto
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) \<noteq> V_PRE"
      proof (cases)
        case 1
        then show ?thesis 
          using `inv_nstate (i + 2 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 2
        then show ?thesis 
          using `inv_nstate (i + 2 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 3
        then show ?thesis 
          using `inv_nstate (i + 2 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          apply (cases "bval_of (wline_of (i + 2 * clk_period, snd tw') CTR_NEQ_0 (get_time (i + 2 * clk_period, snd tw') - 1))")
          by auto
      next
        case 4
        then show ?thesis 
          using `inv_nstate (i + 2 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by auto
      next
        case 5
        then show ?thesis 
          using `inv_nstate (i + 2 * clk_period, snd tw')` unfolding inv_nstate_alt_def 
          by (auto)
      qed
      thus False
        using \<open>wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PRE\<close> by blast
    qed
    moreover have "bval_of (wline_of tw' INREADY (i + 2 * clk_period - 1))"
    proof (rule ccontr)
      assume "\<not> bval_of (wline_of tw' INREADY (i + 2 * clk_period - 1))"
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_WAIT"
        using `Inv_core (i + 2 * clk_period, snd tw')` `wline_of tw' STATE (i + 2 * clk_period - 1) = V_WAIT`
        unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      thus False
        using `wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PRE` by auto
    qed
    ultimately have "ubin_of NEXT_COUNTER at_time i + 2 * clk_period on tw' = 4"
      using `Inv_core (i + 2 * clk_period, snd tw')` 
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
    hence "ubin_of COUNTER at_time i + 2 * clk_period + 1 on tw' = 4"
      using a b d unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    hence "ubin_of COUNTER at_time i + 3 * clk_period - 1 on tw' = 4"
    proof -
      have *: "get_time tw \<le> i + 2 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have **: "i + 2 * clk_period + 1 \<le> i + 3 * clk_period - 1"
        using assms by auto
      have "wline_of tw' COUNTER (i + 2 * clk_period + 1) = wline_of tw' COUNTER (i + 3 * clk_period - 1)"
        using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` * ** _ fd]
        using assms by (auto)
      thus ?thesis
        using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 2 * clk_period + 1))) = 4\<close> by auto
    qed        
    with `bintrunc 3 (ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1) = 2`
    show False
      by auto
  qed
  ultimately have "wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1))"
    by auto

  \<comment> \<open>obtaining counter value\<close>
  have "bintrunc 3 (ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1) = 2"
  proof -
    have "Inv_core (i + 3 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      using `ubin_of NEXT_COUNTER at_time (i + 3 * clk_period) on tw' = 2`
      `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1))`
      unfolding inv_ncounter_alt_def fst_conv comp_def snd_conv by auto
  qed
  hence "(ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1) mod 8 = 2" 
    unfolding bintrunc_mod2p by auto
  have "0 < ubin_of COUNTER at_time i + 3 * clk_period - 2 on tw'"
  proof -
    have "Inv_core (i + 3 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    hence "inv_n0 (i + 3 * clk_period - 1, snd tw')"
      by auto
    hence "0 < bl_to_bin (lval_of (snd (snd tw') COUNTER (i + 3 * clk_period - 1 - 1)))"
      using `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1))`
      unfolding inv_n0_def comp_def snd_conv fst_conv by auto
    thus ?thesis
      unfolding comp_def snd_conv fst_conv
      by (metis diff_diff_left nat_1_add_1)
  qed
  moreover have "ubin_of COUNTER at_time i + 3 * clk_period - 2 on tw' = ubin_of COUNTER at_time i + 3 * clk_period - 1 on tw'"
  proof -
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 3 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 2 * clk_period < i + 3 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 2 * clk_period - 2 < i + 3 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 3 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 3 * clk_period - 2)"
      using ** by auto
    moreover have "Inv_core (i + 3 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    ultimately show ?thesis
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed
  ultimately have "0 < ubin_of COUNTER at_time i + 3 * clk_period - 1 on tw'"
    by auto
  moreover have "ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' \<le> 7"
    using ubin_counter_atmost[OF `wityping \<Gamma> (snd tw')`] by auto
  ultimately have "(ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1) mod 8 = ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1"
    by (auto intro!: int_mod_eq')
  hence "ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' = 3"  
    using `(ubin_of COUNTER at_time (i + 3 * clk_period - 1) on tw' - 1) mod 8 = 2` by auto

  \<comment> \<open> obtaining frac\<close>
  have "bin_of NEXT_FRAC at_time (i + 3 *clk_period) on tw' = approx_sixth"
  proof -
    have "Inv_core (i + 3 *clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nfrac (i + 3 *clk_period, snd tw')"
      by auto
    thus ?thesis
      using `ubin_of COUNTER at_time i + 3 *clk_period - 1 on tw' = 3`
      unfolding inv_nfrac_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of FRAC at_time (i + 4 * clk_period - 1) on tw' = approx_sixth"
    using \<open>wline_of tw' FRAC (i + 3 * clk_period + 1) = wline_of tw' FRAC (i + 4 * clk_period - 1)\<close>
    \<open>wline_of tw' NEXT_FRAC (i + 3 * clk_period) = wline_of tw' FRAC (i + 3 * clk_period + 1)\<close> by
    auto

  have "bin_of TERM1 at_time (i + 4 * clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 4 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 * clk_period - 2) on tw')"
  proof -
    have "Inv_core (i + 4 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      unfolding inv_term1_def comp_def snd_conv fst_conv  by (metis diff_diff_left one_add_one)
  qed

  have "Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_sixth) :: (1 + 31) word)"
    using `bin_of FRAC at_time i + 4 * clk_period - 1 on tw' = approx_sixth` by auto
  have "((word_of_int approx_sixth) :: (1 + 31) word) = (approx_sixth :: (1 + 31) word)"
    unfolding word_uint.inverse_norm by eval
  hence "Fixed ((word_of_int approx_sixth) :: (1 + 31) word) = Fixed (approx_sixth :: (1 + 31) word)"
    by auto
  also have "... = approx_div_fact 3"
    by (simp add: numeral_3_eq_3)
  finally have "Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) = approx_div_fact 3"
    using `Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_sixth) :: (1 + 31) word)`
    by auto
  moreover have "Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) = (fixed_of_sval (wline_of tw' FRAC (i + 4 * clk_period - 1)) :: (1,31) fixed)"
  proof -
    have "type_of (wline_of tw' FRAC (i + 4 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' FRAC (i + 4 * clk_period - 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' FRAC (i + 4 * clk_period - 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' FRAC (i + 4 * clk_period - 1)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' FRAC (i + 4 * clk_period - 1))"
    proof -
      have "wline_of tw' FRAC (i + 4 * clk_period - 1) = Lv Sig (lval_of (wline_of tw' FRAC (i + 4 * clk_period - 1)))"
        using `type_of (wline_of tw' FRAC (i + 4 *clk_period - 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  ultimately have "(fixed_of_sval (wline_of tw' FRAC (i + 4 * clk_period - 1)) :: (1,31) fixed) = approx_div_fact 3"
    by auto

  \<comment> \<open> obtaining accum\<close>
  have  "bin_of NEXT_ACCUM at_time (i + 4 * clk_period) on tw' = 
            sbintrunc 31 (bin_of FRAC at_time i + 4 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})))"
  proof -
    have "Inv_core (i + 4 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 4 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 4 *clk_period - 1))`
      unfolding inv_naccum_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of ACCUM at_time (i + 4 * clk_period + 1) on tw' = 
        sbintrunc 31 (bin_of FRAC at_time i + 4 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})))"
    using `wline_of tw' NEXT_ACCUM  (i + 4 * clk_period) = wline_of tw' ACCUM (i + 4 * clk_period + 1)` 
    by auto
  hence "(word_of_int (bin_of ACCUM at_time i + 4 * clk_period + 1 on tw') :: (1 + 31) word) =  word_of_int (sbintrunc 31 (bin_of FRAC at_time i + 4 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (sbintrunc (LENGTH((1 + 31)) - 1) (bin_of FRAC at_time i + 4 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})))"
    unfolding word_sbin.Abs_norm by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32}))"
    unfolding wi_hom_syms(1) by auto
  finally have "(word_of_int (bin_of ACCUM at_time i + 4 * clk_period + 1 on tw') :: (1 + 31) word) = 
                 word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32}))"
    by auto
  hence "Fixed (word_of_int (bin_of ACCUM at_time i + 4 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})))"
    unfolding plus_fixed.abs_eq by auto
  have "Fixed (word_of_int (bin_of ACCUM at_time i + 4 * clk_period + 1 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period + 1))"
    (is "?lhs4 = ?rhs4")
  proof -
    have "type_of (wline_of tw' ACCUM (i + 4 * clk_period + 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 4 * clk_period + 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "?lhs4 = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period + 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period + 1)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period + 1))"
    proof -
      have "wline_of tw' ACCUM (i + 4 * clk_period + 1) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 4 * clk_period + 1)))"
        using `type_of (wline_of tw' ACCUM (i + 4 * clk_period + 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed

  have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
        word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31)"
  proof -
    have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)= 
          word_of_int
     (sbintrunc (length (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32}) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32})))"
      unfolding sbl_to_bin_alt_def by auto
    moreover have "(length (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32}) - 1) = 31"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "card {1::nat ..32} = 32"
        unfolding card_atLeastAtMost by auto 
      show ?thesis
        unfolding length_nths * 
        using card_slice[where len="64" and l=62 and r="31"] by auto
    qed
    ultimately have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                     word_of_int (sbintrunc 31 (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = (word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32})) :: (1 + 31) word) "
      unfolding word_sbin.Abs_norm by auto
    finally have "word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1+31) word)"
      by auto

    have interval: "{1 :: nat .. 32} = {1 :: nat ..< 33}"
      by auto
    have nths: "\<And>xs:: bool list. nths xs {1 :: nat .. 32} = drop 1 (take 33 xs)"
      unfolding interval  nths_from_upt_eq_drop_take[where m="1" and n="33"] by auto
    have " bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1 ..32}) = 
           bl_to_bin (drop 1 (take 33 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
      using nths[of "(lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))"] by auto
    also have "... = bintrunc (length (take 33 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))) - 1) (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
      unfolding bl2bin_drop by auto
    also have "... = bintrunc 32 (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence " length (take 33 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))) = 33"
        unfolding length_take by auto
      thus ?thesis
        by auto
    qed
    also have "... = bintrunc 32 (bl_to_bin (take (length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) - 31)  (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        by auto
    qed
    also have "... =  bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
      unfolding take_rest_bl2bin  by auto
    finally have "bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1 ..32}) = 
                      bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
      by auto


    have "(word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1 ..32})) :: (1+31) word)= 
           word_of_int (bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))"
      using \<open>bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) {1..32}) = bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))\<close> 
      by auto
    \<comment> \<open>push bintrunc 32 inside\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (bintrunc 63 (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))"
      using bin_rest_power_trunc[where n="63" and k="31", symmetric] by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using bl2bin_drop by auto
    qed
    \<comment> \<open>pull bl_to_bin to left\<close>
    also have "... =  word_of_int (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))"
      unfolding butlast_pow_rest_bl2bin[symmetric] by auto
    \<comment> \<open>change to sbl_to_bin\<close>
    also have "... = (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... =  word_of_int (sbl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))) = 32"
        unfolding butlast_power length_take length_drop * by eval
      hence "(word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))) :: (1 + 31) word) = 
            (word_of_int (sbintrunc (length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))) :: (1 + 31) word)"
        by auto
      thus ?thesis
        using sbl_to_bin_alt_def by auto
    qed
    \<comment> \<open>push sbl_to_bin back to right\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (sbl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))" 
    proof -
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))) = 63"
        unfolding length_take length_drop * by eval
      hence **: "31 < length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)))))"
        by auto
      show ?thesis
        unfolding butlast_pow_rest_sbl2bin[OF **] by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (sbl_to_bin (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 4 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 4 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using sbl2bin_drop by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (bin_of COMMON at_time (i + 4 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 * clk_period - 2) on tw')))"
      using `bin_of TERM1 at_time (i + 4 *clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 4 *clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 *clk_period - 2) on tw')` 
      by auto
    also have "... =  word_of_int (sbintrunc 31 ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 4 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 * clk_period - 2) on tw')))"
    proof -
      have "(31 :: nat) \<le> 62" by auto
      show ?thesis
        unfolding bin_rest_power_strunc[OF `31 \<le> 62`]
        by auto
    qed
    also have "... =  word_of_int (sbintrunc (LENGTH(1 + 31) - 1) ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 4 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 * clk_period - 2) on tw')))"
      by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 4 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 * clk_period - 2) on tw'))"
      unfolding word_sbin.Abs_norm by auto
    also have "... = word_of_int ((bin_of COMMON at_time (i + 4 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 4 * clk_period - 2) on tw') div 2 ^ 31)"
      unfolding bin_rest_compow by auto
    also have "... = word_of_int (sbintrunc (length (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))) * 
                                  sbintrunc (length (lval_of (wline_of tw' ACCUM  (i + 4 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))) div 2 ^ 31)"
      using sbl_to_bin_alt_def2 by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))) * 
                                  sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))) div 2 ^ 31)"
    proof - 
      have "type_of (wline_of tw' COMMON (i + 4 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "type_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence **: "length (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      with * show ?thesis
        by auto
    qed
    also have "... = word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))) :: (1 + 31) word) * 
                                  sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))) :: (1 + 31) word ) div 2 ^ 31)"
      unfolding sint_sbintrunc' by auto
    finally show ?thesis
      unfolding `(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)`
      by auto
  qed
  hence "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
         Fixed (word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31))"
    by auto
  also have "... = Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2))))) * Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))))"
    using times_fixed.abs_eq[where xa="word_of_int (bin_of COMMON at_time i + 4 * clk_period - 2 on tw') :: (1 + 31) word" and 
                                    x="word_of_int (bin_of ACCUM at_time i + 4 * clk_period - 2 on tw') :: (1 + 31) word", symmetric]
    by auto
  also have "... = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2))"
  proof -
    have "type_of (wline_of tw' COMMON (i + 4 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of COMMON at_time i + 4 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2))"
    proof -
      have "wline_of tw' COMMON (i + 4 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2)))"
        using `type_of (wline_of tw' COMMON (i + 4 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of COMMON at_time i + 4 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2))"
      by auto

    have "type_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of ACCUM at_time i + 4 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2))"
    proof -
      have "wline_of tw' ACCUM (i + 4 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 4 * clk_period - 2)))"
        using `type_of (wline_of tw' ACCUM (i + 4 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of ACCUM at_time i + 4 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2))"
      by auto
    thus ?thesis
      using \<open>Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 4 * clk_period - 2))))) = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2))\<close> by auto
  qed  
  finally have "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2))"
    by auto  
  hence "fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period + 1)) = 
          approx_div_fact 3 + fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2))"
    using `?lhs4 = ?rhs4`
        `Fixed (word_of_int (bin_of ACCUM at_time i + 4 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 4 * clk_period - 1)) {1 .. 32})))`
        `Fixed (word_of_int (bin_of FRAC at_time i + 4 * clk_period - 1 on tw')) = approx_div_fact 3`
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2)))))"
    using `fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 5 * clk_period - 2))))`
        `wline_of tw' COMMON (i + 4 * clk_period - 2) = wline_of tw' COMMON (i + 4 * clk_period - 1)`
        `(fixed_of_sval (wline_of tw' COMMON (i + 5 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 1))`
        `wline_of tw' ACCUM  (i + 4 * clk_period + 1) = wline_of tw' ACCUM (i + 5 * clk_period - 2)`
    by auto

  \<comment> \<open> obtaining common and accum\<close>
  have "wline_of tw' COMMON (i + 3 * clk_period + 1) = wline_of tw' COMMON (i + 4 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 3 * clk_period + 1) = wline_of tw' ACCUM (i + 4 * clk_period - 2)"
  proof -
    have a: "fst tw \<le> i + 3 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 3 * clk_period + 1 \<le> i + 4 * clk_period - 2"
      using assms by (auto simp add: field_simps)
    have c: "i + 4 * clk_period - 2 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 4 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 3 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 4 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 3 * clk_period = m1 * clk_period"
        using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 4 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 4 * clk_period = m2 * clk_period"
          using `(i + 4 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 5 * clk_period - (i + 4 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 3 * clk_period = m1 * clk_period` `i + 4  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 4 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 3 * clk_period + 1 \<le> n" and "n \<le> i + 4 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 3 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 4 * clk_period - 1` `i + 4 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' COMMON (i + 3 * clk_period + 1) = wline_of tw' COMMON (i + 4 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 3 * clk_period + 1) = wline_of tw' ACCUM (i + 4 * clk_period - 2)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  have "Inv_core (i + 3 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
    by auto
  have "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 4 * clk_period)"
      using `is_posedge2 (snd tw') CLK (i + 4 * clk_period)` 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 4 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 3 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 3 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  have "wline_of tw' RST (i + 3 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 3 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
      using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 3 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 3 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 3 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' STATE (i + 3 * clk_period + 1) = V_INIT"
      using  `Inv_core ((i + 3 * clk_period + 1, snd tw'))` `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv by auto
    with `wline_of tw' STATE (i + 3 * clk_period + 1) = V_PROC` show False
      by auto
  qed
  have "wline_of tw' NEXT_COMMON (i + 3 * clk_period) = wline_of tw' COMMON (i + 3 * clk_period + 1)"
    and "wline_of tw' NEXT_ACCUM  (i + 3 * clk_period) = wline_of tw' ACCUM (i + 3 * clk_period + 1)"
    using `Inv_core (i + 3 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` `wline_of tw' RST (i + 3 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  have "bin_of COMMON at_time (i + 3 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 3 * clk_period) on tw'"
  proof -
    have "Inv_core (i + 3 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1))`
      unfolding inv_ncommon_alt_def comp_def snd_conv fst_conv by auto
  qed
  have "(fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) :: (1,31) fixed) = fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 1))"
  proof -
    have typof2: "type_of (wline_of tw' COMMON (i + 3 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs2 where " wline_of tw' COMMON (i + 3 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32"
      using type_of.elims[OF typof2] by fastforce
    have typof: "type_of (wline_of tw' COMMON (i + 4 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    then obtain bs1 where " wline_of tw' COMMON (i + 4 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32"
      using type_of.elims[OF typof] by fastforce
    hence "fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) = Fixed (of_bl bs1 :: (1 + 31) word)"
      using fixed_of_sval.simps by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs1) :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs1)))"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs1"] by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs1 - 1) (bl_to_bin bs1)))"
      using `wline_of tw' COMMON (i + 4 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs1))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbl_to_bin bs2))"
      using `bin_of COMMON at_time (i + 3 * clk_period - 1) on tw' = bin_of NEXT_COMMON at_time (i + 3 * clk_period) on tw'`
        `wline_of tw' COMMON (i + 3 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
        `wline_of tw' COMMON (i + 4 * clk_period - 2) = Lv Sig bs1 \<and> length bs1 = 32` 
      using \<open>wline_of tw' COMMON (i + 3 * clk_period + 1) = wline_of tw' COMMON (i + 4 * clk_period - 2)\<close> \<open>wline_of tw' NEXT_COMMON (i + 3 * clk_period) = wline_of tw' COMMON (i + 3 * clk_period + 1)\<close> by auto
    also have "... = Fixed (word_of_int (sbintrunc (length bs2- 1) (bl_to_bin bs2)))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin bs2)))"
      using `wline_of tw' COMMON (i + 3 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32` by auto
    also have "... = Fixed (word_of_int (bl_to_bin bs2) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm[symmetric, where x="bl_to_bin bs2"] by auto
    also have "... = Fixed (of_bl bs2 :: (1 + 31) word)"
      unfolding of_bl_def by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 1))"
      using `wline_of tw' COMMON (i + 3 * clk_period - 1) = Lv Sig bs2 \<and> length bs2 = 32`
      using fixed_of_sval.simps by auto
    finally show ?thesis
      by auto
  qed
  have "wline_of tw' COMMON (i + 3 * clk_period - 2) = wline_of tw' COMMON (i + 3 * clk_period - 1)"
  proof - 
    have "Inv_core (i + 3 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 3 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 2 * clk_period < i + 3 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 3 * clk_period - 2 < i + 6 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 3 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 3 * clk_period - 2)"
      using ** by auto
    thus ?thesis
      using `Inv_core (i + 3 * clk_period - 1, snd tw')`  unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed

  \<comment> \<open> obtaining state\<close>
  have "wline_of tw' STATE (i + 2 * clk_period + 1) = wline_of tw' STATE (i + 3 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 2 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 2 * clk_period + 1 \<le> i + 3 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 3 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 2 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 3 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 2 * clk_period = m1 * clk_period"
        using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 3 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 3 * clk_period = m2 * clk_period"
          using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 3 * clk_period - (i + 2 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 2 * clk_period = m1 * clk_period` `i + 3  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 3 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 2 * clk_period + 1 \<le> n" and "n \<le> i + 3 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 2 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 3 * clk_period - 1` `i + 3 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' STATE (i + 2 * clk_period + 1) = wline_of tw' STATE (i + 3 * clk_period - 1)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  hence "wline_of tw' STATE (i + 2 * clk_period + 1) = V_PROC"
    using `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 * clk_period - 1))`
    by auto
  have "wline_of tw' FRAC (i + 2 * clk_period + 1) = wline_of tw' FRAC (i + 3 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 2 * clk_period + 1) = wline_of tw' COUNTER (i + 3 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 2 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 2 * clk_period + 1 \<le> i + 3 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 3 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 2 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 3 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 2 * clk_period = m1 * clk_period"
        using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 3 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 3 * clk_period = m2 * clk_period"
          using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 3 * clk_period - (i + 2 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 2 * clk_period = m1 * clk_period` `i + 3  * clk_period = m2 * clk_period` by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 3 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 2 * clk_period + 1 \<le> n" and "n \<le> i + 3 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 2 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 3 * clk_period - 1` `i + 3 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
  show "wline_of tw' FRAC (i + 2 * clk_period + 1) = wline_of tw' FRAC (i + 3 * clk_period - 1)"
   and "wline_of tw' COUNTER (i + 2 * clk_period + 1) = wline_of tw' COUNTER (i + 3 * clk_period - 1)"
    using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d] by auto
  qed
  have "wline_of tw' NEXT_FRAC (i + 2 * clk_period) = wline_of tw' FRAC (i + 2 * clk_period + 1)"
   and "wline_of tw' NEXT_STATE (i + 2 * clk_period) = wline_of tw' STATE (i + 2 * clk_period + 1)"
   and "wline_of tw' NEXT_COUNTER (i + 2 * clk_period) = wline_of tw' COUNTER (i + 2 * clk_period + 1)"
  proof -
    have "Inv_core (i + 2 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto  
    moreover have "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 3 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 3 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 3 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 2 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have "wline_of tw' RST (i + 2 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "wline_of tw' RST (i + 2 * clk_period) \<noteq> Bv False" 
      have "wityping \<Gamma> (snd tw')"
        using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
      hence "type_of (wline_of tw' RST (i + 2 * clk_period)) = Bty"
        unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence "wline_of tw' RST (i + 2 * clk_period) = Bv True"
        using `wline_of tw' RST (i + 2 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 2 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 2 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 2 * clk_period)` unfolding inv_reg_alt_def
        comp_def snd_conv fst_conv  by auto
      with `wline_of tw' STATE (i + 2 * clk_period + 1) = V_PROC` show False
        using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
    qed
    ultimately show "wline_of tw' NEXT_FRAC (i + 2 * clk_period) = wline_of tw' FRAC (i + 2 * clk_period + 1)"
      and "wline_of tw' NEXT_STATE (i + 2 * clk_period) = wline_of tw' STATE (i + 2 * clk_period + 1)"
      and "wline_of tw' NEXT_COUNTER (i + 2 * clk_period) = wline_of tw' COUNTER (i + 2 * clk_period + 1)"
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PROC" and "ubin_of NEXT_COUNTER at_time i + 2 * clk_period on tw' = 3"
    using `wline_of tw' STATE (i + 2 * clk_period + 1) = V_PROC`  `ubin_of COUNTER at_time i + 3 *clk_period - 1 on tw' = 3` 
    using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 3 *clk_period - 1))) = 3\<close> \<open>wline_of tw' COUNTER (i + 2 * clk_period + 1) = wline_of tw' COUNTER (i + 3 *clk_period - 1)\<close> \<open>wline_of tw' NEXT_COUNTER (i + 2 * clk_period) = wline_of tw' COUNTER (i + 2 * clk_period + 1)\<close> 
    by auto
  have "wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE"
  proof (rule ccontr)
    have "Inv_core (i + 2 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 2 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1)) 
      \<or> wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE)"
    hence *: "(wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<Longrightarrow> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1)))" and 
      **: "wline_of tw' STATE (i + 2 * clk_period - 1) \<noteq> V_PRE" (is "?state \<noteq> _")by auto
    then consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PROC`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) \<noteq> V_PROC"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') INREADY (i + 2 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PROC`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PROC`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PROC`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 2 * clk_period) \<noteq> V_PROC"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 2 * clk_period) = V_PROC`
        by auto
    qed
  qed
  moreover have "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 3 * clk_period)"
      using `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 3 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 2 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  moreover have "\<not> (wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1)))"
  proof (rule ccontr)
    assume "\<not> \<not> (wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1)))"
    hence "(wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1)))"
      by auto
    have "bintrunc 3 (ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' - 1) = 3"
    proof -
      have "Inv_core (i + 2 * clk_period, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
        by auto
      thus ?thesis
        using `ubin_of NEXT_COUNTER at_time (i + 2 * clk_period) on tw' = 3`
        `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1))`
        unfolding inv_ncounter_alt_def fst_conv comp_def snd_conv by auto
    qed    
    hence "(ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' - 1) mod 8 = 3" 
      unfolding bintrunc_mod2p by auto
    have "0 < ubin_of COUNTER at_time i + 2  * clk_period - 2 on tw'"
    proof -
      have "Inv_core (i + 2 * clk_period - 1, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
      hence "inv_n0 (i + 2 * clk_period - 1, snd tw')"
        by auto
      hence "0 < bl_to_bin (lval_of (snd (snd tw') COUNTER (i + 2 * clk_period - 1 - 1)))"
        using `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1))`
        unfolding inv_n0_def comp_def snd_conv fst_conv by auto
      thus ?thesis
        unfolding comp_def snd_conv fst_conv
        by (metis diff_diff_left nat_1_add_1)
    qed   
    moreover have "ubin_of COUNTER at_time i + 2 * clk_period - 2 on tw' = ubin_of COUNTER at_time i + 2 * clk_period - 1 on tw'"
    proof -
      have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
        using `wityping \<Gamma> w` cosine_locale_axioms
        unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
      have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
        using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
      hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
      hence "(i + 7 * clk_period) mod clk_period = 0"
        using posedge by blast
      hence "(i + 2 * clk_period) mod clk_period = 0"
        by auto
      have "(i + 2 * clk_period - 2) mod clk_period \<noteq> 0"
      proof -
        have "i + 1 * clk_period < i + 2 * clk_period - 2"
          using assms by (auto)
        moreover have "i + 2 * clk_period - 2 < i + 2 * clk_period"
          using assms by auto
        ultimately show ?thesis
          by (metis \<open>(i + 2 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
          dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
      qed
      hence "\<not> is_posedge2 (snd tw') CLK (i + 2 * clk_period - 2)"
        using ** by auto
      moreover have "Inv_core (i + 2 * clk_period - 1, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
      ultimately show ?thesis
        unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
        using diff_diff_left nat_1_add_1 by presburger
    qed
    ultimately have "0 < ubin_of COUNTER at_time i + 2 * clk_period - 1 on tw'"
      by auto
    moreover have "ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' \<le> 7"
      using ubin_counter_atmost[OF `wityping \<Gamma> (snd tw')`] by auto
    ultimately have "(ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' - 1) mod 8 = ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' - 1"
      by (auto intro!: int_mod_eq')
    hence "ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' = 4"  
      using `(ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' - 1) mod 8 = 3` by auto

    have "wline_of tw' STATE (i + 1 * clk_period + 1) = V_PROC \<and> ubin_of COUNTER at_time (i + 1 * clk_period + 1) on tw' = 4"
    proof -
      have f0: "fst tw \<le> i + 1 * clk_period + 1"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
      have f1: "i + 1 * clk_period + 1 \<le> i + 2 * clk_period - 1"
        using assms by auto
      have f2: "i + 2 * clk_period - 1 \<le> i + 7 * clk_period + 1"
        by auto
      note temp = registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` f0 f1 f2]
      have f3: "\<And>k. i + 1 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 2 * clk_period - 1 \<Longrightarrow> \<not> (is_posedge2 (snd tw') CLK k)"
      proof -
        fix k 
        assume " i + 1 * clk_period + 1 \<le> k" and "k \<le> i + 2 * clk_period - 1"
        have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
          using `wityping \<Gamma> w` cosine_locale_axioms
          unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
        have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
          using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
        hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
          using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
        hence "(i + 7 * clk_period) mod clk_period = 0"
          using posedge by blast
        hence "(i + 1 * clk_period) mod clk_period = 0" and "(i + 2 * clk_period) mod clk_period = 0"
          by auto
        then obtain k1 where "i + 1 * clk_period = k1 * clk_period" 
          by (metis Nat.add_0_right div_mult_mod_eq)
        hence "i + 2 * clk_period = (k1 + 1) * clk_period"
          by simp        
        have "i + 1 * clk_period < k"
          using \<open>i + 1 * clk_period + 1 \<le> k\<close> by linarith
        have "k < i + 2 * clk_period"
          using \<open>k \<le> i + 2 * clk_period - 1\<close> f1 by linarith
        have "k div clk_period = k1"
          apply (rule Misc_Arithmetic.sdl)
          apply (metis \<open>i + 1 * clk_period < k\<close> \<open>i + 1 * clk_period = k1 * clk_period\<close> less_le_not_le mult.commute)
          by (metis Suc_eq_plus1 \<open>i + 2 * clk_period = (k1 + 1) * clk_period\<close> \<open>k < i + 2 * clk_period\<close> mult.commute)
        hence "k = k1 * clk_period + k mod clk_period"
          by (meson mod_div_decomp)
        hence "k mod clk_period \<noteq> 0"
          using \<open>i + 1 * clk_period < k\<close> \<open>i + 1 * clk_period = k1 * clk_period\<close> by linarith
        thus "\<not> (is_posedge2 (snd tw') CLK k)"
          using "**" by auto
      qed
      have "wline_of tw' STATE (i + 1 * clk_period + 1) = wline_of tw' STATE (i + 2 * clk_period - 1)" and 
           "wline_of tw' COUNTER (i + 1 * clk_period + 1) = wline_of tw' COUNTER (i + 2 * clk_period - 1)"
        using temp[OF f3] by auto
      thus ?thesis
        using `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 2 * clk_period - 1))`
        `ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' = 4`
        by auto
    qed   
    have "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 2 * clk_period)"
        using \<open>is_posedge2 (snd tw') CLK (i + 2 * clk_period)\<close> 
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 2 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 1 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    have "wline_of tw' RST (i + 1 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False" 
      have "wityping \<Gamma> (snd tw')"
        using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
        using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
      hence "type_of (wline_of tw' RST (i + 1 * clk_period)) = Bty"
        unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence "wline_of tw' RST (i + 1 * clk_period) = Bv True"
        using `wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
      moreover have "Inv_core (i + 1 * clk_period + 1, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
      ultimately have "wline_of tw' STATE (i + 1 * clk_period + 1) = V_INIT"
        using `is_posedge2 (snd tw') CLK (i + 1 * clk_period)`
        unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
      thus False
        using `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PROC \<and> ubin_of COUNTER at_time (i + 1 * clk_period + 1) on tw' = 4`
        by auto
    qed
    have "wline_of tw' NEXT_STATE (i + 1 * clk_period ) = V_PROC"
    proof -
      have "Inv_core (i + 1 * clk_period + 1, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
      thus ?thesis
        using `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
        `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PROC \<and> ubin_of COUNTER at_time (i + 1 * clk_period + 1) on tw' = 4`
        unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    qed
    have "wline_of tw' STATE (i + 1 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))
        \<or> wline_of tw' STATE (i + 1 * clk_period - 1) = V_PRE"
    proof (rule ccontr)
      have "Inv_core (i + 1 * clk_period, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
        by auto
      hence inv:"inv_nstate (i + 1 * clk_period, snd tw')"
        by auto
      assume "\<not> (wline_of tw' STATE (i + 1 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))
        \<or> wline_of tw' STATE (i + 1 * clk_period - 1) = V_PRE)"
      hence *: "(wline_of tw' STATE (i + 1 * clk_period - 1) = V_PROC \<Longrightarrow> \<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1)))" and
        **: "wline_of tw' STATE (i + 1 * clk_period - 1) \<noteq> V_PRE"
        by auto
      let ?state = "wline_of tw' STATE (i + 1 * clk_period - 1) "
      consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
        | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
        using ** by auto
      thus False
      proof (cases)
        case 1
        hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PROC"
          using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
        then show ?thesis 
          using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PROC`
          by auto
      next
        case 2
        hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PROC"
          using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv  
          by (cases "bval_of (snd (snd tw') INREADY (i + 1 * clk_period - 1))") auto
        then show ?thesis 
          using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PROC`
          by auto
      next
        case 3
        hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PROC"
          using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv  by auto
        then show ?thesis 
          using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PROC`
          by auto
      next
        case 4
        hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PROC"
          using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
        then show ?thesis 
          using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PROC`
          by auto
      next
        case 5
        hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PROC"
          using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
        then show ?thesis 
          using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PROC`
          by auto
      qed
    qed

    moreover
    { assume "wline_of tw' STATE (i + 1 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))"
      have "ubin_of NEXT_COUNTER at_time i + 1 * clk_period on tw' = 4"
      proof -
        have "Inv_core (i + 1 * clk_period + 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
        thus ?thesis
          using `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PROC \<and> ubin_of COUNTER at_time (i + 1 * clk_period + 1) on tw' = 4`
          `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
          unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
      qed
      have "bintrunc 3 (ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) = 4"
      proof -
        have "Inv_core (i + 1 * clk_period, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
          by auto
        thus ?thesis
          using `ubin_of NEXT_COUNTER at_time (i + 1 * clk_period) on tw' = 4`
          `wline_of tw' STATE (i + 1 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))`
          unfolding inv_ncounter_alt_def fst_conv comp_def snd_conv by auto
      qed    
      hence "(ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) mod 8 = 4" 
        unfolding bintrunc_mod2p by auto
      have "0 < ubin_of COUNTER at_time i + 1  * clk_period - 2 on tw'"
      proof -
        have "Inv_core (i + 1 * clk_period - 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
        hence "inv_n0 (i + 1 * clk_period - 1, snd tw')"
          by auto
        hence "0 < bl_to_bin (lval_of (snd (snd tw') COUNTER (i + 1 * clk_period - 1 - 1)))"
          using `wline_of tw' STATE (i + 1 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))`
          unfolding inv_n0_def comp_def snd_conv fst_conv by auto
        thus ?thesis
          unfolding comp_def snd_conv fst_conv
          by (metis diff_diff_left nat_1_add_1)
      qed   
      moreover have "ubin_of COUNTER at_time i + 1 * clk_period - 2 on tw' = ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw'"
      proof -
        have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
          using `wityping \<Gamma> w` cosine_locale_axioms
          unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
        have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
          using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
        hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
          using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
        hence "(i + 7 * clk_period) mod clk_period = 0"
          using posedge by blast
        hence "(i + 1 * clk_period) mod clk_period = 0"
          by auto
        have "(i + 1 * clk_period - 2) mod clk_period \<noteq> 0"
        proof -
          have "i + 0 * clk_period < i + 1 * clk_period - 2"
            using assms by (auto)
          moreover have "i + 1 * clk_period - 2 < i + 1 * clk_period"
            using assms by auto
          ultimately show ?thesis
            by (metis \<open>(i + 1 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
            dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
        qed
        hence "\<not> is_posedge2 (snd tw') CLK (i + 1 * clk_period - 2)"
          using ** by auto
        moreover have "Inv_core (i + 1 * clk_period - 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
        ultimately show ?thesis
          unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
          using diff_diff_left nat_1_add_1 by presburger
      qed
      ultimately have "0 < ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw'"
        by auto
      moreover have "ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' \<le> 7"
        using ubin_counter_atmost[OF `wityping \<Gamma> (snd tw')`] by auto
      ultimately have "(ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) mod 8 = ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1"
        by (auto intro!: int_mod_eq')
      hence "ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' = 5"  
        using `(ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) mod 8 = 4` by auto 
      have "ubin_of COUNTER at_time (i + 1) on tw' = 5"
      proof -
        have f0: "fst tw \<le> i + 0 * clk_period + 1"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
        have f1: "i + 0 * clk_period + 1 \<le> i + 1 * clk_period - 1"
          using assms by auto
        have f2: "i + 1 * clk_period - 1 \<le> i + 7 * clk_period + 1"
          by auto
        note temp = registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` f0 f1 f2]
        have f3: "\<And>k. i + 0 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 1 * clk_period - 1 \<Longrightarrow> \<not> (is_posedge2 (snd tw') CLK k)"
        proof -
          fix k 
          assume " i + 0 * clk_period + 1 \<le> k" and "k \<le> i + 1 * clk_period - 1"
          have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
            using `wityping \<Gamma> w` cosine_locale_axioms
            unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
          have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
            using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
          hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
            using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
          hence "(i + 7 * clk_period) mod clk_period = 0"
            using posedge by blast
          hence "(i + 0 * clk_period) mod clk_period = 0" and "(i + 1 * clk_period) mod clk_period = 0"
            by auto
          then obtain k1 where "i + 0 * clk_period = k1 * clk_period" 
            by (metis Nat.add_0_right div_mult_mod_eq)
          hence "i + 1 * clk_period = (k1 + 1) * clk_period"
            by simp        
          have "i + 0 * clk_period < k"
            using \<open>i + 0 * clk_period + 1 \<le> k\<close> by linarith
          have "k < i + 1 * clk_period"
            using \<open>k \<le> i + 1 * clk_period - 1\<close> f1 by linarith
          have "k div clk_period = k1"
            apply (rule Misc_Arithmetic.sdl)
            apply (metis \<open>i + 0 * clk_period < k\<close> \<open>i + 0 * clk_period = k1 * clk_period\<close> less_le_not_le mult.commute)
            by (metis Suc_eq_plus1 \<open>i + 1 * clk_period = (k1 + 1) * clk_period\<close> \<open>k < i + 1 * clk_period\<close> mult.commute)
          hence "k = k1 * clk_period + k mod clk_period"
            by (meson mod_div_decomp)
          hence "k mod clk_period \<noteq> 0"
            using \<open>i + 0 * clk_period < k\<close> \<open>i + 0 * clk_period = k1 * clk_period\<close> by linarith
          thus "\<not> (is_posedge2 (snd tw') CLK k)"
            using "**" by auto
        qed
        have "wline_of tw' COUNTER (i + 0 * clk_period + 1) = wline_of tw' COUNTER (i + 1 * clk_period - 1)" 
          using temp[OF f3] by auto
        thus ?thesis
          using `ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' = 5`
          by auto
      qed }

    moreover
    { assume "wline_of tw' STATE (i + 1 * clk_period - 1) = V_PRE"
      have "bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))"
      proof (rule ccontr)
        assume "\<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))"
        have "Inv_core (i + 1 * clk_period + 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
          by auto
        have "Inv_core (i + 1 * clk_period - 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
          by auto
        hence "inv_n0 (i + 1 * clk_period - 1, snd tw')"
          by auto
        hence "\<not> (0 < ubin_of COUNTER at_time i + 1 * clk_period - 1 - 1 on tw')"
          using `\<not> bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))`
          unfolding inv_n0_def comp_def snd_conv fst_conv by auto
        hence "\<not> (0 < ubin_of COUNTER at_time i + 1 * clk_period - 2 on tw')"
          by (metis diff_diff_left nat_1_add_1)
        hence "ubin_of COUNTER at_time i + 1 * clk_period - 2 on tw' = 0"
          using bl_to_bin_ge0 by smt
        hence "ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw' = 0"
        proof -
          have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
            using `wityping \<Gamma> w` cosine_locale_axioms
            unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
          have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
            using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
          hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
            using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
          hence "(i + 7 * clk_period) mod clk_period = 0"
            using posedge by blast
          hence "(i + 1 * clk_period) mod clk_period = 0"
            by auto
          have "(i + 1 * clk_period - 2) mod clk_period \<noteq> 0"
          proof -
            have "i + 0 * clk_period < i + 1 * clk_period - 2"
              using assms by (auto)
            moreover have "i + 1 * clk_period - 2 < i + 1 * clk_period"
              using assms by auto
            ultimately show ?thesis
              by (metis \<open>(i + 1 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
              dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
          qed
          hence "\<not> is_posedge2 (snd tw') CLK (i + 1 * clk_period - 2)"
            using ** by auto
          moreover have "inv_reg (i + 1 * clk_period - 1, snd tw')"
            using `Inv_core (i + 1 * clk_period - 1, snd tw')` by auto
          ultimately have "wline_of tw' COUNTER (i + 1 * clk_period - 1) = wline_of tw' COUNTER (i + 1 * clk_period - 2)"
            using `\<not> is_posedge2 (snd tw') CLK (i + 1 * clk_period - 2)`
            unfolding inv_reg_alt_def comp_def snd_conv fst_conv  by (metis diff_diff_left one_add_one)
          thus ?thesis
            using `ubin_of COUNTER at_time i + 1 * clk_period - 2 on tw' = 0` by auto
        qed
        have "ubin_of NEXT_COUNTER at_time i + 1 * clk_period on tw' = 7"
        proof -
          have "Inv_core (i + 1 * clk_period, snd tw')"
            using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
            by auto
          hence "inv_ncounter (i + 1 * clk_period, snd tw')"
            by auto
          hence "ubin_of NEXT_COUNTER at_time i + 1 * clk_period on tw' = bintrunc 3 ((ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw') - 1)"
            using `wline_of tw' STATE (i + 1 * clk_period - 1) = V_PRE`
            unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
          also have "... = bintrunc 3 (-1)"
            using `ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw' = 0` by auto
          also have "... = 7"
            by eval
          finally show ?thesis
            by auto
        qed
        hence "ubin_of COUNTER at_time i + 1 * clk_period + 1 on tw' = 7"
          using `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
          using `Inv_core (i + 1 * clk_period + 1, snd tw')` 
          unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
        with `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PROC \<and> ubin_of COUNTER at_time (i + 1 * clk_period + 1) on tw' = 4`
        show False
          by auto
      qed
      have "ubin_of NEXT_COUNTER at_time i + 1 * clk_period on tw' = 4"
      proof -
        have "Inv_core (i + 1 * clk_period + 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
        thus ?thesis
          using `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PROC \<and> ubin_of COUNTER at_time (i + 1 * clk_period + 1) on tw' = 4`
          `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
          unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
      qed
      have "bintrunc 3 (ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) = 4"
      proof -
        have "Inv_core (i + 1 * clk_period, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
          by auto
        thus ?thesis
          using `ubin_of NEXT_COUNTER at_time (i + 1 * clk_period) on tw' = 4`
          `wline_of tw' STATE (i + 1 * clk_period - 1) = V_PRE` `bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))`
          unfolding inv_ncounter_alt_def fst_conv comp_def snd_conv by auto
      qed    
      hence "(ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) mod 8 = 4" 
        unfolding bintrunc_mod2p by auto
      have "0 < ubin_of COUNTER at_time i + 1  * clk_period - 2 on tw'"
      proof -
        have "Inv_core (i + 1 * clk_period - 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
        hence "inv_n0 (i + 1 * clk_period - 1, snd tw')"
          by auto
        hence "0 < bl_to_bin (lval_of (snd (snd tw') COUNTER (i + 1 * clk_period - 1 - 1)))"
          using `wline_of tw' STATE (i + 1 * clk_period - 1) = V_PRE` `bval_of (wline_of tw' CTR_NEQ_0 (i + 1 * clk_period - 1))`
          unfolding inv_n0_def comp_def snd_conv fst_conv by auto
        thus ?thesis
          unfolding comp_def snd_conv fst_conv
          by (metis diff_diff_left nat_1_add_1)
      qed   
      moreover have "ubin_of COUNTER at_time i + 1 * clk_period - 2 on tw' = ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw'"
      proof -
        have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
          using `wityping \<Gamma> w` cosine_locale_axioms
          unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
        have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
          using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
        hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
          using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
        hence "(i + 7 * clk_period) mod clk_period = 0"
          using posedge by blast
        hence "(i + 1 * clk_period) mod clk_period = 0"
          by auto
        have "(i + 1 * clk_period - 2) mod clk_period \<noteq> 0"
        proof -
          have "i + 0 * clk_period < i + 1 * clk_period - 2"
            using assms by (auto)
          moreover have "i + 1 * clk_period - 2 < i + 1 * clk_period"
            using assms by auto
          ultimately show ?thesis
            by (metis \<open>(i + 1 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
            dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
        qed
        hence "\<not> is_posedge2 (snd tw') CLK (i + 1 * clk_period - 2)"
          using ** by auto
        moreover have "Inv_core (i + 1 * clk_period - 1, snd tw')"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
        ultimately show ?thesis
          unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
          using diff_diff_left nat_1_add_1 by presburger
      qed
      ultimately have "0 < ubin_of COUNTER at_time i + 1 * clk_period - 1 on tw'"
        by auto
      moreover have "ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' \<le> 7"
        using ubin_counter_atmost[OF `wityping \<Gamma> (snd tw')`] by auto
      ultimately have "(ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) mod 8 = ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1"
        by (auto intro!: int_mod_eq')
      hence "ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' = 5"  
        using `(ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' - 1) mod 8 = 4` by auto 
      have "ubin_of COUNTER at_time (i + 1) on tw' = 5"
      proof -
        have f0: "fst tw \<le> i + 0 * clk_period + 1"
          using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
        have f1: "i + 0 * clk_period + 1 \<le> i + 1 * clk_period - 1"
          using assms by auto
        have f2: "i + 1 * clk_period - 1 \<le> i + 7 * clk_period + 1"
          by auto
        note temp = registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` f0 f1 f2]
        have f3: "\<And>k. i + 0 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 1 * clk_period - 1 \<Longrightarrow> \<not> (is_posedge2 (snd tw') CLK k)"
        proof -
          fix k 
          assume " i + 0 * clk_period + 1 \<le> k" and "k \<le> i + 1 * clk_period - 1"
          have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
            using `wityping \<Gamma> w` cosine_locale_axioms
            unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
          have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
            using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
          hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
            using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
          hence "(i + 7 * clk_period) mod clk_period = 0"
            using posedge by blast
          hence "(i + 0 * clk_period) mod clk_period = 0" and "(i + 1 * clk_period) mod clk_period = 0"
            by auto
          then obtain k1 where "i + 0 * clk_period = k1 * clk_period" 
            by (metis Nat.add_0_right div_mult_mod_eq)
          hence "i + 1 * clk_period = (k1 + 1) * clk_period"
            by simp        
          have "i + 0 * clk_period < k"
            using \<open>i + 0 * clk_period + 1 \<le> k\<close> by linarith
          have "k < i + 1 * clk_period"
            using \<open>k \<le> i + 1 * clk_period - 1\<close> f1 by linarith
          have "k div clk_period = k1"
            apply (rule Misc_Arithmetic.sdl)
            apply (metis \<open>i + 0 * clk_period < k\<close> \<open>i + 0 * clk_period = k1 * clk_period\<close> less_le_not_le mult.commute)
            by (metis Suc_eq_plus1 \<open>i + 1 * clk_period = (k1 + 1) * clk_period\<close> \<open>k < i + 1 * clk_period\<close> mult.commute)
          hence "k = k1 * clk_period + k mod clk_period"
            by (meson mod_div_decomp)
          hence "k mod clk_period \<noteq> 0"
            using \<open>i + 0 * clk_period < k\<close> \<open>i + 0 * clk_period = k1 * clk_period\<close> by linarith
          thus "\<not> (is_posedge2 (snd tw') CLK k)"
            using "**" by auto
        qed
        have "wline_of tw' COUNTER (i + 0 * clk_period + 1) = wline_of tw' COUNTER (i + 1 * clk_period - 1)" 
          using temp[OF f3] by auto
        thus ?thesis
          using `ubin_of COUNTER at_time (i + 1 * clk_period - 1) on tw' = 5`
          by auto
      qed }
    ultimately have "ubin_of COUNTER at_time (i + 1) on tw' = 5"
      by auto 
    with assms(10) show False
      by auto
  qed
  ultimately have "wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE"
    by auto

  \<comment> \<open>obtaining counter\<close>
  have "wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE "
  proof -
    have f0: "fst tw \<le> i + 1 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have f1: "i + 1 * clk_period + 1 \<le> i + 2 * clk_period - 1"
      using assms by auto
    have f2: "i + 2 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    note temp = registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` f0 f1 f2]
    have f3: "\<And>k. i + 1 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 2 * clk_period - 1 \<Longrightarrow> \<not> (is_posedge2 (snd tw') CLK k)"
    proof -
      fix k 
      assume " i + 1 * clk_period + 1 \<le> k" and "k \<le> i + 2 * clk_period - 1"
      have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
        using `wityping \<Gamma> w` cosine_locale_axioms
        unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
      have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
        using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
      hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
      hence "(i + 7 * clk_period) mod clk_period = 0"
        using posedge by blast
      hence "(i + 1 * clk_period) mod clk_period = 0" and "(i + 2 * clk_period) mod clk_period = 0"
        by auto
      then obtain k1 where "i + 1 * clk_period = k1 * clk_period" 
        by (metis Nat.add_0_right div_mult_mod_eq)
      hence "i + 2 * clk_period = (k1 + 1) * clk_period"
        by simp        
      have "i + 1 * clk_period < k"
        using \<open>i + 1 * clk_period + 1 \<le> k\<close> by linarith
      have "k < i + 2 * clk_period"
        using \<open>k \<le> i + 2 * clk_period - 1\<close> f1 by linarith
      have "k div clk_period = k1"
        apply (rule Misc_Arithmetic.sdl)
        apply (metis \<open>i + 1 * clk_period < k\<close> \<open>i + 1 * clk_period = k1 * clk_period\<close> less_le_not_le mult.commute)
        by (metis Suc_eq_plus1 \<open>i + 2 * clk_period = (k1 + 1) * clk_period\<close> \<open>k < i + 2 * clk_period\<close> mult.commute)
      hence "k = k1 * clk_period + k mod clk_period"
        by (meson mod_div_decomp)
      hence "k mod clk_period \<noteq> 0"
        using \<open>i + 1 * clk_period < k\<close> \<open>i + 1 * clk_period = k1 * clk_period\<close> by linarith
      thus "\<not> (is_posedge2 (snd tw') CLK k)"
        using "**" by auto
    qed
    have "wline_of tw' STATE (i + 1 * clk_period + 1) = wline_of tw' STATE (i + 2 * clk_period - 1)" 
      using temp[OF f3] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE`
      by auto
  qed 
  have "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 2 * clk_period)"
      using \<open>is_posedge2 (snd tw') CLK (i + 2 * clk_period)\<close> 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 2 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 1 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  have "wline_of tw' RST (i + 1 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
      using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 1 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 1 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    moreover have "Inv_core (i + 1 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    ultimately have "wline_of tw' STATE (i + 1 * clk_period + 1) = V_INIT"
      using `is_posedge2 (snd tw') CLK (i + 1 * clk_period)`
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
    thus False
      using `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE`
      by auto
  qed
  have "wline_of tw' NEXT_STATE (i + 1 * clk_period ) = V_PRE"
  proof -
    have "Inv_core (i + 1 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
      `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE`
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  qed    
  have "wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1))"
  proof (rule ccontr)
    have "Inv_core (i + 1 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 1 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1)))"
    hence *: "(wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<Longrightarrow> \<not> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1)))" 
      by auto
    let ?state = "wline_of tw' STATE (i + 1 * clk_period - 1) "
    consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      | "?state = V_PRE"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv  by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') CTR_NEQ_0 (i + 1 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 6
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    qed
  qed    
  have "wline_of tw' STATE (i + 1) = V_WAIT"
  proof -
    have f0: "fst tw \<le> i + 0 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have f1: "i + 0 * clk_period + 1 \<le> i + 1 * clk_period - 1"
      using assms by auto
    have f2: "i + 1 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    note temp = registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` f0 f1 f2]
    have f3: "\<And>k. i + 0 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 1 * clk_period - 1 \<Longrightarrow> \<not> (is_posedge2 (snd tw') CLK k)"
    proof -
      fix k 
      assume " i + 0 * clk_period + 1 \<le> k" and "k \<le> i + 1 * clk_period - 1"
      have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
        using `wityping \<Gamma> w` cosine_locale_axioms
        unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
      have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
        using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
      hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
      hence "(i + 7 * clk_period) mod clk_period = 0"
        using posedge by blast
      hence "(i + 0 * clk_period) mod clk_period = 0" and "(i + 1 * clk_period) mod clk_period = 0"
        by auto
      then obtain k1 where "i + 0 * clk_period = k1 * clk_period" 
        by (metis Nat.add_0_right div_mult_mod_eq)
      hence "i + 1 * clk_period = (k1 + 1) * clk_period"
        by simp        
      have "i + 0 * clk_period < k"
        using \<open>i + 0 * clk_period + 1 \<le> k\<close> by linarith
      have "k < i + 1 * clk_period"
        using \<open>k \<le> i + 1 * clk_period - 1\<close> f1 by linarith
      have "k div clk_period = k1"
        apply (rule Misc_Arithmetic.sdl)
        apply (metis \<open>i + 0 * clk_period < k\<close> \<open>i + 0 * clk_period = k1 * clk_period\<close> less_le_not_le mult.commute)
        by (metis Suc_eq_plus1 \<open>i + 1 * clk_period = (k1 + 1) * clk_period\<close> \<open>k < i + 1 * clk_period\<close> mult.commute)
      hence "k = k1 * clk_period + k mod clk_period"
        by (meson mod_div_decomp)
      hence "k mod clk_period \<noteq> 0"
        using \<open>i + 0 * clk_period < k\<close> \<open>i + 0 * clk_period = k1 * clk_period\<close> by linarith
      thus "\<not> (is_posedge2 (snd tw') CLK k)"
        using "**" by auto
    qed
    have "wline_of tw' STATE (i + 0 * clk_period + 1) = wline_of tw' STATE (i + 1 * clk_period - 1)" 
      using temp[OF f3] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1))`
      by auto
  qed

  have "ubin_of NEXT_COUNTER at_time (i + clk_period) on tw' = 4"
  proof -
    have "Inv_core (i + 1 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1))`
      unfolding inv_ncounter_alt_def comp_def snd_conv fst_conv by auto
  qed
  moreover have "Inv_core (i + 1 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
    by auto
  ultimately have "ubin_of COUNTER at_time (i + clk_period + 1) on tw' = 4"
    using `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  moreover have "ubin_of COUNTER at_time (i + clk_period + 1) on tw' = ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw'"
  proof -
    have a: "fst tw \<le> i + 1 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 1 * clk_period + 1 \<le> i + 2 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 2 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 1 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 1 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 2 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 1 * clk_period = m1 * clk_period"
        using `(i + 1 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 2 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 2 * clk_period = m2 * clk_period"
          using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 2 * clk_period - (i + 1 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 1 * clk_period = m1 * clk_period` `i + 2  * clk_period = m2 * clk_period` by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 2 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 1 * clk_period + 1 \<le> n" and "n \<le> i + 2 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 1 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 2 * clk_period - 1` `i + 2 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show ?thesis
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d] by auto
  qed
  ultimately have "ubin_of COUNTER at_time (i + 2 * clk_period - 1) on tw' = 4"
    by auto

  \<comment> \<open> obtaining frac\<close>
  have "bin_of NEXT_FRAC at_time (i + 2 *clk_period) on tw' = approx_eighth"
  proof -
    have "Inv_core (i + 2 *clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence "inv_nfrac (i + 2 *clk_period, snd tw')"
      by auto
    thus ?thesis
      using `ubin_of COUNTER at_time i + 2 *clk_period - 1 on tw' = 4`
      unfolding inv_nfrac_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of FRAC at_time (i + 3 * clk_period - 1) on tw' = approx_eighth"
    using \<open>wline_of tw' FRAC (i + 2 * clk_period + 1) = wline_of tw' FRAC (i + 3 * clk_period - 1)\<close>
    \<open>wline_of tw' NEXT_FRAC (i + 2 * clk_period) = wline_of tw' FRAC (i + 2 * clk_period + 1)\<close> by
    auto

  have "bin_of TERM1 at_time (i + 3 * clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 3 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 * clk_period - 2) on tw')"
  proof -
    have "Inv_core (i + 3 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      unfolding inv_term1_def comp_def snd_conv fst_conv  by (metis diff_diff_left one_add_one)
  qed

  have "Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_eighth) :: (1 + 31) word)"
    using `bin_of FRAC at_time i + 3 * clk_period - 1 on tw' = approx_eighth` by auto
  have "((word_of_int approx_eighth) :: (1 + 31) word) = (approx_eighth :: (1 + 31) word)"
    unfolding word_uint.inverse_norm by eval
  hence "Fixed ((word_of_int approx_eighth) :: (1 + 31) word) = Fixed (approx_eighth :: (1 + 31) word)"
    by auto
  also have "... = approx_div_fact 4"
    by (simp add: eval_nat_numeral(2) numeral_3_eq_3)
  finally have "Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) = approx_div_fact 4"
    using `Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) = Fixed ((word_of_int approx_eighth) :: (1 + 31) word)`
    by auto
  moreover have "Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) = (fixed_of_sval (wline_of tw' FRAC (i + 3 * clk_period - 1)) :: (1,31) fixed)"
  proof -
    have "type_of (wline_of tw' FRAC (i + 3 * clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' FRAC (i + 3 * clk_period - 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' FRAC (i + 3 * clk_period - 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' FRAC (i + 3 * clk_period - 1)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' FRAC (i + 3 * clk_period - 1))"
    proof -
      have "wline_of tw' FRAC (i + 3 * clk_period - 1) = Lv Sig (lval_of (wline_of tw' FRAC (i + 3 * clk_period - 1)))"
        using `type_of (wline_of tw' FRAC (i + 3 *clk_period - 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  ultimately have "(fixed_of_sval (wline_of tw' FRAC (i + 3 * clk_period - 1)) :: (1,31) fixed) = approx_div_fact 4"
    by auto

  \<comment> \<open> obtaining accum\<close>
  have  "bin_of NEXT_ACCUM at_time (i + 3 * clk_period) on tw' = 
            sbintrunc 31 (bin_of FRAC at_time i + 3 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})))"
  proof -
    have "Inv_core (i + 3 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 3 * clk_period - 1) = V_PROC \<and> bval_of (wline_of tw' CTR_NEQ_0 (i + 3 *clk_period - 1))`
      unfolding inv_naccum_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "bin_of ACCUM at_time (i + 3 * clk_period + 1) on tw' = 
        sbintrunc 31 (bin_of FRAC at_time i + 3 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})))"
    using `wline_of tw' NEXT_ACCUM  (i + 3 * clk_period) = wline_of tw' ACCUM (i + 3 * clk_period + 1)` 
    by auto
  hence "(word_of_int (bin_of ACCUM at_time i + 3 * clk_period + 1 on tw') :: (1 + 31) word) =  word_of_int (sbintrunc 31 (bin_of FRAC at_time i + 3 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (sbintrunc (LENGTH((1 + 31)) - 1) (bin_of FRAC at_time i + 3 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32}))))"
    by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw' +  (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})))"
    unfolding word_sbin.Abs_norm by auto
  also have "... = word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32}))"
    unfolding wi_hom_syms(1) by auto
  finally have "(word_of_int (bin_of ACCUM at_time i + 3 * clk_period + 1 on tw') :: (1 + 31) word) = 
                 word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw') + word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32}))"
    by auto
  hence "Fixed (word_of_int (bin_of ACCUM at_time i + 3 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})))"
    unfolding plus_fixed.abs_eq by auto
  have "Fixed (word_of_int (bin_of ACCUM at_time i + 3 * clk_period + 1 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period + 1))"
    (is "?lhs4 = ?rhs4")
  proof -
    have "type_of (wline_of tw' ACCUM (i + 3 * clk_period + 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 3 * clk_period + 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "?lhs4 = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period + 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period + 1)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period + 1))"
    proof -
      have "wline_of tw' ACCUM (i + 3 * clk_period + 1) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 3 * clk_period + 1)))"
        using `type_of (wline_of tw' ACCUM (i + 3 * clk_period + 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed

  have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
        word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31)"
  proof -
    have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)= 
          word_of_int
     (sbintrunc (length (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32}) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32})))"
      unfolding sbl_to_bin_alt_def by auto
    moreover have "(length (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32}) - 1) = 31"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "card {1::nat ..32} = 32"
        unfolding card_atLeastAtMost by auto 
      show ?thesis
        unfolding length_nths * 
        using card_slice[where len="64" and l=62 and r="31"] by auto
    qed
    ultimately have "(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                     word_of_int (sbintrunc 31 (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32})))"
      by auto
    also have "... = (word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32})) :: (1 + 31) word) "
      unfolding word_sbin.Abs_norm by auto
    finally have "word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1+31) word)"
      by auto

    have interval: "{1 :: nat .. 32} = {1 :: nat ..< 33}"
      by auto
    have nths: "\<And>xs:: bool list. nths xs {1 :: nat .. 32} = drop 1 (take 33 xs)"
      unfolding interval  nths_from_upt_eq_drop_take[where m="1" and n="33"] by auto
    have " bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1 ..32}) = 
           bl_to_bin (drop 1 (take 33 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
      using nths[of "(lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))"] by auto
    also have "... = bintrunc (length (take 33 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))) - 1) (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
      unfolding bl2bin_drop by auto
    also have "... = bintrunc 32 (bl_to_bin (take 33 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence " length (take 33 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))) = 33"
        unfolding length_take by auto
      thus ?thesis
        by auto
    qed
    also have "... = bintrunc 32 (bl_to_bin (take (length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) - 31)  (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
    proof-
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        by auto
    qed
    also have "... =  bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
      unfolding take_rest_bl2bin  by auto
    finally have "bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1 ..32}) = 
                      bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
      by auto


    have "(word_of_int (bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1 ..32})) :: (1+31) word)= 
           word_of_int (bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))"
      using \<open>bl_to_bin (nths (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) {1..32}) = bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))\<close> 
      by auto
    \<comment> \<open>push bintrunc 32 inside\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (bintrunc 63 (bl_to_bin (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))"
      using bin_rest_power_trunc[where n="63" and k="31", symmetric] by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using bl2bin_drop by auto
    qed
    \<comment> \<open>pull bl_to_bin to left\<close>
    also have "... =  word_of_int (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))"
      unfolding butlast_pow_rest_bl2bin[symmetric] by auto
    \<comment> \<open>change to sbl_to_bin\<close>
    also have "... = (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... =  word_of_int (sbl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))) = 32"
        unfolding butlast_power length_take length_drop * by eval
      hence "(word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))) :: (1 + 31) word) = 
            (word_of_int (sbintrunc (length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))) :: (1 + 31) word)"
        by auto
      thus ?thesis
        using sbl_to_bin_alt_def by auto
    qed
    \<comment> \<open>push sbl_to_bin back to right\<close>
    also have "... = word_of_int ((bin_rest ^^ 31) (sbl_to_bin (drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))" 
    proof -
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))) = 63"
        unfolding length_take length_drop * by eval
      hence **: "31 < length ((drop 1 (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)))))"
        by auto
      show ?thesis
        unfolding butlast_pow_rest_sbl2bin[OF **] by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (sbl_to_bin (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))))))"
    proof -
      have "type_of (wline_of tw' TERM1 (i + 3 * clk_period - 1)) = Lty Sig 64"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' TERM1 (i + 3 * clk_period - 1))) = 64"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      thus ?thesis
        using sbl2bin_drop by auto
    qed
    also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (bin_of COMMON at_time (i + 3 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 * clk_period - 2) on tw')))"
      using `bin_of TERM1 at_time (i + 3 *clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 3 *clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 *clk_period - 2) on tw')` 
      by auto
    also have "... =  word_of_int (sbintrunc 31 ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 3 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 * clk_period - 2) on tw')))"
    proof -
      have "(31 :: nat) \<le> 62" by auto
      show ?thesis
        unfolding bin_rest_power_strunc[OF `31 \<le> 62`]
        by auto
    qed
    also have "... =  word_of_int (sbintrunc (LENGTH(1 + 31) - 1) ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 3 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 * clk_period - 2) on tw')))"
      by auto
    also have "... = word_of_int ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 3 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 * clk_period - 2) on tw'))"
      unfolding word_sbin.Abs_norm by auto
    also have "... = word_of_int ((bin_of COMMON at_time (i + 3 * clk_period - 2) on tw' * bin_of ACCUM at_time (i + 3 * clk_period - 2) on tw') div 2 ^ 31)"
      unfolding bin_rest_compow by auto
    also have "... = word_of_int (sbintrunc (length (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))) * 
                                  sbintrunc (length (lval_of (wline_of tw' ACCUM  (i + 3 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))) div 2 ^ 31)"
      using sbl_to_bin_alt_def2 by auto
    also have "... = word_of_int (sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))) * 
                                  sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))) div 2 ^ 31)"
    proof - 
      have "type_of (wline_of tw' COMMON (i + 3 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence *: "length (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      have "type_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence **: "length (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      with * show ?thesis
        by auto
    qed
    also have "... = word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))) :: (1 + 31) word) * 
                                  sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))) :: (1 + 31) word ) div 2 ^ 31)"
      unfolding sint_sbintrunc' by auto
    finally show ?thesis
      unfolding `(word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) =
                 (word_of_int ( bl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)`
      by auto
  qed
  hence "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
         Fixed (word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))) :: (1 + 31) word ) * 
                     sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31))"
    by auto
  also have "... = Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2))))) * Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))))"
    using times_fixed.abs_eq[where xa="word_of_int (bin_of COMMON at_time i + 3 * clk_period - 2 on tw') :: (1 + 31) word" and 
                                    x="word_of_int (bin_of ACCUM at_time i + 3 * clk_period - 2 on tw') :: (1 + 31) word", symmetric]
    by auto
  also have "... = fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))"
  proof -
    have "type_of (wline_of tw' COMMON (i + 3 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of COMMON at_time i + 3 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2))"
    proof -
      have "wline_of tw' COMMON (i + 3 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2)))"
        using `type_of (wline_of tw' COMMON (i + 3 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of COMMON at_time i + 3 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2))"
      by auto

    have "type_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of ACCUM at_time i + 3 * clk_period - 2 on tw')) =  
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))) :: (1 + 31) word)"
      unfolding word_sbin.Abs_norm by auto
    also have "... = fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))"
    proof -
      have "wline_of tw' ACCUM (i + 3 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' ACCUM (i + 3 * clk_period - 2)))"
        using `type_of (wline_of tw' ACCUM (i + 3 *clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally have "Fixed (word_of_int (bin_of ACCUM at_time i + 3 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))"
      by auto
    thus ?thesis
      using \<open>Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 3 * clk_period - 2))))) = fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2))\<close> by auto
  qed  
  finally have "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))"
    by auto  
  hence "fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period + 1)) = 
          approx_div_fact 4 + fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))"
    using `?lhs4 = ?rhs4`
        `Fixed (word_of_int (bin_of ACCUM at_time i + 3 * clk_period + 1 on tw') :: (1 + 31) word) = 
         Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) + Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' TERM1 (i + 3 * clk_period - 1)) {1 .. 32})))`
        `Fixed (word_of_int (bin_of FRAC at_time i + 3 * clk_period - 1 on tw')) = approx_div_fact 4`
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 4 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))))))"
    using `fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 4 * clk_period - 2)))))`
    using \<open>fixed_of_sval (wline_of tw' COMMON (i + 4 * clk_period - 2)) = fixed_of_sval (wline_of
    tw' COMMON (i + 3 * clk_period - 1))\<close> \<open>wline_of tw' ACCUM (i + 3 * clk_period + 1) = wline_of
    tw' ACCUM (i + 4 * clk_period - 2)\<close> \<open>wline_of tw' COMMON (i + 3 * clk_period - 2) = wline_of tw'
    COMMON (i + 3 * clk_period - 1)\<close> by auto

  \<comment> \<open>obtaining common and accum\<close>
  have "wline_of tw' COMMON (i + 2 * clk_period + 1) = wline_of tw' COMMON (i + 3 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 2 * clk_period + 1) = wline_of tw' ACCUM (i + 3 * clk_period - 2)"
  proof -
    have a: "fst tw \<le> i + 2 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 2 * clk_period + 1 \<le> i + 3 * clk_period - 2"
      using assms by (auto simp add: field_simps)
    have c: "i + 3 * clk_period - 2 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 3 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 2 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 3 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 2 * clk_period = m1 * clk_period"
        using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 3 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 3 * clk_period = m2 * clk_period"
          using `(i + 3 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 4 * clk_period - (i + 3 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 2 * clk_period = m1 * clk_period` `i + 3  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 3 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 2 * clk_period + 1 \<le> n" and "n \<le> i + 3 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 2 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 3 * clk_period - 1` `i + 3 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' COMMON (i + 2 * clk_period + 1) = wline_of tw' COMMON (i + 3 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 2 * clk_period + 1) = wline_of tw' ACCUM (i + 3 * clk_period - 2)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  have "Inv_core (i + 2 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
    by auto
  have "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 3 * clk_period)"
      using `is_posedge2 (snd tw') CLK (i + 3 * clk_period)` 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 3 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 2 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 2 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  have "wline_of tw' RST (i + 2 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 2 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
      using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 2 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 2 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 2 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' STATE (i + 2 * clk_period + 1) = V_INIT"
      using  `Inv_core ((i + 2 * clk_period + 1, snd tw'))` `is_posedge2 (snd tw') CLK (i + 2 * clk_period)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv by auto
    with `wline_of tw' STATE (i + 2 * clk_period + 1) = V_PROC` show False
      by auto
  qed
  have "wline_of tw' NEXT_COMMON (i + 2 * clk_period) = wline_of tw' COMMON (i + 2 * clk_period + 1)"
    and "wline_of tw' NEXT_ACCUM  (i + 2 * clk_period) = wline_of tw' ACCUM (i + 2 * clk_period + 1)"
    using `Inv_core (i + 2 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 2 * clk_period)` `wline_of tw' RST (i + 2 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  have "sbintrunc 31 ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32})))  = 
        bin_of NEXT_COMMON at_time (i + 2 * clk_period) on tw'"
  proof -
    have "Inv_core (i + 2 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE`
      unfolding inv_ncommon_alt_def comp_def snd_conv fst_conv by auto
  qed
  have "(fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) :: (1,31) fixed) = 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) "
  proof -
    \<comment> \<open> obtaining square-temp\<close>
  
    have "bin_of SQUARE_TEMP at_time (i + 2 * clk_period - 1) on tw' = 
         sbintrunc 63 ((sbl_to_bin (lval_of (snd (snd tw') COMMON (i + 2 * clk_period - 1 - 1))))\<^sup>2)"
    proof -
      have "Inv_core (i + 2 * clk_period - 1, snd tw')"
        using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
        by auto
      thus ?thesis
        unfolding inv_sqr_def comp_def snd_conv fst_conv  by auto
    qed
    hence "bin_of SQUARE_TEMP at_time (i + 2 *clk_period - 1) on tw' = sbintrunc 63
       (bin_of COMMON at_time (i + 2 *clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 *clk_period - 2) on tw')"
      unfolding power2_eq_square comp_def 
      using diff_diff_left nat_1_add_1 by presburger

    \<comment> \<open> obtaining common\<close>
    have "bin_of NEXT_COMMON at_time (i + 2 * clk_period) on tw' = 
           sbintrunc 31 ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32})))"
      using `sbintrunc 31 ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32})))  = 
        bin_of NEXT_COMMON at_time (i + 2 * clk_period) on tw'`
      by auto
    hence "(word_of_int (bin_of NEXT_COMMON at_time i + 2 * clk_period on tw') :: (1 + 31) word) =  
            word_of_int (sbintrunc 31 ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32}))))"
      by auto
    also have "... = word_of_int (sbintrunc (LENGTH((1 + 31)) - 1)  ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32}))))"
      by auto
    also have "... = word_of_int ( ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32}))))"
      unfolding word_sbin.Abs_norm by auto
    finally have "(word_of_int (bin_of NEXT_COMMON at_time i + 2 * clk_period on tw') :: (1 + 31) word) = 
                   word_of_int ( ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32}))))"
      by auto
    hence "Fixed (word_of_int (bin_of NEXT_COMMON at_time i + 2 * clk_period on tw') :: (1 + 31) word) = 
           Fixed (word_of_int ( ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32})))))"
      unfolding plus_fixed.abs_eq by auto
    have "Fixed (word_of_int (bin_of NEXT_COMMON at_time i + 2 * clk_period on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' NEXT_COMMON (i + 2 * clk_period))"
      (is "?lhs5 = ?rhs5")
    proof -
      have "type_of (wline_of tw' NEXT_COMMON (i + 2 * clk_period)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
      hence "length (lval_of (wline_of tw' NEXT_COMMON (i + 2 * clk_period))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence "?lhs5 = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' NEXT_COMMON (i + 2 * clk_period))))))"
        unfolding sbl_to_bin_alt_def by auto
      also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' NEXT_COMMON (i + 2 * clk_period)))))"
        unfolding word_sbin.Abs_norm  by auto
      also have "... = fixed_of_sval (wline_of tw' NEXT_COMMON (i + 2 * clk_period))"
      proof -
        have "wline_of tw' NEXT_COMMON (i + 2 * clk_period) = Lv Sig (lval_of (wline_of tw' NEXT_COMMON (i + 2 * clk_period)))"
          using `type_of (wline_of tw' NEXT_COMMON (i + 2 * clk_period)) = Lty Sig 32` 
          by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
        thus ?thesis
          using fixed_of_sval.simps unfolding of_bl_def by smt
      qed
      finally show ?thesis
        by auto
    qed

    have "(word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
          word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word ) * 
                       sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31)"
    proof -
      have "(word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)= 
            word_of_int
       (sbintrunc (length (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32}) - 1) (bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32})))"
        unfolding sbl_to_bin_alt_def by auto
      moreover have "(length (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32}) - 1) = 31"
      proof -
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        have "card {1::nat ..32} = 32"
          unfolding card_atLeastAtMost by auto 
        show ?thesis
          unfolding length_nths * 
          using card_slice[where len="64" and l=62 and r="31"] by auto
      qed
      ultimately have "(word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                       word_of_int (sbintrunc 31 (bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32})))"
        by auto
      also have "... = word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32})))"
        by auto
      also have "... = (word_of_int (bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32})) :: (1 + 31) word) "
        unfolding word_sbin.Abs_norm by auto
      finally have "word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) =
                   (word_of_int ( bl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1+31) word)"
        by auto
    
      have interval: "{1 :: nat .. 32} = {1 :: nat ..< 33}"
        by auto
      have nths: "\<And>xs:: bool list. nths xs {1 :: nat .. 32} = drop 1 (take 33 xs)"
        unfolding interval  nths_from_upt_eq_drop_take[where m="1" and n="33"] by auto
      have " bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1 ..32}) = 
             bl_to_bin (drop 1 (take 33 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
        using nths[of "(lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))"] by auto
      also have "... = bintrunc (length (take 33 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))) - 1) (bl_to_bin (take 33 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
        unfolding bl2bin_drop by auto
      also have "... = bintrunc 32 (bl_to_bin (take 33 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
      proof-
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        hence " length (take 33 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))) = 33"
          unfolding length_take by auto
        thus ?thesis
          by auto
      qed
      also have "... = bintrunc 32 (bl_to_bin (take (length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) - 31)  (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
      proof-
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        thus ?thesis
          by auto
      qed
      also have "... =  bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
        unfolding take_rest_bl2bin  by auto
      finally have "bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1 ..32}) = 
                        bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
        by auto
    
    
      have "(word_of_int (bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1 ..32})) :: (1+31) word)= 
             word_of_int (bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))"
        using \<open>bl_to_bin (nths (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) {1..32}) = bintrunc 32 ((bin_rest ^^ 31) (bl_to_bin (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))\<close> 
        by auto
      \<comment> \<open>push bintrunc 32 inside\<close>
      also have "... = word_of_int ((bin_rest ^^ 31) (bintrunc 63 (bl_to_bin (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))"
        using bin_rest_power_trunc[where n="63" and k="31", symmetric] by auto
      also have "... = word_of_int ((bin_rest ^^ 31) (bl_to_bin (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))"
      proof -
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        thus ?thesis
          using bl2bin_drop by auto
      qed
      \<comment> \<open>pull bl_to_bin to left\<close>
      also have "... =  word_of_int (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))"
        unfolding butlast_pow_rest_bl2bin[symmetric] by auto
      \<comment> \<open>change to sbl_to_bin\<close>
      also have "... = (word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))) :: (1 + 31) word)"
        unfolding word_sbin.Abs_norm by auto
      also have "... =  word_of_int (sbl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))"
      proof -
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        have "length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))) = 32"
          unfolding butlast_power length_take length_drop * by eval
        hence "(word_of_int (sbintrunc (LENGTH(1+31) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))) :: (1 + 31) word) = 
              (word_of_int (sbintrunc (length ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))) - 1) (bl_to_bin ((butlast ^^ 31) (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))) :: (1 + 31) word)"
          by auto
        thus ?thesis
          using sbl_to_bin_alt_def by auto
      qed
      \<comment> \<open>push sbl_to_bin back to right\<close>
      also have "... = word_of_int ((bin_rest ^^ 31) (sbl_to_bin (drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))" 
      proof -
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        have "length ((drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))) = 63"
          unfolding length_take length_drop * by eval
        hence **: "31 < length ((drop 1 (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)))))"
          by auto
        show ?thesis
          unfolding butlast_pow_rest_sbl2bin[OF **] by auto
      qed
      also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (sbl_to_bin (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))))))"
      proof -
        have "type_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1)) = Lty Sig 64"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' SQUARE_TEMP (i + 2 * clk_period - 1))) = 64"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        thus ?thesis
          using sbl2bin_drop by auto
      qed
      also have "... = word_of_int ((bin_rest ^^ 31) (sbintrunc 62 (bin_of COMMON at_time (i + 2 * clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 * clk_period - 2) on tw')))"
        using `bin_of SQUARE_TEMP at_time (i + 2 *clk_period - 1) on tw' = sbintrunc 63 (bin_of COMMON at_time (i + 2 *clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 *clk_period - 2) on tw')` 
        by auto
      also have "... =  word_of_int (sbintrunc 31 ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 2 * clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 * clk_period - 2) on tw')))"
      proof -
        have "(31 :: nat) \<le> 62" by auto
        show ?thesis
          unfolding bin_rest_power_strunc[OF `31 \<le> 62`]
          by auto
      qed
      also have "... =  word_of_int (sbintrunc (LENGTH(1 + 31) - 1) ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 2 * clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 * clk_period - 2) on tw')))"
        by auto
      also have "... = word_of_int ((bin_rest ^^ 31) (bin_of COMMON at_time (i + 2 * clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 * clk_period - 2) on tw'))"
        unfolding word_sbin.Abs_norm by auto
      also have "... = word_of_int ((bin_of COMMON at_time (i + 2 * clk_period - 2) on tw' * bin_of COMMON at_time (i + 2 * clk_period - 2) on tw') div 2 ^ 31)"
        unfolding bin_rest_compow by auto
      also have "... = word_of_int (sbintrunc (length (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) * 
                                    sbintrunc (length (lval_of (wline_of tw' COMMON  (i + 2 * clk_period - 2))) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) div 2 ^ 31)"
        using sbl_to_bin_alt_def2 by auto
      also have "... = word_of_int (sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) * 
                                    sbintrunc (LENGTH(1 + 31) - 1) (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) div 2 ^ 31)"
      proof - 
        have "type_of (wline_of tw' COMMON (i + 2 * clk_period - 2)) = Lty Sig 32"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence *: "length (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))) = 32"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        have "type_of (wline_of tw' COMMON (i + 2 * clk_period - 2)) = Lty Sig 32"
          using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
          using cosine_locale_axioms unfolding cosine_locale_def by auto
        hence **: "length (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))) = 32"
          by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
        with * show ?thesis
          by auto
      qed
      also have "... = word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word) * 
                                    sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word ) div 2 ^ 31)"
        unfolding sint_sbintrunc' by auto
      finally show ?thesis
        unfolding `(word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) =
                   (word_of_int ( bl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word)`
        by auto
    qed
    hence "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
           Fixed (word_of_int (sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word ) * 
                       sint (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word) div 2 ^ 31))"
      by auto
    also have "... = Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))))) * Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))))"
      using times_fixed.abs_eq[where xa="word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw') :: (1 + 31) word" and 
                                      x="word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw') :: (1 + 31) word", symmetric]
      by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
    proof -
      have "type_of (wline_of tw' COMMON (i + 2 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
      hence "length (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence "Fixed (word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw')) =  
             Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))))))"
        unfolding sbl_to_bin_alt_def by auto
      also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word)"
        unfolding word_sbin.Abs_norm by auto
      also have "... = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
      proof -
        have "wline_of tw' COMMON (i + 2 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))"
          using `type_of (wline_of tw' COMMON (i + 2 *clk_period - 2)) = Lty Sig 32` 
          by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
        thus ?thesis
          using fixed_of_sval.simps unfolding of_bl_def by smt
      qed
      finally have "Fixed (word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
        by auto
    
      have "type_of (wline_of tw' COMMON (i + 2 * clk_period - 2)) = Lty Sig 32"
        using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
        using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
      hence "length (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))) = 32"
        by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
      hence "Fixed (word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw')) =  
             Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))))))"
        unfolding sbl_to_bin_alt_def by auto
      also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))) :: (1 + 31) word)"
        unfolding word_sbin.Abs_norm by auto
      also have "... = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
      proof -
        have "wline_of tw' COMMON (i + 2 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))"
          using `type_of (wline_of tw' COMMON (i + 2 *clk_period - 2)) = Lty Sig 32` 
          by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
        thus ?thesis
          using fixed_of_sval.simps unfolding of_bl_def by smt
      qed
      finally have "Fixed (word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
        by auto
      thus ?thesis
        using \<open>Fixed (word_of_int (sbl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))))) = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))\<close> by auto
    qed  
    finally have "Fixed (word_of_int (sbl_to_bin (nths (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1)) {1 .. 32})) :: (1 + 31) word) = 
                  fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
      by auto  
    thus ?thesis
      using `?lhs5 = ?rhs5`
            `Fixed (word_of_int (bin_of NEXT_COMMON at_time i + 2 * clk_period on tw') :: (1 + 31) word) =  Fixed (word_of_int ( ((sbl_to_bin (nths  (lof_wline tw' SQUARE_TEMP (i + 2 * clk_period - 1))  {1 .. 32})))))`
            `wline_of tw' NEXT_COMMON (i + 2 * clk_period) = wline_of tw' COMMON (i + 2 * clk_period + 1)`          
            `wline_of tw' COMMON (i + 2 * clk_period + 1) = wline_of tw' COMMON (i + 3 * clk_period - 2)`
      by auto
  qed
  have "wline_of tw' COMMON (i + 2 * clk_period - 2) = wline_of tw' COMMON (i + 2 * clk_period - 1)"
  proof - 
    have "Inv_core (i + 2 * clk_period - 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence **: "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using posedge by blast
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto
    have "(i + 2 * clk_period - 2) mod clk_period \<noteq> 0"
    proof -
      have "i + 1 * clk_period < i + 2 * clk_period - 2"
        using assms by (auto)
      moreover have "i + 2 * clk_period - 2 < i + 6 * clk_period"
        using assms by auto
      ultimately show ?thesis
        by (metis \<open>(i + 2 * clk_period) mod clk_period = 0\<close> assms(3) assms(4) diff_add_0 diff_add_inverse 
        dvd_add_left_iff dvd_antisym less_imp_add_positive less_nat_zero_code mod_0_imp_dvd nat_diff_split_asm numeral_plus_numeral semiring_norm(5))
    qed
    hence "\<not> is_posedge2 (snd tw') CLK (i + 2 * clk_period - 2)"
      using ** by auto
    thus ?thesis
      using `Inv_core (i + 2 * clk_period - 1, snd tw')`  unfolding inv_reg_alt_def comp_def snd_conv fst_conv 
      using diff_diff_left nat_1_add_1 by presburger
  qed

  have "bin_of NEXT_ACCUM at_time (i + 2 * clk_period) on tw' = 0"
  proof -
    have "Inv_core (i + 2 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE`
      unfolding inv_naccum_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "word_of_int (bin_of NEXT_ACCUM at_time (i + 2 * clk_period) on tw') = (0 :: (1 + 31) word)"
    by auto
  hence "Fixed (word_of_int (bin_of NEXT_ACCUM at_time (i + 2 * clk_period) on tw') :: (1 + 31) word) = (0 :: (1, 31) fixed)"
    apply transfer' unfolding word_ubin.norm_eq_iff by auto
  have "Fixed (word_of_int (bin_of NEXT_ACCUM at_time i + 2 * clk_period on tw') :: (1 + 31) word) = fixed_of_sval (wline_of tw' NEXT_ACCUM (i + 2 * clk_period))"
    (is "?lhs6 = ?rhs6")
  proof -
    have "type_of (wline_of tw' NEXT_ACCUM (i + 2 * clk_period)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' NEXT_ACCUM (i + 2 * clk_period))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "?lhs6 = Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' NEXT_ACCUM (i + 2 * clk_period))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' NEXT_ACCUM (i + 2 * clk_period)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' NEXT_ACCUM (i + 2 * clk_period))"
    proof -
      have "wline_of tw' NEXT_ACCUM (i + 2 * clk_period) = Lv Sig (lval_of (wline_of tw' NEXT_ACCUM (i + 2 * clk_period)))"
        using `type_of (wline_of tw' NEXT_ACCUM (i + 2 * clk_period)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  hence "fixed_of_sval (wline_of tw' NEXT_ACCUM (i + 2 * clk_period)) = (0 :: (1, 31) fixed)"
    using `Fixed (word_of_int (bin_of NEXT_ACCUM at_time (i + 2 * clk_period) on tw') :: (1 + 31) word) = (0 :: (1, 31) fixed)` by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2)) = (0 :: (1, 31) fixed)"
    using \<open>wline_of tw' ACCUM (i + 2 * clk_period + 1) = wline_of tw' ACCUM (i + 3 * clk_period -
    2)\<close> \<open>wline_of tw' NEXT_ACCUM (i + 2 * clk_period) = wline_of tw' ACCUM (i + 2 * clk_period + 1)\<close>
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 4 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * 0))))"
    using `fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * (approx_div_fact 4 + 
         fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) * fixed_of_sval (wline_of tw' ACCUM (i + 3 * clk_period - 2))))))`
    using \<open>fixed_of_sval (wline_of tw' COMMON (i + 3 * clk_period - 2)) = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))\<close> 
    by auto
  hence "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 4 + 0))))"  
    unfolding fixed_mult_zero by auto
  
  have "wline_of tw' COMMON (i + 1 * clk_period + 1) = wline_of tw' COMMON (i + 2 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 1 * clk_period + 1) = wline_of tw' ACCUM  (i + 2 * clk_period - 2)"
  proof -
    have a: "fst tw \<le> i + 1 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 1 * clk_period + 1 \<le> i + 2 * clk_period - 2"
      using assms by (auto simp add: field_simps)
    have c: "i + 2 * clk_period - 2 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 1 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 1 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 2 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 1 * clk_period = m1 * clk_period"
        using `(i + 1 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 2 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 2 * clk_period = m2 * clk_period"
          using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 2 * clk_period - (i + 1 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 1 * clk_period = m1 * clk_period` `i + 2  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 2 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 1 * clk_period + 1 \<le> n" and "n \<le> i + 2 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 1 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 2 * clk_period - 1` `i + 2 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' COMMON (i + 1 * clk_period + 1) = wline_of tw' COMMON (i + 2 * clk_period - 2)"
   and "wline_of tw' ACCUM  (i + 1 * clk_period + 1) = wline_of tw' ACCUM (i + 2 * clk_period - 2)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  have "Inv_core (i + 1 * clk_period + 1, snd tw')"
    using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
    by auto
  have "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
  proof -
    have "is_posedge2 w CLK (i + 2 * clk_period)"
      using `is_posedge2 (snd tw') CLK (i + 2 * clk_period)` 
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
    hence "is_posedge2 w CLK (i + 2 * clk_period - clk_period)"
      using assms by auto
    hence "is_posedge2 w CLK (i + 1 * clk_period)"
      by (auto simp add:field_simps)
    thus "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
      unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
      by auto
  qed
  have "wline_of tw' RST (i + 1 * clk_period) = Bv False"
  proof (rule ccontr)
    assume "wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False" 
    have "wityping \<Gamma> (snd tw')"
      using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] 
      using conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
    hence "type_of (wline_of tw' RST (i + 1 * clk_period)) = Bty"
      unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
    hence "wline_of tw' RST (i + 1 * clk_period) = Bv True"
      using `wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
    hence "wline_of tw' STATE (i + 1 * clk_period + 1) = V_INIT"
      using  `Inv_core ((i + 1 * clk_period + 1, snd tw'))` `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` unfolding inv_reg_alt_def
      comp_def snd_conv fst_conv by auto
    with `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE` show False
      by auto
  qed
  have "wline_of tw' NEXT_COMMON (i + 1 * clk_period) = wline_of tw' COMMON (i + 1 * clk_period + 1)"
    and "wline_of tw' NEXT_ACCUM  (i + 1 * clk_period) = wline_of tw' ACCUM (i + 1 * clk_period + 1)"
    using `Inv_core (i + 1 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` `wline_of tw' RST (i + 1 * clk_period) = Bv False`
    unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto

  \<comment> \<open> obtaining state\<close>
  have "wline_of tw' STATE (i + 1 * clk_period + 1) = wline_of tw' STATE (i + 2 * clk_period - 1)"
  proof -
    have a: "fst tw \<le> i + 1 * clk_period + 1"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] by auto
    have b: "i + 1 * clk_period + 1 \<le> i + 2 * clk_period - 1"
      using assms by (auto simp add: field_simps)
    have c: "i + 2 * clk_period - 1 \<le> i + 7 * clk_period + 1"
      by auto
    have *: "\<And>k. type_of (wline_of (0, w) CLK k) = Bty"
      using `wityping \<Gamma> w` cosine_locale_axioms
      unfolding wityping_def wtyping_def comp_def snd_conv cosine_locale_def by auto
    have "\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0"
      using * posedge_only_if_mod_clk_period[OF assms(3) _ assms(5-7)] assms(4) by auto
    hence "\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0"
      using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    hence "(i + 7 * clk_period) mod clk_period = 0"
      using \<open>\<And>m. is_posedge2 (snd tw') CLK m \<Longrightarrow> m mod clk_period = 0\<close> assms by blast
    hence "(i + 2 * clk_period) mod clk_period = 0"
      by auto      
    hence "(i + 1 * clk_period) mod clk_period = 0"
      by auto      
    have d: "\<And>k. i + 1 * clk_period + 1 \<le> k \<Longrightarrow> k \<le> i + 2 * clk_period - 1 \<Longrightarrow> \<not> is_posedge2 (snd tw') CLK k"
    proof -
      fix n 
      obtain m1 where "i + 1 * clk_period = m1 * clk_period"
        using `(i + 1 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
      have "i + 2 * clk_period = (m1 + 1) * clk_period"
      proof -
        obtain m2 where "i + 2 * clk_period = m2 * clk_period"
          using `(i + 2 * clk_period) mod clk_period = 0`  by (metis Nat.add_0_right div_mult_mod_eq)
        have "i + 2 * clk_period - (i + 1 * clk_period) = clk_period"
          by (auto simp add: field_simps)
        hence "m2 * clk_period - m1 * clk_period = clk_period"
          using `i + 1 * clk_period = m1 * clk_period` `i + 2  * clk_period = m2 * clk_period`
          by auto
        hence "(m2 - m1) * clk_period = clk_period"
          by (auto simp add: algebra_simps)
        hence "m2 = Suc m1"
          using `3 < clk_period ` by auto
        thus ?thesis
          using Suc_eq_plus1 \<open>i + 2 * clk_period = m2 * clk_period\<close> by presburger
      qed
      assume "i + 1 * clk_period + 1 \<le> n" and "n \<le> i + 2 * clk_period - 1"
      hence "m1 * clk_period < n"
        using `i + 1 * clk_period = m1 * clk_period`  by linarith
      have "n mod clk_period \<noteq> 0"
      proof -        
        have "n div clk_period = m1"
          apply (rule Misc_Arithmetic.sdl)
          using \<open>m1 * clk_period < n\<close>  apply (simp add: mult.commute) 
          using `n \<le> i + 2 * clk_period - 1` `i + 2 * clk_period = (m1 + 1) * clk_period` assms 
          by (auto simp add: field_simps)
        hence "n = m1 * clk_period + n mod clk_period"
          by auto
        moreover have "n mod clk_period < clk_period"
          using assms by (auto intro!: mod_less_divisor)
        ultimately show ?thesis
          using \<open>m1 * clk_period < n\<close> by linarith
      qed
      hence "\<not> is_posedge2 w CLK n"
        using \<open>\<And>m. is_posedge2 w CLK m \<Longrightarrow> m mod clk_period = 0\<close> by auto
      thus "\<not> is_posedge2 (snd tw') CLK n"
        using \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close> by auto
    qed
    show "wline_of tw' STATE (i + 1 * clk_period + 1) = wline_of tw' STATE (i + 2 * clk_period - 1)"
      using registers_unchanged_no_rising_edge[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)` a b c d]
      by auto
  qed
  hence "wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE"
    using `wline_of tw' STATE (i + 2 * clk_period - 1) = V_PRE`
    by auto
  have "wline_of tw' NEXT_STATE (i + 1 * clk_period) = wline_of tw' STATE (i + 1 * clk_period + 1)"
  proof -
    have "Inv_core (i + 1 * clk_period + 1, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] by auto  
    moreover have "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
    proof -
      have "is_posedge2 w CLK (i + 2 * clk_period)"
        using `is_posedge2 (snd tw') CLK (i + 2 * clk_period)`
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
      hence "is_posedge2 w CLK (i + 2 * clk_period - clk_period)"
        using assms by auto
      hence "is_posedge2 w CLK (i + 1 * clk_period)"
        by (auto simp add:field_simps)
      thus "is_posedge2 (snd tw') CLK (i + 1 * clk_period)"
        unfolding \<open>\<And>k. wline_of (0, w) CLK k = wline_of tw' CLK k\<close>[unfolded comp_def snd_conv] 
        by auto
    qed
    moreover have "wline_of tw' RST (i + 1 * clk_period) = Bv False"
    proof (rule ccontr)
      assume "wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False" 
      have "wityping \<Gamma> (snd tw')"
        using `wityping \<Gamma> (snd tw)` world_sim_fin_preserves_wityping[OF 0] conc_stmt_wf_arch cwt_arch nonneg_delay_conc_architecture by blast
      hence "type_of (wline_of tw' RST (i + 1 * clk_period)) = Bty"
        unfolding wityping_def wtyping_def using cosine_locale_axioms unfolding cosine_locale_def by auto
      hence "wline_of tw' RST (i + 1 * clk_period) = Bv True"
        using `wline_of tw' RST (i + 1 * clk_period) \<noteq> Bv False` type_of_bty_cases by blast
      hence "wline_of tw' STATE (i + 1 * clk_period + 1) = V_INIT"
        using `Inv_core (i + 1 * clk_period + 1, snd tw')` `is_posedge2 (snd tw') CLK (i + 1 * clk_period)` unfolding inv_reg_alt_def
        comp_def snd_conv fst_conv  by auto
      with `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE` show False
        using \<open>wline_of tw' OUTREADY_REG (get_time tw') = Bv True\<close> by auto
    qed
    ultimately show ?thesis      
      unfolding inv_reg_alt_def comp_def snd_conv fst_conv by auto
  qed
  hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE" 
    using `wline_of tw' STATE (i + 1 * clk_period + 1) = V_PRE` 
    using \<open>bl_to_bin (lval_of (wline_of tw' COUNTER (i + 3 *clk_period - 1))) = 3\<close> \<open>wline_of tw' COUNTER (i + 2 * clk_period + 1) = wline_of tw' COUNTER (i + 3 *clk_period - 1)\<close> \<open>wline_of tw' NEXT_COUNTER (i + 2 * clk_period) = wline_of tw' COUNTER (i + 2 * clk_period + 1)\<close> 
    by auto
  have "wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1))"
  proof (rule ccontr)
    have "Inv_core (i + 1 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    hence inv:"inv_nstate (i + 1 * clk_period, snd tw')"
      by auto
    assume "\<not> (wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1)))"
    hence *: "(wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<Longrightarrow> \<not> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1)))" 
      by auto
    let ?state = "wline_of tw' STATE (i + 1 * clk_period - 1)"
    consider "?state = V_INIT" | "?state = V_WAIT" | "?state = V_PROC" | "?state = V_POST" 
      | "?state \<noteq> V_INIT \<and> ?state \<noteq> V_WAIT \<and> ?state \<noteq> V_PRE \<and> ?state \<noteq> V_PROC \<and> ?state \<noteq> V_POST"
      | "?state = V_PRE"
      by auto
    thus False
    proof (cases)
      case 1
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 2
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') INREADY (i + 1 * clk_period - 1))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 3
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv 
        by (cases "bval_of (snd (snd tw') CTR_NEQ_0 (i + clk_period - Suc 0))") auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 4
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 5
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    next
      case 6
      hence "wline_of tw' NEXT_STATE (i + 1 * clk_period) \<noteq> V_PRE"
        using inv * unfolding inv_nstate_alt_def comp_def snd_conv fst_conv by auto
      then show ?thesis 
        using `wline_of tw' NEXT_STATE (i + 1 * clk_period) = V_PRE`
        by auto
    qed
  qed

  have "bin_of NEXT_COMMON at_time (i + clk_period) on tw' = bin_of INPUT at_time (i + clk_period - 1) on tw'"
  proof -
    have "Inv_core (i + 1 * clk_period, snd tw')"
      using fst_init_sim2[OF `init_sim2 (0, w) architecture tw`] assms Inv_core_everywhere_strict[OF 0 `Inv tw` `wityping \<Gamma> (snd tw)`] 
      by auto
    thus ?thesis
      using `wline_of tw' STATE (i + 1 * clk_period - 1) = V_WAIT \<and> bval_of (wline_of tw' INREADY (i + 1 * clk_period - 1))`
      unfolding inv_ncommon_alt_def comp_def snd_conv fst_conv by auto
  qed
  
  hence "bin_of COMMON at_time (i + 2 * clk_period - 2) on tw' = bin_of INPUT at_time (i + clk_period - 1) on tw'"
    using \<open>wline_of tw' COMMON (i + 1 * clk_period + 1) = wline_of tw' COMMON (i + 2 * clk_period -
    2)\<close> \<open>wline_of tw' NEXT_COMMON (i + 1 * clk_period) = wline_of tw' COMMON (i + 1 * clk_period +
    1)\<close> by auto
  moreover have "Fixed (word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw') :: (1 + 31) word) =  fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
  proof -
    have "type_of (wline_of tw' COMMON (i + 2 * clk_period - 2)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of COMMON at_time i + 2 * clk_period - 2 on tw') :: (1 + 31) word)  = 
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2))"
    proof -
      have "wline_of tw' COMMON (i + 2 * clk_period - 2) = Lv Sig (lval_of (wline_of tw' COMMON (i + 2 * clk_period - 2)))"
        using `type_of (wline_of tw' COMMON (i + 2 * clk_period - 2)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  moreover have "Fixed (word_of_int (bin_of INPUT at_time i + clk_period - 1 on tw') :: (1 + 31) word) =  fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))"
  proof -
    have "type_of (wline_of tw' INPUT (i + clk_period - 1)) = Lty Sig 32"
      using `wityping \<Gamma> (snd tw')` unfolding wityping_def wtyping_def
      using cosine_locale_axioms unfolding cosine_locale_def comp_def by auto
    hence "length (lval_of (wline_of tw' INPUT (i + clk_period - 1))) = 32"
      by (metis (no_types, lifting) ty.distinct(1) ty.inject type_of.elims val.sel(3))
    hence "Fixed (word_of_int (bin_of INPUT at_time i + clk_period - 1 on tw') :: (1 + 31) word)  = 
           Fixed (word_of_int (sbintrunc (LENGTH((1+31)) - 1) (bl_to_bin (lval_of (wline_of tw' INPUT (i + clk_period - 1))))))"
      unfolding sbl_to_bin_alt_def by auto
    also have "... = Fixed (word_of_int (bl_to_bin (lval_of (wline_of tw' INPUT (i + clk_period - 1)))))"
      unfolding word_sbin.Abs_norm  by auto
    also have "... = fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))"
    proof -
      have "wline_of tw' INPUT (i + clk_period - 1) = Lv Sig (lval_of (wline_of tw' INPUT (i + clk_period - 1)))"
        using `type_of (wline_of tw' INPUT (i + clk_period - 1)) = Lty Sig 32` 
        by (metis (no_types, hide_lams) ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2) val.sel(3))
      thus ?thesis
        using fixed_of_sval.simps unfolding of_bl_def by smt
    qed
    finally show ?thesis
      by auto
  qed
  ultimately have "(fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) :: (1, 31) fixed) = fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))"
    by auto
  hence final: "fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         (fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1)) * fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))) * (approx_div_fact 1 + 
         (fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1)) * fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))) * (approx_div_fact 2 + 
         (fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1)) * fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))) * (approx_div_fact 3 + 
         (fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1)) * fixed_of_sval (wline_of tw' INPUT (i + clk_period - 1))) * (approx_div_fact 4 + 0))))"
    using `fixed_of_sval (wline_of tw' ACCUM (fst tw')) = approx_div_fact 0 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 1 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 2 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 3 + 
         fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * fixed_of_sval (wline_of tw' COMMON (i + 2 * clk_period - 2)) * (approx_div_fact 4 + 0))))`
    by auto
  have "[0::nat ..<5] = [0, 1, 2, 3, 4]"
    by eval
  show ?thesis
    unfolding `[0::nat ..<5] = [0, 1, 2, 3, 4]` 
    using approx_div_fact.simps[symmetric] final 
    by (auto simp add: fixed_mult_zero) 
qed

end