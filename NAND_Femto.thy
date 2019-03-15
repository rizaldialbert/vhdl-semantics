(*
 * Copyright 2018, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Femto
imports
  Femto_VHDL Femto_VHDL_Executable
begin

lemma trans_post_empty_trans_upd:
  "trans_post sig v def empty_trans t dly = 
    (if v \<noteq> def then Poly_Mapping.update (t + dly) [sig \<mapsto> v] empty_trans else empty_trans)"
proof transfer'
  fix sig :: "'a" 
  fix v def t dly
  have "post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def \<or> \<not> post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    by auto
  moreover
  { assume nec: "post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    hence "v \<noteq> def"
      by (metis post_necessary_raw_correctness zero_fun_def zero_option_def)
    hence "(if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then trans_post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_nonstrict sig (\<lambda>k. 0) (t + dly)) = 
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using nec unfolding trans_post_raw_def zero_upd zero_map fun_upd_def by (auto) }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    hence "v = def"
      by (simp add: post_necessary_raw_correctness zero_fun_def zero_option_def)
    hence "(if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then trans_post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_nonstrict sig (\<lambda>k. 0) (t + dly)) = 
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using not_nec by (auto simp add: preempt_nonstrict_def zero_fun_def zero_option_def) }
  ultimately show " (if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then trans_post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_nonstrict sig (\<lambda>k. 0) (t + dly)) =
       (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))" by auto
qed

lemma get_trans_trans_upd_cancel:
  "get_trans (Poly_Mapping.update n [sig \<mapsto> v] \<tau>) n = [sig \<mapsto> v]"
  by (transfer) (auto)

lemma is_stable_empty_trans:
  "is_stable n empty_trans now sig v"
  unfolding is_stable_correct
  by (auto simp add:zero_map)

definition nand :: "sig conc_stmt" where
  "nand = process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1"

theorem
  assumes "10, 0, def_state, {A}, 0 \<turnstile> <nand, empty_trans> \<leadsto> beh"
  shows "get_trans beh 1 C = Some True"
  using assms
proof (cases)
  case (1 \<tau>')
  have base: "0 , def_state , {A} , 0 \<turnstile> <nand , rem_curr_trans 0 empty_trans> \<longrightarrow>\<^sub>c
                                                                         (Poly_Mapping.update 1 [C \<mapsto> True] 0)"
    unfolding nand_def by (auto simp add: is_stable_empty_trans inr_post_def  trans_post_empty_trans_upd)
  hence \<tau>'_def: "\<tau>' = (Poly_Mapping.update 1 [C \<mapsto> True] 0)"
    using 1 by auto
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(Poly_Mapping.update 1 [C \<mapsto> True] 0) \<noteq> empty_trans"
      by (transfer, metis fun_upd_same option.simps(3) zero_map)
    moreover have "(LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (transfer, rule Least_equality)
      show "dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) \<noteq> {}"
          by auto }
      thus "\<And>y::nat. dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  have ns: "next_state 0 \<tau>' def_state = def_state (C := True)" (is "?lhs = ?rhs")
    by (metis \<tau>'_def dom_eq_singleton_conv fun_upd_same get_trans_trans_upd_cancel next_state_def nt
              o_apply option.sel override_on_emptyset override_on_insert')
  have ne: "next_event 0 \<tau>' def_state = {C}"
    unfolding nt next_event_def
    by (smt "1"(3) Collect_cong base dom_empty dom_fun_upd fun_upd_comp fun_upd_idem fun_upd_same
            get_trans_trans_upd_cancel insert_absorb insert_iff insert_not_empty map_upd_nonempty
            option.sel singleton_conv)
  have nb: "add_to_beh def_state 0 0 1 =
       Poly_Mapping.update 0 (Some o def_state) 0" (is "_ = ?beh'")
    unfolding add_to_beh_def by auto
  define beh2 :: "(nat \<Rightarrow>\<^sub>0 sig \<Rightarrow> bool option)" where "beh2 = ?beh'"
  hence snd_cyc: "10, 1, def_state (C := True), {C} , beh2 \<turnstile> <nand , \<tau>'> \<leadsto> beh"
    using 1 nt ns ne nb by metis
  thus "get_trans beh 1 C = Some True"
  proof (cases)
    case (1 \<tau>'')
    have t''_def: "\<tau>'' = 0"
      unfolding nand_def
      using 1(3) unfolding nand_def  apply (auto simp add: \<tau>'_def rem_curr_trans_def)
      by (transfer', auto)
    have nt2: "next_time 1 0 = 1"
      by auto
    moreover have "next_state 1 \<tau>'' (def_state(C := True)) = def_state (C := True)"
      unfolding next_state_def Let_def t''_def nt2 by auto
    moreover have "next_event 1 \<tau>'' (def_state(C := True)) = {}"
      unfolding next_event_def Let_def t''_def nt2 by (auto simp add: zero_map)
    moreover have "add_to_beh (def_state(C := True)) beh2 1 (next_time 1 \<tau>'') = beh2"
      unfolding add_to_beh_def t''_def nt2 by (auto simp add: override_coeffs_open_right_same_idx)
    moreover have "rem_curr_trans 1 (Poly_Mapping.update 1 [C \<mapsto> True] empty_trans) = 0"
      unfolding rem_curr_trans_def by (transfer, auto)
    ultimately have "(10, 1, def_state (C := True), {}, beh2 \<turnstile> <nand, \<tau>''> \<leadsto> beh)"
      using 1(4) using t''_def by auto
    then show ?thesis
    proof (cases)
      case (1 \<tau>')
      then show ?thesis unfolding quiet_def t''_def by auto
    next
      case 2
      then show ?thesis unfolding quiet_def t''_def
        by (transfer, auto)
    next
      case 3
      then show ?thesis by auto
    qed
  next
    case 2
    then show ?thesis by (auto simp add:quiet_def)
  next
    case 3
    then show ?thesis by auto
  qed
next
  case 2
  then show ?thesis unfolding quiet_def by auto
next
  case 3
  then show ?thesis by auto
qed

values  "{lookup beh 1 C | beh. b_simulate_fin 10 0 def_state {A} 0 nand empty_trans beh}"

value "get_trans (functional_simulate_fin 10 0 def_state {A} 0 nand empty_trans) 1 C"

theorem
  "get_trans (functional_simulate_fin 10 0 def_state {A} 0 nand empty_trans) 1 C = Some True"
  by eval

value "get_trans (functional_simulate 10 nand) 1 C"

value "signal_of (functional_simulate 10 nand) C 100"

value [code] "to_signal (to_transaction2 (empty_trans :: nat \<Rightarrow>\<^sub>0 sig \<rightharpoonup> bool)) A 123456"

definition nand2 :: "sig conc_stmt" where
  "nand2 = process {A, B} : Bcomp
                            (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)
                            (Bassign_trans A (Bnand (Bsig A) (Bsig B)) 3)"

definition "test_trans = Pm_fmap (fmap_of_list [(4::nat, [A \<mapsto> True, B \<mapsto> True])])"
definition  "test2 = functional_simulate_fin 2 0 def_state {A, B, C} 0 nand2 test_trans"

value [code] "to_transaction2 test2 C"

definition nand3 :: "sig conc_stmt" where
  "nand3 = process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1"

\<comment> \<open>Specific lemmas about @{term "nand"} and @{term "nand3"}\<close>

lemma nand_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand) \<tau> = \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(3) singletonD)

lemma nand3_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand3) \<tau> = \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand3_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(2) singletonD)

lemma nand_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand) \<tau> = \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using assms unfolding nand_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand_does_not_modify_AB not_le)

lemma nand3_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand3) \<tau> = \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using assms unfolding nand3_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand3_does_not_modify_AB not_le)

lemma seq_nand_does_not_modify_signals_AB:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand) \<tau> = \<tau>'"
  assumes "s \<noteq> C"
  shows "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
  using b_seq_does_not_modify_signals[OF assms(1-2)] assms(3) unfolding nand_def
  by auto

lemma seq_nand3_does_not_modify_signals_AB:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand3) \<tau> = \<tau>'"
  assumes "s \<noteq> C"
  shows "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
  using b_seq_does_not_modify_signals[OF assms(1-2)] assms(3) unfolding nand3_def
  by auto

lemma nand_does_not_modify_signals_AB:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> nand \<tau> = \<tau>'"
  assumes "s \<noteq> C"
  shows "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
  using b_conc_exec_does_not_modify_signals[OF assms(1-2)] assms(3)
  unfolding nand_def by auto

lemma nand3_does_not_modify_signals_AB:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> nand3 \<tau> = \<tau>'"
  assumes "s \<noteq> C"
  shows "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
  using b_conc_exec_does_not_modify_signals[OF assms(1-2)] assms(3)
  unfolding nand3_def by auto

lemma maxtime_maxtime_bigstep:
  assumes "maxtime, maxtime, \<sigma>, \<gamma>, \<theta> \<turnstile> <nand3, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n < maxtime \<Longrightarrow> lookup \<tau> n = 0"
  assumes "\<And>n. maxtime \<le> n \<Longrightarrow> lookup \<theta> n = 0"
  shows "beh = Poly_Mapping.update maxtime (Some o \<sigma>) \<theta>"
proof (cases "quiet \<tau> \<gamma>")
  case True
  then show ?thesis
    using case_quiesce[OF _ True assms(1)] by auto
next
  case False
  then obtain \<tau>' where cyc: "maxtime, \<sigma>, \<gamma>, \<theta> \<turnstile> <nand3, rem_curr_trans maxtime \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and
    big: "maxtime, next_time maxtime \<tau>', next_state maxtime \<tau>' \<sigma>, next_event maxtime \<tau>' \<sigma>,
                        add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>') \<turnstile> <nand3, \<tau>'> \<leadsto> beh"
    using case_bau2[OF _ False assms(1)] by auto
  have 0: "\<And>n. n < maxtime \<Longrightarrow> lookup \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF assms(2)] cyc by auto
  have "maxtime \<le> next_time maxtime \<tau>'"
    using next_time_at_least[OF 0, of "maxtime"] by auto

  define \<sigma>2 where "\<sigma>2 = next_state maxtime \<tau>' \<sigma>"
  define \<gamma>2 where "\<gamma>2 = next_event maxtime \<tau>' \<sigma>"
  hence big2: "maxtime, next_time maxtime \<tau>', \<sigma>2, \<gamma>2, add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>')
                                                                              \<turnstile> <nand3, \<tau>'> \<leadsto> beh"
    using big unfolding  \<sigma>2_def \<gamma>2_def by auto
  have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0"
    by auto
  moreover
  { assume "\<tau>' = 0"
    hence ntime: "next_time maxtime \<tau>' = maxtime"
      by auto
    hence ntheta: "add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>') = \<theta>"
      by auto
    have "\<sigma>2 = \<sigma>"
      unfolding `\<tau>' = 0` \<sigma>2_def next_state_def by auto
    hence "\<gamma>2 = {}"
      unfolding `\<tau>' = 0` \<gamma>2_def next_event_def by (simp add: domIff zero_map)
    hence "quiet \<tau>' \<gamma>2"
      using `\<tau>' = 0` `\<gamma>2 = {}` unfolding quiet_def by auto
    have "beh = Poly_Mapping.update maxtime (Some \<circ> \<sigma>) \<theta>"
      using case_quiesce[OF _ `quiet \<tau>' \<gamma>2` big2] `\<sigma>2 = \<sigma>`
      unfolding ntime ntheta by auto }
  moreover
  { assume "\<tau>' \<noteq> 0"
    have "disjnt \<gamma> {A, B} \<or> \<not> disjnt \<gamma> {A, B}"
      by auto
    moreover
    { assume "disjnt \<gamma> {A, B}"
      hence "\<tau>' = rem_curr_trans maxtime \<tau>"
        using cyc unfolding nand3_def by auto
      hence "lookup \<tau>' maxtime = 0"
        unfolding rem_curr_trans_def by (simp add: lookup_update)
      have max_less: "maxtime < next_time maxtime \<tau>'"
      proof (rule ccontr)
        assume "\<not> maxtime < next_time maxtime \<tau>'" hence "maxtime = next_time maxtime \<tau>'"
          using `maxtime \<le> next_time maxtime \<tau>'` by auto
        hence least: "(LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) = maxtime"
          using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger
        have "\<exists>n. lookup \<tau>' n \<noteq> 0"
          using `\<tau>' \<noteq> 0` using aux by blast
        hence 0: "\<exists>n. dom (lookup \<tau>' n) \<noteq> {}"
        proof -
          { assume "dom (0::sig \<Rightarrow> bool option) \<noteq> {}"
            then have ?thesis
              by (metis \<open>get_trans \<tau>' maxtime = 0\<close>) }
          then show ?thesis
            using \<open>\<exists>n. get_trans \<tau>' n \<noteq> 0\<close> by force
        qed
        have "dom (lookup \<tau>' maxtime) \<noteq> {}"
          using LeastI_ex[OF 0] unfolding least by auto
        with `lookup \<tau>' maxtime = 0` show "False"
          by (metis dom_eq_empty_conv zero_map)
      qed }

    moreover
    { assume "\<not> disjnt \<gamma> {A, B}"
      hence \<tau>'_def: "\<tau>' = trans_post C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) (rem_curr_trans maxtime \<tau>) maxtime 1"
        using cyc unfolding nand3_def by auto
      hence "lookup \<tau>' maxtime = 0"
        unfolding rem_curr_trans_def by (transfer', auto simp add: trans_post_raw_def preempt_nonstrict_def)
      have "maxtime < next_time maxtime \<tau>'"
      proof (rule ccontr)
        assume "\<not> maxtime < next_time maxtime \<tau>'" hence "maxtime = next_time maxtime \<tau>'"
          using `maxtime \<le> next_time maxtime \<tau>'` by auto  
        hence least: "(LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) = maxtime"
          using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger        
        have "\<exists>n. lookup \<tau>' n \<noteq> 0"
          using `\<tau>' \<noteq> 0` using aux by blast
        hence 0: "\<exists>n. dom (lookup \<tau>' n) \<noteq> {}"
        proof -
          { assume "dom (0::sig \<Rightarrow> bool option) \<noteq> {}"
            then have ?thesis
              by (metis \<open>get_trans \<tau>' maxtime = 0\<close>) }
          then show ?thesis
            using \<open>\<exists>n. get_trans \<tau>' n \<noteq> 0\<close> by force
        qed
        have "dom (lookup \<tau>' maxtime) \<noteq> {}"
          using LeastI_ex[OF 0] unfolding least by auto
        with `lookup \<tau>' maxtime = 0` show "False"
          by (metis dom_eq_empty_conv zero_map)
      qed }
    ultimately have max_less: "maxtime < next_time maxtime \<tau>'"
      by auto

    hence new_beh: "add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>') =  Poly_Mapping.update maxtime (Some o \<sigma>) \<theta>"
      unfolding add_to_beh_def by auto
    have "beh =
      override_lookups_on_open_left (Poly_Mapping.update maxtime (Some \<circ> \<sigma>) \<theta>) 0 maxtime
                                                                           (next_time maxtime \<tau>')"
      using max_less case_timesup[OF _ big2] unfolding new_beh by auto
    also have "... = Poly_Mapping.update maxtime (Some \<circ> \<sigma>) \<theta>"
      using assms(3) apply transfer' unfolding override_on_def by auto
    finally have "beh = Poly_Mapping.update maxtime (Some \<circ> \<sigma>) \<theta>"
      by auto }
  ultimately show "beh = Poly_Mapping.update maxtime (Some \<circ> \<sigma>) \<theta>"
    by auto
qed

lemma t_strictly_increasing:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <nand3, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "t < next_time t \<tau>'"
proof (cases "A \<in> \<gamma> \<or> B \<in> \<gamma>")
  case True
  hence \<tau>'_def: "\<tau>' = trans_post C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) (rem_curr_trans t \<tau>) t 1"
    using assms unfolding nand3_def by auto
  hence "lookup \<tau>' t = 0"
    unfolding rem_curr_trans_def by (transfer', auto simp add: trans_post_raw_def preempt_nonstrict_def)
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least assms b_conc_exec_rem_curr_trans_preserve_trans_removal by blast
  show "t < next_time t \<tau>'"
  proof (rule ccontr)
    assume "\<not> t < next_time t \<tau>'" hence "t = next_time t \<tau>'"
      using `t \<le> next_time t \<tau>'` by auto  
    hence least: "(LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) = t"
      using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger        
    have "\<exists>n. lookup \<tau>' n \<noteq> 0"
      using `\<tau>' \<noteq> 0` using aux by blast
    hence 0: "\<exists>n. dom (lookup \<tau>' n) \<noteq> {}"
    proof -
      { assume "dom (0::sig \<Rightarrow> bool option) \<noteq> {}"
        then have ?thesis
          by (metis \<open>get_trans \<tau>' t = 0\<close>) }
      then show ?thesis
        using \<open>\<exists>n. get_trans \<tau>' n \<noteq> 0\<close> by force
    qed
    have "dom (lookup \<tau>' t) \<noteq> {}"
      using LeastI_ex[OF 0] unfolding least by auto
    with `lookup \<tau>' t = 0` show "False"
      by (metis dom_eq_empty_conv zero_map)
  qed 
next
  case False
  hence \<tau>'_def: "\<tau>' = rem_curr_trans t \<tau>"
    using assms unfolding nand3_def by auto
  have "lookup \<tau>' t = 0"
    unfolding \<tau>'_def rem_curr_trans_def by transfer' auto
  have "next_time t \<tau>' = (LEAST n. dom (lookup \<tau>' n) \<noteq> {})"
    using assms(3) unfolding next_time_def by auto
  also have " (LEAST n. dom (lookup \<tau>' n) \<noteq> {}) \<noteq> t"
  proof (rule ccontr)
    have asm: "\<exists>x. dom (get_trans \<tau>' x) \<noteq> {}"
      using `\<tau>' \<noteq> 0` by (metis \<open>get_trans \<tau>' t = 0\<close> aux empty_iff map_add_subsumed1 map_add_subsumed2
       map_le_def)
    assume "\<not> (LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) \<noteq> t"
    hence "dom (lookup \<tau>' t) \<noteq> {}"
      using LeastI_ex[where P="\<lambda>x. dom (lookup \<tau>' x) \<noteq> {}"] asm by auto
    hence "lookup \<tau>' t \<noteq> 0"
      by (metis dom_eq_empty_conv zero_map)
    with `lookup \<tau>' t = 0` show "False" by auto
  qed
  finally have "next_time t \<tau>' \<noteq> t"
    by auto
  have *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF assms(2)] assms(1) by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  with `next_time t \<tau>' \<noteq> t` show ?thesis by auto
qed

lemma beh_res2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "t \<le> maxtime" and "cs = nand3"
  assumes "\<And>s. s \<in> dom (lookup \<tau> t) \<Longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
  assumes "\<And>n. t \<le> n \<Longrightarrow> lookup \<theta> n = 0"
  shows "\<And>n. n \<le> t \<Longrightarrow> lookup (Poly_Mapping.update t (Some o \<sigma>) \<theta>) n = lookup beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF 1(7)] 1(3) by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0" by auto
  moreover
  { assume "\<tau>' = 0"
    hence "next_time t \<tau>' = t"
      unfolding next_time_def by auto
    moreover have " next_state t \<tau>' \<sigma> = \<sigma>"
      unfolding next_state_def Let_def `next_time t \<tau>' = t` `\<tau>' = 0` override_on_def
      apply transfer' unfolding zero_map by auto
    moreover hence "next_event t \<tau>' \<sigma> = {}"
      unfolding next_event_def next_state_def Let_def `next_time t \<tau>' = t` `\<tau>' = 0`
      by (auto simp add: zero_map)
    moreover hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>"
      unfolding `next_time t \<tau>' = t` by auto
    ultimately have " maxtime, t, \<sigma>, {}, \<theta> \<turnstile> <cs, \<tau>'> \<leadsto> res"
      using ` maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs , \<tau>'> \<leadsto> res`
      by auto
    hence "res = Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>"
      using case_quiesce[OF `t \<le> maxtime`] unfolding `\<tau>' = 0` quiet_def
      by (simp add: \<open>\<And>res cs \<theta> \<tau> \<sigma> \<gamma>. \<lbrakk>quiet \<tau> \<gamma>; maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res\<rbrakk>
                                            \<Longrightarrow> res = Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>\<close> quiet_def)
    hence ?case
      by transfer' auto }
  moreover
  { assume "\<tau>' \<noteq> 0"
    hence "t < next_time t \<tau>'"
      using t_strictly_increasing[OF _ 1(7) `\<tau>' \<noteq> 0`] 1(3) unfolding `cs = nand3` by auto
    hence ind1: "n \<le> next_time t \<tau>'"
      using `n \<le> t` by auto
    have ind2: "(\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans \<tau>' n = 0) "
      by (simp add: next_time_at_least2)
    have h1: "\<And>s. s \<in> dom (get_trans \<tau>' (next_time t \<tau>')) \<Longrightarrow>
                                          next_state t \<tau>' \<sigma> s = the (get_trans \<tau>' (next_time t \<tau>') s)"
      unfolding next_state_def Let_def by auto
    have "next_time t \<tau>' \<le> maxtime \<or> maxtime < next_time t \<tau>'"
      by auto
    moreover
    { assume ind3: "next_time t \<tau>' \<le> maxtime"
      have h2: "\<And>n. next_time t \<tau>' \<le> n \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
        unfolding add_to_beh_def
        by (metis (mono_tags) "1.prems"(6) \<open>t < next_time t \<tau>'\<close> \<open>t \<le> next_time t \<tau>'\<close> leD lookup_update order_trans)
      have "get_trans (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))) n = get_trans res n"
        using 1(5)[OF ind1 ind2 ind3 `cs = nand3` h1 h2]  by blast
      hence ?case
        using `n \<le> t` `t < next_time t \<tau>'` unfolding add_to_beh_def
      proof -
        assume a1: "get_trans (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (if t < next_time t \<tau>' then Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> else \<theta>)) n = get_trans res n"
        have "next_time t \<tau>' \<noteq> n"
          using \<open>n \<le> t\<close> \<open>t < next_time t \<tau>'\<close> leD by blast
        then have "get_trans (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (if t < next_time t \<tau>' then Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> else \<theta>)) n = get_trans (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) n"
          by (simp add: \<open>t < next_time t \<tau>'\<close> lookup_update)
        then show ?thesis
          using a1 by presburger
      qed }
    moreover
    { assume "maxtime < next_time t \<tau>'"
      have "t < next_time t \<tau>'"
        using `t \<le> maxtime` `maxtime < next_time t \<tau>'` by auto
      have ?case
        using borderline_big_step[OF 1(4) 1(3) `t \<le> maxtime` `maxtime < next_time t \<tau>'` 1(11) _ ind1]
        `t < next_time t \<tau>'` unfolding add_to_beh_def  using nat_less_le by presburger }
    ultimately have ?case by auto }
  ultimately show ?case by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  show ?case
    using 2(3) by transfer' auto
next
  case (3 t maxtime \<theta> res \<sigma> \<gamma> cs \<tau>)
  then show ?case by auto
qed

(* lemma beh_and_res_same_until_now2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "cs = nand3"
  shows "\<And>i. i \<le> t \<Longrightarrow> i \<le> maxtime \<Longrightarrow> lookup (Poly_Mapping.update t (Some o \<sigma>) \<theta>) i = lookup res i"
proof -
  fix i
  assume "i \<le> maxtime"
  assume "i \<le> t"
  hence "i < t \<or> i = t" by auto
  moreover
  { assume "i < t"
    have "get_trans \<theta> i = get_trans res i"
      using beh_and_res_same_until_now[OF assms(1-2) `i < t` `i \<le> maxtime`] by auto
    moreover have "lookup (Poly_Mapping.update t (Some o \<sigma>) \<theta>) i = lookup \<theta> i"
      using `i < t` by transfer' auto
    ultimately have " get_trans (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) i = get_trans res i"
      by auto }
  moreover
  { assume "i = t" *)
                       


theorem nand3_correctness_ind:
  assumes "maxtime, t, \<sigma>, \<gamma>, beh \<turnstile> <cs, ctrans> \<leadsto> res"
  assumes "cs = nand3" and "maxtime = Suc i"
  assumes "\<And>n. n < t \<Longrightarrow> lookup ctrans n = 0"
  assumes "\<And>s. s \<in> dom (lookup ctrans t) \<Longrightarrow> \<sigma> s = the (lookup ctrans t s)"
  assumes "\<And>n. t \<le> n \<Longrightarrow> lookup beh n = 0"
  assumes "t \<le> i" and "A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<Longrightarrow> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
  assumes "\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 ctrans C) n = 0"
  shows "signal_of2 def res C (Suc i) \<longleftrightarrow> \<not> (signal_of2 (\<sigma> A) ctrans A i \<and> signal_of2 (\<sigma> B) ctrans B i)"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have "t \<le> Suc i"
    using `t \<le> i` by auto
  have *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
    using "1.hyps"(3) "1.prems"(3) b_conc_exec_rem_curr_trans_preserve_trans_removal by blast
  hence **: "\<And>n. dom (get_trans \<tau>' n) \<noteq> {} \<Longrightarrow> t \<le> n"
    using zero_map by force
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *] by auto
  have h0: "\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`]
    `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'`  by (simp add: next_time_at_least2)

  have h1: "\<And>s. s \<in> dom (get_trans \<tau>' (next_time t \<tau>')) \<Longrightarrow>
                                        next_state t \<tau>' \<sigma> s = the (get_trans \<tau>' (next_time t \<tau>') s)"
    unfolding next_state_def Let_def by auto
  have h2: "\<And>n. next_time t \<tau>' \<le> n \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
    unfolding add_to_beh_def
  proof -
    fix n :: nat
    assume a1: "next_time t \<tau>' \<le> n"
    then have f2: "t \<le> n"
      by (meson \<open>t \<le> next_time t \<tau>'\<close> order_trans)
    { assume "n \<noteq> t"
      then have "get_trans (if t < next_time t \<tau>' then Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> else \<theta>) n = 0 \<or> next_time t \<tau>' \<le> t"
        using f2 by (simp add: "1.prems"(5) lookup_update) }
    then show "get_trans (if t < next_time t \<tau>' then Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> else \<theta>) n = 0"
      using a1 "1.prems"(5) \<open>t \<le> next_time t \<tau>'\<close> by fastforce
  qed
  { assume asm: "A \<notin> next_event t \<tau>' \<sigma> \<and> B \<notin> next_event t \<tau>' \<sigma> "
    have sigA: "next_state t \<tau>' \<sigma> A = \<sigma> A" and sigB: "next_state t \<tau>' \<sigma> B = \<sigma> B"
      using next_state_fixed_point asm by metis+
    hence "next_event t \<tau>' \<sigma> = {C} \<or> next_event t \<tau>' \<sigma> = {}"
    proof -
      have "\<And>S Sa. B \<in> S \<or> S \<subseteq> insert C Sa \<or> A \<in> S"
        by (metis (full_types) insertI1 sig.exhaust subset_eq)
      then show ?thesis
        by (meson \<open>A \<notin> next_event t \<tau>' \<sigma> \<and> B \<notin> next_event t \<tau>' \<sigma>\<close> subset_singletonD)
    qed
    moreover
    { assume "next_event t \<tau>' \<sigma> = {}"
      hence "C \<notin> next_event t \<tau>' \<sigma>"
        by auto
      hence sigC: "next_state t \<tau>' \<sigma> C = \<sigma> C" using next_state_fixed_point[OF `C \<notin> next_event t \<tau>' \<sigma>`]
        by auto
      have " A \<notin> \<gamma> \<and> B \<notin> \<gamma>  \<or> \<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )" by auto
      moreover
      { assume " A \<notin> \<gamma> \<and> B \<notin> \<gamma> "
        hence " \<sigma> C = (\<not> (\<sigma> A \<and> \<sigma> B))"
          using `A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<Longrightarrow>  \<sigma> C = (\<not> (\<sigma> A \<and> \<sigma> B))` by auto
        hence " next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
          using sigA sigB sigC by auto }
      moreover
      { assume "\<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )"
        hence \<tau>'_def: "\<tau>' = trans_post C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) (rem_curr_trans t \<tau>) t 1"
          using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        have "(\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)) \<or>  (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
          by auto
        moreover 
        { assume "\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          have "to_transaction2 (rem_curr_trans t \<tau>) C = 0"
            using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
            unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def 
            by (metis fun_upd_apply nat_neq_iff zero_fun_def)
          hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
            unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by (metis zero_option_def)
          hence "post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          proof -
            have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and> lookup (rem_curr_trans t \<tau>) i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                    (\<forall>j>i. j \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) j C = None))"
              using `to_transaction2 (rem_curr_trans t \<tau>) C = 0` unfolding rem_curr_trans_def
              apply transfer' unfolding to_trans_raw2_def  by (metis option.simps(3) zero_option_def)
            thus ?thesis
              using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
              `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)` by simp
          qed
          hence "\<tau>' \<noteq> 0"
            using trans_post_imply_neq_map_empty 
            by (simp add: trans_post_imply_neq_map_empty \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
          hence "next_time t \<tau>' = (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = t + 1"
          proof (rule Least_equality)
            show "dom (get_trans \<tau>' (t + 1)) \<noteq> {}"
              using `post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
              unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def 
              by (auto simp add: zero_fun_def zero_option_def)
          next
            have "lookup \<tau>' t = 0"
              unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
              by auto
            thus "\<And>y. dom (get_trans \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
              using **
              by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
          qed
          finally have "next_time t \<tau>' = t + 1"
            by auto
          moreover have "lookup \<tau>' (t + 1) C = Some (\<not> (\<sigma> A \<and> \<sigma> B))"
            using `post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_def
            by (auto split:option.split simp add: zero_fun_def zero_option_def)
          ultimately have "next_state t \<tau>' \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
            unfolding next_state_def Let_def  by (simp add: domIff)
          hence " next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
            using sigA sigB sigC by auto }
        moreover
        { assume "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          hence " next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
            using sigA sigB sigC by auto }
        ultimately have " next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
          by auto }
      ultimately have "next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
        by auto }
    moreover
    { assume "next_event t \<tau>' \<sigma> = {C}"
      hence "C \<in> dom (lookup \<tau>' (next_time t \<tau>'))"
        unfolding next_event_def Let_def by transfer' auto
      have " A \<notin> \<gamma> \<and> B \<notin> \<gamma>  \<or> \<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )" by auto
      moreover
      { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
        hence "\<tau>' = rem_curr_trans t \<tau>"
          using ` t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        with `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` and `t \<le> next_time t \<tau>'`
        have "C \<notin> dom (lookup \<tau>' (next_time t \<tau>'))"
          unfolding rem_curr_trans_def next_time_def apply transfer' unfolding to_trans_raw2_def
          by (metis (no_types, lifting) antisym_conv2 domIff fun_upd_apply zero_fun_def zero_map)
        with `C \<in> dom (lookup \<tau>' (next_time t \<tau>'))` have "False" by auto
        hence "next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
          by auto }
      moreover
      { assume "\<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )"
        hence \<tau>'_def: "\<tau>' = trans_post C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) (rem_curr_trans t \<tau>) t 1"
          using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        have "\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
        proof (rule ccontr)
          assume "\<not> (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))" hence "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)" by auto
          moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
            using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
            unfolding rem_curr_trans_def by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_option_def )
          ultimately have "\<not> post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
            using post_necessary_raw_correctness by auto
          hence "to_transaction2 \<tau>' C = 0"
            using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)`
            using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
            unfolding \<tau>'_def rem_curr_trans_def 
            apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def zero_fun_def zero_option_def zero_map
          proof (rule ext)
            fix tb :: nat and \<tau>'' :: "nat \<Rightarrow> sig \<Rightarrow> bool option" and \<sigma>'' :: "sig \<Rightarrow> bool" and n :: nat
            assume a1: "\<not> post_necessary_raw 0 (\<tau>''(tb := Map.empty)) tb C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<sigma>'' C)"
            assume a2: "\<And>n. n < tb \<Longrightarrow> \<tau>'' n = Map.empty"
            assume a3: "\<forall>i\<ge>tb. i \<le> tb + 1 \<longrightarrow> (\<tau>''(tb := Map.empty)) i C = None"
            { assume "(if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C \<noteq> None"
              have "\<not> tb + 1 < n \<and> \<not> n < tb \<or> (if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C = None"
                using a2 by simp
              then have "(if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C = None"
                using a3 by fastforce }
            then show "(if post_necessary_raw (1-1) (\<tau>''(tb := Map.empty)) tb C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<sigma>'' C) then trans_post_raw C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<tau>''(tb := Map.empty)) (tb + 1) else (\<lambda>n. if tb + 1 \<le> n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n)) n C = None"
              using a1 by force
          qed
          with `C \<in> dom (lookup \<tau>' (next_time t \<tau>'))` have "lookup \<tau>' (next_time t \<tau>') C \<noteq> 0"
            by (metis domIff fun_upd_same zero_fun_def zero_upd)
          hence "lookup (to_transaction2 \<tau>' C) (next_time t \<tau>') \<noteq> 0"
            unfolding next_time_def apply transfer' unfolding to_trans_raw2_def by auto
          with `to_transaction2 \<tau>' C = 0` show False
            unfolding next_time_def apply transfer' unfolding to_trans_raw2_def  by meson
        qed
        have "to_transaction2 (rem_curr_trans t \<tau>) C = 0"
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def 
          by (metis fun_upd_apply nat_neq_iff zero_fun_def)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by (metis zero_option_def)
        hence "post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
        proof -
          have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and> lookup (rem_curr_trans t \<tau>) i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                  (\<forall>j>i. j \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) j C = None))"
            using `to_transaction2 (rem_curr_trans t \<tau>) C = 0` unfolding rem_curr_trans_def
            apply transfer' unfolding to_trans_raw2_def  by (metis option.simps(3) zero_option_def)
          thus ?thesis
            using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)` by simp
        qed
        hence "\<tau>' \<noteq> 0"
          by (simp add: trans_post_imply_neq_map_empty \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
        hence "next_time t \<tau>' = (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom (get_trans \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def 
            by (auto simp add: zero_fun_def zero_option_def)
        next
          have "lookup \<tau>' t = 0"
            unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
            by auto
          thus "\<And>y. dom (get_trans \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            using **
            by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        moreover have "lookup \<tau>' (t + 1) C = Some (\<not> (\<sigma> A \<and> \<sigma> B))"
          using `post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
          unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def
          by (auto split:option.split simp add: zero_fun_def zero_option_def)
        ultimately have "next_state t \<tau>' \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          unfolding next_state_def Let_def  by (simp add: domIff)
        hence " next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
          using sigA sigB by auto }
      ultimately have " next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
        by auto }
    ultimately have "next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
      by auto }
  note h3 = this

  have h4: "\<And>n. next_time t \<tau>' < n \<Longrightarrow> lookup (to_transaction2 \<tau>' C) n = 0"
  proof -
    fix n
    assume "next_time t \<tau>' < n"
    have "A \<in> \<gamma> \<or> B \<in> \<gamma> \<or> (A \<notin> \<gamma> \<and> B \<notin> \<gamma>)"
      by auto
    moreover
    { assume "A \<in> \<gamma> \<or> B \<in> \<gamma>"
      hence \<tau>'_def: "\<tau>' = trans_post C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) (rem_curr_trans t \<tau>) t 1"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
        nand3_def by auto
      have "(\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)) \<or> (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        by auto
      moreover
      { assume "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
        moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding rem_curr_trans_def by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_option_def )
        ultimately have "\<not> post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          using post_necessary_raw_correctness by auto        
        hence "to_transaction2 \<tau>' C = 0"
          using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)`
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding \<tau>'_def rem_curr_trans_def 
          apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def zero_fun_def zero_option_def zero_map
        proof (rule ext)
          fix tb :: nat and \<tau>'' :: "nat \<Rightarrow> sig \<Rightarrow> bool option" and \<sigma>'' :: "sig \<Rightarrow> bool" and n :: nat
          assume a1: "\<not> post_necessary_raw 0 (\<tau>''(tb := Map.empty)) tb C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<sigma>'' C)"
          assume a2: "\<And>n. n < tb \<Longrightarrow> \<tau>'' n = Map.empty"
          assume a3: "\<forall>i\<ge>tb. i \<le> tb + 1 \<longrightarrow> (\<tau>''(tb := Map.empty)) i C = None"
          { assume "(if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C \<noteq> None"
            have "\<not> tb + 1 < n \<and> \<not> n < tb \<or> (if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C = None"
              using a2 by simp
            then have "(if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C = None"
              using a3 by fastforce }
          then show "(if post_necessary_raw (1-1) (\<tau>''(tb := Map.empty)) tb C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<sigma>'' C) then trans_post_raw C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<tau>''(tb := Map.empty)) (tb + 1) else (\<lambda>n. if tb + 1 \<le> n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n)) n C = None"
            using a1 by force
        qed
        hence "lookup (to_transaction2 \<tau>' C) n = 0"
          by auto }
      moreover
      { assume "(\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        have "to_transaction2 (rem_curr_trans t \<tau>) C = 0"
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def 
          by (metis fun_upd_apply nat_neq_iff zero_fun_def)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by (metis zero_option_def)
        hence "post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
        proof -
          have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and> lookup (rem_curr_trans t \<tau>) i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                  (\<forall>j>i. j \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) j C = None))"
            using `to_transaction2 (rem_curr_trans t \<tau>) C = 0` unfolding rem_curr_trans_def
            apply transfer' unfolding to_trans_raw2_def  by (metis option.simps(3) zero_option_def)
          thus ?thesis
            using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)` by simp
        qed        
        hence "\<tau>' \<noteq> 0"
          using trans_post_imply_neq_map_empty by (simp add: trans_post_imply_neq_map_empty 
          \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
        hence "next_time t \<tau>' = (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom (get_trans \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def 
            by (auto simp add: zero_fun_def zero_option_def)
        next
          have "lookup \<tau>' t = 0"
            unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
            by auto
          thus "\<And>y. dom (get_trans \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            using **
            by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        hence "lookup (to_transaction2 \<tau>' C) n = 0"
          using `next_time t \<tau>' < n` unfolding \<tau>'_def rem_curr_trans_def next_time_def apply transfer'
          unfolding trans_post_raw_def to_trans_raw2_def preempt_nonstrict_def
          by (simp add: zero_option_def) }
      ultimately have "lookup (to_transaction2 \<tau>' C) n = 0"
        by auto } 
    moreover
    { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
      hence \<tau>'_def: "\<tau>' = rem_curr_trans t \<tau>"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      hence "lookup (to_transaction2 \<tau>' C) n = 0"
        using `t \<le> next_time t \<tau>'` `next_time t \<tau>' < n` `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0`
        by (metis leD le_less_trans trans_value_same_except_at_removed) }
    ultimately show "lookup (to_transaction2 \<tau>' C) n = 0"
      by auto
  qed

  have h5: "\<And>n. n < t \<Longrightarrow> get_trans (rem_curr_trans t \<tau>) n = 0"
    using `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0` unfolding rem_curr_trans_def by transfer' auto
  have IH: " next_time t \<tau>' \<le> i \<Longrightarrow>
             signal_of2 def res C (Suc i) =
            (\<not> (signal_of2 (next_state t \<tau>' \<sigma> A) \<tau>' A i \<and> signal_of2 (next_state t \<tau>' \<sigma> B) \<tau>' B i))"
    using 1(5)[OF `cs = nand3` `maxtime = Suc i` h0 h1 h2 _ h3 h4] by auto
  have "i < next_time t \<tau>' \<or> next_time t \<tau>' \<le> i"
    by auto
  moreover
  { assume "i < next_time t \<tau>'"
    have "t \<noteq> next_time t \<tau>'"
    proof (rule ccontr)
      assume "\<not> t \<noteq> next_time t \<tau>'" hence "t = next_time t \<tau>'" by auto
      hence "i < t"  using `i < next_time t \<tau>'` by auto
      with `t \<le> i` show False by auto
    qed

    have "A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<or> A \<in> \<gamma> \<or> B \<in> \<gamma>" by auto
    moreover
    { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
      hence \<tau>'_def: "\<tau>' = rem_curr_trans t \<tau>"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      have "signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B"
        using signal_of2_init'[OF `t \<le> i`, of "\<tau>" _ "\<sigma>"] `i < next_time t \<tau>'` 1(9) 1(8)
        unfolding \<tau>'_def by auto
      note no_trans_c = 1(13)
      hence "\<And>n. t \<le> n \<Longrightarrow> lookup (to_transaction2 \<tau>' C) n = 0"
        unfolding \<tau>'_def unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
        by (simp add: zero_fun_def)
      note next_big_step = 1(4)
      have "next_time t \<tau>' \<le> maxtime \<or> maxtime < next_time t \<tau>'" by auto
      moreover
      { assume "next_time t \<tau>' \<le> maxtime"
        hence pre: "\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = get_trans res n"
          using   beh_res[OF next_big_step h0] by auto
        hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow> lookup (Poly_Mapping.update t (Some o \<sigma>) \<theta>) n = lookup res n"
          using`t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` unfolding add_to_beh_def by auto
        hence *: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
            get_trans (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))) n = get_trans res n"
          using beh_res2[OF next_big_step h0 `next_time t \<tau>' \<le> maxtime` `cs = nand3` h1 h2 ]
          by auto
        have "Suc i \<le> next_time t \<tau>'"
          using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` by auto
        hence "Suc i < next_time t \<tau>' \<or> Suc i = next_time t \<tau>'"
          by auto
        moreover have "\<not> Suc i < next_time t \<tau>'"
          using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` `maxtime = Suc i` by linarith
        ultimately have "Suc i = next_time t \<tau>'"
          by auto
        hence **: "signal_of2 def res C (Suc i) =
               signal_of2 def (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))) C (Suc i)"
          using signal_of2_lookup_same[OF * `Suc i \<le> next_time t \<tau>'`] by auto
        define t' where "t' = next_time t \<tau>'"
        define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
        define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
        hence "signal_of2 def res C (Suc i) =
               signal_of2 def (Poly_Mapping.update t' (Some o \<sigma>') \<theta>') C (Suc i)"
          unfolding t'_def \<sigma>'_def \<theta>'_def using ** by auto
        also have "... = \<sigma>' C"
        proof -
          have "next_time t \<tau>' \<le> Suc i"
            using `Suc i = next_time t \<tau>'` by auto
          hence "inf_time (to_transaction2 (Poly_Mapping.update t' (\<lambda>x. Some (\<sigma>' x)) \<theta>')) C (Suc i) = Some t'"
            using inf_time_update[OF h2 _ `next_time t \<tau>' \<le> Suc i`, of "\<sigma>'"] unfolding \<theta>'_def t'_def comp_def
            by blast
          thus ?thesis
            unfolding to_signal2_def comp_def
            by (simp add: lookup_update to_trans_raw2_def to_transaction2.rep_eq)
        qed
        finally have "signal_of2 def res C (Suc i) = \<sigma>' C"
          by auto
        also have "... = \<sigma> C"
        proof -
          have "C \<notin> dom (lookup (rem_curr_trans t \<tau>) (i + 1))"
            using 1(13) `t \<le> Suc i`
            unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
            by (auto simp add: zero_map zero_option_def)
          moreover have *: "(next_time t (rem_curr_trans t \<tau>)) = i + 1"
            using `Suc i = next_time t \<tau>'` unfolding \<tau>'_def by auto
          ultimately show ?thesis
            unfolding \<sigma>'_def next_state_def \<tau>'_def * Let_def by auto
        qed
        finally have "signal_of2 def res C (Suc i) = \<sigma> C"
          by auto
        moreover have "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          using 1(12) `A \<notin> \<gamma> \<and> B \<notin> \<gamma>` by auto
        ultimately have ?case
          using `signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B` by auto }
      moreover
      { assume "maxtime < next_time t \<tau>'"
        hence pre: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = get_trans res n"
          using borderline_big_step[OF next_big_step `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `t \<le> maxtime` `maxtime < next_time t \<tau>'` 1(10)]
          by auto
        have "Suc i < next_time t \<tau>'"
          using `maxtime = Suc i` `maxtime < next_time t \<tau>'` by auto
        hence "Suc i < next_time t (rem_curr_trans t \<tau>)"
          unfolding \<tau>'_def by auto
        hence "signal_of2 def res C (Suc i) =
               signal_of2 def (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) C (Suc i)"
          using signal_of2_lookup_same[OF pre] `Suc i < next_time t \<tau>'` by auto
        also have "... =  signal_of2 def (Poly_Mapping.update t (Some o \<sigma>) \<theta>) C (Suc i)"
          unfolding add_to_beh_def using `t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` by auto
        also have "... = \<sigma> C"
        proof -
          have "inf_time (to_transaction2 (Poly_Mapping.update t (Some o \<sigma>) \<theta>)) C (Suc i) = Some t"
            using inf_time_update[OF 1(10)]  using \<open>t \<le> Suc i\<close> by blast
          thus ?thesis
            unfolding to_signal2_def comp_def
            by (simp add: lookup_update to_trans_raw2_def to_transaction2.rep_eq)
        qed
        finally have "signal_of2 def res C (Suc i) = \<sigma> C"
          by auto
        moreover have "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          using 1(12) `A \<notin> \<gamma> \<and> B \<notin> \<gamma>` by auto
        ultimately have ?case
          using `signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B` by auto }
      ultimately have ?case by auto }
    moreover
    { assume "A \<in> \<gamma> \<or> B \<in> \<gamma>"
      hence \<tau>'_def: "\<tau>' = trans_post C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) (rem_curr_trans t \<tau>) t 1"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      have "(\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)) \<or> (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        by auto
      moreover
      { assume "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
        moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding rem_curr_trans_def by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_option_def )
        ultimately have "\<not> post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          using post_necessary_raw_correctness `\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` by auto        
        hence "to_transaction2 \<tau>' C = 0"
          using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)`
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding \<tau>'_def rem_curr_trans_def 
          apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def zero_fun_def zero_option_def zero_map
        proof (rule ext)
          fix tb :: nat and \<tau>'' :: "nat \<Rightarrow> sig \<Rightarrow> bool option" and \<sigma>'' :: "sig \<Rightarrow> bool" and n :: nat
          assume a1: "\<not> post_necessary_raw 0 (\<tau>''(tb := Map.empty)) tb C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<sigma>'' C)"
          assume a2: "\<And>n. n < tb \<Longrightarrow> \<tau>'' n = Map.empty"
          assume a3: "\<forall>i\<ge>tb. i \<le> tb + 1 \<longrightarrow> (\<tau>''(tb := Map.empty)) i C = None"
          { assume "(if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C \<noteq> None"
            have "\<not> tb + 1 < n \<and> \<not> n < tb \<or> (if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C = None"
              using a2 by simp
            then have "(if tb + 1 < n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n) C = None"
              using a3 by fastforce }
          then show "(if post_necessary_raw (1-1) (\<tau>''(tb := Map.empty)) tb C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<sigma>'' C) then trans_post_raw C (\<not> (\<sigma>'' A \<and> \<sigma>'' B)) (\<tau>''(tb := Map.empty)) (tb + 1) else (\<lambda>n. if tb + 1 \<le> n then ((\<tau>''(tb := Map.empty)) n)(C := None) else (\<tau>''(tb := Map.empty)) n)) n C = None"
            using a1 by force
        qed
        have "next_time t (rem_curr_trans t \<tau>) = next_time t \<tau>'"
        proof (cases "rem_curr_trans t \<tau> = 0")
          case True
          hence "next_time t (rem_curr_trans t \<tau>) = t"
            unfolding next_time_def by auto
          have "\<tau>' = 0"
            using True `to_transaction2 \<tau>' C = 0` `\<not> post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def rem_curr_trans_def 
            by (transfer', auto simp add: zero_map zero_fun_def zero_option_def to_trans_raw2_def preempt_nonstrict_def)
          hence "next_time t \<tau>' = t"
            by auto
          then show ?thesis 
            using `next_time t (rem_curr_trans t \<tau>) = t` by auto
        next
          case False
          hence "next_time t (rem_curr_trans t \<tau>) = (LEAST n. dom (get_trans (rem_curr_trans t \<tau>) n) \<noteq> {})"
            unfolding next_time_def by auto
          from `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          have lookC: "lookup (to_transaction2 (rem_curr_trans t \<tau>) C) = 0"
            unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def 
            by (rule ext, auto simp add: zero_map zero_fun_def zero_option_def nat_neq_iff)
          hence "lookup (to_transaction2 (rem_curr_trans t \<tau>) A) \<noteq> 0 \<or> 
                 lookup (to_transaction2 (rem_curr_trans t \<tau>) B) \<noteq> 0"
            using False unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
            unfolding zero_map zero_fun_def by (metis sig.exhaust)
          moreover have lookA: "lookup (to_transaction2 \<tau>' A) = lookup (to_transaction2 (rem_curr_trans t \<tau>) A)"
            unfolding \<tau>'_def  by (metis lookup_trans_post poly_mapping_eqI sig.simps(4))
          moreover have lookB: "lookup (to_transaction2 \<tau>' B) = lookup (to_transaction2 (rem_curr_trans t \<tau>) B)"
            unfolding \<tau>'_def  using lookup_trans_post by fastforce
          ultimately have "\<tau>' \<noteq> 0" unfolding rem_curr_trans_def  
            by (transfer', auto simp add: to_trans_raw2_def zero_map zero_fun_def zero_option_def)
          hence "next_time t \<tau>' = (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = (LEAST n. dom (lookup (rem_curr_trans t \<tau>) n) \<noteq> {})"
            apply (rule LEAST_ext)
            using lookA lookB lookC `to_transaction2 \<tau>' C = 0` unfolding rem_curr_trans_def
            apply transfer' unfolding to_trans_raw2_def zero_map zero_fun_def zero_option_def 
            by (smt Collect_empty_eq dom_def sig.exhaust)
          finally show ?thesis
            by (simp add: \<open>next_time t (rem_curr_trans t \<tau>) = (LEAST n. dom (get_trans (rem_curr_trans t \<tau>) n) \<noteq> {})\<close>)
        qed
        hence "signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B"
          using signal_of2_init'[OF `t \<le> i` _ _ `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`] 1(9)
          `i < next_time t \<tau>'` by auto
        note next_big_step = 1(4)
        have "next_time t \<tau>' \<le> maxtime \<or> maxtime < next_time t \<tau>'" by auto
        moreover
        { assume "next_time t \<tau>' \<le> maxtime"
          hence pre: "\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = get_trans res n"
            using   beh_res[OF next_big_step h0] by auto
          hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow> lookup (Poly_Mapping.update t (Some o \<sigma>) \<theta>) n = lookup res n"
            using`t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` unfolding add_to_beh_def by auto
          hence *: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
              get_trans (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))) n = get_trans res n"
            using beh_res2[OF next_big_step h0 `next_time t \<tau>' \<le> maxtime` `cs = nand3` h1 h2 ]
            by auto
          have "Suc i \<le> next_time t \<tau>'"
            using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` by auto
          hence "Suc i < next_time t \<tau>' \<or> Suc i = next_time t \<tau>'"
            by auto
          moreover have  "\<not> Suc i < next_time t \<tau>'"
            using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` `maxtime = Suc i` by auto
          ultimately have "Suc i = next_time t \<tau>'"
            by auto
          hence **: "signal_of2 def res C (Suc i) =
                 signal_of2 def (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))) C (Suc i)"
            using signal_of2_lookup_same[OF * `Suc i \<le> next_time t \<tau>'`] by auto
          define t' where "t' = next_time t \<tau>'"
          define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
          define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
          hence "signal_of2 def res C (Suc i) =
                 signal_of2 def (Poly_Mapping.update t' (Some o \<sigma>') \<theta>') C (Suc i)"
            unfolding t'_def \<sigma>'_def \<theta>'_def using ** by auto
          also have "... = \<sigma>' C"
          proof -
            have "next_time t \<tau>' \<le> Suc i"
              using `Suc i = next_time t \<tau>'` by auto
            hence "inf_time (to_transaction2 (Poly_Mapping.update t' (\<lambda>x. Some (\<sigma>' x)) \<theta>')) C (Suc i) = Some t'"
              using inf_time_update[OF h2 _ `next_time t \<tau>' \<le> Suc i`, of "\<sigma>'"] unfolding \<theta>'_def t'_def comp_def
              by blast
            thus ?thesis
              unfolding to_signal2_def comp_def
              by (simp add: lookup_update to_trans_raw2_def to_transaction2.rep_eq)
          qed
          finally have "signal_of2 def res C (Suc i) = \<sigma>' C"
            by auto
          also have "... = \<sigma> C"
          proof -
            have "\<And>n. C \<notin> dom (lookup \<tau>' n)"
              using `to_transaction2 \<tau>' C = 0`  apply transfer' unfolding to_trans_raw2_def
              by (metis domIff fun_upd_idem_iff zero_fun_def zero_upd)
            thus ?thesis
              unfolding \<sigma>'_def next_state_def \<tau>'_def Let_def  by simp
          qed
          finally have "signal_of2 def res C (Suc i) = \<sigma> C"
            by auto
          hence ?case
            using `signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B` 
            `\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` by auto }
        moreover
        { assume "maxtime < next_time t \<tau>'"
          hence pre: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = get_trans res n"
            using borderline_big_step[OF next_big_step `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `t \<le> maxtime` `maxtime < next_time t \<tau>'` 1(10)]
            by auto
          have "Suc i < next_time t \<tau>'"
            using `maxtime = Suc i` `maxtime < next_time t \<tau>'` by auto
          hence "signal_of2 def res C (Suc i) =
                 signal_of2 def (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) C (Suc i)"
            using signal_of2_lookup_same[OF pre] `Suc i < next_time t \<tau>'` by auto
          also have "... =  signal_of2 def (Poly_Mapping.update t (Some o \<sigma>) \<theta>) C (Suc i)"
            unfolding add_to_beh_def using `t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` by auto
          also have "... = \<sigma> C"
          proof -
            have "inf_time (to_transaction2 (Poly_Mapping.update t (Some o \<sigma>) \<theta>)) C (Suc i) = Some t"
              using inf_time_update[OF 1(10)]  using \<open>t \<le> Suc i\<close> by blast
            thus ?thesis
              unfolding to_signal2_def comp_def
              by (simp add: lookup_update to_trans_raw2_def to_transaction2.rep_eq)
          qed
          finally have "signal_of2 def res C (Suc i) = \<sigma> C"
            by auto
          hence ?case
            using `signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B` `\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            by auto }
        ultimately have ?case by auto }
      moreover
      { assume "(\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        have "to_transaction2 (rem_curr_trans t \<tau>) C = 0"
          using `\<And>n. t < n \<Longrightarrow> lookup (to_transaction2 \<tau> C) n = 0` `\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0`
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def 
          by (metis fun_upd_apply nat_neq_iff zero_fun_def)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)"
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by (metis zero_option_def)
        hence "post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
        proof -
          have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and> lookup (rem_curr_trans t \<tau>) i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                  (\<forall>j>i. j \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) j C = None))"
            using `to_transaction2 (rem_curr_trans t \<tau>) C = 0` unfolding rem_curr_trans_def
            apply transfer' unfolding to_trans_raw2_def  by (metis option.simps(3) zero_option_def)
          thus ?thesis
            using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> lookup (rem_curr_trans t \<tau>) i C = None)` by simp
        qed        
        hence "\<tau>' \<noteq> 0"
          using trans_post_imply_neq_map_empty 
          by (simp add: trans_post_imply_neq_map_empty \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
        hence "next_time t \<tau>' = (LEAST n. dom (lookup \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom (get_trans \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 (lookup (rem_curr_trans t \<tau>)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_def 
            by (auto simp add: zero_fun_def zero_option_def)
        next
          { fix y
            assume "\<not> t + 1 \<le> y" hence "y < t + 1" by auto
            hence "dom (get_trans \<tau>' y) = {}"
              using 1(8) unfolding \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
              by (auto simp add:zero_map) }
          thus "\<And>y. dom (get_trans \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            by auto
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        with `i < next_time t \<tau>'` have "i < t + 1" by auto
        with `t \<le> i` have "i = t" by auto
        hence "signal_of2 (\<sigma> A) \<tau> A i = signal_of2 (\<sigma> A) \<tau> A t"
          by auto
        also have "... = \<sigma> A"
        proof -
        consider "inf_time (to_transaction2 \<tau>) A t = None" |  ta where "inf_time (to_transaction2 \<tau>) A t = Some ta"
          by blast
        thus ?thesis
        proof (cases)
          case 1
          then show ?thesis unfolding to_signal2_def comp_def by auto
        next
          case 2
          have "t = ta"
          proof (rule ccontr)
            assume "t \<noteq> ta"
            with 2 have "ta \<le> t" by (auto dest!:inf_time_at_most)
            with `t \<noteq> ta` have "ta < t" by auto
            hence "lookup \<tau> ta = 0"
              using 1(8) by auto
            have "ta \<in> dom (lookup (to_transaction2 \<tau> A))"
              using inf_time_someE2[OF 2] by auto
            hence "lookup (to_transaction2 \<tau> A) ta \<noteq> 0"
              apply transfer' unfolding to_trans_raw2_def by (metis domIff zero_fun_def zero_map)
            hence "lookup \<tau> ta \<noteq> 0"
              apply transfer' unfolding to_trans_raw2_def by (metis zero_fun_def)
            thus False
              using `lookup \<tau> ta = 0` by auto
          qed
          hence "inf_time (to_transaction2 \<tau>) A t = Some t"
            using 2 by auto
          hence "t \<in> dom (lookup (to_transaction2 \<tau> A))"
            by (auto dest!:inf_time_someE2)
          hence "A \<in> dom (get_trans \<tau> t)"
            apply transfer' unfolding to_trans_raw2_def by auto
          hence "the (lookup (to_transaction2 \<tau> A) t) = \<sigma> A"
            using 1(9) apply transfer' unfolding to_trans_raw2_def by auto
          then show ?thesis
            using `inf_time (to_transaction2 \<tau>) A t = Some t` unfolding to_signal2_def comp_def
            by auto
        qed
        qed
        finally have sigA: "signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A"
          by auto
        have "signal_of2 (\<sigma> B) \<tau> B i = signal_of2 (\<sigma> B) \<tau> B t"
          using `i = t` by auto
        also have "... = \<sigma> B"
        proof -
        consider "inf_time (to_transaction2 \<tau>) B t = None" |  ta where "inf_time (to_transaction2 \<tau>) B t = Some ta"
          by blast
        thus ?thesis
        proof (cases)
          case 1
          then show ?thesis unfolding to_signal2_def comp_def by auto
        next
          case 2
          have "t = ta"
          proof (rule ccontr)
            assume "t \<noteq> ta"
            with 2 have "ta \<le> t" by (auto dest!:inf_time_at_most)
            with `t \<noteq> ta` have "ta < t" by auto
            hence "lookup \<tau> ta = 0"
              using 1(8) by auto
            have "ta \<in> dom (lookup (to_transaction2 \<tau> B))"
              using inf_time_someE2[OF 2] by auto
            hence "lookup (to_transaction2 \<tau> B) ta \<noteq> 0"
              apply transfer' unfolding to_trans_raw2_def by (metis domIff zero_fun_def zero_map)
            hence "lookup \<tau> ta \<noteq> 0"
              apply transfer' unfolding to_trans_raw2_def by (metis zero_fun_def)
            thus False
              using `lookup \<tau> ta = 0` by auto
          qed
          hence "inf_time (to_transaction2 \<tau>) B t = Some t"
            using 2 by auto
          hence "t \<in> dom (lookup (to_transaction2 \<tau> B))"
            by (auto dest!:inf_time_someE2)
          hence "B \<in> dom (get_trans \<tau> t)"
            apply transfer' unfolding to_trans_raw2_def by auto
          hence "the (lookup (to_transaction2 \<tau> B) t) = \<sigma> B"
            using 1(9) apply transfer' unfolding to_trans_raw2_def by auto
          then show ?thesis
            using `inf_time (to_transaction2 \<tau>) B t = Some t` unfolding to_signal2_def comp_def
            by auto
        qed
        qed
        finally have sigB: "signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B"
          by auto
        note next_big_step = 1(4)
        have "next_time t \<tau>' \<le> maxtime"
          using `next_time t \<tau>' = t + 1` `maxtime = Suc i` `i = t` by auto
        have "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
              get_trans (Poly_Mapping.update (next_time t \<tau>') (Some \<circ> next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))) n = get_trans res n"
          using beh_res2[OF next_big_step h0 `next_time t \<tau>' \<le> maxtime` `cs = nand3` h1 h2] by auto
        hence "lookup res (next_time t \<tau>') = (Some o next_state t \<tau>' \<sigma>)"
          by (metis lookup_update order_refl)
        hence "lookup res (Suc i) = (Some o next_state t \<tau>' \<sigma>)"
          using `next_time t \<tau>' = t + 1` `i = t` by auto
        hence "signal_of2 def res C (Suc i) = next_state t \<tau>' \<sigma> C"
          by (auto dest!: lookup_some_signal_of2)
        also have "... = (let m = get_trans \<tau>' (t + 1) in override_on \<sigma> (the o m) (dom m)) C"
          using `next_time t \<tau>' = t + 1` unfolding next_state_def by auto
        also have "... \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          unfolding Let_def \<tau>'_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
          by (auto split:option.split simp add: zero_fun_def zero_option_def override_on_def)
        finally have "signal_of2 def res C (Suc i) \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          by auto
        hence ?case
          using sigA sigB by auto }
      ultimately have ?case by auto }
    ultimately have ?case by auto }
  moreover
  { assume "next_time t \<tau>' \<le> i"
    with IH have IH': "signal_of2 def res C (Suc i) =
            (\<not> (signal_of2 (next_state t \<tau>' \<sigma> A) \<tau>' A i \<and> signal_of2 (next_state t \<tau>' \<sigma> B) \<tau>' B i))"
      by auto
    have Anot: "A \<notin> set (signals_from cs)"
      unfolding `cs = nand3` nand3_def by auto
    have "signal_of2 (next_state t \<tau>' \<sigma> A) \<tau>' A i  = signal_of2 (\<sigma> A) (rem_curr_trans t \<tau>) A i"
      using b_conc_exec_does_not_modify_signals2[OF h5 `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` Anot `next_time t \<tau>' \<le> i`]
      unfolding `cs = nand3` nand3_def by auto
    also have "... = signal_of2 (\<sigma> A) \<tau> A i"
    proof -
      obtain ta where  "inf_time (to_transaction2 \<tau>) A i = None \<or>  inf_time (to_transaction2 \<tau>) A i = Some ta"
        (is "?none \<or> ?some")
        using option.exhaust_sel by blast
      moreover
      { assume "?none"
        hence "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> A)). i < t"
          by (auto dest!:inf_time_noneE)
        moreover have "dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) A)) \<subseteq> dom (lookup (to_transaction2 \<tau> A))"
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
          by (simp add: Collect_mono dom_def zero_map)
        ultimately have "\<forall>t \<in> dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) A)). i < t"
          by (simp add: subset_iff)
        hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) A i = None"
          by (auto intro!: inf_time_noneI)
        hence ?thesis using `?none` unfolding to_signal2_def comp_def
          by auto }
      moreover
      { assume "?some"
        hence "ta \<in> dom (lookup (to_transaction2 \<tau> A))" and *: "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> A)). t \<le> i \<longrightarrow> t \<le> ta"
          using inf_time_someE2[OF `?some`] inf_time_someE[OF `?some`] by auto
        have "ta = t \<or> ta \<noteq> t" by auto
        moreover
        { assume "ta \<noteq> t"
          hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) A i = Some ta"
            using `?some` by (simp add: inf_time_rem_curr_trans)
          moreover have "lookup (to_transaction2 (rem_curr_trans t \<tau>) A) ta = lookup (to_transaction2 \<tau> A) ta"
            using `ta \<noteq> t` unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by auto
          ultimately have ?thesis using `?some` unfolding to_signal2_def comp_def
            using `ta \<noteq> t` by auto }
        moreover
        { assume "ta = t"
          hence "A \<in> dom (get_trans \<tau> t)"
            using `ta \<in> dom (lookup (to_transaction2 \<tau> A))` apply transfer' unfolding to_trans_raw2_def
            by auto
          have "\<forall>k \<in> dom (lookup (to_transaction2 \<tau> A)). k \<le> i \<longrightarrow> k \<le> t"
            using * `ta = t` by auto
          moreover have "dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) A)) \<subseteq> dom (lookup (to_transaction2 \<tau> A))"
            unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
            by (simp add: Collect_mono dom_def zero_map)
          moreover have "\<forall>k \<in> dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) A)). k > t"
            using 1(8) unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
            by (metis domIff fun_upd_apply nat_neq_iff zero_map)
          ultimately have "\<forall>k \<in> dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) A)). i < k"
            by (meson leD le_less_linear subset_iff)
          hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) A i = None"
            by (auto intro!: inf_time_noneI)
          hence "signal_of2 (\<sigma> A) (rem_curr_trans t \<tau>) A i = \<sigma> A"
            unfolding to_signal2_def comp_def by auto
          also have "... = the (lookup \<tau> t A)"
            using `\<And>s. s \<in> dom (get_trans \<tau> t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau> t s)` `A \<in> dom (get_trans \<tau> t)`
            by auto
          finally have ?thesis
            using `?some` `ta = t` unfolding to_signal2_def comp_def
            by (simp add: to_trans_raw2_def to_transaction2.rep_eq) }
        ultimately have ?thesis by auto }
      ultimately show ?thesis by auto
    qed
    finally have "signal_of2 (next_state t \<tau>' \<sigma> A) \<tau>' A i  = signal_of2 (\<sigma> A) \<tau> A i"
      by auto

    have Bnot: "B \<notin> set (signals_from cs)"
      unfolding `cs = nand3` nand3_def by auto
    have "signal_of2 (next_state t \<tau>' \<sigma> B) \<tau>' B i  = signal_of2 (\<sigma> B) (rem_curr_trans t \<tau>) B i"
      using b_conc_exec_does_not_modify_signals2[OF h5 `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'` Bnot `next_time t \<tau>' \<le> i`]
      unfolding `cs = nand3` nand3_def by auto
    also have "... = signal_of2 (\<sigma> B) \<tau> B i"
    proof -
      obtain ta where  "inf_time (to_transaction2 \<tau>) B i = None \<or>  inf_time (to_transaction2 \<tau>) B i = Some ta"
        (is "?none \<or> ?some")
        using option.exhaust_sel by blast
      moreover
      { assume "?none"
        hence "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> B)). i < t"
          by (auto dest!:inf_time_noneE)
        moreover have "dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) B)) \<subseteq> dom (lookup (to_transaction2 \<tau> B))"
          unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
          by (simp add: Collect_mono dom_def zero_map)
        ultimately have "\<forall>t \<in> dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) B)). i < t"
          by (simp add: subset_iff)
        hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) B i = None"
          by (auto intro!: inf_time_noneI)
        hence ?thesis using `?none` unfolding to_signal2_def comp_def
          by auto }
      moreover
      { assume "?some"
        hence "ta \<in> dom (lookup (to_transaction2 \<tau> B))" and *: "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> B)). t \<le> i \<longrightarrow> t \<le> ta"
          using inf_time_someE2[OF `?some`] inf_time_someE[OF `?some`] by auto
        have "ta = t \<or> ta \<noteq> t" by auto
        moreover
        { assume "ta \<noteq> t"
          hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) B i = Some ta"
            using `?some` by (simp add: inf_time_rem_curr_trans)
          moreover have "lookup (to_transaction2 (rem_curr_trans t \<tau>) B) ta = lookup (to_transaction2 \<tau> B) ta"
            using `ta \<noteq> t` unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by auto
          ultimately have ?thesis using `?some` unfolding to_signal2_def comp_def
            using `ta \<noteq> t` by auto }
        moreover
        { assume "ta = t"
          hence "B \<in> dom (get_trans \<tau> t)"
            using `ta \<in> dom (lookup (to_transaction2 \<tau> B))` apply transfer' unfolding to_trans_raw2_def
            by auto
          have "\<forall>k \<in> dom (lookup (to_transaction2 \<tau> B)). k \<le> i \<longrightarrow> k \<le> t"
            using * `ta = t` by auto
          moreover have "dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) B)) \<subseteq> dom (lookup (to_transaction2 \<tau> B))"
            unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
            by (simp add: Collect_mono dom_def zero_map)
          moreover have "\<forall>k \<in> dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) B)). k > t"
            using 1(8) unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def
            by (metis domIff fun_upd_apply nat_neq_iff zero_map)
          ultimately have "\<forall>k \<in> dom (lookup (to_transaction2 (rem_curr_trans t \<tau>) B)). i < k"
            by (meson leD le_less_linear subset_iff)
          hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) B i = None"
            by (auto intro!: inf_time_noneI)
          hence "signal_of2 (\<sigma> B) (rem_curr_trans t \<tau>) B i = \<sigma> B"
            unfolding to_signal2_def comp_def by auto
          also have "... = the (lookup \<tau> t B)"
            using `\<And>s. s \<in> dom (get_trans \<tau> t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau> t s)` `B \<in> dom (get_trans \<tau> t)`
            by auto
          finally have ?thesis
            using `?some` `ta = t` unfolding to_signal2_def comp_def
            by (simp add: to_trans_raw2_def to_transaction2.rep_eq) }
        ultimately have ?thesis by auto }
      ultimately show ?thesis by auto
    qed
    finally have "signal_of2 (next_state t \<tau>' \<sigma> B) \<tau>' B i  = signal_of2 (\<sigma> B) \<tau> B i"
      by auto
    hence ?case
      using `signal_of2 (next_state t \<tau>' \<sigma> A) \<tau>' A i  = signal_of2 (\<sigma> A) \<tau> A i` IH'
      by auto }
  ultimately show ?case by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  have "\<tau> = 0"
    using `quiet \<tau> \<gamma>` unfolding quiet_def by metis
  hence *: "signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A" and **: "signal_of2 (\<sigma> B) \<tau> B i = \<sigma> B"
    unfolding to_signal2_def by auto
  have "inf_time (to_transaction2 res) C (Suc i) = Some t"
    using inf_time_update[OF `\<And>n. t \<le> n \<Longrightarrow> get_trans \<theta> n = 0` ` Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> = res`
    `t \<le> maxtime`] unfolding  `maxtime = Suc i` by auto
  hence "signal_of2 def res C (Suc i) = \<sigma> C"
    using `Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> = res` unfolding to_signal2_def comp_def
    unfolding inf_time_def apply transfer' unfolding to_trans_raw2_def by auto
  moreover have "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
    using `quiet \<tau> \<gamma>` unfolding quiet_def  by (metis emptyE)
  ultimately show ?case
    using * ** 2(10)[OF `A \<notin> \<gamma> \<and> B \<notin> \<gamma>`]  by auto
next
  case (3 t maxtime \<theta> res \<sigma> \<gamma> cs \<tau>)
  then show ?case by auto
qed

lemma signal_of2_cong_neq_none_at_0:
  assumes "lookup (to_transaction2 \<tau> sig) 0 \<noteq> None"
  shows "signal_of2 def1 \<tau> sig i = signal_of2 def2 \<tau> sig i"
proof -
  have "inf_time (to_transaction2 \<tau>) sig i \<noteq> None"
  proof (rule ccontr)
    assume "\<not> inf_time (to_transaction2 \<tau>) sig i \<noteq> None"
    hence "inf_time (to_transaction2 \<tau>) sig i = None"
      by auto
    hence "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau> sig) k = 0"
      by (auto dest!: inf_time_noneE2)
    hence "lookup (to_transaction2 \<tau> sig) 0 = 0"
      by auto
    with assms show "False"
      by (simp add: zero_option_def)
  qed
  thus ?thesis
    unfolding to_signal2_def comp_def by auto
qed

theorem nand3_correctness:
  assumes "b_simulate2 (Suc i) nand3 \<tau> res"
  assumes "lookup (to_transaction2 \<tau> C) = 0"
  shows "signal_of2 def res C (Suc i) \<longleftrightarrow> \<not> (signal_of2 False \<tau> A i \<and> signal_of2 False \<tau> B i)"
proof (cases "lookup \<tau> 0 = 0")
  case True
  hence "init' 0 def_state {} 0 nand3 \<tau> = trans_post C True False \<tau> 0 1" (is "_ = ?\<tau>'")
    unfolding nand3_def by auto
  hence ntime: "next_time 0 ?\<tau>' = 1"
  proof -
    have "?\<tau>' \<noteq> 0"
      by (simp add: trans_post_imply_neq_map_empty)
    hence "next_time 0 ?\<tau>' = (LEAST n. dom (lookup ?\<tau>' n) \<noteq> {})"
      unfolding next_time_def by auto
    also have "... = 1"
    proof (rule Least_equality)
      show "dom (get_trans (trans_post C True False \<tau> 0 1) 1) \<noteq> {}"
        using True
        by (transfer', auto simp add: trans_post_raw_def preempt_def zero_fun_def zero_option_def)
    next
      { fix y :: nat
        assume "y < 1"
        hence "dom (get_trans (trans_post C True False \<tau> 0 1) y) = {}"
          using True by (transfer', simp add: trans_post_raw_def dom_def zero_map preempt_def) }
      thus "\<And>y. dom (get_trans (trans_post C True False \<tau> 0 1) y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
        using le_less_linear by auto
    qed
    finally show "next_time 0 ?\<tau>' = 1"
      by auto
  qed
  have ind1: "\<And>n. n < next_time 0 ?\<tau>' \<Longrightarrow> lookup ?\<tau>' n = 0"
    using True unfolding `next_time 0 ?\<tau>' = 1` by (transfer', auto simp add: trans_post_raw_def preempt_nonstrict_def)
  have ind2: "\<And>s. s \<in> dom (lookup ?\<tau>' (next_time 0 ?\<tau>')) \<Longrightarrow>
                        next_state 0 ?\<tau>' def_state s = the (lookup ?\<tau>' (next_time 0 ?\<tau>') s)"
    unfolding next_state_def `next_time 0 ?\<tau>' = 1` Let_def by auto
  have ind3: "\<And>n. next_time 0 ?\<tau>' \<le> n \<Longrightarrow> lookup (add_to_beh def_state 0 0 (next_time 0 ?\<tau>')) n = 0"
    unfolding ntime add_to_beh_def by (transfer', auto)
  have Cin: "C \<in> dom (lookup ?\<tau>' (next_time 0 ?\<tau>'))"
    using True unfolding `next_time 0 ?\<tau>' = 1`  
    by (transfer', auto split:option.split simp add: trans_post_raw_def preempt_def zero_fun_def zero_option_def)
  { assume "A \<notin> next_event 0 ?\<tau>' def_state \<and> B \<notin> next_event 0 ?\<tau>' def_state"
    hence "A \<notin> dom (lookup ?\<tau>' (next_time 0 ?\<tau>')) \<or> the (lookup ?\<tau>' (next_time 0 ?\<tau>') A) = False"
      and "B \<notin> dom (lookup ?\<tau>' (next_time 0 ?\<tau>')) \<or> the (lookup ?\<tau>' (next_time 0 ?\<tau>') B) = False"
      unfolding next_event_def ntime Let_def by auto
    hence "True \<longleftrightarrow>  \<not> (next_state 0 ?\<tau>' def_state A \<and> next_state 0 ?\<tau>' def_state B)"
      unfolding next_state_def ntime Let_def  by (simp add: override_on_def)
    moreover have "next_state 0 ?\<tau>' def_state C = True"
      using Cin unfolding next_state_def ntime Let_def  by (transfer', auto simp add: trans_post_raw_def preempt_nonstrict_def)
    ultimately have "next_state 0 ?\<tau>' def_state C \<longleftrightarrow>
                                     \<not> (next_state 0 ?\<tau>' def_state A \<and> next_state 0 ?\<tau>' def_state B)"
      by auto }
  note ind4 = this
  have ind5: "\<And>n. next_time 0 ?\<tau>' < n \<Longrightarrow> lookup (to_transaction2 ?\<tau>' C) n = 0"
    unfolding ntime by (transfer', auto simp add: trans_post_raw_def to_trans_raw2_def zero_option_def preempt_nonstrict_def)
  hence bigstep: "(Suc i),
         next_time 0 (trans_post C True False \<tau> 0 1) ,
         next_state 0 (trans_post C True False \<tau> 0 1) def_state ,
         next_event 0 (trans_post C True False \<tau> 0 1) def_state ,
         add_to_beh def_state empty_trans 0 (next_time 0 (trans_post C True False \<tau> 0 1))
      \<turnstile> <nand3 , trans_post C True False \<tau> 0 1> \<leadsto> res"
    using bsimulate2_obt_big_step[OF assms(1) `init' 0 def_state {} 0 nand3 \<tau> = ?\<tau>'`] by auto
  have *: "1 \<le> i \<Longrightarrow>
     signal_of2 def res C (Suc i) \<longleftrightarrow>
  \<not> (signal_of2 (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i \<and> signal_of2 (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i)"
    using nand3_correctness_ind[OF bigstep _ _ ind1 ind2 ind3 _ ind4 ind5] unfolding ntime by auto
  moreover have "1 \<le> i \<Longrightarrow> signal_of2 (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i = signal_of2 False ?\<tau>' A i"
  proof (cases "inf_time (to_transaction2 ?\<tau>') A i = None")
    case True
    assume "1 \<le> i"
    have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 ?\<tau>' A) k = 0"
      using True by (auto dest!: inf_time_noneE2)
    hence "lookup (to_transaction2 ?\<tau>' A) 1 = 0"
      using `1 \<le> i` by auto
    hence "A \<notin> dom (lookup ?\<tau>' 1)"
      apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
      by (simp add: domIff zero_option_def)
    have "signal_of2 (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i = next_state 0 ?\<tau>' def_state A"
      using True unfolding to_signal2_def comp_def by auto
    also have "... = False"
      using `A \<notin> dom (lookup ?\<tau>' 1)` unfolding next_state_def ntime Let_def by auto
    finally have 0: "signal_of2 (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i = False"
      by auto
    have 1: "signal_of2 False ?\<tau>' A i = False"
      using True unfolding to_signal2_def comp_def by auto
    then show ?thesis
      using 0 1 by auto
  next
    case False
    then obtain ta where "inf_time (to_transaction2 (trans_post C True False \<tau> 0 1)) A i = Some ta"
      by auto
    then show ?thesis
      unfolding to_signal2_def comp_def by auto
  qed
  moreover have "1 \<le> i \<Longrightarrow> signal_of2 (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = signal_of2 False ?\<tau>' B i"
  proof (cases "inf_time (to_transaction2 ?\<tau>') B i = None")
    case True
    assume "1 \<le> i"
    have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 ?\<tau>' B) k = 0"
      using True by (auto dest!: inf_time_noneE2)
    hence "lookup (to_transaction2 ?\<tau>' B) 1 = 0"
      using `1 \<le> i` by auto
    hence "B \<notin> dom (lookup ?\<tau>' 1)"
      apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
      by (simp add: domIff zero_option_def)
    have "signal_of2 (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = next_state 0 ?\<tau>' def_state B"
      using True unfolding to_signal2_def comp_def by auto
    also have "... = False"
      using `B \<notin> dom (lookup ?\<tau>' 1)` unfolding next_state_def ntime Let_def by auto
    finally have 0: "signal_of2 (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = False"
      by auto
    have 1: "signal_of2 False ?\<tau>' B i = False"
      using True unfolding to_signal2_def comp_def by auto
    then show ?thesis
      using 0 1 by auto
  next
    case False
    then obtain ta where "inf_time (to_transaction2 (trans_post C True False \<tau> 0 1)) B i = Some ta"
      by auto
    then show ?thesis
      unfolding to_signal2_def comp_def by auto
  qed
  ultimately have IR: "1 \<le> i \<Longrightarrow> signal_of2 def res C (Suc i) \<longleftrightarrow>
                                            \<not> (signal_of2 False ?\<tau>' A i \<and> signal_of2 False ?\<tau>' B i)"
    by auto
  have "lookup ?\<tau>' 0 = 0"
    using True by (transfer', simp add: trans_post_raw_def preempt_nonstrict_def)
  have "signal_of2 False ?\<tau>' A 0 = False"
    using inf_time_at_zero[OF `lookup ?\<tau>' 0 = 0`] unfolding to_signal2_def comp_def by auto
  have "signal_of2 False ?\<tau>' B 0 = False"
    using inf_time_at_zero[OF `lookup ?\<tau>' 0 = 0`] unfolding to_signal2_def comp_def by auto
  have "next_time 0 (trans_post C True False \<tau> 0 1) \<le> Suc i"
    unfolding ntime by auto
  have "1 \<le> next_time 0 (trans_post C True False \<tau> 0 1)"
    unfolding ntime by auto
  have "lookup res 1 = get_trans
   (Poly_Mapping.update (next_time 0 (trans_post C True False \<tau> 0 1)) (Some \<circ> next_state 0 (trans_post C True False \<tau> 0 1) def_state)
     (add_to_beh def_state empty_trans 0 (next_time 0 (trans_post C True False \<tau> 0 1)))) 1"
    using beh_res2[OF bigstep ind1 `next_time 0 (trans_post C True False \<tau> 0 1) \<le> Suc i` _ ind2 ind3 `1 \<le> next_time 0 (trans_post C True False \<tau> 0 1)`]
    by auto
  also have "... = lookup (Poly_Mapping.update 1 (Some o next_state 0 ?\<tau>' def_state) (add_to_beh def_state 0 0 1)) 1"
    unfolding ntime by auto
  also have "... = Some o next_state 0 ?\<tau>' def_state"
    by (simp add: lookup_update)
  finally have "lookup res 1  = Some o next_state 0 ?\<tau>' def_state"
    by auto
  hence "signal_of2 def res C 1 = next_state 0 ?\<tau>' def_state C"
    using lookup_some_signal_of2[OF `lookup res 1 = Some o next_state 0 ?\<tau>' def_state`] by auto
  also have "... = True"
    using True unfolding next_state_def ntime Let_def 
    by (transfer', auto split:option.split simp add: trans_post_raw_def preempt_def override_on_def zero_option_def zero_fun_def)
  also have "... \<longleftrightarrow> \<not> (signal_of2 False ?\<tau>' A 0 \<and> signal_of2 False ?\<tau>' B 0)"
    unfolding `signal_of2 False ?\<tau>' A 0 = False` `signal_of2 False ?\<tau>' B 0 = False` by auto
  finally have IR0: "signal_of2 def res C 1 \<longleftrightarrow> \<not> (signal_of2 False ?\<tau>' A 0 \<and> signal_of2 False ?\<tau>' B 0)"
    by auto
  have "signal_of2 False ?\<tau>' A i = signal_of2 False \<tau> A i" and "signal_of2 False ?\<tau>' B i = signal_of2 False \<tau> B i"
    using signal_of_trans_post   by (metis sig.distinct(3))(meson sig.simps(6) signal_of_trans_post)
  thus ?thesis
    using IR IR0  using le_less_linear by auto
next
  case False
  hence "init' 0 def_state {} 0 nand3 \<tau> = trans_post C True False \<tau> 0 1" (is "_ = ?\<tau>'")
    unfolding nand3_def by auto
  have "post_necessary_raw 0 (lookup \<tau>) 0 C True False"
  proof -
    have "\<forall>i \<le> 0. (lookup \<tau>) i C = None"
      using assms(2) apply transfer' unfolding to_trans_raw2_def  
      by (metis zero_map)
    moreover have "\<not> (\<exists>i \<le> 0. (lookup \<tau>) i C = Some True \<and> (\<forall>j>i. j \<le> 0 \<longrightarrow> lookup \<tau> j C = None))"
      using assms(2) apply transfer' unfolding to_trans_raw2_def
      by (metis option.distinct(1) zero_map)
    ultimately show ?thesis
      using post_necessary_raw_correctness by auto
  qed
  hence "get_trans ?\<tau>' 1 C = Some True"
    by (transfer', auto simp add: trans_post_raw_def)
  hence ntime: "next_time 0 ?\<tau>' = 0"
  proof -
    have "?\<tau>' \<noteq> 0"
      by(auto simp add: trans_post_imply_neq_map_empty)
    hence "next_time 0 ?\<tau>' = (LEAST n. dom (lookup ?\<tau>' n) \<noteq> {})"
      unfolding next_time_def by auto
    also have "... = 0"
    proof (rule Least_equality)
      show "dom (get_trans (trans_post C True False \<tau> 0 1) 0) \<noteq> {}"
        using False by (transfer', auto simp add: trans_post_raw_def zero_fun_def zero_option_def preempt_nonstrict_def)
    next
      { fix y :: nat
        assume "y < 0"
        hence "False" by auto
        hence "dom (get_trans (trans_post C True False \<tau> 0 1) y) = {}"
          by auto }
      thus "\<And>y. dom (get_trans (trans_post C True False \<tau> 0 1) y) \<noteq> {} \<Longrightarrow> 0 \<le> y "
        using le_less_linear by auto
    qed
    finally show "next_time 0 ?\<tau>' = 0"
      by auto
  qed
  define t' where "t' = next_time 0 ?\<tau>'"
  hence t'_def': "t' = 0"
    using ntime by auto

  define \<sigma>' where "\<sigma>' = next_state 0 ?\<tau>' def_state"
  hence "\<sigma>' C = False"
    using assms(2)  unfolding next_state_def `next_time 0 ?\<tau>' = 0` apply transfer'
    unfolding to_trans_raw2_def Let_def trans_post_raw_def preempt_nonstrict_def 
    by (smt add.commute add.right_neutral domIff fun_upd_same override_on_apply_notin zero_neq_one zero_upd)
  define \<gamma>' where "\<gamma>' = next_event 0 ?\<tau>' def_state"
  define \<theta>' where "\<theta>' = add_to_beh def_state (0 :: sig transaction) 0 t'"
  hence "\<theta>' = 0"
    unfolding t'_def' add_to_beh_def by auto

  hence bigstep: "(Suc i), t' , \<sigma>' , \<gamma>', \<theta>' \<turnstile> <nand3 , ?\<tau>'> \<leadsto> res"
    using bsimulate2_obt_big_step[OF assms(1) `init' 0 def_state {} 0 nand3 \<tau> = ?\<tau>'`]
    unfolding \<sigma>'_def \<gamma>'_def \<theta>'_def t'_def by auto
  hence bigstep': "(Suc i), 0 , \<sigma>' , \<gamma>', 0 \<turnstile> <nand3 , ?\<tau>'> \<leadsto> res"
    unfolding t'_def' `\<theta>' = 0` by auto
  have "\<not> quiet ?\<tau>' \<gamma>'"
    using False unfolding quiet_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
    by (smt One_nat_def add.left_neutral le_zero_eq n_not_Suc_n not_less_zero)
    
  moreover have "0 \<le> Suc i"
    by auto
  obtain \<tau>'' where cyc: "0 , \<sigma>' , \<gamma>' , empty_trans \<turnstile> <nand3 , rem_curr_trans 0 ?\<tau>'> \<longrightarrow>\<^sub>c \<tau>''" and
    bigstep'': "(Suc i), next_time 0 \<tau>'' , next_state 0 \<tau>'' \<sigma>' , next_event 0 \<tau>'' \<sigma>' , add_to_beh \<sigma>' empty_trans 0 (next_time 0 \<tau>'') \<turnstile> <nand3 , \<tau>''> \<leadsto> res"
    using case_bau2[OF `0 \<le> Suc i` `\<not> quiet ?\<tau>' \<gamma>'` bigstep'] by auto
  define \<sigma>'' where "\<sigma>'' = next_state 0 \<tau>'' \<sigma>'"
  define \<gamma>'' where "\<gamma>'' = next_event 0 \<tau>'' \<sigma>'"
  define \<theta>'' where "\<theta>'' = add_to_beh \<sigma>' 0 0 (next_time 0 \<tau>'')"
  have bigstep3 : "(Suc i), next_time 0 \<tau>'' , \<sigma>'' , \<gamma>'' , \<theta>'' \<turnstile> <nand3 , \<tau>''> \<leadsto> res"
    using bigstep'' unfolding \<sigma>''_def \<gamma>''_def \<theta>''_def by auto

  have ind1: "\<And>n. n < next_time 0 ?\<tau>' \<Longrightarrow> lookup ?\<tau>' n = 0"
    unfolding `next_time 0 ?\<tau>' = 0` by (transfer', auto simp add: trans_post_raw_def)
  have ind1': "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow> lookup \<tau>'' n = 0"
  proof (cases "\<tau>'' = 0")
    case True
    hence "next_time 0 \<tau>'' = 0"
      by auto
    { fix n
      assume "n < next_time 0 \<tau>''"
      hence "n < 0" unfolding `next_time 0 \<tau>'' = 0` by auto
      hence "False" by auto
      hence "lookup \<tau>'' n = 0" by auto }
    then show "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow> lookup \<tau>'' n = 0" by auto
  next
    case False
    hence "next_time 0 \<tau>'' = (LEAST n. dom (lookup \<tau>'' n) \<noteq> {})"
      unfolding next_time_def by auto
    then show "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow> lookup \<tau>'' n = 0"
      using Least_le  next_time_at_least2 by blast
  qed
  have ind2: "\<And>s. s \<in> dom (lookup ?\<tau>' (next_time 0 ?\<tau>')) \<Longrightarrow>
                        next_state 0 ?\<tau>' def_state s = the (lookup ?\<tau>' (next_time 0 ?\<tau>') s)"
    unfolding next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
  have ind2': "\<And>s. s \<in> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<Longrightarrow>
                        \<sigma>'' s = the (lookup \<tau>'' (next_time 0 \<tau>'') s)"
    unfolding next_state_def Let_def \<sigma>''_def by auto
  have ind3: "\<And>n. next_time 0 ?\<tau>' \<le> n \<Longrightarrow> lookup (add_to_beh def_state 0 0 (next_time 0 ?\<tau>')) n = 0"
    unfolding ntime add_to_beh_def by (transfer', auto)
  have ind3': "\<And>n. next_time 0 \<tau>'' \<le> n \<Longrightarrow> lookup \<theta>'' n = 0"
    unfolding \<theta>''_def add_to_beh_def by transfer' auto
  consider (either) "A \<in> \<gamma>' \<or> B \<in> \<gamma>'" | (none) "A \<notin> \<gamma>' \<and> B \<notin> \<gamma>'"
    by auto
  thus ?thesis
  proof (cases)
    case either
    hence \<tau>''_def: "\<tau>'' = trans_post C (\<not> (\<sigma>' A \<and> \<sigma>' B)) (\<sigma>' C) (rem_curr_trans 0 ?\<tau>') 0 1"
      using cyc unfolding nand3_def by auto
    have "(\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)) \<or> (\<not> \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B))"
      by auto
    moreover
    { assume "\<not> \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
      hence "True \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        using `\<sigma>' C = False` by auto
      hence nec: "post_necessary_raw 0 (lookup (rem_curr_trans 0 ?\<tau>')) 0 C (\<not> (\<sigma>' A \<and> \<sigma>' B)) (\<sigma>' C)"
      proof -
        have "lookup (rem_curr_trans 0 ?\<tau>') 0 C = None" 
          unfolding rem_curr_trans_def by transfer' (auto simp add:zero_map)
        thus ?thesis using post_necessary_raw_correctness `\<not> \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)`
          by auto
      qed 
      hence "\<tau>'' \<noteq> 0"
        using `lookup ?\<tau>' 1 C = Some True`
        by (simp add: trans_post_imply_neq_map_empty \<open>(\<not> \<sigma>' C) = (\<not> (\<sigma>' A \<and> \<sigma>' B))\<close> \<tau>''_def)
      hence "next_time 0 \<tau>'' = (LEAST n. dom (lookup \<tau>'' n) \<noteq> {})"
        unfolding next_time_def by auto
      also have "... = 1"
      proof (rule Least_equality)
        show "dom (get_trans \<tau>'' 1) \<noteq> {}"
          using nec `get_trans ?\<tau>' 1 C = Some True`
          unfolding \<tau>''_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def
          by (auto simp add: zero_fun_def zero_option_def)
      next
        { fix y :: nat
          assume "y < 1"
          hence "y = 0" by auto
          have "dom (get_trans \<tau>'' y) = {}" unfolding `y = 0` \<tau>''_def rem_curr_trans_def
            apply transfer' unfolding trans_post_raw_def  preempt_nonstrict_def by (simp add: dom_def zero_map) }
        thus "\<And>y. dom (get_trans \<tau>'' y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
          using le_less_linear by auto
      qed
      finally have "next_time 0 \<tau>'' = 1"
        by auto 
      { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
        hence "A \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<or> the (lookup \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
          and "B \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<or> the (lookup \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
          unfolding next_event_def ntime Let_def by auto
        hence helper: "\<not> (\<sigma>' A \<and> \<sigma>' B) \<longleftrightarrow>  \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          unfolding next_state_def Let_def  by (simp add: override_on_def)
        have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> (let m = get_trans \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding next_state_def by auto
        also have "... = (let m = get_trans \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding `next_time 0 \<tau>'' = 1` by auto
        also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
          unfolding \<tau>''_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def preempt_nonstrict_def Let_def
          by (auto split:option.split simp add:zero_fun_def zero_option_def override_on_def)
        finally have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
          by auto
        hence "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          using helper by auto }
      hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> \<sigma>'' C = (\<not> (\<sigma>'' A \<and> \<sigma>'' B))"
        unfolding \<gamma>''_def \<sigma>''_def by auto
      have "\<And>n. 1 < n \<Longrightarrow> lookup (to_transaction2 \<tau>'' C) n = 0"
        unfolding \<tau>''_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def preempt_nonstrict_def
        by (simp add: zero_option_def )
      hence ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow> lookup (to_transaction2 \<tau>'' C) n = 0"
        unfolding `next_time 0 \<tau>'' = 1` by auto
      have *: "1 \<le> i \<Longrightarrow>
         signal_of2 def res C (Suc i) = (\<not> (signal_of2 (\<sigma>'' A) \<tau>'' A i \<and> signal_of2 (\<sigma>'' B) \<tau>'' B i))"
        using nand3_correctness_ind[OF bigstep3 _ _ ind1' ind2' ind3' _ ind4' ind5']
        unfolding `next_time 0 \<tau>'' = 1` by auto
      moreover have "1 \<le> i \<Longrightarrow> signal_of2 (\<sigma>'' A) \<tau>'' A i = signal_of2 (\<sigma>' A) \<tau>'' A i"
      proof (cases "inf_time (to_transaction2 \<tau>'') A i = None")
        case True
        assume "1 \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>'' A) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence "lookup (to_transaction2 \<tau>'' A) 1 = 0"
          using `1 \<le> i` by auto
        hence "A \<notin> dom (lookup \<tau>'' 1)"
          apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
          by (simp add: domIff zero_option_def)
        have "signal_of2 (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
          using True unfolding to_signal2_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' A"
          using `A \<notin> dom (lookup \<tau>'' 1)` unfolding next_state_def
          by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
        finally have 0: "signal_of2 (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
          by auto
        have 1: "signal_of2 (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
          using True unfolding to_signal2_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_transaction2 \<tau>'') A i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal2_def comp_def by auto
      qed
      moreover have "1 \<le> i \<Longrightarrow> signal_of2 (\<sigma>'' B) \<tau>'' B i = signal_of2 (\<sigma>' B) \<tau>'' B i"
      proof (cases "inf_time (to_transaction2 \<tau>'') B i = None")
        case True
        assume "1 \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>'' B) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence "lookup (to_transaction2 \<tau>'' B) 1 = 0"
          using `1 \<le> i` by auto
        hence "B \<notin> dom (lookup \<tau>'' 1)"
          apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
          by (simp add: domIff zero_option_def)
        have "signal_of2 (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
          using True unfolding to_signal2_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' B"
          using `B \<notin> dom (lookup \<tau>'' 1)` unfolding next_state_def
          by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
        finally have 0: "signal_of2 (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
          by auto
        have 1: "signal_of2 (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
          using True unfolding to_signal2_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_transaction2 \<tau>'') B i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal2_def comp_def by auto
      qed
      ultimately have IR: "1 \<le> i \<Longrightarrow> signal_of2 def res C (Suc i) \<longleftrightarrow>
                                            \<not> (signal_of2 (\<sigma>' A) \<tau>'' A i \<and> signal_of2 (\<sigma>' B) \<tau>'' B i)"
        by auto
      have "lookup \<tau>'' 0 = 0"
        unfolding \<tau>''_def rem_curr_trans_def by (transfer', auto simp add: trans_post_raw_def preempt_nonstrict_def)
      have sA: "signal_of2 (\<sigma>' A) \<tau>'' A 0 = \<sigma>' A"
        using inf_time_at_zero[OF `lookup \<tau>'' 0 = 0`] unfolding to_signal2_def comp_def by auto
      have sB: "signal_of2 (\<sigma>' B) \<tau>'' B 0 = \<sigma>' B"
        using inf_time_at_zero[OF `lookup \<tau>'' 0 = 0`] unfolding to_signal2_def comp_def by auto
      have "next_time 0 \<tau>'' \<le> Suc i" and "1 \<le> next_time 0 \<tau>''"
        unfolding `next_time 0 \<tau>'' = 1` by auto
      have "get_trans res 1 = get_trans (Poly_Mapping.update 1 (Some \<circ> \<sigma>'') \<theta>'') 1"
        using beh_res2[OF bigstep3 ind1' `next_time 0 \<tau>'' \<le> Suc i` _ ind2' ind3' `1 \<le> next_time 0 \<tau>''`]
        unfolding `next_time 0 \<tau>'' = 1` by auto
      also have "... = Some o \<sigma>''"
        by (simp add: lookup_update)
      finally have "lookup res 1  = Some o \<sigma>''"
        by auto
      hence "signal_of2 def res C 1 = \<sigma>'' C"
        using lookup_some_signal_of2[OF `lookup res 1 =Some o \<sigma>''`] by auto
      also have "... \<longleftrightarrow> (let m = get_trans \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
        unfolding \<sigma>''_def next_state_def `next_time 0 \<tau>'' = 1` by auto
      also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        unfolding \<tau>''_def Let_def rem_curr_trans_def apply transfer'  unfolding trans_post_raw_def preempt_nonstrict_def
        by (auto split:option.split simp add: zero_fun_def zero_option_def override_on_def)
      also have "... \<longleftrightarrow> \<not> (signal_of2 (\<sigma>' A) \<tau>'' A 0 \<and> signal_of2 (\<sigma>' B) \<tau>'' B 0)"
        using sA sB by auto
      finally have IR0: "signal_of2 def res C 1 \<longleftrightarrow> \<not> (signal_of2 (\<sigma>' A) \<tau>'' A 0 \<and> signal_of2 (\<sigma>' B) \<tau>'' B 0)"
        by auto
  
      have "signal_of2 (\<sigma>' A) \<tau>'' A i = signal_of2 (\<sigma>' A) (rem_curr_trans 0 ?\<tau>') A i"
        unfolding \<tau>''_def  by (metis lookup_trans_post sig.distinct(3) signal_of2_lookup_sig_same)
      also have "... = signal_of2 (\<sigma>' A) ?\<tau>' A i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
      also have "... = signal_of2 (\<sigma>' A) \<tau> A i"  
        by (metis lookup_trans_post sig.distinct(3) signal_of2_lookup_sig_same)
      also have "... = signal_of2 False \<tau> A i"
      proof -
        have "lookup (to_transaction2 \<tau> A) 0 \<noteq> None \<or> lookup (to_transaction2 \<tau> A) 0 = None"
          by auto
        moreover
        { assume "lookup (to_transaction2 \<tau> A) 0 \<noteq> None"
          with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
        moreover
        { assume "lookup (to_transaction2 \<tau> A) 0 = None"
          hence "A \<notin> dom (get_trans (trans_post C True False \<tau> 0 1) 0)"
            apply transfer' unfolding to_trans_raw2_def trans_post_raw_def preempt_nonstrict_def
            by auto
          hence "\<sigma>' A = False"
            unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
          hence ?thesis by auto }
        ultimately show ?thesis by auto
      qed
      finally have hel: "signal_of2 (\<sigma>' A) \<tau>'' A i = signal_of2 False \<tau> A i"
        by auto
  
      have "signal_of2 (\<sigma>' B) \<tau>'' B i = signal_of2 (\<sigma>' B) (rem_curr_trans 0 ?\<tau>') B i"
        unfolding \<tau>''_def   by (metis lookup_trans_post sig.distinct(5) signal_of2_lookup_sig_same)
      also have "... = signal_of2 (\<sigma>' B) ?\<tau>' B i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
      also have "... = signal_of2 (\<sigma>' B) \<tau> B i"  
        by (metis lookup_trans_post sig.distinct(5) signal_of2_lookup_sig_same)
      also have "... = signal_of2 False \<tau> B i"
      proof -
        have "lookup (to_transaction2 \<tau> B) 0 \<noteq> None \<or> lookup (to_transaction2 \<tau> B) 0 = None"
          by auto
        moreover
        { assume "lookup (to_transaction2 \<tau> B) 0 \<noteq> None"
          with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
        moreover
        { assume "lookup (to_transaction2 \<tau> B) 0 = None"
          hence "B \<notin> dom (get_trans (trans_post C True False \<tau> 0 1) 0)"
            apply transfer' unfolding to_trans_raw2_def trans_post_raw_def preempt_nonstrict_def by auto
          hence "\<sigma>' B = False"
            unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
          hence ?thesis by auto }
        ultimately show ?thesis by auto
      qed
      finally have "signal_of2 (\<sigma>' B) \<tau>'' B i = signal_of2 False \<tau> B i"
        by auto
      then have ?thesis
        using IR IR0 hel le_less_linear by auto }
    moreover
    { assume "\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
      hence "False \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        using `\<sigma>' C = False` by auto
      hence not_nec: "\<not> post_necessary_raw 0 (lookup (rem_curr_trans 0 ?\<tau>')) 0 C (\<not> (\<sigma>' A \<and> \<sigma>' B)) (\<sigma>' C)"
      proof -
        have "lookup (rem_curr_trans 0 ?\<tau>') 0 C = None" 
          unfolding rem_curr_trans_def by transfer' (auto simp add:zero_map)
        thus ?thesis using post_necessary_raw_correctness `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)`
          by auto
      qed
      hence lookup: "lookup \<tau>'' = preempt_nonstrict C (lookup (rem_curr_trans 0 ?\<tau>')) 1"
        unfolding \<tau>''_def rem_curr_trans_def by transfer' auto
      hence "to_transaction2 \<tau>'' C = 0"
        unfolding rem_curr_trans_def apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def
        by (rule ext, auto simp add: zero_map zero_option_def)
      { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
        hence "A \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<or> the (lookup \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
          and "B \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<or> the (lookup \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
          unfolding next_event_def ntime Let_def by auto
        hence helper: "\<not> (\<sigma>' A \<and> \<sigma>' B) \<longleftrightarrow>  \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          unfolding next_state_def Let_def  by (simp add: override_on_def)
        have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> (let m = get_trans \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding next_state_def by auto
        also have "... = \<sigma>' C"
        proof -
          define m where "m = lookup \<tau>'' (next_time 0 \<tau>'')"
          hence "C \<notin> dom m"
            using `to_transaction2 \<tau>'' C = 0` unfolding next_time_def apply transfer'
            unfolding to_trans_raw2_def  by (metis domIff zero_option_def)
          thus ?thesis
            unfolding Let_def override_on_def m_def by auto
        qed
        also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
          using `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)` by auto
        finally have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
          by auto
        hence "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          using helper by auto }
      hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> \<sigma>'' C = (\<not> (\<sigma>'' A \<and> \<sigma>'' B))"
        unfolding \<gamma>''_def \<sigma>''_def by auto
      have ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow> lookup (to_transaction2 \<tau>'' C) n = 0"
        using `to_transaction2 \<tau>'' C = 0` by auto
      have *: "next_time 0 \<tau>'' \<le> i \<Longrightarrow>
         signal_of2 def res C (Suc i) = (\<not> (signal_of2 (\<sigma>'' A) \<tau>'' A i \<and> signal_of2 (\<sigma>'' B) \<tau>'' B i))"
        using nand3_correctness_ind[OF bigstep3 _ _ ind1' ind2' ind3' _ ind4' ind5'] by auto
      moreover have "next_time 0 \<tau>'' \<le> i \<Longrightarrow> signal_of2 (\<sigma>'' A) \<tau>'' A i = signal_of2 (\<sigma>' A) \<tau>'' A i"
      proof (cases "inf_time (to_transaction2 \<tau>'') A i = None")
        case True
        assume "next_time 0 \<tau>'' \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>'' A) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence "lookup (to_transaction2 \<tau>'' A) (next_time 0 \<tau>'') = 0"
          using `next_time 0 \<tau>'' \<le> i` by auto
        hence "A \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>''))"
          unfolding next_time_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
          by (simp add: domIff zero_option_def)
        have "signal_of2 (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
          using True unfolding to_signal2_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' A"
          using `A \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>''))` unfolding next_state_def
          by (metis override_on_apply_notin)
        finally have 0: "signal_of2 (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
          by auto
        have 1: "signal_of2 (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
          using True unfolding to_signal2_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_transaction2 \<tau>'') A i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal2_def comp_def by auto
      qed
      moreover have "(next_time 0 \<tau>'') \<le> i \<Longrightarrow> signal_of2 (\<sigma>'' B) \<tau>'' B i = signal_of2 (\<sigma>' B) \<tau>'' B i"
      proof (cases "inf_time (to_transaction2 \<tau>'') B i = None")
        case True
        assume "(next_time 0 \<tau>'') \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>'' B) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence "lookup (to_transaction2 \<tau>'' B) (next_time 0 \<tau>'') = 0"
          using `(next_time 0 \<tau>'') \<le> i` by auto
        hence "B \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>''))"
          unfolding next_time_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
          by (simp add: domIff zero_option_def)
        have "signal_of2 (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
          using True unfolding to_signal2_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' B"
          using `B \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>''))` unfolding next_state_def
          by (metis override_on_apply_notin)
        finally have 0: "signal_of2 (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
          by auto
        have 1: "signal_of2 (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
          using True unfolding to_signal2_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_transaction2 \<tau>'') B i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal2_def comp_def by auto
      qed
      ultimately have **: "next_time 0 \<tau>'' \<le> i \<Longrightarrow>
         signal_of2 def res C (Suc i) = (\<not> (signal_of2 (\<sigma>' A) \<tau>'' A i \<and> signal_of2 (\<sigma>' B) \<tau>'' B i))"
        by auto
      have "signal_of2 (\<sigma>' A) \<tau>'' A i = signal_of2 (\<sigma>' A) (rem_curr_trans 0 ?\<tau>') A i"
        unfolding \<tau>''_def  by (metis lookup_trans_post sig.distinct(3) signal_of2_lookup_sig_same)
      also have "... = signal_of2 (\<sigma>' A) ?\<tau>' A i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
      also have "... = signal_of2 (\<sigma>' A) \<tau> A i"  
        by (metis lookup_trans_post sig.distinct(3) signal_of2_lookup_sig_same)
      also have "... = signal_of2 False \<tau> A i"
      proof -
        have "lookup (to_transaction2 \<tau> A) 0 \<noteq> None \<or> lookup (to_transaction2 \<tau> A) 0 = None"
          by auto
        moreover
        { assume "lookup (to_transaction2 \<tau> A) 0 \<noteq> None"
          with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
        moreover
        { assume "lookup (to_transaction2 \<tau> A) 0 = None"
          hence "A \<notin> dom (get_trans (trans_post C True False \<tau> 0 1) 0)"
            apply transfer' unfolding to_trans_raw2_def trans_post_raw_def preempt_nonstrict_def
            by auto
          hence "\<sigma>' A = False"
            unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
          hence ?thesis by auto }
        ultimately show ?thesis by auto
      qed
      finally have hel: "signal_of2 (\<sigma>' A) \<tau>'' A i = signal_of2 False \<tau> A i"
        by auto

      have "signal_of2 (\<sigma>' B) \<tau>'' B i = signal_of2 (\<sigma>' B) (rem_curr_trans 0 ?\<tau>') B i"
        unfolding \<tau>''_def   by (metis lookup_trans_post sig.distinct(5) signal_of2_lookup_sig_same)
      also have "... = signal_of2 (\<sigma>' B) ?\<tau>' B i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
      also have "... = signal_of2 (\<sigma>' B) \<tau> B i"  
        by (metis lookup_trans_post sig.distinct(5) signal_of2_lookup_sig_same)
      also have "... = signal_of2 False \<tau> B i"
      proof -
          have "lookup (to_transaction2 \<tau> B) 0 \<noteq> None \<or> lookup (to_transaction2 \<tau> B) 0 = None"
            by auto
          moreover
          { assume "lookup (to_transaction2 \<tau> B) 0 \<noteq> None"
            with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
          moreover
          { assume "lookup (to_transaction2 \<tau> B) 0 = None"
            hence "B \<notin> dom (get_trans (trans_post C True False \<tau> 0 1) 0)"
              apply transfer' unfolding to_trans_raw2_def trans_post_raw_def preempt_nonstrict_def by auto
            hence "\<sigma>' B = False"
              unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
            hence ?thesis by auto }
          ultimately show ?thesis by auto
        qed
        finally have hel2: "signal_of2 (\<sigma>' B) \<tau>'' B i = signal_of2 False \<tau> B i"
          by auto

      { assume "i < next_time 0 \<tau>''"
        hence sA: "signal_of2 (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
        proof (intro signal_of2_init[where t="0"])
          show "i < next_time 0 \<tau>'' \<Longrightarrow> A \<in> dom (get_trans \<tau>'' 0) \<Longrightarrow> \<sigma>' A = the (get_trans \<tau>'' 0 A)"
            by (metis (full_types) domIff fun_upd_apply ind1' neq0_conv not_less0 zero_upd)
        qed (auto)

        have sB: "signal_of2 (\<sigma>' B) \<tau>'' B i = \<sigma>' B" using `i < next_time 0 \<tau>''`
        proof (intro signal_of2_init[where t="0"])
          show "i < next_time 0 \<tau>'' \<Longrightarrow>  B \<in> dom (get_trans \<tau>'' 0) \<Longrightarrow> \<sigma>' B = the (get_trans \<tau>'' 0 B)"
            by (metis (full_types) domIff fun_upd_apply ind1' neq0_conv not_less0 zero_upd)
        qed (auto)

        have "Suc i < next_time 0 \<tau>'' \<or> Suc i = next_time 0 \<tau>''"
          using `i < next_time 0 \<tau>''` by auto
        moreover
        { assume "Suc i = next_time 0 \<tau>''"
          hence "get_trans res (Suc i) = get_trans (Poly_Mapping.update (Suc i) (Some \<circ> \<sigma>'') \<theta>'') (Suc i)"
            using beh_res2[OF bigstep3 ind1' _ _ ind2' ind3'] by auto
          hence "signal_of2 def res C (Suc i) = \<sigma>'' C"
            using lookup_some_signal_of2  by (metis lookup_update)
          also have "... = \<sigma>' C"
          proof -
            define m where "m = lookup \<tau>'' (next_time 0 \<tau>'')"
            hence "C \<notin> dom m"
              using `to_transaction2 \<tau>'' C = 0` unfolding next_time_def apply transfer'
              unfolding to_trans_raw2_def  by (metis domIff zero_option_def)
            thus ?thesis
              unfolding \<sigma>''_def next_state_def Let_def override_on_def m_def by auto
          qed
          finally have "signal_of2 def res C (Suc i) = \<sigma>' C"
            by auto
          with sA sB hel hel2 have ?thesis
            using `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)` by auto }
        moreover
        { assume "Suc i < next_time 0 \<tau>''"
          hence "\<And>t. t \<le> Suc i \<Longrightarrow> get_trans \<theta>'' t = get_trans res t"
            using   beh_and_res_same_until_now[OF bigstep3 ind1'] by auto
          have "0 < next_time 0 \<tau>''"
            using `Suc i < next_time 0 \<tau>''` by auto
          hence "\<theta>'' = Poly_Mapping.update 0 (Some o \<sigma>') 0"
            using \<theta>''_def unfolding add_to_beh_def by auto
          have "signal_of2 def res C (Suc i) = signal_of2 def res C 0"
          proof (intro signal_of2_less_ind)
            show "\<And>n. 0 < n \<Longrightarrow> n \<le> Suc i \<Longrightarrow> get_trans res n = 0"
              using `\<And>t. t \<le> Suc i \<Longrightarrow> get_trans \<theta>'' t = get_trans res t` 
              `\<theta>'' = Poly_Mapping.update 0 (Some o \<sigma>') 0` by transfer' fastforce
          qed auto
          also have "... = \<sigma>' C"
            apply(rule lookup_some_signal_of2) 
            using `\<And>t. t \<le> Suc i \<Longrightarrow> get_trans \<theta>'' t = get_trans res t` `\<theta>'' = Poly_Mapping.update 0 (Some o \<sigma>') 0`
            by (metis le0 lookup_update)
          finally have "signal_of2 def res C (Suc i) = \<sigma>' C"
            by auto
          with sA sB hel hel2 have ?thesis
            using `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)` by auto }
        ultimately have "signal_of2 def res C (Suc i) = (\<not> (signal_of2 False \<tau> A i \<and> signal_of2 False \<tau> B i))"
          by auto }
      hence "i < next_time 0 \<tau>'' \<Longrightarrow> signal_of2 def res C (Suc i) = (\<not> (signal_of2 False \<tau> A i \<and> signal_of2 False \<tau> B i))"
        by auto
      with ** have ?thesis
        using hel hel2  using le_less_linear by blast }
    ultimately show ?thesis by auto
  next
    case none
    hence \<tau>''_def: "\<tau>'' = rem_curr_trans 0 ?\<tau>'"
      using cyc unfolding nand3_def by auto
    have "post_necessary_raw 0 (lookup \<tau>) 0 C True False"
    proof -
      have "lookup \<tau> 0 C = None"
        using assms(2) by (transfer', metis to_trans_raw2_def zero_map)
      thus ?thesis
        using post_necessary_raw_correctness2 \<open>post_necessary_raw 0 (get_trans \<tau>) 0 C True False\<close> by blast
    qed
    moreover have "lookup \<tau> 0 C = None"
      using assms(2) apply transfer' unfolding to_trans_raw2_def  by (metis zero_map)
    moreover have "lookup ?\<tau>' 1 C = Some True"
        using `post_necessary_raw 0 (lookup \<tau>) 0 C True False` apply transfer' unfolding trans_post_raw_def
        by auto
    ultimately have "\<tau>'' \<noteq> 0"
      using False unfolding \<tau>''_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def
      by (smt fun_upd_apply option.distinct(1) zero_neq_one zero_upd)
    hence "next_time 0 \<tau>'' = (LEAST n. dom (lookup \<tau>'' n) \<noteq> {})"
      unfolding next_time_def by auto
    also have "... = 1"
    proof (rule Least_equality)
      show "dom (get_trans \<tau>'' 1) \<noteq> {}"
        using False `lookup ?\<tau>' 1 C = Some True` unfolding \<tau>''_def rem_curr_trans_def 
        by transfer' auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y < 1" by auto hence "y = 0" by auto
        hence "dom (get_trans \<tau>'' y) = {}"
          unfolding \<tau>''_def rem_curr_trans_def apply transfer' by (auto simp add: trans_post_raw_def zero_map) }
      thus "\<And>y. dom (get_trans \<tau>'' y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
        by auto
    qed
    finally have "next_time 0 \<tau>'' = 1"
      by auto
    have "\<sigma>' A = False" and "\<sigma>' B = False"
      using none unfolding \<gamma>'_def \<sigma>'_def next_event_def Let_def ntime
      by (metis \<gamma>'_def next_state_fixed_point none)+
    { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
      hence "A \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<or> the (lookup \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
        and "B \<notin> dom (lookup \<tau>'' (next_time 0 \<tau>'')) \<or> the (lookup \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
        unfolding next_event_def ntime Let_def by auto
      hence helper: "\<not> (\<sigma>' A \<and> \<sigma>' B) \<longleftrightarrow>  \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
        unfolding next_state_def Let_def  by (simp add: override_on_def)
      have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> (let m = get_trans \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
        unfolding next_state_def by auto
      also have "... = (let m = get_trans \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
        unfolding `next_time 0 \<tau>'' = 1` by auto
      also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        unfolding \<tau>''_def rem_curr_trans_def `\<sigma>' A = False` `\<sigma>' B = False` using False `lookup ?\<tau>' 1 C = Some True`
        apply transfer' unfolding trans_post_raw_def Let_def preempt_def by (auto simp add:override_on_def)
      finally have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        by auto
      hence "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
        using helper by auto }
    hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> \<sigma>'' C = (\<not> (\<sigma>'' A \<and> \<sigma>'' B))"
      unfolding \<gamma>''_def \<sigma>''_def by auto
    have "\<And>n. 1 < n \<Longrightarrow> lookup (to_transaction2 \<tau>'' C) n = 0"
      unfolding \<tau>''_def rem_curr_trans_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def preempt_nonstrict_def
      by (simp add: zero_option_def)
    hence ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow> lookup (to_transaction2 \<tau>'' C) n = 0"
      unfolding `next_time 0 \<tau>'' = 1` by auto
    have *: "1 \<le> i \<Longrightarrow>
       signal_of2 def res C (Suc i) = (\<not> (signal_of2 (\<sigma>'' A) \<tau>'' A i \<and> signal_of2 (\<sigma>'' B) \<tau>'' B i))"
      using nand3_correctness_ind[OF bigstep3 _ _ ind1' ind2' ind3' _ ind4' ind5']
      unfolding `next_time 0 \<tau>'' = 1` by auto
    moreover have "1 \<le> i \<Longrightarrow> signal_of2 (\<sigma>'' A) \<tau>'' A i = signal_of2 (\<sigma>' A) \<tau>'' A i"
    proof (cases "inf_time (to_transaction2 \<tau>'') A i = None")
      case True
      assume "1 \<le> i"
      have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>'' A) k = 0"
        using True by (auto dest!: inf_time_noneE2)
      hence "lookup (to_transaction2 \<tau>'' A) 1 = 0"
        using `1 \<le> i` by auto
      hence "A \<notin> dom (lookup \<tau>'' 1)"
        apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
        by (simp add: domIff zero_option_def)
      have "signal_of2 (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
        using True unfolding to_signal2_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
      also have "... = \<sigma>' A"
        using `A \<notin> dom (lookup \<tau>'' 1)` unfolding next_state_def
        by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
      finally have 0: "signal_of2 (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
        by auto
      have 1: "signal_of2 (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
        using True unfolding to_signal2_def comp_def by auto
      then show ?thesis
        using 0 1 by auto
    next
      case False
      then obtain ta where "inf_time (to_transaction2 \<tau>'') A i = Some ta"
        by auto
      then show ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    moreover have "1 \<le> i \<Longrightarrow> signal_of2 (\<sigma>'' B) \<tau>'' B i = signal_of2 (\<sigma>' B) \<tau>'' B i"
    proof (cases "inf_time (to_transaction2 \<tau>'') B i = None")
      case True
      assume "1 \<le> i"
      have "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>'' B) k = 0"
        using True by (auto dest!: inf_time_noneE2)
      hence "lookup (to_transaction2 \<tau>'' B) 1 = 0"
        using `1 \<le> i` by auto
      hence "B \<notin> dom (lookup \<tau>'' 1)"
        apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
        by (simp add: domIff zero_option_def)
      have "signal_of2 (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
        using True unfolding to_signal2_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
      also have "... = \<sigma>' B"
        using `B \<notin> dom (lookup \<tau>'' 1)` unfolding next_state_def
        by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
      finally have 0: "signal_of2 (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
        by auto
      have 1: "signal_of2 (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
        using True unfolding to_signal2_def comp_def by auto
      then show ?thesis
        using 0 1 by auto
    next
      case False
      then obtain ta where "inf_time (to_transaction2 \<tau>'') B i = Some ta"
        by auto
      then show ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    ultimately have IR: "1 \<le> i \<Longrightarrow> signal_of2 def res C (Suc i) \<longleftrightarrow>
                                          \<not> (signal_of2 (\<sigma>' A) \<tau>'' A i \<and> signal_of2 (\<sigma>' B) \<tau>'' B i)"
      by auto
    have "lookup \<tau>'' 0 = 0"
      unfolding \<tau>''_def rem_curr_trans_def by (transfer', auto simp add: trans_post_raw_def)
    have sA: "signal_of2 (\<sigma>' A) \<tau>'' A 0 = \<sigma>' A"
      using inf_time_at_zero[OF `lookup \<tau>'' 0 = 0`] unfolding to_signal2_def comp_def by auto
    have sB: "signal_of2 (\<sigma>' B) \<tau>'' B 0 = \<sigma>' B"
      using inf_time_at_zero[OF `lookup \<tau>'' 0 = 0`] unfolding to_signal2_def comp_def by auto
    have "next_time 0 \<tau>'' \<le> Suc i" and "1 \<le> next_time 0 \<tau>''"
      unfolding `next_time 0 \<tau>'' = 1` by auto
    have "get_trans res 1 = get_trans (Poly_Mapping.update 1 (Some \<circ> \<sigma>'') \<theta>'') 1"
      using beh_res2[OF bigstep3 ind1' `next_time 0 \<tau>'' \<le> Suc i` _ ind2' ind3' `1 \<le> next_time 0 \<tau>''`]
      unfolding `next_time 0 \<tau>'' = 1` by auto
    also have "... = Some o \<sigma>''"
      by (simp add: lookup_update)
    finally have "lookup res 1  = Some o \<sigma>''"
      by auto
    hence "signal_of2 def res C 1 = \<sigma>'' C"
      using lookup_some_signal_of2[OF `lookup res 1 =Some o \<sigma>''`] by auto
    also have "... \<longleftrightarrow> (let m = get_trans \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
      unfolding \<sigma>''_def next_state_def `next_time 0 \<tau>'' = 1` by auto
    also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
      using `lookup ?\<tau>' 1 C = Some True` unfolding \<tau>''_def Let_def rem_curr_trans_def `\<sigma>' A = False` `\<sigma>' B = False`
      apply transfer'  unfolding trans_post_raw_def  preempt_def by (auto simp add: override_on_def)
    also have "... \<longleftrightarrow> \<not> (signal_of2 (\<sigma>' A) \<tau>'' A 0 \<and> signal_of2 (\<sigma>' B) \<tau>'' B 0)"
      using sA sB by auto
    finally have IR0: "signal_of2 def res C 1 \<longleftrightarrow> \<not> (signal_of2 (\<sigma>' A) \<tau>'' A 0 \<and> signal_of2 (\<sigma>' B) \<tau>'' B 0)"
      by auto

    have "signal_of2 (\<sigma>' A) \<tau>'' A i = signal_of2 (\<sigma>' A) (rem_curr_trans 0 ?\<tau>') A i"
      using signal_of_trans_post unfolding \<tau>''_def by (metis \<tau>''_def sig.distinct(3))
    also have "... = signal_of2 (\<sigma>' A) ?\<tau>' A i"
      using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
    also have "... = signal_of2 (\<sigma>' A) \<tau> A i"
      using signal_of_trans_post   by (metis (full_types) \<open>\<sigma>' A = False\<close> sig.distinct(3))
    also have "... = signal_of2 False \<tau> A i"
    proof -
      have "lookup (to_transaction2 \<tau> A) 0 \<noteq> None \<or> lookup (to_transaction2 \<tau> A) 0 = None"
        by auto
      moreover
      { assume "lookup (to_transaction2 \<tau> A) 0 \<noteq> None"
        with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
      moreover
      { assume "lookup (to_transaction2 \<tau> A) 0 = None"
        hence "A \<notin> dom (get_trans (trans_post C True False \<tau> 0 1) 0)"
          apply transfer' unfolding to_trans_raw2_def trans_post_raw_def preempt_nonstrict_def by auto
        hence "\<sigma>' A = False"
          unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
        hence ?thesis by auto }
      ultimately show ?thesis by auto
    qed
    finally have hel: "signal_of2 (\<sigma>' A) \<tau>'' A i = signal_of2 False \<tau> A i"
      by auto
    have "signal_of2 (\<sigma>' B) \<tau>'' B i = signal_of2 (\<sigma>' B) (rem_curr_trans 0 ?\<tau>') B i"
      using signal_of_trans_post unfolding \<tau>''_def  by fastforce
    also have "... = signal_of2 (\<sigma>' B) ?\<tau>' B i"
      using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
    also have "... = signal_of2 (\<sigma>' B) \<tau> B i"
      using signal_of_trans_post  using \<open>\<sigma>' B = False\<close> by fastforce
    also have "... = signal_of2 False \<tau> B i"
    proof -
      have "lookup (to_transaction2 \<tau> B) 0 \<noteq> None \<or> lookup (to_transaction2 \<tau> B) 0 = None"
        by auto
      moreover
      { assume "lookup (to_transaction2 \<tau> B) 0 \<noteq> None"
        with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
      moreover
      { assume "lookup (to_transaction2 \<tau> B) 0 = None"
        hence "B \<notin> dom (get_trans (trans_post C True False \<tau> 0 1) 0)"
          apply transfer' unfolding to_trans_raw2_def trans_post_raw_def preempt_nonstrict_def by auto
        hence "\<sigma>' B = False"
          unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
        hence ?thesis by auto }
      ultimately show ?thesis by auto
    qed
    finally have "signal_of2 (\<sigma>' B) \<tau>'' B i = signal_of2 False \<tau> B i"
      by auto
    then show ?thesis
      using IR IR0 hel le_less_linear by auto
  qed
qed

end