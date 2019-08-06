(*
 * Copyright 2018-2019, NTU
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
    hence "(if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) = 
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using nec unfolding trans_post_raw_def post_raw_def preempt_raw_def zero_upd zero_map fun_upd_def 
      by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    hence "v = def"
      by (meson signal_of_def zero_fun_def)
    hence "(if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) = 
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using not_nec by (auto simp add: preempt_raw_def zero_fun_def zero_option_def) }
  ultimately have " (if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
       (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))" by auto
  thus "trans_post_raw sig v def (\<lambda>k. 0) t dly = (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0)) "
    unfolding trans_post_raw_def by auto
qed

lemma get_trans_trans_upd_cancel:
  "lookup (Poly_Mapping.update n [sig \<mapsto> v] \<tau>) n = [sig \<mapsto> v]"
  by transfer auto

lemma is_stable_empty_trans:
  "is_stable n empty_trans now sig v"
  by (transfer', auto simp add:zero_map is_stable_raw_correct)

definition nand :: "sig conc_stmt" where
  "nand = process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1"

code_thms simulate_fin

code_thms functional_simulate_fin

values  "{lookup (get_beh beh) 1 C | beh. simulate_fin_ind 10 0 def_state {A} 0 nand empty_trans beh}"
                                                   
value " ((lookup o get_beh) (functional_simulate_fin 10 0 def_state {A} 0 nand 0)) 1 C"

theorem
  "(lookup o get_beh) (functional_simulate_fin 10 0 def_state {A} 0 nand empty_trans) 1 C = Some True"
  by eval

value "(lookup o get_beh) (functional_simulate 10 nand empty_trans) 1 C"

value "signal_of2 False (get_beh (functional_simulate 10 nand empty_trans)) C 100"

value [code] "to_signal False (to_transaction_sig (empty_trans :: nat \<Rightarrow>\<^sub>0 sig \<rightharpoonup> bool)) A 123456"

hide_const Femto_VHDL.next_time Femto_VHDL.next_state Femto_VHDL.next_event Femto_VHDL.add_to_beh
           Femto_VHDL.quiet Femto_VHDL.inf_time Femto_VHDL.init' Femto_VHDL.to_signal
hide_fact  Femto_VHDL.next_time_def Femto_VHDL.next_state_def Femto_VHDL.next_event_def
           Femto_VHDL.add_to_beh_def Femto_VHDL.quiet_def Femto_VHDL.to_signal_def Femto_VHDL.inf_time_def
           Femto_VHDL.init'_def

theorem
  assumes "10, 0, def_state, {A}, 0 \<turnstile> <nand, 0> \<leadsto> beh"
  shows "(get_beh beh) 1 C = Some True"
  using assms
proof (cases)
  case (1 \<tau>')
  have "trans_post_raw C True False (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 (Suc 0) = 
        0(Suc 0 := [C \<mapsto> True])"
  proof -
    let ?\<tau> = "override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
    have "signal_of False ?\<tau> C 0 = False"
      by (metis (no_types, lifting) greaterThanAtMost_iff less_irrefl_nat override_on_def
      signal_of_zero zero_fun_def)
    hence "post_necessary_raw (Suc 0 - 1) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 C True False"
      by auto
    hence "trans_post_raw C True False ?\<tau> 0 (Suc 0) = post_raw C True ?\<tau> (Suc 0)"
      unfolding trans_post_raw_def by auto
    also have "... = 0(Suc 0 := [C \<mapsto> True])"
      unfolding post_raw_def by (auto simp add: zero_fun_def zero_option_def)
    finally show ?thesis
      by auto
  qed
  hence "0 , def_state , {A} , 0 \<turnstile> <get_seq nand , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> True]))"
    unfolding nand_def  by (auto simp add: inr_post_raw_def purge_raw_def to_signal_def  split: option.splits)
  hence base: "0 , def_state , {A} , 0 \<turnstile> <nand , 0> \<longrightarrow>\<^sub>c (0(1 := [C \<mapsto> True]))"
    unfolding nand_def  by auto
  hence \<tau>'_def: "\<tau>' = (0(1:=[C \<mapsto> True]))"
    using 1 by auto
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(0(1:=[C \<mapsto> True])) \<noteq> 0"
      by (metis fun_upd_same option.distinct(1) zero_fun_def zero_option_def)
    moreover have "(LEAST n. dom (\<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (rule Least_equality)
      show "dom ((0(1 := [C \<mapsto> True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) \<noteq> {}"
          by auto 
        hence "\<not> dom ((0(1 := [C \<mapsto> True])) y) \<noteq> {}"
          by (simp add: zero_fun_def) }
      thus "\<And>y::nat.  dom ((0(1 := [C \<mapsto> True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  have ns: "next_state 0 \<tau>' def_state = def_state (C := True)" (is "?lhs = ?rhs")
    unfolding next_state_def Let_def nt 
    by (simp add: \<tau>'_def override_on_insert')
  have ne: "next_event 0 \<tau>' def_state = {C}"
  proof -
    {
      fix sig
      assume "sig \<in> dom (\<tau>' 1)"
      hence "sig = C"
        unfolding \<tau>'_def by transfer' auto 
      hence "(the \<circ> \<tau>' 1) sig \<noteq> False"
        unfolding \<tau>'_def by transfer' auto 
      with `sig = C` have "sig = C" and "(the \<circ> \<tau>' 1) sig \<noteq> False" 
        by auto }
    hence "\<And>sig. sig \<in> dom (\<tau>' 1) \<Longrightarrow> (the o \<tau>' 1) sig \<noteq> False \<Longrightarrow> sig = C"
      by auto
    hence "next_event 0 \<tau>' def_state \<subseteq> {C}"
      unfolding next_event_def Let_def nt by auto
    have "C \<in> dom (\<tau>' 1)"
      unfolding \<tau>'_def by (simp add: get_trans_trans_upd_cancel)
    moreover have "(the \<circ> \<tau>' 1) C \<noteq> False"
      unfolding \<tau>'_def  using \<open>\<And>sig. sig \<in> dom (\<tau>' 1) \<Longrightarrow> (the \<circ> \<tau>' 1) sig \<noteq> False\<close> 
      \<tau>'_def calculation by blast
    ultimately have "{C} \<subseteq> next_event 0 \<tau>' def_state"
      unfolding next_event_def Let_def nt by auto
    with `next_event 0 \<tau>' def_state \<subseteq> {C}` show ?thesis
      by auto
  qed
  have nb: "add_to_beh def_state 0 0 1 =
       0(0 := (Some o def_state))" (is "_ = ?beh'")
    unfolding add_to_beh_def by auto
  define beh2 :: "(nat \<Rightarrow> sig \<Rightarrow> bool option)" where "beh2 = ?beh'"
  hence snd_cyc: "10, 1, def_state (C := True), {C} , beh2 \<turnstile> <nand , (\<tau>'(1:=0))> \<leadsto> beh"
    using 1 nt ns ne nb by metis
  thus "get_beh beh 1 C = Some True"
  proof (cases)
    case (1 \<tau>'')
    have t''_def: "\<tau>'' = 0"
      unfolding nand_def
      using 1(3) unfolding nand_def by (auto simp add: \<tau>'_def zero_fun_def)
    have nt2: "next_time 1 0 = 2"
      by auto
    moreover have "next_state 1 \<tau>'' (def_state(C := True)) = def_state (C := True)"
      unfolding next_state_def Let_def t''_def nt2 zero_fun_def zero_option_def
      by auto
    moreover have "next_event 1 \<tau>'' (def_state(C := True)) = {}"
      unfolding next_event_def Let_def t''_def nt2 
      by (auto simp add: zero_fun_def zero_option_def)
    moreover have "add_to_beh (def_state(C := True)) beh2 1 (next_time 1 \<tau>'') = 
                   beh2(1 := (Some o def_state(C := True)))"
      unfolding add_to_beh_def t''_def nt2 by simp
    moreover have "(0(1 := [C \<mapsto> True]))(1:=0) = 0"
      unfolding zero_fun_def zero_option_def by auto
    ultimately have "(10, 2, def_state (C := True), {}, beh2(1 :=(Some o def_state(C := True))) \<turnstile> <nand, (\<tau>''(2:=0))> \<leadsto> beh)"
      using 1(4) using t''_def by metis
    then show ?thesis
    proof (cases)
      case (1 \<tau>')
      then show ?thesis unfolding quiet_def t''_def zero_fun_def zero_option_def 
        by (simp add: fun_upd_idem)
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

definition nand2 :: "sig conc_stmt" where
  "nand2 = process {A, B} : Bcomp
                            (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)
                            (Bassign_trans A (Bnand (Bsig A) (Bsig B)) 3)"

definition "test_trans = Pm_fmap (fmap_of_list [(4::nat, [A \<mapsto> True, B \<mapsto> True])])"
definition  "test2 = functional_simulate_fin 2 0 def_state {A, B, C} 0 nand2 test_trans"

value [code] "to_transaction_sig (get_beh test2) C"

definition nand3 :: "sig conc_stmt" where
  "nand3 = process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1"

\<comment> \<open>Specific lemmas about @{term "nand"} and @{term "nand3"}\<close>

lemma nand_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand) \<tau> = \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(3) singletonD)

lemma nand3_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand3) \<tau> = \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand3_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(2) singletonD)

lemma nand_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand) \<tau> = \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using assms unfolding nand_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand_does_not_modify_AB not_le)

lemma nand3_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> (get_seq nand3) \<tau> = \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using assms unfolding nand3_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand3_does_not_modify_AB not_le)

lemma maxtime_maxtime_bigstep:
  assumes "maxtime, maxtime, \<sigma>, \<gamma>, \<theta> \<turnstile> <nand3, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> \<tau> n = 0"
  assumes "\<And>n. maxtime \<le> n \<Longrightarrow> \<theta> n = 0"
  shows "get_beh beh = \<theta> (maxtime := (Some o \<sigma>))"
proof (cases "quiet \<tau> \<gamma>")
  case True
  then show ?thesis
    using case_quiesce[OF _ True assms(1)] by auto
next
  case False
  then obtain \<tau>' where cyc: "maxtime, \<sigma>, \<gamma>, \<theta> \<turnstile> <nand3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and
    big: "maxtime, next_time maxtime \<tau>', 
                   next_state maxtime \<tau>' \<sigma>, 
                   next_event maxtime \<tau>' \<sigma>,
                   add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>') \<turnstile> 
                   <nand3, (\<tau>'(next_time maxtime \<tau>':=0))> \<leadsto> beh"
    using case_bau2[OF _ False assms(1)] by auto
  have 0: "\<And>n. n < maxtime \<Longrightarrow> \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF assms(2)] cyc by auto
  have "maxtime \<le> next_time maxtime \<tau>'"
    using next_time_at_least[OF 0, of "maxtime"] by auto

  define \<sigma>2 where "\<sigma>2 = next_state maxtime \<tau>' \<sigma>"
  define \<gamma>2 where "\<gamma>2 = next_event maxtime \<tau>' \<sigma>"
  hence big2: "maxtime, next_time maxtime \<tau>', \<sigma>2, \<gamma>2, 
                        add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>')
                        \<turnstile> <nand3, \<tau>'(next_time maxtime \<tau>':=0)> \<leadsto> beh"
    using big unfolding  \<sigma>2_def \<gamma>2_def by auto
  have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0"
    by auto
  moreover
  { assume "\<tau>' = 0"
    hence ntime: "next_time maxtime \<tau>' = maxtime + 1"
      by auto
    hence ntheta: "add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>') = 
                   \<theta>(maxtime := (Some o \<sigma>))"
      unfolding add_to_beh_def by auto
    have "\<sigma>2 = \<sigma>"
      unfolding `\<tau>' = 0` \<sigma>2_def next_state_def zero_fun_def zero_option_def
      by auto
    hence "\<gamma>2 = {}"
      unfolding `\<tau>' = 0` \<gamma>2_def next_event_def 
      by (simp add: domIff zero_fun_def zero_option_def)
    hence "quiet \<tau>' \<gamma>2"
      using `\<tau>' = 0` `\<gamma>2 = {}` unfolding quiet_def by auto
    hence "quiet (\<tau>'(next_time maxtime \<tau>':=0)) \<gamma>2"
      unfolding ntime using `\<tau>' = 0`  by (simp add: fun_upd_idem zero_fun_def)
    have "get_beh beh = \<theta>(maxtime := (Some \<circ> \<sigma>))"
      using case_timesup[OF _ big2] ntheta unfolding ntime by auto }
  moreover
  { assume "\<tau>' \<noteq> 0"
    have "disjnt \<gamma> {A, B} \<or> \<not> disjnt \<gamma> {A, B}"
      by auto
    moreover
    { assume "disjnt \<gamma> {A, B}"
      hence "\<tau>' = \<tau>"
        using cyc unfolding nand3_def by auto
      hence "\<tau>' maxtime = 0"
        using assms(2) by auto
      have max_less: "maxtime < next_time maxtime \<tau>'"
      proof (rule ccontr)
        assume "\<not> maxtime < next_time maxtime \<tau>'" 
        hence "maxtime = next_time maxtime \<tau>'"
          using `maxtime \<le> next_time maxtime \<tau>'` by auto
        hence least: "(LEAST n. dom (\<tau>' n) \<noteq> {}) = maxtime"
          using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger
        have "\<exists>n. \<tau>' n \<noteq> 0"
          using `\<tau>' \<noteq> 0` by (metis (full_types) next_time_def lessI
          next_time_at_least not_le)
        hence 0: "\<exists>n. dom (\<tau>' n) \<noteq> {}"
        proof -
          { assume "dom (0::sig \<Rightarrow> bool option) \<noteq> {}"
            then have ?thesis
              by (metis \<open>\<tau>' maxtime = 0\<close>) }
          then show ?thesis
            using \<open>\<exists>n. \<tau>' n \<noteq> 0\<close> by force
        qed
        have "dom (\<tau>' maxtime) \<noteq> {}"
          using LeastI_ex[OF 0] unfolding least by auto
        with `\<tau>' maxtime = 0` show "False"
          by (metis dom_eq_empty_conv zero_map)
      qed }
    moreover
    { assume "\<not> disjnt \<gamma> {A, B}"
      hence \<tau>'_def: "\<tau>' = trans_post_raw C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) \<tau> maxtime 1"
        using cyc unfolding nand3_def by auto
      hence "\<tau>' maxtime = 0"
        using assms(2) by (auto simp add: trans_post_raw_def post_raw_def preempt_raw_def)
      have "maxtime < next_time maxtime \<tau>'"
      proof (rule ccontr)
        assume "\<not> maxtime < next_time maxtime \<tau>'" 
        hence "maxtime = next_time maxtime \<tau>'"
          using `maxtime \<le> next_time maxtime \<tau>'` by auto  
        hence least: "(LEAST n. dom (\<tau>' n) \<noteq> {}) = maxtime"
          using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger        
        have "\<exists>n. \<tau>' n \<noteq> 0"
          using `\<tau>' \<noteq> 0` by (metis (full_types) next_time_def lessI
          next_time_at_least not_le)
        hence 0: "\<exists>n. dom (\<tau>' n) \<noteq> {}"
        proof -
          { assume "dom (0::sig \<Rightarrow> bool option) \<noteq> {}"
            then have ?thesis
              by (metis \<open>\<tau>' maxtime = 0\<close>) }
          then show ?thesis
            using \<open>\<exists>n. \<tau>' n \<noteq> 0\<close> by force
        qed
        have "dom (\<tau>' maxtime) \<noteq> {}"
          using LeastI_ex[OF 0] unfolding least by auto
        with `\<tau>' maxtime = 0` show "False"
          by (metis dom_eq_empty_conv zero_map)
      qed }
    ultimately have max_less: "maxtime < next_time maxtime \<tau>'"
      by auto

    hence new_beh: "add_to_beh \<sigma> \<theta> maxtime (next_time maxtime \<tau>') =  
                    \<theta>(maxtime := (Some o \<sigma>))"
      unfolding add_to_beh_def by auto
    have "get_beh beh = \<theta>(maxtime := (Some \<circ> \<sigma>))"
      using max_less case_timesup[OF _ big2] unfolding new_beh by auto }
  ultimately show "get_beh beh = \<theta>(maxtime :=(Some \<circ> \<sigma>))"
    by auto
qed

lemma t_strictly_increasing:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <nand3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "t < next_time t \<tau>'"
proof (cases "A \<in> \<gamma> \<or> B \<in> \<gamma>")
  case True
  hence \<tau>'_def: "\<tau>' = trans_post_raw C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) \<tau> t 1"
    using assms unfolding nand3_def by auto
  hence " \<tau>' t = 0"
    using assms(2) by (auto simp add: trans_post_raw_def post_raw_def preempt_raw_def)
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least assms b_conc_exec_preserve_trans_removal 
    by (metis dual_order.strict_implies_order)
  show "t < next_time t \<tau>'"
  proof (rule ccontr)
    assume "\<not> t < next_time t \<tau>'" 
    hence "t = next_time t \<tau>'"
      using `t \<le> next_time t \<tau>'` by auto  
    hence least: "(LEAST n. dom (\<tau>' n) \<noteq> {}) = t"
      using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger        
    have "\<exists>n. \<tau>' n \<noteq> 0"
      using `\<tau>' \<noteq> 0` by (metis (full_types) next_time_def lessI next_time_at_least
      not_le)
    hence 0: "\<exists>n. dom (\<tau>' n) \<noteq> {}"
    proof -
      { assume "dom (0::sig \<Rightarrow> bool option) \<noteq> {}"
        then have ?thesis
          by (metis \<open>\<tau>' t = 0\<close>) }
      then show ?thesis
        using \<open>\<exists>n. \<tau>' n \<noteq> 0\<close> by force
    qed
    have "dom (\<tau>' t) \<noteq> {}"
      using LeastI_ex[OF 0] unfolding least by auto
    with `\<tau>' t = 0` show "False"
      by (metis dom_eq_empty_conv zero_map)
  qed 
next
  case False
  hence \<tau>'_def: "\<tau>' = \<tau>"
    using assms unfolding nand3_def by auto
  have "\<tau>' t = 0"
    unfolding \<tau>'_def using assms(2) by auto
  have "next_time t \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})"
    using assms(3) unfolding next_time_def by auto
  also have " (LEAST n. dom (\<tau>' n) \<noteq> {}) \<noteq> t"
  proof (rule ccontr)
    have asm: "\<exists>x. dom (\<tau>' x) \<noteq> {}"
      using `\<tau>' \<noteq> 0` 
    proof -
      have "\<exists>n. next_time n \<tau>' < n"
        by (metis next_time_def assms(3) lessI)
      then have "\<exists>n. \<tau>' n \<noteq> 0"
        by (meson next_time_at_least not_le)
      moreover
      { assume "\<exists>s n. \<tau>' n s \<noteq> None"
        then have ?thesis
          by (metis (no_types) dom_empty dom_eq_singleton_conv dom_fun_upd fun_upd_idem_iff
          option.distinct(1)) }
      ultimately show ?thesis
        using \<open>\<tau>' t = 0\<close> by fastforce
    qed
    assume "\<not> (LEAST n. dom (\<tau>' n) \<noteq> {}) \<noteq> t"
    hence "dom (\<tau>' t) \<noteq> {}"
      using LeastI_ex[where P="\<lambda>x. dom (\<tau>' x) \<noteq> {}"] asm by auto
    hence "\<tau>' t \<noteq> 0"
      by (metis dom_eq_empty_conv zero_map)
    with `\<tau>' t = 0` show "False" by auto
  qed
  finally have "next_time t \<tau>' \<noteq> t"
    by auto
  have *: "\<And>n. n < t \<Longrightarrow> \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF assms(2)] assms(1) by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  with `next_time t \<tau>' \<noteq> t` show ?thesis by auto
qed

lemma beh_res2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "t \<le> maxtime" and "cs = nand3"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows "\<And>n. n \<le> t \<Longrightarrow> (\<theta>(t:= Some o \<sigma>)) n = get_beh beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF 1(7)] 1(3) by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0" by auto
  moreover
  { assume "\<tau>' = 0"
    hence "next_time t \<tau>' = t + 1"
      unfolding next_time_def by auto
    moreover have " next_state t \<tau>' \<sigma> = \<sigma>"
      unfolding next_state_def Let_def 
      `next_time t \<tau>' = t + 1` `\<tau>' = 0` override_on_def
      by (auto simp add: zero_fun_def zero_option_def)
    moreover hence "next_event t \<tau>' \<sigma> = {}"
      unfolding next_event_def next_state_def Let_def `next_time t \<tau>' = t + 1` `\<tau>' = 0`
      by (auto simp add: zero_fun_def zero_option_def)
    moreover hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t := (Some o \<sigma>))"
      unfolding `next_time t \<tau>' = t + 1` add_to_beh_def by auto
    ultimately have ul: " maxtime, t + 1, \<sigma>, {}, \<theta>(t :=(Some o \<sigma>)) \<turnstile> <cs, (\<tau>'(t + 1 := 0))> \<leadsto> res"
      using 1(4) by auto
    have "t + 1 \<le> maxtime \<or> maxtime < t + 1" 
      by auto
    moreover
    { assume "t + 1 \<le> maxtime"
      have "get_beh res = (\<theta>(t := Some o \<sigma>))(t + 1 := Some \<circ> \<sigma>)"
        using case_quiesce[OF `t + 1 \<le> maxtime` _ ul] unfolding `\<tau>' = 0` quiet_def 
        by (simp add: fun_upd_idem zero_fun_def)
      hence ?case
        using `n \<le> t` fun_upd_def by auto }
    moreover
    { assume "maxtime < t + 1"
      hence "get_beh res = \<theta> (t := Some o \<sigma>)"
        using case_timesup[OF _ ul] by auto
      hence ?case  by metis }
    ultimately have ?case
      by auto }
  moreover
  { assume "\<tau>' \<noteq> 0"
    hence "t < next_time t \<tau>'"
      using t_strictly_increasing[OF _ 1(7) `\<tau>' \<noteq> 0`] 1(3) unfolding `cs = nand3` by auto
    hence ind1: "n \<le> next_time t \<tau>'"
      using `n \<le> t` by auto
    have ind2: "(\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>  (\<tau>'(next_time t \<tau>' := 0)) n = 0) "
      by (simp add: nat_less_le next_time_at_least2)
    have "next_time t \<tau>' \<le> maxtime \<or> maxtime < next_time t \<tau>'"
      by auto
    moreover
    { assume ind3: "next_time t \<tau>' \<le> maxtime"
      have h2: "\<And>n. next_time t \<tau>' \<le> n \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
        unfolding add_to_beh_def
        using "1.prems"(5) \<open>t \<le> next_time t \<tau>'\<close> by auto
      have " ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))(next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n = get_beh res n"
        using 1(5)[OF ind1 ind2 ind3 `cs = nand3` h2]  by blast
      hence ?case
        using `n \<le> t` `t < next_time t \<tau>'` unfolding add_to_beh_def
        by (metis (full_types) fun_upd_apply le_antisym less_irrefl_nat less_or_eq_imp_le) }
    moreover
    { assume "maxtime < next_time t \<tau>'"
      have "t < next_time t \<tau>'"
        using `t \<le> maxtime` `maxtime < next_time t \<tau>'` by auto
      have ?case
        using borderline_big_step[OF 1(4) 1(3) `t \<le> maxtime` `maxtime < next_time t \<tau>'` 1(10) _ ind1]
        `t < next_time t \<tau>'` unfolding add_to_beh_def  using nat_less_le 
        by presburger }
    ultimately have ?case by auto }
  ultimately show ?case by blast
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  show ?case
    using 2(3) by transfer' auto
next
  case (3 t maxtime \<theta> res \<sigma> \<gamma> cs \<tau>)
  then show ?case by auto
qed

theorem nand3_correctness_ind:
  assumes "maxtime, t, \<sigma>, \<gamma>, beh \<turnstile> <cs, ctrans> \<leadsto> res"
  assumes "cs = nand3" and "maxtime = Suc i"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  ctrans n = 0"
  assumes "\<And>s. s \<in> dom (ctrans t) \<Longrightarrow> \<sigma> s = the ( ctrans t s)"
  assumes "\<And>n. t \<le> n \<Longrightarrow>  beh n = 0"
  assumes "t \<le> i" and "A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<Longrightarrow> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
  assumes "\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig ctrans C) n = 0"
  shows "signal_of def (get_beh res) C (Suc i) \<longleftrightarrow> \<not> (signal_of (\<sigma> A) ctrans A i \<and> signal_of (\<sigma> B) ctrans B i)"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have "t \<le> Suc i"
    using `t \<le> i` by auto
  have *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using "1.hyps"(3) "1.prems"(3) b_conc_exec_preserve_trans_removal  by (metis nat_less_le)
  hence **: "\<And>n. dom (\<tau>' n) \<noteq> {} \<Longrightarrow> t \<le> n"
    using zero_map by force
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *] by auto
  have h0: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow> (\<tau>' (next_time t \<tau>' := 0)) n = 0"
    using b_conc_exec_preserve_trans_removal[OF `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`]
    `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`  by (simp add: nat_less_le next_time_at_least2) 
  have h0': "\<And>n. n < next_time t \<tau>' \<Longrightarrow> \<tau>' n = 0"
  proof -
    fix n
    assume "n < next_time t \<tau>'"
    hence "n < t \<or> t \<le> n \<and> n < next_time t \<tau>'"
      using `t \<le> next_time t \<tau>'` by auto
    moreover
    { assume "n < t"
      hence " \<tau>' n = 0"
        using b_conc_exec_preserve_trans_removal[OF `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`]
        `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` by auto }
    moreover
    { assume "t \<le> n \<and> n < next_time t \<tau>'"
      hence " \<tau>' n = 0"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`  using next_time_at_least2 by blast }
    ultimately show " \<tau>' n = 0"
      by auto
  qed
  have h1: "\<And>s. s \<in> dom ((\<tau>'(next_time t \<tau>':=0)) (next_time t \<tau>')) \<Longrightarrow>
                                        next_state t \<tau>' \<sigma> s = the ( (\<tau>'(next_time t \<tau>':=0)) (next_time t \<tau>') s)"
    unfolding next_state_def Let_def 
    by (simp add: zero_fun_def zero_option_def)
  have h1': "\<And>s. s \<in> dom ( \<tau>' (next_time t \<tau>')) \<Longrightarrow>
                                        next_state t \<tau>' \<sigma> s = the ( \<tau>' (next_time t \<tau>') s)"
    unfolding next_state_def Let_def by auto
  have h2: "\<And>n. next_time t \<tau>' \<le> n \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
    unfolding add_to_beh_def
    using "1.prems"(5) \<open>t \<le> next_time t \<tau>'\<close> by auto
  { assume asm: "A \<notin> next_event t \<tau>' \<sigma> \<and> B \<notin> next_event t \<tau>' \<sigma> "
    have sigA: "next_state t \<tau>' \<sigma> A = \<sigma> A" and sigB: "next_state t \<tau>' \<sigma> B = \<sigma> B"
      using next_state_fixed_point asm by metis+
    hence "next_event t \<tau>' \<sigma> = {C} \<or> next_event t \<tau>' \<sigma> = {}"
    proof -
      have "\<And>S Sa. B \<in> S \<or> S \<subseteq> insert C Sa \<or> A \<in> S"
        by (metis (full_types) insertI1 sig.exhaust subset_eq)
      then show ?thesis
        by (meson asm subset_singleton_iff)
    qed
    moreover
    { assume "next_event t \<tau>' \<sigma> = {}"
      hence "C \<notin> next_event t \<tau>' \<sigma>"
        by auto
      hence sigC: "next_state t \<tau>' \<sigma> C = \<sigma> C" 
        using next_state_fixed_point[OF `C \<notin> next_event t \<tau>' \<sigma>`]
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
        hence \<tau>'_def: "\<tau>' = trans_post_raw C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) \<tau> t 1"
          using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        have "(\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)) \<or>  (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
          by auto
        moreover 
        { assume "\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          have "to_trans_raw_sig \<tau> C = 0"
            using `\<And>n. t < n \<Longrightarrow> (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
            unfolding to_trans_raw_sig_def zero_fun_def zero_option_def
            by (meson leI)            
          hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
            unfolding to_trans_raw_sig_def by (metis zero_map)
          hence "post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          proof -
            have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and>  \<tau> i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                    (\<forall>j>i. j \<le> t + 1 \<longrightarrow>  \<tau> j C = None))"
              using `to_trans_raw_sig \<tau> C = 0` \<open>\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow> \<tau> i C = None\<close> 
              unfolding to_trans_raw_sig_def    by auto
            thus ?thesis
              using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
              `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` 
              by (metis \<open>to_trans_raw_sig \<tau> C = 0\<close> signal_of_def to_trans_raw_sig_def zero_fun_def)
          qed
          hence "\<tau>' \<noteq> 0"
            by (simp add: trans_post_raw_imply_neq_map_empty \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
          hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = t + 1"
          proof (rule Least_equality)
            show "dom ( \<tau>' (t + 1)) \<noteq> {}"
              using `post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
              unfolding \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def
              by (auto simp add: zero_fun_def zero_option_def)
          next
            have " \<tau>' t = 0"
              by (metis "1" \<open>\<tau>' \<noteq> 0\<close> \<open>t \<le> next_time t \<tau>'\<close> fun_upd_apply h0
              less_not_refl2 t_strictly_increasing)
            thus "\<And>y. dom (\<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
              using **
              by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
          qed
          finally have "next_time t \<tau>' = t + 1"
            by auto
          moreover have " \<tau>' (t + 1) C = Some (\<not> (\<sigma> A \<and> \<sigma> B))"
            using `post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def  unfolding trans_post_raw_def post_raw_def
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
      hence "C \<in> dom ( \<tau>' (next_time t \<tau>'))"
        unfolding next_event_def Let_def by transfer' auto
      have " A \<notin> \<gamma> \<and> B \<notin> \<gamma>  \<or> \<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )" by auto
      moreover
      { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
        hence "\<tau>' = \<tau>"
          using ` t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        have "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` 1(8)
           unfolding to_trans_raw_sig_def  by (metis le_neq_implies_less zero_fun_def)
        with `t \<le> next_time t \<tau>'`
        have "C \<notin> dom ( \<tau>' (next_time t \<tau>'))"
          using 1(8) unfolding `\<tau>' = \<tau>` next_time_def  unfolding to_trans_raw_sig_def
          by (simp add: domIff zero_option_def)
        with `C \<in> dom ( \<tau>' (next_time t \<tau>'))` have "False" by auto
        hence "next_state t \<tau>' \<sigma> C = (\<not> (next_state t \<tau>' \<sigma> A \<and> next_state t \<tau>' \<sigma> B))"
          by auto }
      moreover
      { assume "\<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )"
        hence \<tau>'_def: "\<tau>' = trans_post_raw C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) \<tau> t 1"
          using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        have "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` 1(8) 
          by (metis leI to_trans_raw_sig_def zero_fun_def)
        have "\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
        proof (rule ccontr)
          assume "\<not> (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))" hence "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)" by auto
          moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
            using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
            by (transfer', auto simp add: to_trans_raw_sig_def zero_fun_def zero_option_def )
          ultimately have "\<not> post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
            using post_necessary_raw_correctness 
            by (metis "1.prems"(3) Nat.add_0_right le0 le_add_same_cancel1)
          hence "to_trans_raw_sig \<tau>' C = 0"
            using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
            unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def to_trans_raw_sig_def
            zero_fun_def zero_option_def zero_map by auto
          with `C \<in> dom ( \<tau>' (next_time t \<tau>'))` have " \<tau>' (next_time t \<tau>') C \<noteq> 0"
            by (metis domIff fun_upd_same zero_fun_def zero_upd)
          hence " (to_trans_raw_sig \<tau>' C) (next_time t \<tau>') \<noteq> 0"
            unfolding next_time_def  unfolding to_trans_raw_sig_def by auto
          with `to_trans_raw_sig \<tau>' C = 0` show False
            unfolding next_time_def  unfolding to_trans_raw_sig_def  
            by (metis zero_fun_def)
        qed
        have "to_trans_raw_sig \<tau> C = 0"
          using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding to_trans_raw_sig_def zero_fun_def zero_option_def  by (meson linear)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          unfolding to_trans_raw_sig_def  by (metis zero_fun_def zero_option_def)
        hence "post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
        proof -
          have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and>  \<tau> i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                  (\<forall>j>i. j \<le> t + 1 \<longrightarrow>  \<tau> j C = None))"
            using `to_trans_raw_sig \<tau> C = 0` unfolding rem_curr_trans_def
             unfolding to_trans_raw_sig_def  by (metis option.simps(3) zero_fun_def zero_option_def)
          thus ?thesis
            using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` sledgehammer
            by (metis "1.prems"(3) add.commute add.right_neutral le_add2)
        qed
        hence "\<tau>' \<noteq> 0"
          by (simp add: trans_post_raw_imply_neq_map_empty \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom ( \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def trans_post_raw_def post_raw_def
            by (auto simp add: zero_fun_def zero_option_def)
        next
          have " \<tau>' t = 0"
            using "1.hyps"(3) "1.prems"(1) "1.prems"(3) \<open>\<tau>' \<noteq> 0\<close> next_time_at_least2 t_strictly_increasing 
            by blast
          thus "\<And>y. dom ( \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            using **
            by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        moreover have " \<tau>' (t + 1) C = Some (\<not> (\<sigma> A \<and> \<sigma> B))"
          using `post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
          unfolding \<tau>'_def trans_post_raw_def post_raw_def
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

  have h4': "\<And>n. next_time t \<tau>' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>' C) n = 0"
  proof -
    fix n
    assume "next_time t \<tau>' < n"
    have "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
      using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` 1(8) 
       unfolding to_trans_raw_sig_def by (metis leI zero_fun_def)
    have "A \<in> \<gamma> \<or> B \<in> \<gamma> \<or> (A \<notin> \<gamma> \<and> B \<notin> \<gamma>)"
      by auto
    moreover
    { assume "A \<in> \<gamma> \<or> B \<in> \<gamma>"
      hence \<tau>'_def: "\<tau>' = trans_post_raw C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) \<tau> t 1"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
        nand3_def by auto
      have "(\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)) \<or> (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        by auto
      moreover
      { assume "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
        moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          by (transfer', auto simp add: to_trans_raw_sig_def zero_fun_def zero_option_def )
        ultimately have "\<not> post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          using post_necessary_raw_correctness 
          by (metis "1.prems"(3) Nat.add_0_right signal_of_def zero_map zero_option_def)
        hence "to_trans_raw_sig \<tau>' C = 0"
          using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def to_trans_raw_sig_def
          zero_fun_def zero_option_def zero_map by auto
        hence " (to_trans_raw_sig \<tau>' C) n = 0"
          by (simp add: zero_fun_def) }
      moreover
      { assume "(\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        have "to_trans_raw_sig \<tau> C = 0"
          using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
           unfolding to_trans_raw_sig_def zero_fun_def zero_option_def 
           by (meson linear)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
           unfolding to_trans_raw_sig_def by (metis zero_fun_def zero_option_def)
        hence "post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
        proof -
          have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and>  \<tau> i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                  (\<forall>j>i. j \<le> t + 1 \<longrightarrow>  \<tau> j C = None))"
            using `to_trans_raw_sig \<tau> C = 0` unfolding to_trans_raw_sig_def  
            by (metis option.simps(3) zero_fun_def zero_option_def)
          thus ?thesis
            using post_necessary_raw_correctness `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` 
            by (metis (full_types) \<open>to_trans_raw_sig \<tau> C = 0\<close> to_trans_raw_sig_def zero_fun_def
            zero_option_def)
        qed        
        hence "\<tau>' \<noteq> 0"
          by (simp add: trans_post_raw_imply_neq_map_empty  \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom ( \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def  trans_post_raw_def post_raw_def
            by (auto simp add: zero_fun_def zero_option_def)
        next
          have " \<tau>' t = 0"
            using "1.hyps"(3) "1.prems"(1) "1.prems"(3) \<open>\<tau>' \<noteq> 0\<close> h0' t_strictly_increasing by auto
          thus "\<And>y. dom ( \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            using **
            by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        hence " (to_trans_raw_sig \<tau>' C) n = 0"
          using `next_time t \<tau>' < n` unfolding \<tau>'_def  next_time_def 
          trans_post_raw_def to_trans_raw_sig_def post_raw_def preempt_raw_def
          by (simp add: zero_option_def) }
      ultimately have " (to_trans_raw_sig \<tau>' C) n = 0"
        by auto } 
    moreover
    { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
      hence \<tau>'_def: "\<tau>' = \<tau>"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      hence " (to_trans_raw_sig \<tau>' C) n = 0"
        using `t \<le> next_time t \<tau>'` `next_time t \<tau>' < n` `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0`
        by (metis le_less_trans) }
    ultimately show " (to_trans_raw_sig \<tau>' C) n = 0"
      by auto
  qed
  hence h4: "\<And>n. next_time t \<tau>' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>'(next_time t \<tau>' :=0)) C) n = 0"
    by (simp add: to_trans_raw_sig_def)
  have h5: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0` unfolding rem_curr_trans_def by  auto
  have IH: " next_time t \<tau>' \<le> i \<Longrightarrow>
             signal_of def (get_beh res) C (Suc i) =
             (\<not> (signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i \<and>
                  signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i))"
                using 1(5)[OF `cs = nand3` `maxtime = Suc i` h0 h1 h2 _ h3 h4] by metis
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
      hence \<tau>'_def: "\<tau>' = \<tau>"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      have "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
        using signal_of2_init[OF `t \<le> i`, of "\<tau>" _ "\<sigma>"] `i < next_time t \<tau>'` 1(9) 1(8)
        unfolding \<tau>'_def by auto
      note no_trans_c = 1(13)
      moreover have " \<tau> t = 0"
        by (simp add: "1.prems"(3))
      ultimately have 13: "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
         unfolding to_trans_raw_sig_def 
        by (metis dual_order.order_iff_strict zero_fun_def)
      note next_big_step = 1(4)
      have "next_time t \<tau>' \<le> maxtime \<or> maxtime < next_time t \<tau>'" by auto
      moreover
      { assume "next_time t \<tau>' \<le> maxtime"
        hence pre: "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
          using   beh_res[OF next_big_step h0] by auto
        hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<theta>(t:=(Some o \<sigma>))) n =  get_beh res n"
          using`t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` unfolding add_to_beh_def by auto
        hence *: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
             ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))(next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n =  get_beh res n"
          using beh_res2[OF next_big_step h0 `next_time t \<tau>' \<le> maxtime` `cs = nand3` h2]
          by auto
        have "Suc i \<le> next_time t \<tau>'"
          using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` by auto
        hence "Suc i < next_time t \<tau>' \<or> Suc i = next_time t \<tau>'"
          by auto
        moreover have "\<not> Suc i < next_time t \<tau>'"
          using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` `maxtime = Suc i` by linarith
        ultimately have "Suc i = next_time t \<tau>'"
          by auto
        hence **: "signal_of def (get_beh res) C (Suc i) =
               signal_of def ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))(next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) C (Suc i)"
          using "1.prems"(1) "1.prems"(2) h0 h2 maxtime_maxtime_bigstep next_big_step by auto 
        define t' where "t' = next_time t \<tau>'"
        define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
        define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
        hence "signal_of def (get_beh res) C (Suc i) = signal_of def (\<theta>' (t' := (Some o \<sigma>'))) C (Suc i)"
          unfolding t'_def \<sigma>'_def \<theta>'_def using ** by auto
        also have "... = \<sigma>' C"
          by (metis \<open>Suc i = next_time t \<tau>'\<close> fun_upd_same t'_def trans_some_signal_of)
        finally have "signal_of def (get_beh res) C (Suc i) = \<sigma>' C"
          by auto
        also have "... = \<sigma> C"
        proof -
          have "C \<notin> dom (\<tau> (i + 1))"
            using 13 `t \<le> Suc i`  unfolding to_trans_raw_sig_def
            by (auto simp add: zero_map zero_option_def)
          moreover have *: "(next_time t \<tau>) = i + 1"
            using `Suc i = next_time t \<tau>'` unfolding \<tau>'_def by auto
          ultimately show ?thesis
            unfolding \<sigma>'_def next_state_def \<tau>'_def * Let_def by auto
        qed
        finally have "signal_of def (get_beh res) C (Suc i) = \<sigma> C"
          by auto
        moreover have "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          using 1(12) `A \<notin> \<gamma> \<and> B \<notin> \<gamma>` by auto
        ultimately have ?case
          using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` by auto }
      moreover
      { assume "maxtime < next_time t \<tau>'"
        hence pre: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
          using borderline_big_step[OF next_big_step `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `t \<le> maxtime` `maxtime < next_time t \<tau>'` 1(10)]
          by auto
        have "Suc i < next_time t \<tau>'"
          using `maxtime = Suc i` `maxtime < next_time t \<tau>'` by auto
        hence "Suc i < next_time t \<tau>"
          unfolding \<tau>'_def by auto
        hence "signal_of def (get_beh res) C (Suc i) =
               signal_of def (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) C (Suc i)"
          using \<open>maxtime < next_time t \<tau>'\<close> bau next_big_step
          by (metis (mono_tags) case_timesup(1) leD)
        also have "... =  signal_of def (\<theta> (t:= (Some o \<sigma>))) C (Suc i)"
          unfolding add_to_beh_def using `t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` by auto
        also have "... = \<sigma> C"
        proof -
          have "inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) C (Suc i) = Some t"
            using inf_time_update[OF 1(10)]  using \<open>t \<le> Suc i\<close> by simp
          thus ?thesis
            unfolding to_signal_def comp_def
            by (simp add: lookup_update to_trans_raw_sig_def)
        qed   
        finally have "signal_of def (get_beh res) C (Suc i) = \<sigma> C"
          by auto
        moreover have "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          using 1(12) `A \<notin> \<gamma> \<and> B \<notin> \<gamma>` by auto
        ultimately have ?case
          using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` by auto }
      ultimately have ?case by auto }
    moreover
    { assume "A \<in> \<gamma> \<or> B \<in> \<gamma>"
      hence \<tau>'_def: "\<tau>' = trans_post_raw C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C) \<tau> t 1"
        using `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      have "(\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)) \<or> (\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        by auto
      moreover
      { assume "\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
        moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  (\<tau>(t:=0)) i C = None)"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          by (auto simp add: to_trans_raw_sig_def zero_fun_def zero_option_def )
        ultimately have "\<not> post_necessary_raw 0 (\<tau>(t:=0)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          using post_necessary_raw_correctness `\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
          by (metis "1.prems"(3) Nat.add_0_right fun_upd_idem_iff le_add1 signal_of_def
          zero_option_def)
        hence "\<not> post_necessary_raw 0 \<tau> t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
          by (metis "1.prems"(3) fun_upd_triv order_refl)
        hence "to_trans_raw_sig \<tau>' C = 0"
          using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  (\<tau>(t:=0)) i C = None)`
          `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def to_trans_raw_sig_def 
                    zero_fun_def zero_option_def zero_map comp_def by auto
        have "next_time t \<tau> = next_time t \<tau>'"
        proof (cases "\<tau> = 0")
          case True
          hence "next_time t \<tau> = t + 1"
            unfolding next_time_def by auto
          have "\<tau>' = 0"
            using True `to_trans_raw_sig \<tau>' C = 0` `\<not> post_necessary_raw 0 (\<tau>(t:=0)) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def  
            by (auto simp add: zero_map zero_fun_def zero_option_def to_trans_raw_sig_def 
                trans_post_raw_def preempt_raw_def)
          hence "next_time t \<tau>' = t + 1"
            by auto
          then show ?thesis 
            using `next_time t \<tau> = t + 1` by auto
        next
          case False
          hence "next_time t \<tau> = (LEAST n. dom ( \<tau> n) \<noteq> {})"
            unfolding next_time_def by auto
          from `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          have lookC: " (to_trans_raw_sig \<tau> C) = 0"
            unfolding to_trans_raw_sig_def  
            by (intro ext, metis leI zero_fun_def)
          hence " (to_trans_raw_sig \<tau> A) \<noteq> 0 \<or> (to_trans_raw_sig \<tau> B) \<noteq> 0"
            using False  unfolding to_trans_raw_sig_def
            unfolding zero_map zero_fun_def by (metis sig.exhaust)
          moreover have lookA: " (to_trans_raw_sig \<tau>' A) =  (to_trans_raw_sig \<tau> A)"
            unfolding \<tau>'_def trans_post_raw_def preempt_raw_def to_trans_raw_sig_def post_raw_def 
            by auto
          moreover have lookB: " (to_trans_raw_sig \<tau>' B) =  (to_trans_raw_sig \<tau> B)"
            unfolding \<tau>'_def trans_post_raw_def preempt_raw_def to_trans_raw_sig_def post_raw_def 
            by auto
          ultimately have "\<tau>' \<noteq> 0"   
            by (auto simp add: to_trans_raw_sig_def zero_map zero_fun_def zero_option_def)
          hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = (LEAST n. dom (\<tau> n) \<noteq> {})"
            apply (rule LEAST_ext)
            using lookA lookB lookC `to_trans_raw_sig \<tau>' C = 0` 
            unfolding to_trans_raw_sig_def zero_map zero_fun_def zero_option_def 
            by (smt Collect_empty_eq dom_def sig.exhaust)
          finally show ?thesis
            by (simp add: \<open>next_time t \<tau> = (LEAST n. dom (\<tau> n) \<noteq> {})\<close>)
        qed
        hence "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
          using  1(9) `i < next_time t \<tau>'` 
          by (metis "1.prems"(3) "1.prems"(6) h5 nat_less_le not_le signal_of2_init)+
        note next_big_step = 1(4)
        have "next_time t \<tau>' \<le> maxtime \<or> maxtime < next_time t \<tau>'" by auto
        moreover
        { assume "next_time t \<tau>' \<le> maxtime"
          hence pre: "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
            using   beh_res[OF next_big_step h0] by auto
          hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<theta> (t := (Some o \<sigma>))) n =  get_beh res n"
            using`t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` unfolding add_to_beh_def by auto
          hence *: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
               ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n =  get_beh res n"
            using beh_res2[OF next_big_step h0 `next_time t \<tau>' \<le> maxtime` `cs = nand3` h2]
            by auto
          have "Suc i \<le> next_time t \<tau>'"
            using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` by auto
          hence "Suc i < next_time t \<tau>' \<or> Suc i = next_time t \<tau>'"
            by auto
          moreover have  "\<not> Suc i < next_time t \<tau>'"
            using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` `maxtime = Suc i` by auto
          ultimately have "Suc i = next_time t \<tau>'"
            by auto
          hence **: "signal_of def (get_beh res) C (Suc i) =
                 signal_of def ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) C (Suc i)"
            using "1.prems"(1) "1.prems"(2) h0 h2 maxtime_maxtime_bigstep next_big_step by auto
          define t' where "t' = next_time t \<tau>'"
          define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
          define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
          hence "signal_of def (get_beh res) C (Suc i) = signal_of def (\<theta>'(t' := (Some o \<sigma>'))) C (Suc i)"
            unfolding t'_def \<sigma>'_def \<theta>'_def using ** by auto
          also have "... = \<sigma>' C"
            by (metis \<open>Suc i = next_time t \<tau>'\<close> fun_upd_same t'_def trans_some_signal_of)
          finally have "signal_of def (get_beh res) C (Suc i) = \<sigma>' C"
            by auto
          also have "... = \<sigma> C"
          proof -
            have "\<And>n. C \<notin> dom ( \<tau>' n)"
              using `to_trans_raw_sig \<tau>' C = 0`   unfolding to_trans_raw_sig_def
              by (metis domIff fun_upd_idem_iff zero_fun_def zero_upd)
            thus ?thesis
              unfolding \<sigma>'_def next_state_def \<tau>'_def Let_def  by simp
          qed
          finally have "signal_of def (get_beh res) C (Suc i) = \<sigma> C"
            by auto
          hence ?case
            using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` 
            `\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` by auto }
        moreover
        { assume "maxtime < next_time t \<tau>'"
          hence pre: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
            using borderline_big_step[OF next_big_step `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `t \<le> maxtime` `maxtime < next_time t \<tau>'` 1(10)]
            by auto
          have "Suc i < next_time t \<tau>'"
            using `maxtime = Suc i` `maxtime < next_time t \<tau>'` by auto
          hence "signal_of def (get_beh res) C (Suc i) =
                 signal_of def (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) C (Suc i)"
            using \<open>maxtime < next_time t \<tau>'\<close> bau next_big_step 
            by (metis (mono_tags) case_timesup(1) leD)
          also have "... =  signal_of def (\<theta>(t := (Some o \<sigma>))) C (Suc i)"
            unfolding add_to_beh_def using `t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` by auto
          also have "... = \<sigma> C"
          proof -
            have "inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) C (Suc i) = Some t"
              using inf_time_update[OF 1(10)]  using \<open>t \<le> Suc i\<close> by simp
            thus ?thesis
              unfolding to_signal_def comp_def
              by (simp add: lookup_update to_trans_raw_sig_def)
          qed
          finally have "signal_of def (get_beh res) C (Suc i) = \<sigma> C"
            by auto
          hence ?case
            using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` `\<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)` 
            by auto }
        ultimately have ?case by auto }
      moreover
      { assume "(\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B))"
        have "to_trans_raw_sig \<tau> C = 0"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding to_trans_raw_sig_def zero_fun_def zero_option_def  by (meson le_less_linear)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          unfolding to_trans_raw_sig_def zero_fun_def zero_option_def by metis
        hence post_nec: "post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)"
        proof -
          have "\<not> (\<exists>i\<ge>t. i \<le> t + 1 \<and>  \<tau> i C = Some (\<not> (\<sigma> A \<and> \<sigma> B)) \<and> 
                  (\<forall>j>i. j \<le> t + 1 \<longrightarrow>  \<tau> j C = None))"
            using `to_trans_raw_sig \<tau> C = 0` unfolding rem_curr_trans_def
            unfolding to_trans_raw_sig_def  zero_fun_def zero_option_def
            by (metis option.simps(3))
          thus ?thesis
            using  `\<not> \<sigma> C \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)`  `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` 
            by (metis "1.prems"(3) Nat.add_0_right le_add1 signal_of_def zero_option_def)
        qed        
        hence "\<tau>' \<noteq> 0"
          by (simp add: trans_post_raw_imply_neq_map_empty \<open>(\<not> \<sigma> C) = (\<not> (\<sigma> A \<and> \<sigma> B))\<close> \<tau>'_def)
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom ( \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 ( \<tau>) t C (\<not> (\<sigma> A \<and> \<sigma> B)) (\<sigma> C)`
            unfolding \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def
            by (auto simp add: zero_fun_def zero_option_def)
        next
          { fix y
            assume "\<not> t + 1 \<le> y" hence "y < t + 1" by auto
            hence "dom ( \<tau>' y) = {}"
              using 1(8) unfolding \<tau>'_def  trans_post_raw_def preempt_raw_def post_raw_def
              by (auto simp add:zero_map) }
          thus "\<And>y. dom ( \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            by auto
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        with `i < next_time t \<tau>'` have "i < t + 1" by auto
        with `t \<le> i` have "i = t" by auto
        hence "signal_of (\<sigma> A) \<tau> A i = signal_of (\<sigma> A) \<tau> A t"
          by auto
        also have "... = \<sigma> A"
        proof -
          consider "inf_time (to_trans_raw_sig \<tau>) A t = None" |  ta where "inf_time (to_trans_raw_sig \<tau>) A t = Some ta"
            by blast
          thus ?thesis
          proof (cases)
            case 1
            then show ?thesis unfolding to_signal_def comp_def by auto
          next
            case 2
            have "t = ta"
            proof (rule ccontr)
              assume "t \<noteq> ta"
              with 2 have "ta \<le> t" by (auto dest!:inf_time_at_most)
              with `t \<noteq> ta` have "ta < t" by auto
              hence "\<tau> ta = 0"
                using 1(8) by auto
              have "ta \<in> dom (to_trans_raw_sig \<tau> A)"
                by (metis "2" \<open>i = t\<close> dom_is_keys inf_time_some_exists)
              hence "(to_trans_raw_sig \<tau> A) ta \<noteq> 0"
                 unfolding to_trans_raw_sig_def by (metis domIff zero_fun_def zero_map)
              hence "\<tau> ta \<noteq> 0"
                 unfolding to_trans_raw_sig_def by (metis zero_fun_def)
              thus False
                using `\<tau> ta = 0` by auto
            qed
            hence "inf_time (to_trans_raw_sig \<tau>) A t = Some t"
              using 2 by auto
            hence "t \<in> dom (to_trans_raw_sig \<tau> A)"
              by (metis Femto_VHDL_raw.keys_def dom_def inf_time_some_exists zero_option_def)
            hence "A \<in> dom (\<tau> t)"
               unfolding to_trans_raw_sig_def by auto
            hence "the ((to_trans_raw_sig \<tau> A) t) = \<sigma> A"
              using 1(9)  unfolding to_trans_raw_sig_def by auto
            then show ?thesis
              using `inf_time (to_trans_raw_sig \<tau>) A t = Some t` unfolding to_signal_def comp_def
              by auto
          qed
        qed
        finally have sigA: "signal_of (\<sigma> A) \<tau> A i = \<sigma> A"
          by auto
        have "signal_of (\<sigma> B) \<tau> B i = signal_of (\<sigma> B) \<tau> B t"
          using `i = t` by auto
        also have "... = \<sigma> B"
        proof -
        consider "inf_time (to_trans_raw_sig \<tau>) B t = None" |  ta where "inf_time (to_trans_raw_sig \<tau>) B t = Some ta"
          by blast
        thus ?thesis
        proof (cases)
          case 1
          then show ?thesis unfolding to_signal_def comp_def by auto
        next
          case 2
          have "t = ta"
          proof (rule ccontr)
            assume "t \<noteq> ta"
            with 2 have "ta \<le> t" by (auto dest!:inf_time_at_most)
            with `t \<noteq> ta` have "ta < t" by auto
            hence "\<tau> ta = 0"
              using 1(8) by auto
            have "ta \<in> dom ((to_trans_raw_sig \<tau> B))"
              by (metis "2" Femto_VHDL_raw.keys_def dom_def inf_time_some_exists zero_option_def)
            hence "(to_trans_raw_sig \<tau> B) ta \<noteq> 0"
              unfolding to_trans_raw_sig_def 
              by (metis domIff zero_fun_def zero_map)
            hence "\<tau> ta \<noteq> 0"
              unfolding to_trans_raw_sig_def 
              by (metis zero_fun_def)
            thus False
              using `\<tau> ta = 0` by auto
          qed
          hence "inf_time (to_trans_raw_sig \<tau>) B t = Some t"
            using 2 by auto
          hence "t \<in> dom ((to_trans_raw_sig \<tau> B))"
            by (metis Femto_VHDL_raw.keys_def dom_def inf_time_some_exists zero_option_def)
          hence "B \<in> dom (\<tau> t)"
            unfolding to_trans_raw_sig_def by auto
          hence "the ((to_trans_raw_sig \<tau> B) t) = \<sigma> B"
            using 1(9) unfolding to_trans_raw_sig_def by auto
          then show ?thesis
            using `inf_time (to_trans_raw_sig \<tau>) B t = Some t` unfolding to_signal_def comp_def
            by auto
        qed
        qed 
        finally have sigB: "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
          by auto
        note next_big_step = 1(4)
        have "next_time t \<tau>' \<le> maxtime"
          using `next_time t \<tau>' = t + 1` `maxtime = Suc i` `i = t` by auto
        have "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
               ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n =  get_beh res n"
          using beh_res2[OF next_big_step h0 `next_time t \<tau>' \<le> maxtime` `cs = nand3` h2] by auto
        hence " get_beh res (next_time t \<tau>') = (Some o next_state t \<tau>' \<sigma>)"
          by force
        hence " get_beh res (Suc i) = (Some o next_state t \<tau>' \<sigma>)"
          using `next_time t \<tau>' = t + 1` `i = t` by auto
        hence "signal_of def (get_beh res) C (Suc i) = next_state t \<tau>' \<sigma> C"
          by (meson trans_some_signal_of)
        also have "... = (let m =  \<tau>' (t + 1) in override_on \<sigma> (the o m) (dom m)) C"
          using `next_time t \<tau>' = t + 1` unfolding next_state_def by auto
        also have "... \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          using post_nec
          unfolding Let_def \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def
          by (auto split:option.split simp add: zero_fun_def zero_option_def override_on_def)
        finally have "signal_of def (get_beh res) C (Suc i) \<longleftrightarrow> \<not> (\<sigma> A \<and> \<sigma> B)"
          by auto
        hence ?case
          using sigA sigB by auto }
      ultimately have ?case by auto }
    ultimately have ?case by auto }
  moreover
  { assume "next_time t \<tau>' \<le> i"
    with IH have IH': "signal_of def (get_beh res) C (Suc i) = 
      (\<not> (signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i \<and> signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i))"
      by auto
    have Anot: "A \<notin> set (signals_from cs)"
      unfolding `cs = nand3` nand3_def by auto
    have "signal_of (\<sigma> A) \<tau> A i = signal_of (next_state t \<tau>' \<sigma> A) \<tau>' A i"
      using b_conc_exec_does_not_modify_signals2[OF h5 `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` Anot `next_time t \<tau>' \<le> i`]
      unfolding `cs = nand3` nand3_def by auto
    also have "... = signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i"
      using h0' h1' by(intro sym[OF signal_of_rem_curr_trans_at_t]) 
    finally have "signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>':=0)) A i  = signal_of (\<sigma> A) \<tau> A i"
      by auto

    have Bnot: "B \<notin> set (signals_from cs)"
      unfolding `cs = nand3` nand3_def by auto
    have " signal_of (\<sigma> B) \<tau> B i = signal_of (next_state t \<tau>' \<sigma> B) \<tau>' B i"
      using b_conc_exec_does_not_modify_signals2[OF h5 `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` Bnot `next_time t \<tau>' \<le> i`]
      unfolding `cs = nand3` nand3_def by auto
    also have "... = signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i"
      using h0' h1' by(intro sym[OF signal_of_rem_curr_trans_at_t]) 
    finally have "signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i  = signal_of (\<sigma> B) \<tau> B i"
      by auto
    hence ?case
      using `signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i  = signal_of (\<sigma> A) \<tau> A i` IH'
      by auto }
  ultimately show ?case by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs)
  have "\<tau> = 0"
    using `quiet \<tau> \<gamma>` unfolding quiet_def by metis
  hence *: "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and **: "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
    unfolding to_signal_def by auto
  have "inf_time (to_trans_raw_sig (\<theta>(t:=Some o \<sigma>))) C (Suc i) = Some t"
    unfolding to_signal_def to_trans_raw_sig_def 
  proof -
    have 0: "t \<in> keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C)"
      unfolding keys_def by (auto simp add: zero_option_def)
    moreover have 1: "t \<le> Suc i"
      using 2 by auto
    ultimately have "\<exists>k\<in>Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C). k \<le> Suc i"
      by auto
    hence "inf_time (\<lambda>sig n. (\<theta>(t := Some \<circ> \<sigma>)) n sig) C (Suc i) = 
            Some (GREATEST k. k \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> k \<le> Suc i)"
      unfolding inf_time_def by auto
    also have "... = Some t"
    proof (unfold option.inject, intro Greatest_equality)
      show "t \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> t \<le> Suc i"
        using 0 1 by auto
    next
      { fix y
        assume "\<not> y \<le> t" hence "t < y" by auto
        hence "y \<notin> keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C)"
          using 2(7) by (auto simp add: keys_def zero_map zero_option_def)
        hence "\<not> (y \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> y \<le> Suc i)"
          by auto }
      thus "\<And>y. y \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> y \<le> Suc i \<Longrightarrow> y \<le> t"
        by auto
    qed
    finally show "inf_time (\<lambda>sig n. (\<theta>(t := Some \<circ> \<sigma>)) n sig) C (Suc i) = Some t"
      by auto
  qed
  hence "signal_of def (\<theta>(t := Some \<circ> \<sigma>)) C (Suc i) = \<sigma> C"
    unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
  moreover have "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
    using `quiet \<tau> \<gamma>` unfolding quiet_def  by (metis emptyE)
  ultimately show ?case
    using 2(9) * **  by (metis comp_apply fst_conv snd_conv)
next
  case (3 t maxtime \<sigma> \<gamma> cs \<tau>)
  then show ?case by auto
qed

lemma signal_of2_cong_neq_none_at_0:
  assumes " (to_trans_raw_sig \<tau> sig) 0 \<noteq> None"
  shows "signal_of def1 \<tau> sig i = signal_of def2 \<tau> sig i"
proof -
  have "inf_time (to_trans_raw_sig \<tau>) sig i \<noteq> None"
  proof (rule ccontr)
    assume "\<not> inf_time (to_trans_raw_sig \<tau>) sig i \<noteq> None"
    hence "inf_time (to_trans_raw_sig \<tau>) sig i = None"
      by auto
    hence "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau> sig) k = 0"
      by (auto dest!: inf_time_noneE2)
    hence " (to_trans_raw_sig \<tau> sig) 0 = 0"
      by auto
    with assms show "False"
      by (simp add: zero_option_def)
  qed
  thus ?thesis
    unfolding to_signal_def comp_def by auto
qed

theorem nand3_correctness:
  assumes "b_simulate (Suc i) nand3 \<tau> res"
  assumes "to_trans_raw_sig \<tau> C = 0"
  shows "signal_of def (get_beh res) C (Suc i) \<longleftrightarrow> \<not> (signal_of False \<tau> A i \<and> signal_of False \<tau> B i)"
proof (cases " \<tau> 0 = 0")
  case True
  hence "init' 0 def_state {} 0 nand3 \<tau> = trans_post_raw C True False \<tau> 0 1" (is "_ = ?\<tau>'")
    unfolding nand3_def by auto
  hence ntime: "next_time 0 ?\<tau>' = 1"
  proof -
    have "?\<tau>' \<noteq> 0"
      by (simp add: trans_post_raw_imply_neq_map_empty)
    hence "next_time 0 ?\<tau>' = (LEAST n. dom ( ?\<tau>' n) \<noteq> {})"
      unfolding next_time_def by auto
    also have "... = 1"
    proof (rule Least_equality)
      show "dom ( (trans_post_raw C True False \<tau> 0 1) 1) \<noteq> {}"
        using True
        by (smt add.commute add_cancel_right_right cancel_comm_monoid_add_class.diff_cancel domIff
        empty_iff fun_upd_apply option.simps(3) post_raw_def signal_of_zero trans_post_raw_def
        zero_fun_def)
    next
      { fix y :: nat
        assume "y < 1"
        hence "dom ( (trans_post_raw C True False \<tau> 0 1) y) = {}"
          using True by (metis dom_eq_empty_conv le_zero_eq less_one
          trans_post_preserve_trans_removal_nonstrict zero_fun_def zero_option_def) }
      thus "\<And>y. dom (trans_post_raw C True False \<tau> 0 1 y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
        using le_less_linear by auto
    qed
    finally show "next_time 0 ?\<tau>' = 1"
      by auto
  qed
  have ind1: "\<And>n. n < next_time 0 ?\<tau>' \<Longrightarrow>  ?\<tau>' n = 0"
    using True unfolding `next_time 0 ?\<tau>' = 1` 
    by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
  hence ind1': "\<And>n. n \<le> next_time 0 ?\<tau>' \<Longrightarrow>  (?\<tau>'(next_time 0 ?\<tau>' := 0)) n = 0"
    by simp
  have ind2: "\<And>s. s \<in> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<Longrightarrow>
                        next_state 0 ?\<tau>' def_state s = the ( ?\<tau>' (next_time 0 ?\<tau>') s)"
    unfolding next_state_def `next_time 0 ?\<tau>' = 1` Let_def by auto
  have ind2': "\<And>s. s \<in> dom ( (?\<tau>'(next_time 0 ?\<tau>' := 0)) (next_time 0 ?\<tau>')) \<Longrightarrow>
                        next_state 0 ?\<tau>' def_state s = the ( (?\<tau>'(next_time 0 ?\<tau>' := 0)) (next_time 0 ?\<tau>') s)"
    by (simp add: zero_fun_def zero_option_def)
  have ind3: "\<And>n. next_time 0 ?\<tau>' \<le> n \<Longrightarrow>  (add_to_beh def_state 0 0 (next_time 0 ?\<tau>')) n = 0"
    unfolding ntime add_to_beh_def by (auto simp add: zero_map zero_option_def zero_fun_def)
  have Cin: "C \<in> dom ( ?\<tau>' (next_time 0 ?\<tau>'))"
    using True unfolding `next_time 0 ?\<tau>' = 1` 
    by (metis (no_types, lifting) add.commute add.right_neutral
    cancel_comm_monoid_add_class.diff_cancel domIff fun_upd_same option.simps(3) post_raw_def
    signal_of_zero trans_post_raw_def zero_fun_def)
  { assume "A \<notin> next_event 0 ?\<tau>' def_state \<and> B \<notin> next_event 0 ?\<tau>' def_state"
    hence "A \<notin> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<or> the ( ?\<tau>' (next_time 0 ?\<tau>') A) = False"
      and "B \<notin> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<or> the ( ?\<tau>' (next_time 0 ?\<tau>') B) = False"
      unfolding next_event_def ntime Let_def by auto
    hence "True \<longleftrightarrow>  \<not> (next_state 0 ?\<tau>' def_state A \<and> next_state 0 ?\<tau>' def_state B)"
      unfolding next_state_def ntime Let_def  by (simp add: override_on_def)
    moreover have "next_state 0 ?\<tau>' def_state C = True"
      using Cin unfolding next_state_def ntime Let_def  
      by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
    ultimately have "next_state 0 ?\<tau>' def_state C \<longleftrightarrow>
                                     \<not> (next_state 0 ?\<tau>' def_state A \<and> next_state 0 ?\<tau>' def_state B)"
      by auto }
  note ind4 = this
  have ind5: "\<And>n. next_time 0 ?\<tau>' < n \<Longrightarrow>  (to_trans_raw_sig ?\<tau>' C) n = 0"
    unfolding ntime by (auto simp add: trans_post_raw_def to_trans_raw_sig_def zero_option_def
    preempt_raw_def post_raw_def)
  have ind5': "\<And>n. next_time 0 ?\<tau>' < n \<Longrightarrow>  (to_trans_raw_sig (?\<tau>'(next_time 0 ?\<tau>' := 0)) C) n = 0"
    by (metis ind5 less_numeral_extra(4) ntime rem_curr_trans_to_trans_raw_sig
    trans_value_same_except_at_removed)
  hence bigstep: "(Suc i),
         next_time 0 (trans_post_raw C True False \<tau> 0 1) ,
         next_state 0 (trans_post_raw C True False \<tau> 0 1) def_state ,
         next_event 0 (trans_post_raw C True False \<tau> 0 1) def_state ,
         add_to_beh def_state 0 0 (next_time 0 (trans_post_raw C True False \<tau> 0 1))
      \<turnstile> <nand3 , (trans_post_raw C True False \<tau> 0 1)(next_time 0 (trans_post_raw C True False \<tau> 0 1) := 0)> \<leadsto> res"
    using bsimulate_obt_big_step[OF assms(1) `init' 0 def_state {} 0 nand3 \<tau> = ?\<tau>'`] by auto
  have *: "1 \<le> i \<Longrightarrow>
     signal_of def (get_beh res) C (Suc i) \<longleftrightarrow>
  \<not> (signal_of (next_state 0 ?\<tau>' def_state A) (?\<tau>'(1:=0)) A i \<and> signal_of (next_state 0 ?\<tau>' def_state B) (?\<tau>'(1:=0)) B i)"
    using nand3_correctness_ind[OF bigstep _ _ ind1' ind2' ind3 _ ind4 ind5']  unfolding ntime by auto
  moreover have "1 \<le> i \<Longrightarrow> signal_of (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i = signal_of False ?\<tau>' A i"
  proof (cases "inf_time (to_trans_raw_sig ?\<tau>') A i = None")
    case True
    assume "1 \<le> i"
    have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig ?\<tau>' A) k = 0"
      using True by (auto dest!: inf_time_noneE2)
    hence " (to_trans_raw_sig ?\<tau>' A) 1 = 0"
      using `1 \<le> i` by auto
    hence "A \<notin> dom ( ?\<tau>' 1)"
       unfolding trans_post_raw_def to_trans_raw_sig_def
      by (simp add: domIff zero_option_def)
    have "signal_of (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i = next_state 0 ?\<tau>' def_state A"
      using True unfolding to_signal_def comp_def by auto
    also have "... = False"
      using `A \<notin> dom ( ?\<tau>' 1)` unfolding next_state_def ntime Let_def by auto
    finally have 0: "signal_of (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i = False"
      by auto
    have 1: "signal_of False ?\<tau>' A i = False"
      using True unfolding to_signal_def comp_def by auto
    then show ?thesis
      using 0 1 by auto
  next
    case False
    then obtain ta where "inf_time (to_trans_raw_sig (trans_post_raw C True False \<tau> 0 1)) A i = Some ta"
      by auto
    then show ?thesis
      unfolding to_signal_def comp_def by auto
  qed
  moreover have "signal_of (next_state 0 ?\<tau>' def_state A) ?\<tau>' A i =   signal_of (next_state 0 ?\<tau>' def_state A) (?\<tau>'(1 := 0)) A i"
    apply(intro sym[OF signal_of_rem_curr_trans_at_t])
    using ind1 ntime ind2 by auto
  moreover have "1 \<le> i \<Longrightarrow> signal_of (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = signal_of False ?\<tau>' B i"
  proof (cases "inf_time (to_trans_raw_sig ?\<tau>') B i = None")
    case True
    assume "1 \<le> i"
    have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig ?\<tau>' B) k = 0"
      using True by (auto dest!: inf_time_noneE2)
    hence " (to_trans_raw_sig ?\<tau>' B) 1 = 0"
      using `1 \<le> i` by auto
    hence "B \<notin> dom ( ?\<tau>' 1)"
       unfolding trans_post_raw_def to_trans_raw_sig_def by (simp add: domIff zero_option_def)
    have "signal_of (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = next_state 0 ?\<tau>' def_state B"
      using True unfolding to_signal_def comp_def by auto
    also have "... = False"
      using `B \<notin> dom ( ?\<tau>' 1)` unfolding next_state_def ntime Let_def by auto
    finally have 0: "signal_of (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = False"
      by auto
    have 1: "signal_of False ?\<tau>' B i = False"
      using True unfolding to_signal_def comp_def by auto
    then show ?thesis
      using 0 1 by auto
  next
    case False
    then obtain ta where "inf_time (to_trans_raw_sig (trans_post_raw C True False \<tau> 0 1)) B i = Some ta"
      by auto
    then show ?thesis
      unfolding to_signal_def comp_def by auto
  qed
  moreover have "signal_of (next_state 0 ?\<tau>' def_state B) ?\<tau>' B i = signal_of (next_state 0 ?\<tau>' def_state B) (?\<tau>'(1:=0)) B i"
    apply(intro sym[OF signal_of_rem_curr_trans_at_t])
    using ind1 ntime ind2 by auto
  ultimately have IR: "1 \<le> i \<Longrightarrow> signal_of def (get_beh res) C (Suc i) \<longleftrightarrow>
                                            \<not> (signal_of False ?\<tau>' A i \<and> signal_of False ?\<tau>' B i)"
    by auto
  have " ?\<tau>' 0 = 0"
    using True by (simp add: trans_post_raw_def post_raw_def preempt_raw_def)
  have "signal_of False ?\<tau>' A 0 = False"
    by (metis \<open>trans_post_raw C True False \<tau> 0 1 0 = 0\<close> signal_of_zero zero_fun_def)
  have "signal_of False ?\<tau>' B 0 = False"
    by (metis \<open>trans_post_raw C True False \<tau> 0 1 0 = 0\<close> signal_of_zero zero_fun_def)
  have "next_time 0 (trans_post_raw C True False \<tau> 0 1) \<le> Suc i"
    unfolding ntime by auto
  have "1 \<le> next_time 0 (trans_post_raw C True False \<tau> 0 1)"
    unfolding ntime by auto

  have " get_beh res 1 = ((add_to_beh def_state 0 0 (next_time 0 (trans_post_raw C True False \<tau> 0 1)))
 (next_time 0 (trans_post_raw C True False \<tau> 0 1) := Some \<circ> next_state 0 (trans_post_raw C True False \<tau> 0 1) def_state))
 1"
    using beh_res2[OF bigstep ind1' `next_time 0 (trans_post_raw C True False \<tau> 0 1) \<le> Suc i` _ ind3 `1 \<le> next_time 0 (trans_post_raw C True False \<tau> 0 1)`]
    by auto
  also have "... =  ((add_to_beh def_state 0 0 1)(1 := (Some o next_state 0 ?\<tau>' def_state))) 1"
    unfolding ntime by auto
  also have "... = Some o next_state 0 ?\<tau>' def_state"
    by simp
  finally have " get_beh res 1  = Some o next_state 0 ?\<tau>' def_state"
    by auto
  hence "signal_of def (get_beh res) C 1 = next_state 0 ?\<tau>' def_state C"
    by (meson trans_some_signal_of)
  also have "... = True"
    using True unfolding next_state_def ntime Let_def 
    by (smt Cin One_nat_def \<open>1 \<le> next_time 0 (trans_post_raw C True False \<tau> 0 1)\<close> add.commute
    comp_apply domD not_less_zero ntime option.sel override_on_def plus_1_eq_Suc
    signal_of_trans_post3 trans_some_signal_of' zero_less_one)
  also have "... \<longleftrightarrow> \<not> (signal_of False ?\<tau>' A 0 \<and> signal_of False ?\<tau>' B 0)"
    unfolding `signal_of False ?\<tau>' A 0 = False` `signal_of False ?\<tau>' B 0 = False` by auto
  finally have IR0: "signal_of def (get_beh res) C 1 \<longleftrightarrow> \<not> (signal_of False ?\<tau>' A 0 \<and> signal_of False ?\<tau>' B 0)"
    by auto
  have "signal_of False ?\<tau>' A i = signal_of False \<tau> A i" and "signal_of False ?\<tau>' B i = signal_of False \<tau> B i"
    using signal_of_trans_post   by (metis sig.distinct(3))(meson sig.simps(6) signal_of_trans_post)
  thus ?thesis
    using IR IR0  using le_less_linear by auto
next
  case False
  hence "init' 0 def_state {} 0 nand3 \<tau> = trans_post_raw C True False \<tau> 0 1" (is "_ = ?\<tau>'")
    unfolding nand3_def by auto
  have "post_necessary_raw 0 ( \<tau>) 0 C True False"
  proof -
    have "\<forall>i \<le> 0. ( \<tau>) i C = None"
      using assms(2)  unfolding to_trans_raw_sig_def  
      by (metis zero_map)
    moreover have "\<not> (\<exists>i \<le> 0. ( \<tau>) i C = Some True \<and> (\<forall>j>i. j \<le> 0 \<longrightarrow>  \<tau> j C = None))"
      using assms(2)  unfolding to_trans_raw_sig_def
      by (metis option.distinct(1) zero_map)
    ultimately show ?thesis
      using post_necessary_raw_correctness  by (metis add.right_neutral)
  qed
  hence " ?\<tau>' 1 C = Some True"
    by (auto simp add: trans_post_raw_def post_raw_def)
  hence ntime: "next_time 0 ?\<tau>' = 0"
  proof -
    have "?\<tau>' \<noteq> 0"
      by(auto simp add: trans_post_raw_imply_neq_map_empty)
    hence "next_time 0 ?\<tau>' = (LEAST n. dom ( ?\<tau>' n) \<noteq> {})"
      unfolding next_time_def by auto
    also have "... = 0"
    proof (rule Least_equality)
      show "dom ( (trans_post_raw C True False \<tau> 0 1) 0) \<noteq> {}"
        using False by (auto simp add: trans_post_raw_def zero_fun_def zero_option_def
        preempt_raw_def post_raw_def)
    next
      { fix y :: nat
        assume "y < 0"
        hence "False" by auto
        hence "dom ( (trans_post_raw C True False \<tau> 0 1) y) = {}"
          by auto }
      thus "\<And>y. dom ( (trans_post_raw C True False \<tau> 0 1) y) \<noteq> {} \<Longrightarrow> 0 \<le> y "
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
    using assms(2)  unfolding next_state_def `next_time 0 ?\<tau>' = 0` 
    unfolding to_trans_raw_sig_def Let_def trans_post_raw_def preempt_raw_def post_raw_def
    by (smt One_nat_def add.right_neutral discrete domIff next_time_def not_add_less2
    override_on_def plus_1_eq_Suc t'_def t'_def' zero_fun_def zero_less_one zero_option_def)
  define \<gamma>' where "\<gamma>' = next_event 0 ?\<tau>' def_state"
  define \<theta>' where "\<theta>' = add_to_beh def_state (0 :: sig trans_raw) 0 t'"
  hence "\<theta>' = 0"
    unfolding t'_def' add_to_beh_def by auto

  hence bigstep: "(Suc i), t' , \<sigma>' , \<gamma>', \<theta>' \<turnstile> <nand3 , (?\<tau>' (t':=0))> \<leadsto> res"
    using bsimulate_obt_big_step[OF assms(1) `init' 0 def_state {} 0 nand3 \<tau> = ?\<tau>'`]
    unfolding \<sigma>'_def \<gamma>'_def \<theta>'_def t'_def by auto
  hence bigstep': "(Suc i), 0 , \<sigma>' , \<gamma>', 0 \<turnstile> <nand3 , (?\<tau>' (t':=0))> \<leadsto> res"
    unfolding t'_def' `\<theta>' = 0` by auto
  have "?\<tau>' (t':=0)\<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (?\<tau>' (t':=0)) \<noteq> 0"
    hence " (?\<tau>' (t':=0)) 1 C = None"
      by (simp add: zero_fun_def zero_option_def)
    moreover have " (?\<tau>' (t':=0)) 1 C = Some True"
      using \<open>post_necessary_raw 0 ( \<tau>) 0 C True False\<close>  unfolding t'_def'
      trans_post_raw_def post_raw_def  by auto
    ultimately show False by auto
  qed
  hence "\<not> quiet (?\<tau>' (t':=0)) \<gamma>'"
    unfolding quiet_def by auto
  moreover have "0 \<le> Suc i"
    by auto
  obtain \<tau>'' where cyc: "0 , \<sigma>' , \<gamma>' , 0 \<turnstile> <nand3 , (?\<tau>' (t':=0))> \<longrightarrow>\<^sub>c \<tau>''" and
    bigstep'': "(Suc i), next_time 0 \<tau>'' , next_state 0 \<tau>'' \<sigma>' , next_event 0 \<tau>'' \<sigma>' , add_to_beh \<sigma>' 0 0 (next_time 0 \<tau>'') \<turnstile> 
                  <nand3 , \<tau>'' (next_time 0 \<tau>'' := 0) > \<leadsto> res"
    using case_bau2[OF `0 \<le> Suc i` `\<not> quiet (?\<tau>' (t':=0)) \<gamma>'` bigstep'] by auto
  define \<sigma>'' where "\<sigma>'' = next_state 0 \<tau>'' \<sigma>'"
  define \<gamma>'' where "\<gamma>'' = next_event 0 \<tau>'' \<sigma>'"
  define \<theta>'' where "\<theta>'' = add_to_beh \<sigma>' 0 0 (next_time 0 \<tau>'')"
  have bigstep3 : "(Suc i), next_time 0 \<tau>'' , \<sigma>'' , \<gamma>'' , \<theta>'' \<turnstile> <nand3 , \<tau>''(next_time 0 \<tau>'' :=0)> \<leadsto> res"
    using bigstep'' unfolding \<sigma>''_def \<gamma>''_def \<theta>''_def by auto
  have ind1: "\<And>n. n < next_time 0 ?\<tau>' \<Longrightarrow>  ?\<tau>' n = 0"
    unfolding `next_time 0 ?\<tau>' = 0` by (auto simp add: trans_post_raw_def)
  have ind1': "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow>  \<tau>'' n = 0"
  proof (cases "\<tau>'' = 0")
    case True
    hence "next_time 0 \<tau>'' = 1"
      by auto
    then show "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow>  \<tau>'' n = 0"
      using Least_le  next_time_at_least2 by blast
  next
    case False
    hence "next_time 0 \<tau>'' = (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
      unfolding next_time_def by auto
    then show "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow>  \<tau>'' n = 0"
      using Least_le  next_time_at_least2 by blast
  qed
  hence ind1'': "\<And>n. n \<le> next_time 0 \<tau>'' \<Longrightarrow>  (\<tau>''(next_time 0 \<tau>'' := 0)) n = 0"
    by simp
  have ind2: "\<And>s. s \<in> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<Longrightarrow>
                        next_state 0 ?\<tau>' def_state s = the ( ?\<tau>' (next_time 0 ?\<tau>') s)"
    unfolding next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
  have ind2': "\<And>s. s \<in> dom ( \<tau>'' (next_time 0 \<tau>'')) \<Longrightarrow>
                        \<sigma>'' s = the ( \<tau>'' (next_time 0 \<tau>'') s)"
    unfolding next_state_def Let_def \<sigma>''_def by auto
  have ind2'': "\<And>s. s \<in> dom ( (\<tau>''(next_time 0 \<tau>'' := 0)) (next_time 0 \<tau>'')) \<Longrightarrow> \<sigma>'' s = the ( (\<tau>''(next_time 0 \<tau>'' := 0)) (next_time 0 \<tau>'') s)"
    by (simp add: zero_fun_def zero_option_def)
  have ind3: "\<And>n. next_time 0 ?\<tau>' \<le> n \<Longrightarrow>  (add_to_beh def_state 0 0 (next_time 0 ?\<tau>')) n = 0"
    unfolding ntime add_to_beh_def by (auto simp add: zero_fun_def)
  have ind3': "\<And>n. next_time 0 \<tau>'' \<le> n \<Longrightarrow>  \<theta>'' n = 0"
    unfolding \<theta>''_def add_to_beh_def by  (auto simp add: zero_fun_def)
  consider (either) "A \<in> \<gamma>' \<or> B \<in> \<gamma>'" | (none) "A \<notin> \<gamma>' \<and> B \<notin> \<gamma>'"
    by auto
  thus ?thesis
  proof (cases)
    case either
    hence \<tau>''_def: "\<tau>'' = trans_post_raw C (\<not> (\<sigma>' A \<and> \<sigma>' B)) (\<sigma>' C) (?\<tau>' (0:=0)) 0 1"
      using cyc unfolding nand3_def t'_def' by auto
    have "(\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)) \<or> (\<not> \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B))"
      by auto
    moreover
    { assume "\<not> \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
      hence "True \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        using `\<sigma>' C = False` by auto
      hence nec: "post_necessary_raw 0 (?\<tau>' (0:=0)) 0 C (\<not> (\<sigma>' A \<and> \<sigma>' B)) (\<sigma>' C)"
      proof -
        have " (?\<tau>' (0:=0)) 0 C = None" 
          by  (auto simp add:zero_map)
        thus ?thesis using  `\<not> \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)`
          by (metis add.right_neutral signal_of_zero zero_option_def)
      qed 
      hence "\<tau>'' \<noteq> 0"
        using ` ?\<tau>' 1 C = Some True`
        by (simp add: trans_post_raw_imply_neq_map_empty \<open>(\<not> \<sigma>' C) = (\<not> (\<sigma>' A \<and> \<sigma>' B))\<close> \<tau>''_def)
      hence "next_time 0 \<tau>'' = (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
        unfolding next_time_def by auto
      also have "... = 1"
      proof (rule Least_equality)
        show "dom ( \<tau>'' 1) \<noteq> {}"
          using nec ` ?\<tau>' 1 C = Some True`
          unfolding \<tau>''_def   unfolding trans_post_raw_def post_raw_def
          by (auto simp add: zero_fun_def zero_option_def )
      next
        { fix y :: nat
          assume "y < 1"
          hence "y = 0" by auto
          have "dom ( \<tau>'' y) = {}" unfolding `y = 0` \<tau>''_def 
            unfolding trans_post_raw_def  post_raw_def preempt_raw_def 
            by (simp add: dom_def zero_map) }
        thus "\<And>y. dom ( \<tau>'' y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
          using le_less_linear by auto
      qed
      finally have "next_time 0 \<tau>'' = 1"
        by auto 
      { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
        hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
          and "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
          unfolding next_event_def ntime Let_def by auto
        hence helper: "\<not> (\<sigma>' A \<and> \<sigma>' B) \<longleftrightarrow>  \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          unfolding next_state_def Let_def  by (simp add: override_on_def)
        have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> (let m =  \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding next_state_def by auto
        also have "... = (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding `next_time 0 \<tau>'' = 1` by auto
        also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
          unfolding \<tau>''_def   unfolding trans_post_raw_def preempt_raw_def Let_def post_raw_def
          by (smt add.left_neutral cancel_comm_monoid_add_class.diff_cancel comp_apply domIff
          fun_upd_same nec option.sel option.simps(3) override_on_def signal_of_zero zero_fun_def)
        finally have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
          by auto
        hence "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          using helper by auto }
      hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> \<sigma>'' C = (\<not> (\<sigma>'' A \<and> \<sigma>'' B))"
        unfolding \<gamma>''_def \<sigma>''_def by auto
      have "\<And>n. 1 < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
        unfolding \<tau>''_def   unfolding trans_post_raw_def to_trans_raw_sig_def post_raw_def 
        preempt_raw_def by (simp add: zero_option_def )
      hence ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
        unfolding `next_time 0 \<tau>'' = 1` by auto
      hence ind5'': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>''(next_time 0 \<tau>'' := 0)) C) n = 0"
        by (simp add: to_trans_raw_sig_def)
      have *: "1 \<le> i \<Longrightarrow>
         signal_of def (get_beh res) C (Suc i) = (\<not> (signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'' := 0)) A i \<and> 
                                           signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i))"
        using nand3_correctness_ind[OF bigstep3 _ _ ind1'' ind2'' ind3' _ ind4' ind5''] 
        unfolding `next_time 0 \<tau>'' = 1` by auto
      moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' A) \<tau>'' A i = signal_of (\<sigma>' A) \<tau>'' A i"
      proof (cases "inf_time (to_trans_raw_sig \<tau>'') A i = None")
        case True
        assume "1 \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' A) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence " (to_trans_raw_sig \<tau>'' A) 1 = 0"
          using `1 \<le> i` by auto
        hence "A \<notin> dom ( \<tau>'' 1)"
           unfolding trans_post_raw_def to_trans_raw_sig_def
          by (simp add: domIff zero_option_def)
        have "signal_of (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
          using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' A"
          using `A \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
          by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
        finally have 0: "signal_of (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
          by auto
        have 1: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
          using True unfolding to_signal_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') A i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal_def comp_def by auto
      qed
      moreover have "signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'':=0)) A i = 
                     signal_of (\<sigma>'' A) \<tau>'' A i"
        apply (intro signal_of_rem_curr_trans_at_t) using ind1' ind2' by auto
      moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' B) \<tau>'' B i = signal_of (\<sigma>' B) \<tau>'' B i"
      proof (cases "inf_time (to_trans_raw_sig \<tau>'') B i = None")
        case True
        assume "1 \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' B) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence " (to_trans_raw_sig \<tau>'' B) 1 = 0"
          using `1 \<le> i` by auto
        hence "B \<notin> dom ( \<tau>'' 1)"
           unfolding trans_post_raw_def to_trans_raw_sig_def
          by (simp add: domIff zero_option_def)
        have "signal_of (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
          using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' B"
          using `B \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
          by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
        finally have 0: "signal_of (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
          by auto
        have 1: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
          using True unfolding to_signal_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') B i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal_def comp_def by auto
      qed
      moreover have "signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'':=0)) B i = 
                     signal_of (\<sigma>'' B) \<tau>'' B i"
        apply (intro signal_of_rem_curr_trans_at_t) using ind1' ind2' by auto
      ultimately have IR: "1 \<le> i \<Longrightarrow> signal_of def (get_beh res) C (Suc i) \<longleftrightarrow>
                                            \<not> (signal_of (\<sigma>' A) \<tau>'' A i \<and> signal_of (\<sigma>' B) \<tau>'' B i)"
        by auto
      have " \<tau>'' 0 = 0"
        unfolding \<tau>''_def  by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
      have sA: "signal_of (\<sigma>' A) \<tau>'' A 0 = \<sigma>' A"
        by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def) 
      have sB: "signal_of (\<sigma>' B) \<tau>'' B 0 = \<sigma>' B"
        by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def) 
      have "next_time 0 \<tau>'' \<le> Suc i" and "1 \<le> next_time 0 \<tau>''"
        unfolding `next_time 0 \<tau>'' = 1` by auto
      have " get_beh res 1 =  (\<theta>'' (1:=(Some \<circ> \<sigma>''))) 1"
        using beh_res2[OF bigstep3 ind1'' `next_time 0 \<tau>'' \<le> Suc i` _ ind3' `1 \<le> next_time 0 \<tau>''`] 
        unfolding `next_time 0 \<tau>'' = 1` by auto
      also have "... = Some o \<sigma>''"
        by auto
      finally have " get_beh res 1  = Some o \<sigma>''"
        by auto
      hence "signal_of def (get_beh res) C 1 = \<sigma>'' C"
        by (meson trans_some_signal_of)
      also have "... \<longleftrightarrow> (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
        unfolding \<sigma>''_def next_state_def `next_time 0 \<tau>'' = 1` by auto
      also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        unfolding \<tau>''_def Let_def trans_post_raw_def post_raw_def preempt_raw_def
        by (smt Nat.add_0_right One_nat_def Suc_eq_plus1 cancel_comm_monoid_add_class.diff_cancel
        comp_apply domIff fun_upd_same nec option.sel option.simps(3) override_on_def signal_of_zero
        zero_fun_def)
      also have "... \<longleftrightarrow> \<not> (signal_of (\<sigma>' A) \<tau>'' A 0 \<and> signal_of (\<sigma>' B) \<tau>'' B 0)"
        using sA sB by auto
      finally have IR0: "signal_of def (get_beh res) C 1 \<longleftrightarrow> \<not> (signal_of (\<sigma>' A) \<tau>'' A 0 \<and> signal_of (\<sigma>' B) \<tau>'' B 0)"
        by auto
  
      have "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (\<sigma>' A) (?\<tau>'(0:=0)) A i"
        unfolding \<tau>''_def  using signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' A) ?\<tau>' A i"
        by (smt \<sigma>'_def comp_apply next_state_def ntime override_on_def signal_of2_rem_curr_trans_at_0)
      also have "... = signal_of (\<sigma>' A) \<tau> A i"  
        using signal_of_trans_post by fastforce
      also have "... = signal_of False \<tau> A i"
      proof -
        have " (to_trans_raw_sig \<tau> A) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> A) 0 = None"
          by auto
        moreover
        { assume " (to_trans_raw_sig \<tau> A) 0 \<noteq> None"
          hence ?thesis 
            by (meson signal_of2_cong_neq_none_at_0) }
        moreover
        { assume " (to_trans_raw_sig \<tau> A) 0 = None"
          hence "A \<notin> dom ( (trans_post_raw C True False \<tau> 0 1) 0)"
            unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def
            by auto
          hence "\<sigma>' A = False"
            unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
          hence ?thesis by auto }
        ultimately show ?thesis by auto
      qed
      finally have hel: "signal_of (\<sigma>' A) \<tau>'' A i = signal_of False \<tau> A i"
        by auto
  
      have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (\<sigma>' B) (?\<tau>'(0:=0)) B i"
        unfolding \<tau>''_def  using signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' B) ?\<tau>' B i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def by metis
      also have "... = signal_of (\<sigma>' B) \<tau> B i"  
        using signal_of_trans_post by fastforce
      also have "... = signal_of False \<tau> B i"
      proof -
        have " (to_trans_raw_sig \<tau> B) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> B) 0 = None"
          by auto
        moreover
        { assume " (to_trans_raw_sig \<tau> B) 0 \<noteq> None"
          with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
        moreover
        { assume " (to_trans_raw_sig \<tau> B) 0 = None"
          hence "B \<notin> dom ( (trans_post_raw C True False \<tau> 0 1) 0)"
             unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def by auto
          hence "\<sigma>' B = False"
            unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
          hence ?thesis by auto }
        ultimately show ?thesis by auto
      qed
      finally have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of False \<tau> B i"
        by auto
      then have ?thesis
        using IR IR0 hel le_less_linear by auto }
    moreover
    { assume "\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
      hence "False \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        using `\<sigma>' C = False` by auto
      hence not_nec: "\<not> post_necessary_raw 0 (?\<tau>'(0:=0)) 0 C (\<not> (\<sigma>' A \<and> \<sigma>' B)) (\<sigma>' C)"
      proof -
        have " (?\<tau>'(0:=0)) 0 C = None" 
          by  (auto simp add:zero_map)
        thus ?thesis using post_necessary_raw_correctness `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)`
          by (metis plus_nat.add_0 signal_of_zero zero_option_def)
      qed
      hence lookup: " \<tau>'' = preempt_raw C (?\<tau>'(0:=0)) 1"
        unfolding \<tau>''_def trans_post_raw_def by auto
      hence "to_trans_raw_sig \<tau>'' C = 0"
        unfolding preempt_raw_def to_trans_raw_sig_def
        apply (intro ext)+ by (auto simp add: zero_fun_def zero_option_def)
      { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
        hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
          and "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
          unfolding next_event_def ntime Let_def by auto
        hence helper: "\<not> (\<sigma>' A \<and> \<sigma>' B) \<longleftrightarrow>  \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
          unfolding next_state_def Let_def  by (simp add: override_on_def)
        have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> (let m =  \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding next_state_def by auto
        also have "... = \<sigma>' C"
        proof -
          define m where "m =  \<tau>'' (next_time 0 \<tau>'')"
          hence "C \<notin> dom m"
            using `to_trans_raw_sig \<tau>'' C = 0` unfolding next_time_def 
            unfolding to_trans_raw_sig_def  by (metis domIff zero_fun_def zero_option_def)
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
      have ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
        using `to_trans_raw_sig \<tau>'' C = 0` by (simp add: zero_fun_def)
      hence ind5'': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>''(next_time 0 \<tau>'':=0)) C) n = 0"
        by (simp add: to_trans_raw_sig_def)
      have *: "next_time 0 \<tau>'' \<le> i \<Longrightarrow>
         signal_of def (get_beh res) C (Suc i) = (\<not> (signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'' := 0)) A i \<and> signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i))"
        using nand3_correctness_ind[OF bigstep3 _ _ ind1'' ind2'' ind3' _ ind4' ind5'']  
        by auto
      moreover have "next_time 0 \<tau>'' \<le> i \<Longrightarrow> signal_of (\<sigma>'' A) \<tau>'' A i = signal_of (\<sigma>' A) \<tau>'' A i"
      proof (cases "inf_time (to_trans_raw_sig \<tau>'') A i = None")
        case True
        assume "next_time 0 \<tau>'' \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' A) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence " (to_trans_raw_sig \<tau>'' A) (next_time 0 \<tau>'') = 0"
          using `next_time 0 \<tau>'' \<le> i` by auto
        hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))"
          unfolding next_time_def  unfolding trans_post_raw_def to_trans_raw_sig_def
          by (simp add: domIff zero_option_def)
        have "signal_of (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
          using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' A"
          using `A \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))` unfolding next_state_def
          by (metis override_on_apply_notin)
        finally have 0: "signal_of (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
          by auto
        have 1: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
          using True unfolding to_signal_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') A i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal_def comp_def by auto
      qed
      moreover have "signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'':=0)) A i = signal_of (\<sigma>'' A) \<tau>'' A i"
        apply (intro signal_of_rem_curr_trans_at_t)
        using ind1' ind2' by auto
      moreover have "(next_time 0 \<tau>'') \<le> i \<Longrightarrow> signal_of (\<sigma>'' B) \<tau>'' B i = signal_of (\<sigma>' B) \<tau>'' B i"
      proof (cases "inf_time (to_trans_raw_sig \<tau>'') B i = None")
        case True
        assume "(next_time 0 \<tau>'') \<le> i"
        have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' B) k = 0"
          using True by (auto dest!: inf_time_noneE2)
        hence " (to_trans_raw_sig \<tau>'' B) (next_time 0 \<tau>'') = 0"
          using `(next_time 0 \<tau>'') \<le> i` by auto
        hence "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))"
          unfolding next_time_def  unfolding trans_post_raw_def to_trans_raw_sig_def
          by (simp add: domIff zero_option_def)
        have "signal_of (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
          using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
        also have "... = \<sigma>' B"
          using `B \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))` unfolding next_state_def
          by (metis override_on_apply_notin)
        finally have 0: "signal_of (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
          by auto
        have 1: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
          using True unfolding to_signal_def comp_def by auto
        then show ?thesis
          using 0 1 by auto
      next
        case False
        then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') B i = Some ta"
          by auto
        then show ?thesis
          unfolding to_signal_def comp_def by auto
      qed
      moreover have "signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i = signal_of (\<sigma>'' B) \<tau>'' B i"
        apply (intro signal_of_rem_curr_trans_at_t)
        using ind1' ind2' by auto
      ultimately have **: "next_time 0 \<tau>'' \<le> i \<Longrightarrow>
         signal_of def (get_beh res) C (Suc i) = (\<not> (signal_of (\<sigma>' A) \<tau>'' A i \<and> signal_of (\<sigma>' B) \<tau>'' B i))"
        by auto
      have "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (\<sigma>' A) (?\<tau>'(0:=0)) A i"
        unfolding \<tau>''_def   using signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' A) ?\<tau>' A i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
      also have "... = signal_of (\<sigma>' A) \<tau> A i"  
        using signal_of_trans_post by fastforce
      also have "... = signal_of False \<tau> A i"
      proof -
        have " (to_trans_raw_sig \<tau> A) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> A) 0 = None"
          by auto
        moreover
        { assume " (to_trans_raw_sig \<tau> A) 0 \<noteq> None"
          with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
        moreover
        { assume " (to_trans_raw_sig \<tau> A) 0 = None"
          hence "A \<notin> dom ((trans_post_raw C True False \<tau> 0 1) 0)"
             unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def
            by auto
          hence "\<sigma>' A = False"
            unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
          hence ?thesis by auto }
        ultimately show ?thesis by auto
      qed
      finally have hel: "signal_of (\<sigma>' A) \<tau>'' A i = signal_of False \<tau> A i"
        by auto
      have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (\<sigma>' B) (?\<tau>'(0:=0)) B i"
        unfolding \<tau>''_def using signal_of_trans_post by fastforce
      also have "... = signal_of (\<sigma>' B) ?\<tau>' B i"
        using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
      also have "... = signal_of (\<sigma>' B) \<tau> B i"
        using signal_of_trans_post by fastforce
      also have "... = signal_of False \<tau> B i"
      proof -
          have " (to_trans_raw_sig \<tau> B) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> B) 0 = None"
            by auto
          moreover
          { assume " (to_trans_raw_sig \<tau> B) 0 \<noteq> None"
            with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
          moreover
          { assume " (to_trans_raw_sig \<tau> B) 0 = None"
            hence "B \<notin> dom ( (trans_post_raw C True False \<tau> 0 1) 0)"
               unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def by auto
            hence "\<sigma>' B = False"
              unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
            hence ?thesis by auto }
          ultimately show ?thesis by auto
        qed
      finally have hel2: "signal_of (\<sigma>' B) \<tau>'' B i = signal_of False \<tau> B i"
        by auto
      { assume "i < next_time 0 \<tau>''"
        hence sA: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
        proof (intro signal_of2_init[where t="0"])
          show "i < next_time 0 \<tau>'' \<Longrightarrow> A \<in> dom ( \<tau>'' 0) \<Longrightarrow> \<sigma>' A = the ( \<tau>'' 0 A)"
            by (metis (full_types) domIff fun_upd_apply ind1' neq0_conv not_less0 zero_upd)
        qed (auto)

        have sB: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B" using `i < next_time 0 \<tau>''`
        proof (intro signal_of2_init[where t="0"])
          show "i < next_time 0 \<tau>'' \<Longrightarrow>  B \<in> dom ( \<tau>'' 0) \<Longrightarrow> \<sigma>' B = the ( \<tau>'' 0 B)"
            by (metis (full_types) domIff fun_upd_apply ind1' neq0_conv not_less0 zero_upd)
        qed (auto)

        have "Suc i < next_time 0 \<tau>'' \<or> Suc i = next_time 0 \<tau>''"
          using `i < next_time 0 \<tau>''` by auto
        moreover
        { assume "Suc i = next_time 0 \<tau>''"
          hence " get_beh res (Suc i) =  (\<theta>''(Suc i := Some \<circ> \<sigma>'')) (Suc i)"
            using beh_res2[OF bigstep3 ind1'' _ _ ind3']  by force
          hence "signal_of def (get_beh res) C (Suc i) = \<sigma>'' C"
            using trans_some_signal_of by fastforce
          also have "... = \<sigma>' C"
          proof -
            define m where "m =  \<tau>'' (next_time 0 \<tau>'')"
            hence "C \<notin> dom m"
              using `to_trans_raw_sig \<tau>'' C = 0` unfolding next_time_def 
              unfolding to_trans_raw_sig_def  by (metis domIff zero_fun_def zero_option_def)
            thus ?thesis
              unfolding \<sigma>''_def next_state_def Let_def override_on_def m_def by auto
          qed
          finally have "signal_of def (get_beh res) C (Suc i) = \<sigma>' C"
            by auto
          with sA sB hel hel2 have ?thesis
            using `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)` by auto }
        moreover
        { assume "Suc i < next_time 0 \<tau>''"
          hence "\<And>t. t \<le> Suc i \<Longrightarrow>  \<theta>'' t =  get_beh res t"
            using   beh_and_res_same_until_now[OF bigstep3 ind1''] by auto
          have "0 < next_time 0 \<tau>''"
            using `Suc i < next_time 0 \<tau>''` by auto
          hence "\<theta>'' = 0 (0:=(Some o \<sigma>'))"
            using \<theta>''_def unfolding add_to_beh_def by auto
          have "signal_of def (get_beh res) C (Suc i) = signal_of def (get_beh res) C 0"
          proof (intro signal_of_less_ind)
            show "\<And>n. 0 < n \<Longrightarrow> n \<le> Suc i \<Longrightarrow>  get_beh res n = 0"
              using `\<And>t. t \<le> Suc i \<Longrightarrow>  \<theta>'' t =  get_beh res t` 
              `\<theta>'' = 0 (0:=Some o \<sigma>')`  
              by (metis (full_types) fun_upd_apply not_less_zero zero_fun_def)
          qed auto
          also have "... = \<sigma>' C"
            by (metis \<open>0 \<le> Suc i\<close> \<open>\<And>t. t \<le> Suc i \<Longrightarrow> \<theta>'' t = get_beh res t\<close> \<open>\<theta>'' = 0(0 := Some \<circ> \<sigma>')\<close>
            fun_upd_same trans_some_signal_of)
          finally have "signal_of def (get_beh res) C (Suc i) = \<sigma>' C"
            by auto
          with sA sB hel hel2 have ?thesis
            using `\<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)` by auto }
        ultimately have "signal_of def (get_beh res) C (Suc i) = (\<not> (signal_of False \<tau> A i \<and> signal_of False \<tau> B i))"
          by auto }
      hence "i < next_time 0 \<tau>'' \<Longrightarrow> signal_of def (get_beh res) C (Suc i) = (\<not> (signal_of False \<tau> A i \<and> signal_of False \<tau> B i))"
        by auto
      with ** have ?thesis
        using hel hel2  using le_less_linear by blast }
    ultimately show ?thesis by auto
  next
    case none
    hence \<tau>''_def: "\<tau>'' = ?\<tau>'(0:=0)"
      using cyc unfolding nand3_def t'_def' by auto
    have "post_necessary_raw 0 ( \<tau>) 0 C True False"
    proof -
      have " \<tau> 0 C = None"
        using assms(2) by (metis to_trans_raw_sig_def zero_map)
      thus ?thesis
        using post_necessary_raw_correctness2 \<open>post_necessary_raw 0 ( \<tau>) 0 C True False\<close> by blast
    qed
    moreover have " \<tau> 0 C = None"
      using assms(2)  unfolding to_trans_raw_sig_def  by (metis zero_map)
    moreover have " ?\<tau>' 1 C = Some True"
      using `post_necessary_raw 0 ( \<tau>) 0 C True False`  unfolding trans_post_raw_def
      post_raw_def by auto
    ultimately have "\<tau>'' \<noteq> 0"
      using False unfolding \<tau>''_def unfolding trans_post_raw_def post_raw_def preempt_raw_def
      by (smt fun_upd_idem_iff fun_upd_triv fun_upd_twist option.distinct(1) zero_fun_def
      zero_neq_one zero_option_def)
    hence "next_time 0 \<tau>'' = (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
      unfolding next_time_def by auto
    also have "... = 1"
    proof (rule Least_equality)
      show "dom ( \<tau>'' 1) \<noteq> {}"
        using False ` ?\<tau>' 1 C = Some True` unfolding \<tau>''_def  
        by  auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y < 1" by auto hence "y = 0" by auto
        hence "dom ( \<tau>'' y) = {}"
          unfolding \<tau>''_def   by (auto simp add: trans_post_raw_def zero_map) }
      thus "\<And>y. dom ( \<tau>'' y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
        by auto
    qed
    finally have "next_time 0 \<tau>'' = 1"
      by auto
    have "\<sigma>' A = False" and "\<sigma>' B = False"
      using none unfolding \<gamma>'_def \<sigma>'_def next_event_def Let_def ntime
      by (metis \<gamma>'_def next_state_fixed_point none)+
    { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
      hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
        and "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
        unfolding next_event_def ntime Let_def by auto
      hence helper: "\<not> (\<sigma>' A \<and> \<sigma>' B) \<longleftrightarrow>  \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
        unfolding next_state_def Let_def  by (simp add: override_on_def)
      have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> (let m =  \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
        unfolding next_state_def by auto
      also have "... = (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
        unfolding `next_time 0 \<tau>'' = 1` by auto
      also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        unfolding \<tau>''_def  `\<sigma>' A = False` `\<sigma>' B = False` using False ` ?\<tau>' 1 C = Some True`
         unfolding trans_post_raw_def Let_def post_raw_def by (auto simp add:override_on_def)
      finally have "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
        by auto
      hence "next_state 0 \<tau>'' \<sigma>' C \<longleftrightarrow> \<not> (next_state 0 \<tau>'' \<sigma>' A \<and> next_state 0 \<tau>'' \<sigma>' B)"
        using helper by auto }
    hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> \<sigma>'' C = (\<not> (\<sigma>'' A \<and> \<sigma>'' B))"
      unfolding \<gamma>''_def \<sigma>''_def by auto
    have "\<And>n. 1 < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
      unfolding \<tau>''_def   unfolding trans_post_raw_def to_trans_raw_sig_def preempt_raw_def 
      post_raw_def by (simp add: zero_option_def)
    hence ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
      unfolding `next_time 0 \<tau>'' = 1` by auto
    hence ind5'': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>'' (next_time 0 \<tau>'':=0)) C) n = 0"
      by (simp add: to_trans_raw_sig_def)
    have *: "1 \<le> i \<Longrightarrow>
       signal_of def (get_beh res) C (Suc i) = (\<not> (signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'' := 0)) A i \<and> signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i))"
      using nand3_correctness_ind[OF bigstep3 _ _ ind1'' ind2'' ind3' _ ind4' ind5'']
      unfolding `next_time 0 \<tau>'' = 1` by auto
    moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' A) \<tau>'' A i = signal_of (\<sigma>' A) \<tau>'' A i"
    proof (cases "inf_time (to_trans_raw_sig \<tau>'') A i = None")
      case True
      assume "1 \<le> i"
      have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' A) k = 0"
        using True by (auto dest!: inf_time_noneE2)
      hence " (to_trans_raw_sig \<tau>'' A) 1 = 0"
        using `1 \<le> i` by auto
      hence "A \<notin> dom ( \<tau>'' 1)"
         unfolding trans_post_raw_def to_trans_raw_sig_def
        by (simp add: domIff zero_option_def)
      have "signal_of (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
        using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
      also have "... = \<sigma>' A"
        using `A \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
        by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
      finally have 0: "signal_of (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
        by auto
      have 1: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
        using True unfolding to_signal_def comp_def by auto
      then show ?thesis
        using 0 1 by auto
    next
      case False
      then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') A i = Some ta"
        by auto
      then show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    moreover have "signal_of (\<sigma>'' A) (\<tau>'' (next_time 0 \<tau>'':=0)) A i =  signal_of (\<sigma>'' A) \<tau>'' A i"
      apply (intro signal_of_rem_curr_trans_at_t)
      using ind1' ind2' by auto
    moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' B) \<tau>'' B i = signal_of (\<sigma>' B) \<tau>'' B i"
    proof (cases "inf_time (to_trans_raw_sig \<tau>'') B i = None")
      case True
      assume "1 \<le> i"
      have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' B) k = 0"
        using True by (auto dest!: inf_time_noneE2)
      hence " (to_trans_raw_sig \<tau>'' B) 1 = 0"
        using `1 \<le> i` by auto
      hence "B \<notin> dom ( \<tau>'' 1)"
         unfolding trans_post_raw_def to_trans_raw_sig_def
        by (simp add: domIff zero_option_def)
      have "signal_of (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
        using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
      also have "... = \<sigma>' B"
        using `B \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
        by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
      finally have 0: "signal_of (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
        by auto
      have 1: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
        using True unfolding to_signal_def comp_def by auto
      then show ?thesis
        using 0 1 by auto
    next
      case False
      then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') B i = Some ta"
        by auto
      then show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    moreover have "signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'':=0)) B i =  signal_of (\<sigma>'' B) \<tau>'' B i"
      apply (intro signal_of_rem_curr_trans_at_t)
      using ind1' ind2' by auto
    ultimately have IR: "1 \<le> i \<Longrightarrow> signal_of def (get_beh res) C (Suc i) \<longleftrightarrow>
                                          \<not> (signal_of (\<sigma>' A) \<tau>'' A i \<and> signal_of (\<sigma>' B) \<tau>'' B i)"
      by auto
    have " \<tau>'' 0 = 0"
      unfolding \<tau>''_def  by (auto simp add: trans_post_raw_def)
    have sA: "signal_of (\<sigma>' A) \<tau>'' A 0 = \<sigma>' A"
      by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def) 
    have sB: "signal_of (\<sigma>' B) \<tau>'' B 0 = \<sigma>' B"
      by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def) 
    have "next_time 0 \<tau>'' \<le> Suc i" and "1 \<le> next_time 0 \<tau>''"
      unfolding `next_time 0 \<tau>'' = 1` by auto
    have " get_beh res 1 =  (\<theta>''(next_time 0 \<tau>'' := Some \<circ> \<sigma>'')) 1"
      using beh_res2[OF bigstep3 ind1'' `next_time 0 \<tau>'' \<le> Suc i` _ ind3' `1 \<le> next_time 0 \<tau>''`] 
      unfolding `next_time 0 \<tau>'' = 1` by auto
    also have "... = Some o \<sigma>''"
      by (simp add: \<open>next_time 0 \<tau>'' = 1\<close>)
    finally have " get_beh res 1  = Some o \<sigma>''"
      by auto
    hence "signal_of def (get_beh res) C 1 = \<sigma>'' C"
      using trans_some_signal_of by fastforce
    also have "... \<longleftrightarrow> (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
      unfolding \<sigma>''_def next_state_def `next_time 0 \<tau>'' = 1` by auto
    also have "... \<longleftrightarrow> \<not> (\<sigma>' A \<and> \<sigma>' B)"
      using ` ?\<tau>' 1 C = Some True` unfolding \<tau>''_def Let_def  `\<sigma>' A = False` `\<sigma>' B = False`
        unfolding trans_post_raw_def  post_raw_def by (auto simp add: override_on_def)
    also have "... \<longleftrightarrow> \<not> (signal_of (\<sigma>' A) \<tau>'' A 0 \<and> signal_of (\<sigma>' B) \<tau>'' B 0)"
      using sA sB by auto
    finally have IR0: "signal_of def (get_beh res) C 1 \<longleftrightarrow> \<not> (signal_of (\<sigma>' A) \<tau>'' A 0 \<and> signal_of (\<sigma>' B) \<tau>'' B 0)"
      by auto

    have "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (\<sigma>' A) (?\<tau>'(0:= 0)) A i"
      unfolding \<tau>''_def by (metis \<tau>''_def sig.distinct(3))
    also have "... = signal_of (\<sigma>' A) ?\<tau>' A i"
      using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
    also have "... = signal_of (\<sigma>' A) \<tau> A i"
      using signal_of_trans_post by fastforce
    also have "... = signal_of False \<tau> A i"
    proof -
      have " (to_trans_raw_sig \<tau> A) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> A) 0 = None"
        by auto
      moreover
      { assume " (to_trans_raw_sig \<tau> A) 0 \<noteq> None"
        with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
      moreover
      { assume " (to_trans_raw_sig \<tau> A) 0 = None"
        hence "A \<notin> dom ( (trans_post_raw C True False \<tau> 0 1) 0)"
          unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def 
          by auto
        hence "\<sigma>' A = False"
          unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
        hence ?thesis by auto }
      ultimately show ?thesis by auto
    qed
    finally have hel: "signal_of (\<sigma>' A) \<tau>'' A i = signal_of False \<tau> A i"
      by auto
    have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (\<sigma>' B) (?\<tau>'(0:=0)) B i"
      unfolding \<tau>''_def  by fastforce
    also have "... = signal_of (\<sigma>' B) ?\<tau>' B i"
      using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
    also have "... = signal_of (\<sigma>' B) \<tau> B i"
      using signal_of_trans_post by fastforce
    also have "... = signal_of False \<tau> B i"
    proof -
      have " (to_trans_raw_sig \<tau> B) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> B) 0 = None"
        by auto
      moreover
      { assume " (to_trans_raw_sig \<tau> B) 0 \<noteq> None"
        with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
      moreover
      { assume " (to_trans_raw_sig \<tau> B) 0 = None"
        hence "B \<notin> dom ( (trans_post_raw C True False \<tau> 0 1) 0)"
           unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def by auto
        hence "\<sigma>' B = False"
          unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
        hence ?thesis by auto }
      ultimately show ?thesis by auto
    qed
    finally have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of False \<tau> B i"
      by auto
    then show ?thesis
      using IR IR0 hel le_less_linear by auto
  qed
qed

end