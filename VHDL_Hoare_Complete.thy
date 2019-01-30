(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory VHDL_Hoare_Complete
  imports Femto_VHDL VHDL_Hoare
begin

subsection "A sound and complete Hoare logic for VHDL's sequential statements"

text \<open>This theory is the second attempt for defining a Hoare logic for VHDL's sequential statement.
As shown in the very last part of this theory, we prove that this definition is both sound and
complete.\<close>

typedef (overloaded) ('signal) worldline2 =
  "{w :: 'signal worldline . (\<exists>t. \<forall>t'. t' > t \<longrightarrow> (\<lambda>s. w s t') = (\<lambda>s. w s t))}"
  morphisms Rep_worldline Abs_worldline
proof -
  define wit :: "'signal worldline" where "wit \<equiv> (\<lambda>s t. False)"
  hence "\<forall>t'. t' > 0 \<longrightarrow> (\<lambda>s. wit s t') = (\<lambda>s. wit s 0)"
    by auto
  thus ?thesis
    by (auto intro: exI[where x="wit"])
qed

setup_lifting type_definition_worldline2

text \<open> The reason why the first attempt of defining the semantics in @{theory Draft.VHDL_Hoare} is
not complete is because not all worldline can be transformed into elements of the operational
semantics, especially the transaction @{term "\<tau> :: 'signal transaction"}. Why is this so?

Imagine a worldline @{term "w"} where it always alternate between @{term "True :: val"} and @{term
"False :: val"} for a specific signal @{term "sig :: 'signal"}. When we attempt to find the
derivative via @{term "derivative_raw w"}, its result cannot be a @{typ "'signal transaction"}
because it will have infinite mappings (since it constantly changes the value between @{term "True
:: val"} and @{term "False :: val"}, and a @{typ "'signal transaction"} needs to be zero at nearly
everywhere, i.e., eventually the mapping will ``die out''.

The typedef of @{typ "'signal worldline2"} imposes that eventually there will be no more mapping.
Hence, when we attempt to find its derivative, we can construct a @{typ "'signal transaction"}.
\<close>

definition worldline_deg :: "'signal worldline2 \<Rightarrow> nat" where
  "worldline_deg w = (LEAST n. \<forall>t > n. \<forall>s. Rep_worldline w s t = Rep_worldline w s n)"

lemma existence_of_degree:
  fixes w :: "'signal worldline2"
  shows "\<exists>x. \<forall>t > x. \<forall>s. Rep_worldline w s t = Rep_worldline w s x"
  by transfer meson

lemma property_of_degree:
  fixes w :: "'signal worldline2"
  defines "d \<equiv> worldline_deg w"
  shows "\<forall>t > d. \<forall>s. Rep_worldline w s t = Rep_worldline w s d"
  using LeastI_ex[OF existence_of_degree] unfolding d_def worldline_deg_def by auto

lift_definition worldline_upd2 ::
  "'signal worldline2 \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline2" ("_[_, _:=\<^sub>2 _]")
  is worldline_upd
proof -
  fix w :: "'signal \<Rightarrow> nat \<Rightarrow> val"
  fix sig v
  fix t :: nat
  assume "\<exists>t. \<forall>t'>t. (\<lambda>s'. w s' t') = (\<lambda>s'. w s' t)"
  then obtain tcurr :: "nat" where *: "\<forall>t' > tcurr. (\<lambda>s'. w s' t') = (\<lambda>s'. w s' tcurr)"
    by auto
  have "t < tcurr \<or> tcurr \<le> t"
    by auto
  moreover
  { assume "t < tcurr"
    hence "\<forall>t'> tcurr. (\<lambda>s. w[sig, t:= v] s t') = (\<lambda>s. w[sig, t:= v] s tcurr)"
      by (metis * less_trans not_less_iff_gr_or_eq worldline_upd_def)
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. w[sig, t:= v] s t') = (\<lambda>s. w[sig, t:= v] s t'')"
      by auto }
  moreover
  { assume "tcurr \<le> t"
    hence "\<forall>t'> t. (\<lambda>s. w[sig, t:= v] s t') = (\<lambda>s. w[sig, t:= v] s t)"
      by (metis (full_types) "*" le_less_trans nat_less_le worldline_upd_def)
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. w[sig, t:= v] s t') = (\<lambda>s. w[sig, t:= v] s t'')"
      by auto }
  ultimately show "\<exists>t''. \<forall>t'>t''. (\<lambda>s. w[sig, t:= v] s t') = (\<lambda>s. w[sig, t:= v] s t'')"
    by auto
qed

lift_definition worldline_inert_upd2 ::
  "'signal worldline2 \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> 'signal worldline2" ("_[_, _, _ :=\<^sub>2 _]")
  is worldline_inert_upd
proof -
  fix w :: "'signal \<Rightarrow> nat \<Rightarrow> val"
  fix sig v
  fix t1 t2 :: nat
  assume "\<exists>t. \<forall>t'>t. (\<lambda>s'. w s' t') = (\<lambda>s'. w s' t)"
  then obtain tcurr :: "nat" where *: "\<forall>t' > tcurr. (\<lambda>s'. w s' t') = (\<lambda>s'. w s' tcurr)"
    by auto
  have "t1 + t2 < tcurr \<or> tcurr \<le> t1 + t2"
    by auto
  moreover
  { assume "t1 + t2 < tcurr"
    hence "\<forall>t'> tcurr. (\<lambda>s. w[sig, t1, t2 := v] s t') = (\<lambda>s. w[sig, t1, t2 := v] s tcurr)"
      by (metis "*" le_add1 le_less_trans less_irrefl_nat order.strict_trans  worldline_inert_upd_def)
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. w[sig, t1, t2:= v] s t') = (\<lambda>s. w[sig, t1, t2:= v] s t'')"
      by auto }
  moreover
  { assume "tcurr \<le> t1 + t2"
    have "\<forall>t'> t1 + t2. (\<lambda>s. w[sig, t1, t2 := v] s t') = (\<lambda>s. w[sig, t1, t2 := v] s (t1 + t2))"
    proof (rule, rule)
      fix t'
      assume "t' > t1 + t2" hence "t' > tcurr" using `t1 + t2 \<ge> tcurr` by auto
      { fix s
        have "s \<noteq> sig \<or> s = sig" by auto
        moreover
        { assume "s \<noteq> sig"
          hence "w[sig, t1, t2:= v] s t' = w[sig, t1, t2 := v] s (t1 + t2)"
            by (metis "*" \<open>tcurr < t'\<close> \<open>tcurr \<le> t1 + t2\<close> le_less option.sel worldline_inert_upd_def) }
        moreover
        { assume "s = sig"
          hence "w[sig, t1, t2 := v] s t' = w[sig, t1, t2 := v] s (t1 + t2)"
            by (metis \<open>t1 + t2 < t'\<close> not_less_iff_gr_or_eq trans_less_add1 worldline_inert_upd_def) }
        ultimately have "w[sig, t1, t2 := v] s t' = w[sig, t1, t2 := v] s (t1 + t2)"
          by auto }
      thus " (\<lambda>s. w[sig, t1, t2 := v] s t') = (\<lambda>s. w[sig, t1, t2 := v] s (t1 + t2))"
        by auto
    qed
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. w[sig, t1, t2:= v] s t') = (\<lambda>s. w[sig, t1, t2:= v] s t'')"
      by auto }
  ultimately show "\<exists>t''. \<forall>t'> t''. (\<lambda>s. w[sig, t1, t2:= v] s t') = (\<lambda>s. w[sig, t1, t2:= v] s t'')"
    by auto
qed

lift_definition state_of_world2 :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal state" is
  state_of_world .

lift_definition event_of_world2 :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal event" is
  event_of_world .

lift_definition beh_of_world2 :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal transaction" is
  beh_of_world_raw  unfolding beh_of_world_raw_def zero_map by auto

lemma [simp]:
  "beh_of_world2 w 0 = 0"
  by (transfer', auto simp add:  beh_of_world_raw_def zero_option_def zero_fun_def)

lift_definition beval_world2 :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal bexp \<Rightarrow> val"
  is beval_world .

type_synonym 'signal assn2 = "'signal worldline2 \<Rightarrow> bool"

inductive
  seq_hoare2 :: "nat \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>_ ([(1_)]/ (_)/ [(1_)])" 50)
  where
Null2: "\<turnstile>\<^sub>t [P] Bnull [P]" |
Assign2: "\<turnstile>\<^sub>t [\<lambda>w. P(w[sig, t + dly :=\<^sub>2 beval_world2 w t exp])] Bassign_trans sig exp dly [P]" |

AssignI2: "\<turnstile>\<^sub>t [\<lambda>w. P(w[sig, t, dly :=\<^sub>2 beval_world2 w t exp])] Bassign_inert sig exp dly [P]" |

Comp2: "\<lbrakk> \<turnstile>\<^sub>t [P] s1 [Q]; \<turnstile>\<^sub>t [Q] s2 [R]\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t [P] Bcomp s1 s2 [R]" |

If2: "\<lbrakk>\<turnstile>\<^sub>t [\<lambda>w. P w \<and> beval_world2 w t g] s1 [Q]; \<turnstile>\<^sub>t [\<lambda>w. P w \<and> \<not> beval_world2 w t  g] s2 [Q]\<rbrakk>
        \<Longrightarrow>  \<turnstile>\<^sub>t [P] Bguarded g s1 s2 [Q]" |

Conseq2: "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile>\<^sub>t [P] s [Q]; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t [P'] s [Q']"

inductive_cases seq_hoare2_ic: "\<turnstile>\<^sub>t [P] s [Q]"

lemma BnullE_hoare2:
  assumes "\<turnstile>\<^sub>t [P] s [Q]"
  assumes "s = Bnull"
  shows "\<forall>w. P w \<longrightarrow> Q w"
  using assms
  by (induction rule:seq_hoare2.induct, auto)

lemma BnullE'_hoare2:
  "\<turnstile>\<^sub>t [P] Bnull [Q] \<Longrightarrow> \<forall>w. P w \<longrightarrow> Q w"
  using BnullE_hoare2 by blast

lemma BassignE_hoare2:
  assumes "\<turnstile>\<^sub>t [P] s [Q]"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly :=\<^sub>2 beval_world2 w t exp])"
  using assms
  by (induction rule: seq_hoare2.induct, auto)

lemma Bassign_inertE_hoare2:
  assumes "\<turnstile>\<^sub>t [P] s [Q]"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>w. P w \<longrightarrow> Q(w[sig, t, dly :=\<^sub>2 beval_world2 w t exp])"
  using assms
  by (induction rule: seq_hoare2.induct, auto)

lemma BcompE_hoare2:
  assumes "\<turnstile>\<^sub>t [P] s [R]"
  assumes "s = Bcomp s1 s2"
  shows "\<exists>Q. \<turnstile>\<^sub>t [P] s1 [Q] \<and> \<turnstile>\<^sub>t [Q] s2 [R]"
  using assms Conseq2
  by (induction rule:seq_hoare2.induct, auto) (blast)

lemmas [simp] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2
lemmas [intro!] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2

lemma strengthen_pre_hoare2:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile>\<^sub>t [P] s [Q]"
  shows "\<turnstile>\<^sub>t [P'] s [Q]"
  using assms by (blast intro: Conseq2)

lemma weaken_post_hoare2:
  assumes "\<forall>w. Q w \<longrightarrow> Q' w" and "\<turnstile>\<^sub>t [P] s [Q]"
  shows "\<turnstile>\<^sub>t [P] s [Q']"
  using assms by (blast intro: Conseq2)

lemma Assign'_hoare2:
  assumes "\<forall>w. P w \<longrightarrow> Q (worldline_upd2 w sig (t + dly) (beval_world2 w t exp))"
  shows "\<turnstile>\<^sub>t [P] Bassign_trans sig exp dly [Q]"
  using assms by (simp add: strengthen_pre_hoare2)

subsubsection \<open>Validity of Hoare proof rules\<close>

lift_definition worldline2 ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal worldline2"
  is worldline
proof -
  fix t0 :: nat
  fix \<sigma> :: "'signal state"
  fix \<theta> \<tau> :: "'signal transaction"

  define last where "last \<equiv> max (Poly_Mapping.degree \<tau>) (Poly_Mapping.degree \<theta>)"

  have "\<forall>t'>max last t0. (\<lambda>s. worldline t0 \<sigma> \<theta> \<tau> s t') = (\<lambda>s. worldline t0 \<sigma> \<theta> \<tau> s (max last t0))"
  proof (rule, rule)
    fix t'
    assume "max last t0 < t'"
    { fix s
      have *: "\<And>n. max last t0 < n \<Longrightarrow> n \<le> t' \<Longrightarrow> lookup \<tau> n = 0"
        by (simp add: beyond_degree_lookup_zero local.last_def)
      have "worldline t0 \<sigma> \<theta> \<tau> s t' = signal_of2 (\<sigma> s) \<tau> s t'"
        by (meson \<open>max last t0 < t'\<close> less_imp_not_less less_max_iff_disj worldline_def)
      also have "... = signal_of2 (\<sigma> s) \<tau> s (max last t0)"
        using signal_of2_less_ind[OF * `max last t0 < t'`] by metis
      also have "... = worldline t0 \<sigma> \<theta> \<tau> s (max last t0)"
        by (simp add: worldline_def)
      finally have "worldline t0 \<sigma> \<theta> \<tau> s t' = worldline t0 \<sigma> \<theta> \<tau> s (max last t0)"
        by auto }
    thus "(\<lambda>s. worldline t0 \<sigma> \<theta> \<tau> s t') = (\<lambda>s. worldline t0 \<sigma> \<theta> \<tau> s (max last t0))"
      by auto
  qed
  thus "\<exists>t''. \<forall>t'>t''. (\<lambda>s. worldline t0 \<sigma> \<theta> \<tau> s t') = (\<lambda>s. worldline t0 \<sigma> \<theta> \<tau> s t'')"
    by (auto intro:exI[where x="max last t0"])
qed

definition difference :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal \<rightharpoonup> val" where
  "difference w t = (\<lambda>s. if Rep_worldline w s t \<noteq> Rep_worldline w s (t - 1) then Some (Rep_worldline w s t) else None)"

lemma difference_beyond_degree:
  fixes w :: "'signal worldline2"
  defines "d \<equiv> worldline_deg w"
  shows "\<forall>n > d. difference w n = 0"
proof -
  { fix s
    have "\<forall>n > d. Rep_worldline w s n = Rep_worldline w s d"
      using property_of_degree unfolding d_def by auto
    hence "\<forall>n > d. Rep_worldline w s n = Rep_worldline w s (n - 1)"
      by (metis (full_types) diff_Suc_1 gr0_implies_Suc less_add_same_cancel2 less_imp_Suc_add
      less_linear not_add_less1 trans_less_add1) }
  thus ?thesis
    unfolding difference_def unfolding zero_fun_def by (simp add: zero_option_def)
qed

lift_definition derivative :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal transaction"
  is "\<lambda>w t n. if n < t then Map.empty else if n = t then Some o (\<lambda>s. Rep_worldline w s t) else difference w n"
  unfolding sym[OF eventually_cofinite] MOST_nat
proof -
  fix w :: "'signal worldline2"
  fix t :: nat
  define d where "d = worldline_deg w"
  have "\<forall>n > max d t. difference w n = 0"
    by (simp add: d_def difference_beyond_degree)
  hence "\<forall>n>max d t. (if n < t then Map.empty else if n = t then Some \<circ> (\<lambda>s. Rep_worldline w s t) else difference w n) = 0"
    by auto
  thus "\<exists>t''. \<forall>n>t''. (if n < t then Map.empty else if n = t then Some \<circ> (\<lambda>s. Rep_worldline w s t) else difference w n) = 0"
    by blast
qed

definition destruct_worldline ::
  "'signal worldline2 \<Rightarrow> nat \<Rightarrow> ('signal state \<times> 'signal event \<times> 'signal transaction \<times> 'signal transaction)"
  where
  "destruct_worldline w t = (let \<sigma> = (\<lambda>s. Rep_worldline w s t);
                                 \<theta> = poly_mapping_of_fun (\<lambda>t. Some o (\<lambda>s. (Rep_worldline w) s t)) 0 t;
                                 \<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)};
                                 \<tau> = derivative_raw (Rep_worldline w) (worldline_deg w) t
                             in (\<sigma>, \<gamma>, \<theta>, \<tau>))"

text \<open>One might concern about the event @{term "\<gamma> :: 'signal event"} obtained from the destruction
@{term "destruct_worldline w t"} above. What happens if @{term "t = 0"}? This is a valid concern
since we have the expression @{term "t - 1"} in the definition of @{term "\<gamma>"} above.

Note that, we impose the requirement of @{term "context_invariant"} here. When this is the case,
history @{term "\<theta> :: 'signal transaction"} is empty when @{term "t = 0"}. Hence the expression
@{term "signal_of2 False \<theta> s (t - 1)"} is equal to @{term "signal_of2 False empty_trans s 0"} and,
subsequently, equals to @{term "False"}. Hence, when @{term "t = 0"}, the @{term "\<gamma>"} enumerates the
signals which are different with the default value @{term "False :: val"}.\<close>

lemma destruct_worldline_exist:
  "\<exists>\<sigma> \<gamma> \<theta> \<tau>. destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
  unfolding destruct_worldline_def Let_def by auto

lemma worldline2_constructible:
  fixes w :: "'signal worldline2"
  assumes "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
  shows "w = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
proof -
  have "\<exists>t. \<forall>t'>t. (\<lambda>s. Rep_worldline w s t') = (\<lambda>s. Rep_worldline w s t)"
    by transfer auto
  thus ?thesis
    using assms unfolding destruct_worldline_def Let_def worldline_deg_def
  proof transfer'
    fix w :: "'signal worldline"
    fix t \<sigma> \<gamma>
    fix \<theta> \<tau> :: "'signal transaction"
    assume *: "\<exists>t. \<forall>t'>t. (\<lambda>s. w s t') = (\<lambda>s. w s t)"
    then obtain d where d_def: "d = (LEAST t. \<forall>t'>t. (\<lambda>s. w s t') = (\<lambda>s. w s t))"
      by auto
    have d_prop: "\<forall>t'>d. (\<lambda>s. w s t') = (\<lambda>s. w s d)"
      using LeastI_ex[OF *] unfolding d_def  by blast
    hence d_prop': "\<And>n s. d < n \<Longrightarrow> w s n = w s d"
      by meson
    have d_def': "d = (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n)"
      unfolding d_def  by metis
    assume **:
      "(\<lambda>s. w s t,
        {s. w s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>t. Some \<circ> (\<lambda>s. w s t)) 0 t) s (t - 1)},
        poly_mapping_of_fun (\<lambda>t. Some \<circ> (\<lambda>s. w s t)) 0 t,
        derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
    hence \<sigma>_def: "\<sigma> = (\<lambda>s. w s t)" and
          \<gamma>_def: "\<gamma> = {s. w s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>t. Some \<circ> (\<lambda>s. w s t)) 0 t) s (t - 1)}" and
          \<theta>_def: "\<theta> = poly_mapping_of_fun (\<lambda>t. Some \<circ> (\<lambda>s. w s t)) 0 t"
      by auto
    have \<tau>_def: "\<tau> = derivative_raw w d t"
      using ** unfolding d_def' by auto
    have "w = worldline t \<sigma> \<theta> \<tau>"
    proof (rule ext, rule ext, cases "t \<le> d")
      case True
      fix s' t'
      have "t' < t \<or> t \<le> t'" by auto
      moreover
      { assume "t' < t"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' =  signal_of2 False \<theta> s' t'"
          unfolding worldline_def by auto
        also have "... = w s' t'"
          using signal_of2_poly_mapping_fun[OF `t' < t`] unfolding \<theta>_def by metis
        finally have "w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      moreover
      { assume "t \<le> t'"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 (\<sigma> s') \<tau> s' t'"
          unfolding worldline_def by auto
        also have "... = w s' t'"
          unfolding \<tau>_def using signal_of2_derivative_raw'[OF `t \<le> t'` True] d_prop' by metis
        finally have "w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      ultimately show "w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
        by auto
    next
      case False
      fix s' t'
      have "t' < t \<or> t \<le> t'" by auto
      moreover
      { assume "t' < t"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' =  signal_of2 False \<theta> s' t'"
          unfolding worldline_def by auto
        also have "... = w s' t'"
          using signal_of2_poly_mapping_fun[OF `t' < t`] unfolding \<theta>_def by metis
        finally have "w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      moreover
      { assume "t \<le> t'"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 (\<sigma> s') \<tau> s' t'"
          unfolding worldline_def by auto
        also have "... = signal_of2 (\<sigma> s') 0 s' t'"
          unfolding \<tau>_def using derivative_raw_zero False  by (metis le_less_linear)
        also have "... = \<sigma> s'"
          using signal_of2_empty by fastforce
        also have "... = w s' t"
          unfolding \<sigma>_def by auto
        also have "... = w s' t'"
          using d_prop'[of "t"] d_prop'[of "t'"] False `t \<le> t'` by auto
        finally have "w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      ultimately show "w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
        by auto
    qed
    have "\<forall>n. t \<le> n \<longrightarrow> lookup \<theta> n = 0"
      unfolding \<theta>_def apply transfer' by auto
    moreover have "\<forall>n. n < t \<longrightarrow> lookup \<tau> n = 0"
      unfolding \<tau>_def
      by (transfer', metis (mono_tags) derivative_raw.rep_eq derivative_raw_zero lookup_zero)
    moreover have "\<forall>s. s \<in> dom (lookup \<tau> t) \<longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
      unfolding \<tau>_def \<sigma>_def by transfer' auto
    ultimately have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
      unfolding \<gamma>_def context_invariant_def \<sigma>_def \<theta>_def by auto
    thus " w = worldline t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
      using `w = worldline t \<sigma> \<theta> \<tau>` by auto
  qed
qed

lemma worldline2_constructible':
  fixes w :: "'signal worldline2"
  fixes t :: nat
  shows "\<exists>\<sigma> \<gamma> \<theta> \<tau>. w = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  by (meson destruct_worldline_def worldline2_constructible)

lemma state_worldline2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "(\<lambda>s. Rep_worldline (worldline2 t \<sigma> \<theta> \<tau>) s t) = \<sigma>"
  using assms
proof (intro ext, transfer')
  fix s t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau>
  assume ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  hence "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
    unfolding context_invariant_def by auto
  have "lookup \<tau> t s = 0 \<or> lookup \<tau> t s \<noteq> 0" by auto
  moreover
  { assume "lookup \<tau> t s \<noteq> 0"
    hence "s \<in> dom (lookup \<tau> t)"
      by (metis domIff zero_fun_def zero_map)
    hence "\<sigma> s = the (lookup \<tau> t s)"
      using ci unfolding context_invariant_def by auto
    hence lookup: "lookup \<tau> t s = Some (\<sigma> s)"
      by (simp add: \<open>s \<in> dom (get_trans \<tau> t)\<close> domD)
    hence " signal_of2 (\<sigma> s) \<tau> s t = \<sigma> s"
      using lookup_some_signal_of2'[of "\<tau>" "t" "s" "\<sigma>", OF lookup] by auto
    hence "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
      unfolding worldline_def by auto }
  moreover
  { assume "lookup \<tau> t s = 0"
    have "\<forall>k\<in>dom (lookup (to_transaction2 \<tau> s)). t < k"
    proof (rule ccontr)
      assume "\<not> (\<forall>k\<in>dom (lookup (to_transaction2 \<tau> s)). t < k)"
      then obtain k where k_dom: "k \<in> dom (lookup (to_transaction2 \<tau> s))" and "k \<le> t"
        using leI by blast
      have "lookup \<tau> k s = 0"
        using `\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0` `lookup \<tau> t s = 0` `k \<le> t`
        by (metis antisym_conv1 zero_fun_def)
      moreover have "lookup \<tau> k s \<noteq> 0"
        using k_dom unfolding domIff zero_option_def apply transfer' unfolding to_trans_raw2_def
        by auto
      ultimately show "False"
        by auto
    qed
    hence "inf_time (to_transaction2 \<tau>) s t = None"
      by (intro inf_time_noneI)
    hence "signal_of2 (\<sigma> s) \<tau> s t = \<sigma> s"
      unfolding to_signal2_def comp_def by auto
    hence "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
      unfolding worldline_def by auto }
  ultimately show "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
    by auto
qed

lemma history_worldline2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. Rep_worldline (worldline2 t \<sigma> \<theta> \<tau>) s ta)) 0 t) s (t - 1) =
         signal_of2 False \<theta> s (t - 1)"
  using assms
proof transfer'
  fix t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> s
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  hence "lookup \<theta> t = 0"
    unfolding context_invariant_def by auto
  have "0 < t \<or> t = 0" by auto
  moreover
  { assume "0 < t"
    hence "t - 1 < t"
      by auto
    have *: "\<And>n.        n \<le> t - 1 \<Longrightarrow>
         lookup (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s taa)) 0 t) n =
         lookup (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) n"
      apply transfer' unfolding worldline_def by auto
    have " signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1) =
           signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s (t - 1)"
      using signal_of2_lookup_same[OF *] by auto
    also have "... = signal_of2 False \<theta> s (t - 1)"
      using signal_of2_poly_mapping_fun[OF `t - 1 < t`] by metis
    finally have "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1) = signal_of2 False \<theta> s (t - 1)"
      by auto }
  moreover
  { assume "t = 0"
    hence "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1) =
           signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline 0 \<sigma> \<theta> \<tau> s ta)) 0 0) s 0"
      by auto
    also have "... =  signal_of2 False 0 s 0"
      unfolding poly_mapping_of_fun_empty_set  by auto
    also have "... = signal_of2 False \<theta> s 0"
      using `lookup \<theta> t = 0` unfolding `t = 0` using signal_of2_zero
      by (metis signal_of2_empty zero_fun_def)
    also have "... = signal_of2 False \<theta> s (t - 1)"
      using `t = 0` by auto
    finally have "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1) = signal_of2 False \<theta> s (t - 1)"
      by auto }
  ultimately show "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1) = signal_of2 False \<theta> s (t - 1)"
    by auto
qed

lemma beh_of_worldline:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "\<And>k. signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. Rep_worldline (worldline2 t \<sigma> \<theta> \<tau>) s ta)) 0 t) s k =
             signal_of2 False \<theta> s k"
  using assms
proof transfer'
  fix k t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> s
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  hence "lookup \<theta> t = 0"
    unfolding context_invariant_def by auto
  have *: "\<And>n.
       lookup (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s taa)) 0 t) n =
       lookup (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) n"
    apply transfer' unfolding worldline_def by auto
  have **: " signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s k =
         signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s k"
    using signal_of2_lookup_same[OF *] by auto
  have "k < t \<or> t \<le> k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s k
          = signal_of2 False \<theta> s (k)"
      using signal_of2_poly_mapping_fun[OF `k < t`] by metis
    hence "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s k = signal_of2 False \<theta> s k"
      using ** by auto }
  moreover
  { assume "t \<le> k"
    have "0 < t \<or> t = 0"
      by auto
    moreover
    { assume "0 < t"
      hence "t - 1 < k" and "t - 1 < t"
        using `0 < t` `t \<le> k` by auto
      have history: "\<And>n. t - 1 < n \<Longrightarrow> n \<le> k \<Longrightarrow> lookup \<theta> n = 0"
        using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
      have "\<And>n. t - 1 < n \<Longrightarrow> n \<le> k \<Longrightarrow> lookup (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) n = 0"
        apply transfer' by auto
      with signal_of2_less_ind[OF this]
      have "signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s k =
             signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s (t - 1)"
        using `t - 1 < k` by auto
      also have "... = signal_of2 False \<theta> s (t - 1)"
        using signal_of2_poly_mapping_fun[OF `t -1 < t`, where w="signal_of2 False \<theta>"] by auto
      also have "... = signal_of2 False \<theta> s k"
        using signal_of2_less_ind[OF history] `t - 1 < k` by auto
      finally have "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s k = signal_of2 False \<theta> s k"
        using ** by auto }
    moreover
    { assume "t = 0"
      hence "signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s k =
            signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 0) s k"
        by auto
      also have "... = signal_of2 False 0 s k"
        unfolding poly_mapping_of_fun_empty_set by auto
      also have "... = False"
        using signal_of2_empty by fastforce
      finally have step: "signal_of2 False (poly_mapping_of_fun (\<lambda>taa. Some \<circ> (\<lambda>s. signal_of2 False \<theta> s taa)) 0 t) s k = False"
        using ** by auto
      have history: "\<And>n. t - 1 < n \<Longrightarrow> n \<le> k \<Longrightarrow> lookup \<theta> n = 0"
        using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
      hence "signal_of2 False \<theta> s k = signal_of2 False \<theta> s 0"
        using signal_of2_less_ind[OF history] `t \<le> k` unfolding `t = 0` by force
      also have "... = False"
        using `lookup \<theta> t = 0`  by (metis \<open>t = 0\<close> signal_of2_zero zero_fun_def)
      finally have "signal_of2 False \<theta> s k = False"
        by auto
      hence "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s k = signal_of2 False \<theta> s k"
        using step using "**" by blast }
    ultimately have "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s k = signal_of2 False \<theta> s k"
      by auto }
  ultimately show "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s k = signal_of2 False \<theta> s k"
    by auto
qed

lemma event_worldline2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "{s. Rep_worldline (worldline2 t \<sigma> \<theta> \<tau>) s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. Rep_worldline (worldline2 t \<sigma> \<theta> \<tau>) s ta)) 0 t) s (t - 1)} = \<gamma>"
  using assms state_worldline2[OF assms]
proof transfer'
  fix t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau>
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assume *: "(\<lambda>s. worldline t \<sigma> \<theta> \<tau> s t) = \<sigma>"
  have **: "\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
    using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
  have "{s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)} =
        {s. \<sigma> s \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)}"
    using * by metis
  moreover have "\<And>s. signal_of2 False \<theta> s (t - 1) =
            signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)"
    using history_worldline2 by (metis \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close> worldline2.rep_eq)
  ultimately have "{s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)} =
                   {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
    by auto
  thus " {s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)} = \<gamma>"
    using ** by auto
qed

lemma transaction_worldline2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "\<And>k s . signal_of2 (\<sigma> s) (derivative_raw (Rep_worldline (worldline2 t \<sigma> \<theta> \<tau>)) (worldline_deg (worldline2 t \<sigma> \<theta> \<tau>)) t) s k =
                signal_of2 (\<sigma> s) \<tau> s k"
  using assms unfolding worldline_deg_def
proof transfer'
  fix k s t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau>
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  define deg where "deg = (LEAST n. \<forall>ta>n. \<forall>s. worldline t \<sigma> \<theta> \<tau> s ta = worldline t \<sigma> \<theta> \<tau> s n)"
  have deg_prop: "\<forall>ta > deg. \<forall>s. worldline t \<sigma> \<theta> \<tau> s ta = worldline t \<sigma> \<theta> \<tau> s deg"
    using LeastI_ex[OF exists_quiesce_worldline[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]] unfolding deg_def
    by blast
  have "k < t \<or> t \<le> k \<and> k \<le> deg \<or> deg < k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k = \<sigma> s"
      using signal_of2_derivative_before_now \<open>k < t\<close> by fastforce
    moreover have "signal_of2 (\<sigma> s) \<tau> s k = \<sigma> s"
    proof -
      have "\<forall>n\<in>dom (lookup (to_transaction2 \<tau> s)). k < n"
      proof (rule ccontr)
        assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 \<tau> s)). k < n)"
        then obtain n where "n \<in> dom (lookup (to_transaction2 \<tau> s))" and "n \<le> k"
          using leI by blast
        hence "lookup \<tau> n = 0"
          using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def using `k < t`
          by auto
        hence "n \<notin> dom (lookup (to_transaction2 \<tau> s))"
          apply transfer' unfolding to_trans_raw2_def  by (simp add: domIff zero_map)
        with `n \<in> dom (lookup (to_transaction2 \<tau> s))` show False by auto
      qed
      hence "inf_time (to_transaction2 \<tau>) s k = None"
        by (rule inf_time_noneI)
      thus ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    ultimately have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k =
                     signal_of2 (\<sigma> s) \<tau> s k"
      by auto }
  moreover
  { assume "t \<le> k \<and> k \<le> deg"
    hence "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k = (worldline t \<sigma> \<theta> \<tau>) s k"
      using signal_of2_derivative_raw by metis
    also have "... = signal_of2 (\<sigma> s) \<tau> s k"
      unfolding worldline_def using `t \<le> k \<and> k \<le> deg` by auto
    finally have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k =
                     signal_of2 (\<sigma> s) \<tau> s k"
      by auto }
  moreover
  { assume "deg < k"
    have "t \<le> deg \<or> deg < t" by auto
    moreover
    { assume "t \<le> deg"
      hence "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k = (worldline t \<sigma> \<theta> \<tau>) s deg"
        using signal_of2_derivative_raw2[OF _ `deg < k`] by metis
      also have "... =  signal_of2 (\<sigma> s) \<tau> s deg"
        unfolding worldline_def using `t \<le> deg` by auto
      also have "... = signal_of2 (\<sigma> s) \<tau> s k"
        using deg_prop `deg < k` `t \<le> deg` unfolding worldline_def by auto
      finally have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k =
                    signal_of2 (\<sigma> s) \<tau> s k"
        by auto }
    moreover
    { assume "deg < t"
      hence "derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t = 0"
        using derivative_raw_zero by auto
      hence "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k = \<sigma> s"
        using signal_of2_derivative_raw_degree_lt_now[OF `deg < t`] by metis
      also have "... = signal_of2 (\<sigma> s) \<tau> s k"
      proof -
        have "worldline t \<sigma> \<theta> \<tau> s k = worldline t \<sigma> \<theta> \<tau> s t"
          using deg_prop `k > deg` `t > deg` by auto
        have "k < t \<or> t \<le> k" by auto
        moreover
        { assume "k < t"
          have "\<forall>n\<in>dom (lookup (to_transaction2 \<tau> s)). k < n"
          proof (rule ccontr)
            assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 \<tau> s)). k < n)"
            then obtain n where "n \<in> dom (lookup (to_transaction2 \<tau> s))" and "n \<le> k"
              using leI by blast
            hence "lookup \<tau> n = 0"
              using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def using `k < t`
              by auto
            hence "n \<notin> dom (lookup (to_transaction2 \<tau> s))"
              apply transfer' unfolding to_trans_raw2_def  by (simp add: domIff zero_map)
            thus False
              by (simp add: \<open>n \<in> dom (lookup (to_transaction2 \<tau> s))\<close>)
          qed
          hence "inf_time (to_transaction2 \<tau>) s k  = None"
            by (rule inf_time_noneI)
          hence ?thesis
            unfolding to_signal2_def comp_def by auto }
        moreover
        { assume "t \<le> k"
          hence "worldline t \<sigma> \<theta> \<tau> s k = signal_of2 (\<sigma> s) \<tau> s k"
            unfolding worldline_def by auto
          have "worldline t \<sigma> \<theta> \<tau> s t = signal_of2 (\<sigma> s) \<tau> s t"
            unfolding worldline_def by auto
          also have "... = \<sigma> s"
            using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
            by (metis calculation state_worldline2 worldline2.rep_eq)
          finally have "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
            by auto
          hence ?thesis
            using \<open>worldline t \<sigma> \<theta> \<tau> s k = signal_of2 (\<sigma> s) \<tau> s k\<close>
            \<open>worldline t \<sigma> \<theta> \<tau> s k = worldline t \<sigma> \<theta> \<tau> s t\<close> by blast }
        ultimately show ?thesis by auto
      qed
      finally have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k =
                    signal_of2 (\<sigma> s) \<tau> s k"
        by auto }
    ultimately have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k =
                    signal_of2 (\<sigma> s) \<tau> s k" by auto }
  ultimately have "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) deg t) s k =
                    signal_of2 (\<sigma> s) \<tau> s k" by auto
  thus "signal_of2 (\<sigma> s) (derivative_raw (worldline t \<sigma> \<theta> \<tau>) (LEAST n. \<forall>ta>n. \<forall>s. worldline t \<sigma> \<theta> \<tau> s ta = worldline t \<sigma> \<theta> \<tau> s n) t) s k =
        signal_of2 (\<sigma> s) \<tau> s k"
    unfolding deg_def by auto
qed

lemma destruct_worldline_correctness:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) t = (\<sigma>', \<gamma>', \<theta>', \<tau>')"
  shows "\<sigma> = \<sigma>'" and "\<gamma> = \<gamma>'"
    and "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False \<theta>' s k"
    and "\<And>k s. signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau>' s k"
  using assms(2) state_worldline2[OF assms(1)] event_worldline2[OF assms(1)] beh_of_worldline[OF assms(1)]
  transaction_worldline2[OF assms(1)] unfolding destruct_worldline_def Let_def by auto

text \<open>Ideally, we want the destructor @{term "destruct_worldline"} is the inverse of the constructor
@{term "worldline2"}. Unfortunately this is not the case here. Note that in the lemma above,
the states are the same @{term "\<sigma> = \<sigma>'"}, the events are the same @{term "\<gamma> = \<gamma>'"} but not with
the history (or behaviours) @{term "\<theta>"} @{term "\<theta>'"} and the transactions @{term "\<tau>"} @{term "\<tau>'"}.
Why is this the case?

To answer this question, we need to explain the ``inverse'' function of the derivative, i.e.,
``integral'' which is achieved via the function @{term "signal_of2"}. It is basically the function
to turn a transaction into a signal. This ``integral'' function runs through over time, note if
there is a mapping, and change the signal value according to this mapping. It is basically like
integration function in real calculus, but the value can only either be ``0'' or ``1''.

The reason why we cannot have the equality @{term "\<tau> = \<tau>'"} and @{term "\<theta> = \<theta>'"} is because a
worldline does not have a unique ``derivative''. Suppose that the transaction @{term "\<tau>"} maps the
signal @{term "sig\<^sub>1 :: 'signal"} to @{term "True :: val"} at time 0 and none at other times.
Suppose also that we have another transaction @{term "\<tau>'"} which is the same with @{term "\<tau>"} except
that it also maps @{term "sig\<^sub>1 :: 'signal"} to @{term "True :: val"} at time 1. When we
``integrate'' both of these transactions, we will obtain an identical worldline; posting (setting) a
signal to @{term "True"} where we have previously posted (maps) the same value is futile.

However, even though the transaction @{term "\<tau>'"} and history @{term "\<theta>"} are not guaranteed to be
the same with @{term "\<tau>"} and @{term "\<theta>"} any longer, the ``integrals'' are still the same; see
property 3 and 4 in the theorem above.\<close>

definition world_seq_exec :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal worldline2" where
  "world_seq_exec w t s = (let (\<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline w t;
                                         \<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> s \<tau>
                           in worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_seq_exec_abb :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal worldline2 \<Rightarrow> bool"
  ("(_, _ , _) \<Rightarrow>\<^sub>s _")
  where "world_seq_exec_abb w t s w' \<equiv> (world_seq_exec w t s = w')"

(* Diagram for lifting the sequential execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>s          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s, \<tau>>    \<longrightarrow>\<^sub>s          \<tau>'
 *
 *)

definition
seq_hoare_valid2 :: "nat \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile>\<^sub>_ [(1_)]/ (_)/ [(1_)]" 50)
where "\<Turnstile>\<^sub>t [P] s [Q] \<longleftrightarrow>  (\<forall>w w'.  P w \<and> (w, t, s \<Rightarrow>\<^sub>s w') \<longrightarrow> Q w')"

text \<open>This is a cleaner definition of the validity compared to @{term "seq_hoare_valid"} in
@{theory "Draft.VHDL_Hoare"}. This also has the same spirit as the definition of validity in
@{theory_text "Hoare"}.\<close>

lemma beval_cong:
  assumes "\<And>k s. signal_of2 False \<theta>1 s k = signal_of2 False \<theta>2 s k"
  shows "beval t \<sigma> \<gamma> \<theta>1 g \<longleftrightarrow> beval t \<sigma> \<gamma> \<theta>2 g"
  using assms by (induction g, auto)

lemma signal_of2_eq_is_stable:
  assumes "is_stable dly \<tau>1 t sig (\<sigma> sig)"
  assumes "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau>1 n = 0"
  assumes "\<And>s. s \<in> dom (lookup \<tau>1 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>1 t s)"
  shows "is_stable dly \<tau>2 t sig (\<sigma> sig)"
  unfolding is_stable_correct
proof safe
  fix m
  assume "t < m"
  assume "m \<le> t + dly"
  obtain x where "lookup \<tau>2 m sig = None \<or> lookup \<tau>2 m sig = Some x"
    by (meson not_None_eq)
  moreover
  { assume "lookup \<tau>2 m sig = None"
    hence "check (get_trans \<tau>2 m) sig (\<sigma> sig)" by auto }
  moreover
  { assume "lookup \<tau>2 m sig = Some x"
    hence "signal_of2 (\<sigma> sig) \<tau>2 sig m = x"
      using lookup_some_signal_of2' by fastforce
    hence "signal_of2 (\<sigma> sig) \<tau>1 sig m = x"
      using assms(2) by auto
    have *: "lookup \<tau>1 m sig = None \<or> lookup \<tau>1 m sig = Some x"
    proof (rule ccontr)
      assume "\<not> (lookup \<tau>1 m sig = None \<or> lookup \<tau>1 m sig = Some x)"
      hence "lookup \<tau>1 m sig \<noteq> None \<and> lookup \<tau>1 m sig \<noteq> Some x"
        by auto
      then obtain y where "y \<noteq> x" and "lookup \<tau>1 m sig = Some y"
        using domD domIff by auto
      hence "signal_of2 (\<sigma> sig) \<tau>1 sig m = y"
        using lookup_some_signal_of2' by fastforce
      with `signal_of2 (\<sigma> sig) \<tau>1 sig m = x` and `y \<noteq> x` show False
        by auto
    qed
    moreover
    { assume "lookup \<tau>1 m sig = Some x"
      hence "x = \<sigma> sig"
        using assms(1) unfolding is_stable_correct using `t < m` `m \<le> t + dly`  by auto
      hence "check (lookup \<tau>2 m) sig (\<sigma> sig)"
        using `lookup \<tau>2 m sig = Some x` by auto }
    moreover
    { assume "lookup \<tau>1 m sig = None"
      obtain k where "find (\<lambda>x. lookup \<tau>1 x sig \<noteq> None) (rev [0..< m]) = None \<or>
                      find (\<lambda>x. lookup \<tau>1 x sig \<noteq> None) (rev [0..< m]) = Some k"
        using option.exhaust_sel by blast
      moreover
      { assume "find (\<lambda>x. lookup \<tau>1 x sig \<noteq> None) (rev [0..< m]) = None"
        hence "\<not> (\<exists>x. x \<in> set [0 ..< m] \<and> lookup \<tau>1 x sig \<noteq> None)"
          unfolding find_None_iff by auto
        hence "\<And>x. x < m \<Longrightarrow> lookup \<tau>1 x sig = None"
          by auto
        hence **: "\<And>x. x \<le> m \<Longrightarrow> lookup \<tau>1 x sig = None"
          using `lookup \<tau>1 m sig = None` using nat_less_le by blast
        have "signal_of2 (\<sigma> sig) \<tau>1 sig m = \<sigma> sig"
        proof -
          have "\<forall>t\<in>dom (lookup (to_transaction2 \<tau>1 sig)). m < t"
          proof (rule ccontr)
            assume "\<not>(\<forall>t\<in>dom (lookup (to_transaction2 \<tau>1 sig)). m < t)"
            then obtain t where "t \<in>dom (lookup (to_transaction2 \<tau>1 sig))" and "t \<le> m"
              using leI by blast
            with ** have "lookup \<tau>1 t sig = None"
              by auto
            hence "t \<notin> dom (lookup (to_transaction2 \<tau>1 sig))"
              apply transfer' unfolding to_trans_raw2_def by auto
            thus False
              using \<open>t \<in> dom (lookup (to_transaction2 \<tau>1 sig))\<close> by blast
          qed
          hence " inf_time (to_transaction2 \<tau>1) sig m = None"
            by (rule inf_time_noneI)
          thus ?thesis
            unfolding to_signal2_def comp_def by auto
        qed
        hence "x = \<sigma> sig"
          using `signal_of2 (\<sigma> sig) \<tau>1 sig m = x` by auto
        hence "check (lookup \<tau>2 m) sig (\<sigma> sig)"
          using `lookup \<tau>2 m sig = Some x` by auto }
      moreover
      { assume "find (\<lambda>x. lookup \<tau>1 x sig \<noteq> None) (rev [0..< m]) = Some k"
        hence " \<exists>i<length (rev [0..<m]). get_trans \<tau>1 (rev [0..<m] ! i) sig \<noteq> None
                                       \<and> k = rev [0..<m] ! i
                                       \<and> (\<forall>j<i. \<not> get_trans \<tau>1 (rev [0..<m] ! j) sig \<noteq> None)"
          unfolding find_Some_iff by auto
        then obtain i where "i<length (rev [0..<m])" and "get_trans \<tau>1 (rev [0..<m] ! i) sig \<noteq> None"
                      and "k = rev [0..<m] ! i " and quant: "\<forall>j<i.  lookup \<tau>1 (rev [0..<m] ! j) sig = None"
          by auto
        have "k = m - i - 1" using `k = rev [0..<m] ! i`
          by (metis One_nat_def \<open>i < length (rev [0..<m])\<close> add.left_neutral add.right_neutral
              add_Suc_right diff_diff_add diff_less diff_zero length_rev length_upt nat_less_le
              neq0_conv nth_upt rev_nth zero_less_Suc zero_order(2))
        hence iless: "i < length ([0..<m])"
          using `i<length (rev [0..<m])` by auto
        have "lookup \<tau>1 k sig \<noteq> None"
          using rev_nth[OF iless] `lookup \<tau>1 (rev [0..<m] ! i) sig \<noteq> None` `k = m - i - 1`
          using \<open>k = rev [0..<m] ! i\<close> by auto
        have "\<And>j. j > k \<Longrightarrow>  j < m \<Longrightarrow> lookup \<tau>1 j sig = None"
        proof -
          fix j
          assume "k < j" and "j < m"
          define j' where "j' = m - j - 1"
          have "m - i - 1 < j"
            using `k < j` unfolding `k  = m - i - 1` by auto
          hence "j' < i"
            unfolding j'_def  using `j < m` by linarith
          hence lookup: "lookup \<tau>1 (rev [0..< m] ! j') sig = None"
            using quant by auto
          have "j' < m"
            unfolding j'_def using `j < m` by auto
          with rev_nth have "rev [0 ..< m] ! j' = [0 ..< m] ! j"
            unfolding j'_def  by (simp add: rev_nth Suc_diff_Suc \<open>j < m\<close> less_imp_le_nat)
          with lookup have "get_trans \<tau>1 ([0 ..< m] ! j) sig = None"
            by auto
          thus "get_trans \<tau>1 j sig = None"
            using nth_upt `j < m` by auto
        qed
        hence ind: "\<And>j. k < j \<Longrightarrow> j \<le> m \<Longrightarrow> lookup \<tau>1 j sig = 0"
          using `lookup \<tau>1 m sig = None` using dual_order.order_iff_strict  zero_option_def by fastforce
        have "t \<le> k"
        proof (rule ccontr)
          assume "\<not> (t \<le> k)" hence "k < t" by auto
          hence "lookup \<tau>1 k sig = None"
            using assms(3)  by (simp add: zero_map)
          with `lookup \<tau>1 k sig \<noteq> None` show "False" by auto
        qed
        have "k < m"
          using \<open>i < length (rev [0..<m])\<close> \<open>k = m - i - 1\<close> by auto
        have "signal_of2 (\<sigma> sig) \<tau>1 sig m = signal_of2 (\<sigma> sig) \<tau>1 sig k"
          using signal_of2_less_ind'[OF ind `k < m`] by auto
        hence "signal_of2 (\<sigma> sig) \<tau>1 sig k = x"
          using `signal_of2 (\<sigma> sig) \<tau>1 sig m = x` by auto
        have "lookup \<tau>1 k sig = None \<or> lookup \<tau>1 k sig = Some x"
        proof (rule ccontr)
          assume "\<not> (lookup \<tau>1 k sig = None \<or> lookup \<tau>1 k sig = Some x)"
          hence "lookup \<tau>1 k sig \<noteq> None \<and> lookup \<tau>1 k sig \<noteq> Some x"
            by auto
          then obtain y where "y \<noteq> x" and "lookup \<tau>1 k sig = Some y"
            using domD domIff by auto
          hence "signal_of2 (\<sigma> sig) \<tau>1 sig k = y"
            using lookup_some_signal_of2' by fastforce
          with `signal_of2 (\<sigma> sig) \<tau>1 sig k = x` and `y \<noteq> x` show False
            by auto
        qed
        with `lookup \<tau>1 k sig \<noteq> None` have "lookup \<tau>1 k sig = Some x"
          by auto
        have "t < k \<or> k = t"
          using `t \<le> k` by auto
        moreover
        { assume "t < k"
          hence "x = \<sigma> sig"
            using `lookup \<tau>1 k sig = Some x` assms(1) unfolding is_stable_correct
            using `t < k` `k < m` `m \<le> t + dly` by auto
          hence "check (lookup \<tau>2 m) sig (\<sigma> sig)"
            using `lookup \<tau>2 m sig = Some x` by auto }
        moreover
        { assume "t = k"
          hence "x = \<sigma> sig"
            using assms(4) `lookup \<tau>1 k sig = Some x`  by (simp add: domIff)
          hence "check (lookup \<tau>2 m) sig (\<sigma> sig)"
            using `lookup \<tau>2 m sig = Some x` by auto }
        ultimately have "check (lookup \<tau>2 m) sig (\<sigma> sig)"
          by auto }
      ultimately have "check (lookup \<tau>2 m) sig (\<sigma> sig)"
        by auto }
    ultimately have "check (lookup \<tau>2 m) sig (\<sigma> sig)"
      by auto }
  ultimately show "check (lookup \<tau>2 m) sig (\<sigma> sig)"
    by auto
qed

lemma signal_of2_eq_is_stable_eq:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau>1 n = 0"
  assumes "\<And>s. s \<in> dom (lookup \<tau>1 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>1 t s)"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau>2 n = 0"
  assumes "\<And>s. s \<in> dom (lookup \<tau>2 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>2 t s)"
  assumes "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
  shows "is_stable dly \<tau>1 t sig (\<sigma> sig) \<longleftrightarrow> is_stable dly \<tau>2 t sig (\<sigma> sig)"
proof
  assume "is_stable dly \<tau>1 t sig (\<sigma> sig)"
  with signal_of2_eq_is_stable[OF _ assms(5) assms(1-2)] show "is_stable dly \<tau>2 t sig (\<sigma> sig)"
    by auto
next
  assume "is_stable dly \<tau>2 t sig (\<sigma> sig)"
  with signal_of2_eq_is_stable[OF _ sym[OF assms(5)] assms(3-4)] show "is_stable dly \<tau>1 t sig (\<sigma> sig)"
    by auto
qed

lemma signal_of2_purge_not_affected:
  assumes "s \<noteq> sig"
  shows "signal_of2 (\<sigma> s) (purge dly \<tau>1 t sig (\<sigma> sig)) s k = signal_of2 (\<sigma> s) \<tau>1 s k"
proof -
  have "\<And>n. lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) s) n = lookup (to_transaction2 \<tau>1 s) n"
    using assms apply transfer' unfolding to_trans_raw2_def  by (simp add: purge_raw_does_not_affect_other_sig)
  from signal_of2_lookup_sig_same[OF this] show ?thesis by auto
qed

lemma signal_of2_purged:
  assumes "k < t + dly"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau>1 n = 0"
  assumes "\<And>s. s \<in> dom (lookup \<tau>1 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>1 t s)"
  shows "signal_of2 (\<sigma> sig) (purge dly \<tau>1 t sig (\<sigma> sig)) sig k = (\<sigma> sig)"
proof -
  have *: "\<And>k. k \<le> t \<Longrightarrow> lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k = lookup \<tau>1 k"
    by (transfer', metis purge_raw_before_now_unchanged)
  have **: "\<And>k. k < t \<Longrightarrow> lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k = 0"
    using assms(2) * by auto
  have "k < t \<or> k = t \<or> t < k"
    by auto
  moreover
  { assume "k < t "
    have ?thesis
    proof -
      have "\<forall>n\<in>dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig)). k < n"
      proof (rule ccontr)
        assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig)). k < n)"
        then obtain n where "n \<in> dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig))"
          and "n \<le> k"  using not_less by blast
        with `k < t` have "n < t" by auto
        hence " lookup (purge dly \<tau>1 t sig (\<sigma> sig)) n = lookup \<tau>1 n "
          using * by auto
        also have "... = 0"
          using assms(2) `n < t` by auto
        finally have "lookup (purge dly \<tau>1 t sig (\<sigma> sig)) n = 0"
          by auto
        hence "n \<notin> dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig))"
          apply transfer' unfolding to_trans_raw2_def
          by (simp add: domIff zero_fun_def zero_option_def)
        with `n \<in> dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig))`
        show False by auto
      qed
      hence "inf_time (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig))) sig k = None"
        by (rule inf_time_noneI)
      thus ?thesis
        unfolding to_signal2_def comp_def by auto
    qed }
  moreover
  { assume "k = t"
    hence "lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = lookup \<tau>1 k sig"
      by (transfer', metis less_or_eq_imp_le purge_raw_before_now_unchanged)
    obtain x where "lookup \<tau>1 k sig = None \<or> lookup \<tau>1 k sig = Some x"
      by (meson not_None_eq)
    moreover
    { assume "lookup \<tau>1 k sig = None"
      have ?thesis
      proof -
        have "\<forall>n\<in>dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig)). k < n"
        proof (rule ccontr)
          assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig)). k < n)"
          then obtain n where "n \<in> dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig))"
            and "n \<le> k"  using not_less by blast
          with `k = t` have "n \<le> t" by auto
          hence " lookup (purge dly \<tau>1 t sig (\<sigma> sig)) n sig = lookup \<tau>1 n sig"
            using * by auto
          also have "... = 0"
            using assms(2) `n \<le> t` `lookup \<tau>1 k sig = None`
            by (metis \<open>k = t\<close> dual_order.order_iff_strict zero_fun_def zero_option_def)
          finally have "lookup (purge dly \<tau>1 t sig (\<sigma> sig)) n sig = 0"
            by auto
          hence "n \<notin> dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig))"
            apply transfer' unfolding to_trans_raw2_def
            by (simp add: domIff zero_fun_def zero_option_def)
          with `n \<in> dom (lookup (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig)) sig))`
          show False by auto
        qed
        hence "inf_time (to_transaction2 (purge dly \<tau>1 t sig (\<sigma> sig))) sig k = None"
          by (rule inf_time_noneI)
        thus ?thesis
          unfolding to_signal2_def comp_def by auto
      qed }
    moreover
    { assume "lookup \<tau>1 k sig = Some x"
      hence "x = \<sigma> sig"
        using assms(3)  by (simp add: \<open>k = t\<close> domIff)
      hence "lookup \<tau>1 k sig = Some (\<sigma> sig)"
        using `lookup \<tau>1 k sig = Some x` by auto
      hence ?thesis
        using \<open>get_trans (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = get_trans \<tau>1 k sig\<close> lookup_some_signal_of2'
        by fastforce }
    ultimately have ?thesis by auto }
  moreover
  { assume "t < k"
    have "lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = None \<or>
          lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = Some (\<sigma> sig)"
      by (simp add: \<open>t < k\<close> assms(1) order.strict_implies_order purge_correctness')
    moreover
    { assume "lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = Some (\<sigma> sig)"
      hence ?thesis
        by (meson lookup_some_signal_of2') }
    moreover
    { assume "lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = None"
      define \<tau>1' where "\<tau>1' = purge dly \<tau>1 t sig (\<sigma> sig)"
      obtain k' where "find (\<lambda>x. lookup \<tau>1' x sig \<noteq> None) (rev [0..< k]) = None \<or>
                       find (\<lambda>x. lookup \<tau>1' x sig \<noteq> None) (rev [0..< k]) = Some k'"
        using option.exhaust_sel by blast
      moreover
      { assume "find (\<lambda>x. lookup \<tau>1' x sig \<noteq> None) (rev [0..< k]) = None"
        hence "\<not> (\<exists>x. x \<in> set [0 ..< k] \<and> lookup \<tau>1' x sig \<noteq> None)"
          unfolding find_None_iff by auto
        hence "\<And>x. x < k \<Longrightarrow> lookup \<tau>1' x sig = None"
          by auto
        hence ***: "\<And>x. x \<le> k \<Longrightarrow> lookup \<tau>1' x sig = None"
          using `lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = None`
          unfolding \<tau>1'_def using nat_less_le by blast
        have "signal_of2 (\<sigma> sig) \<tau>1' sig k = \<sigma> sig"
        proof -
          have "\<forall>t\<in>dom (lookup (to_transaction2 \<tau>1' sig)). k < t"
          proof (rule ccontr)
            assume "\<not>(\<forall>t\<in>dom (lookup (to_transaction2 \<tau>1' sig)). k < t)"
            then obtain t where "t \<in>dom (lookup (to_transaction2 \<tau>1' sig))" and "t \<le> k"
              using leI by blast
            with *** have "lookup \<tau>1' t sig = None"
              by auto
            hence "t \<notin> dom (lookup (to_transaction2 \<tau>1' sig))"
              apply transfer' unfolding to_trans_raw2_def by auto
            thus False
              using \<open>t \<in> dom (lookup (to_transaction2 \<tau>1' sig))\<close> by blast
          qed
          hence " inf_time (to_transaction2 \<tau>1') sig k = None"
            by (rule inf_time_noneI)
          thus ?thesis
            unfolding to_signal2_def comp_def by auto
        qed
        hence ?thesis
          unfolding \<tau>1'_def by auto }
      moreover
      { assume "find (\<lambda>x. lookup \<tau>1' x sig \<noteq> None) (rev [0..< k]) = Some k'"
        hence " \<exists>i<length (rev [0..<k]). get_trans \<tau>1' (rev [0..<k] ! i) sig \<noteq> None
                                       \<and> k' = rev [0..<k] ! i
                                       \<and> (\<forall>j<i. \<not> get_trans \<tau>1' (rev [0..<k] ! j) sig \<noteq> None)"
          unfolding find_Some_iff by auto
        then obtain i where "i<length (rev [0..<k])" and "get_trans \<tau>1' (rev [0..<k] ! i) sig \<noteq> None"
                      and "k' = rev [0..<k] ! i " and quant: "\<forall>j<i.  lookup \<tau>1' (rev [0..<k] ! j) sig = None"
          by auto
        have "k' = k - i - 1" using `k' = rev [0..<k] ! i`
          by (metis One_nat_def \<open>i < length (rev [0..<k])\<close> add.left_neutral add.right_neutral
              add_Suc_right diff_diff_add diff_less diff_zero length_rev length_upt nat_less_le
              neq0_conv nth_upt rev_nth zero_less_Suc zero_order(2))
        hence iless: "i < length ([0..<k])"
          using `i<length (rev [0..<k])` by auto
        have "lookup \<tau>1' k' sig \<noteq> None"
          using rev_nth[OF iless] `lookup \<tau>1' (rev [0..<k] ! i) sig \<noteq> None` `k' = k - i - 1`
          using \<open>k' = rev [0..<k] ! i\<close> by auto
        have "\<And>j. j > k' \<Longrightarrow>  j < k \<Longrightarrow> lookup \<tau>1' j sig = None"
        proof -
          fix j
          assume "k'< j" and "j < k"
          define j' where "j' = k - j - 1"
          have "k - i - 1 < j"
            using `k'< j` unfolding `k' = k - i - 1` by auto
          hence "j' < i"
            unfolding j'_def  using `j < k` by linarith
          hence lookup: "lookup \<tau>1' (rev [0..< k] ! j') sig = None"
            using quant by auto
          have "j' < k"
            unfolding j'_def using `j < k` by auto
          with rev_nth have "rev [0 ..< k] ! j' = [0 ..< k] ! j"
            unfolding j'_def  by (simp add: rev_nth Suc_diff_Suc \<open>j < k\<close> less_imp_le_nat)
          with lookup have "get_trans \<tau>1' ([0 ..< k] ! j) sig = None"
            by auto
          thus "get_trans \<tau>1' j sig = None"
            using nth_upt `j < k` by auto
        qed
        hence ind: "\<And>j. k' < j \<Longrightarrow> j \<le> k \<Longrightarrow> lookup \<tau>1' j sig = 0"
          using `lookup (purge dly \<tau>1 t sig (\<sigma> sig)) k sig = None` unfolding \<tau>1'_def
          using dual_order.order_iff_strict  zero_option_def by fastforce
        have "k' < k"
          using \<open>i < length (rev [0..<k])\<close> \<open>k' = k - i - 1\<close> by auto
        hence " signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) \<tau>1' sig k'"
          using signal_of2_less_ind'[OF ind `k' < k`] by auto
        have "t \<le> k'"
        proof (rule ccontr)
          assume "\<not> t \<le> k'" hence "k' < t" by auto
          have "lookup \<tau>1' k' sig = lookup \<tau>1 k' sig"
            unfolding \<tau>1'_def by (simp add: "**" \<open>k' < t\<close> assms(2))
          also have "... = 0"
            using assms(2) `k' < t` by (simp add: zero_fun_def)
          finally have "lookup \<tau>1' k' sig = 0"
            by auto
          with `lookup \<tau>1' k' sig \<noteq> None` show False  by (simp add: zero_option_def)
        qed
        hence "t \<noteq> k' \<or> t = k'" by auto
        moreover
        { assume "t \<noteq> k'"
          hence "lookup \<tau>1' k' sig = Some (\<sigma> sig)"
            unfolding \<tau>1'_def using `k' < k` `k < t + dly` `t \<le> k'` `lookup \<tau>1' k' sig \<noteq> None`
            by (metis (no_types, lifting) \<tau>1'_def le_cases le_less_trans le_neq_trans less_irrefl purge_correctness')
          hence "signal_of2 (\<sigma> sig) \<tau>1' sig k' = \<sigma> sig"
            by (meson lookup_some_signal_of2')
          with `signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) \<tau>1' sig k'`
          have ?thesis unfolding \<tau>1'_def by auto }
        moreover
        { assume "t = k'"
          have "lookup \<tau>1' k' sig = lookup \<tau>1 k' sig"
            using `t = k'` * unfolding \<tau>1'_def by auto
          obtain m where "lookup \<tau>1 k' sig = None \<or> lookup \<tau>1 k' sig = Some m"
            by (meson not_Some_eq)
          moreover
          { assume "lookup \<tau>1 k' sig = Some m"
            hence "m = \<sigma> sig"
              using `t = k'` assms(3) by (simp add: domIff)
            hence "lookup \<tau>1 k' sig = Some (\<sigma> sig)"
              using `lookup \<tau>1 k' sig = Some m` by auto
            hence "lookup \<tau>1' k' sig = Some (\<sigma> sig)"
              using `lookup \<tau>1' k' sig = lookup \<tau>1 k' sig` by auto
            hence "signal_of2 (\<sigma> sig) \<tau>1' sig k' = \<sigma> sig"
              by (meson lookup_some_signal_of2')
            hence ?thesis
              using `signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) \<tau>1' sig k'`
              unfolding \<tau>1'_def by auto }
          moreover
          { assume "lookup \<tau>1 k' sig = None"
            hence "lookup \<tau>1' k' sig = None"
              using `lookup \<tau>1' k' sig = lookup \<tau>1 k' sig` by auto
            hence "signal_of2 (\<sigma> sig) \<tau>1' sig k = \<sigma> sig"
            proof -
              have "\<forall>n\<in>dom (lookup (to_transaction2 \<tau>1' sig)). k < n"
              proof (rule ccontr)
                assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 \<tau>1' sig)). k < n)"
                then obtain n where "n \<in> dom (lookup (to_transaction2 \<tau>1' sig))" and "n \<le> k"
                  using \<open>get_trans \<tau>1' k' sig = None\<close> \<open>get_trans \<tau>1' k' sig \<noteq> None\<close> by blast
                have "lookup \<tau>1' n sig = None"
                  using `n \<le> k` ** `lookup \<tau>1' k' sig = None` `t = k'` unfolding \<tau>1'_def
                  using \<open>get_trans \<tau>1' k' sig \<noteq> None\<close> \<tau>1'_def by blast
                hence "n \<notin> dom (lookup (to_transaction2 \<tau>1' sig))"
                  by (transfer', auto simp add:to_trans_raw2_def)
                with `n \<in> dom (lookup (to_transaction2 \<tau>1' sig))` show False
                  by auto
              qed
              hence "inf_time (to_transaction2 \<tau>1') sig k = None "
                by (rule inf_time_noneI)
              thus ?thesis
                unfolding to_signal2_def comp_def by auto
            qed
            hence ?thesis
              unfolding \<tau>1'_def by auto }
          ultimately have ?thesis by auto }
        ultimately have ?thesis by auto }
      ultimately have ?thesis by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed

lemma helper':
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of2 False \<theta>1 s k = signal_of2 False \<theta>2 s k"
  assumes "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
  assumes "context_invariant t \<sigma> \<gamma> \<theta>1 \<tau>1" and "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2"
  assumes "nonneg_delay ss"
  shows "\<And>k s. signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
  using assms
proof (induction ss arbitrary:\<tau>1 \<tau>2 \<tau>1' \<tau>2')
  case (Bcomp ss1 ss2)
  then obtain \<tau> \<tau>' where tau1: "t , \<sigma> , \<gamma> , \<theta>1 \<turnstile> <ss1, \<tau>1> \<longrightarrow>\<^sub>s \<tau>" and tau2: "t , \<sigma> , \<gamma> , \<theta>1 \<turnstile> <ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>1'"
      and tau3: "t , \<sigma> , \<gamma> , \<theta>2 \<turnstile> <ss1, \<tau>2> \<longrightarrow>\<^sub>s \<tau>'" and tau4: "t , \<sigma> , \<gamma> , \<theta>2 \<turnstile> <ss2 , \<tau>'> \<longrightarrow>\<^sub>s \<tau>2'"
      and "nonneg_delay ss1" and "nonneg_delay ss2"
    by auto
  have "\<And>k s. signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau>' s k"
    using Bcomp(1)[OF tau1 Bcomp(4) Bcomp(5) tau3 Bcomp(7-8) `nonneg_delay ss1`] by auto
  moreover have "context_invariant t \<sigma> \<gamma> \<theta>1 \<tau>"
    using b_seq_exec_preserves_context_invariant[OF Bcomp(7) tau1 `nonneg_delay ss1`]
    by auto
  moreover have "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>'"
    using b_seq_exec_preserves_context_invariant[OF Bcomp(8) tau3 `nonneg_delay ss1`] .
  ultimately show ?case
    using Bcomp(2)[OF tau2 Bcomp(4) _ tau4] `nonneg_delay ss2` by auto
next
  case (Bguarded g ss1 ss2)
  hence "nonneg_delay ss1" and "nonneg_delay ss2"
    by auto
  have "beval t \<sigma> \<gamma> \<theta>1 g \<or> \<not> beval t \<sigma> \<gamma> \<theta>1 g"
    by auto
  moreover
  { assume "beval t \<sigma> \<gamma> \<theta>1 g"
    hence "\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta>1 ss1 \<tau>1"
      using Bguarded by auto
    have "beval t \<sigma> \<gamma> \<theta>2 g"
      using beval_cong[OF Bguarded(4)] `beval t \<sigma> \<gamma> \<theta>1 g` by auto
    hence "\<tau>2' = b_seq_exec t \<sigma> \<gamma> \<theta>2 ss1 \<tau>2"
      using Bguarded(6) by auto
    hence ?case
      using Bguarded(1) `\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta>1 ss1 \<tau>1` Bguarded(4-5)
      Bguarded.prems(5) Bguarded.prems(6) \<open>nonneg_delay ss1\<close> by blast }
  moreover
  { assume "\<not> beval t \<sigma> \<gamma> \<theta>1 g"
    hence "\<not> beval t \<sigma> \<gamma> \<theta>2 g"
      using beval_cong[OF Bguarded(4)] by auto
    hence "\<tau>1' = b_seq_exec t \<sigma> \<gamma> \<theta>1 ss2 \<tau>1" and "\<tau>2' = b_seq_exec t \<sigma> \<gamma> \<theta>2 ss2 \<tau>2"
      using `\<not> beval t \<sigma> \<gamma> \<theta>1 g` using Bguarded by auto
    hence ?case
      using Bguarded \<open>nonneg_delay ss2\<close> by blast }
  ultimately show ?case
    by auto
next
  case (Bassign_trans sig e dly)
  define x where "x = (beval t \<sigma> \<gamma> \<theta>1 e)"
  hence "x = beval t \<sigma> \<gamma> \<theta>2 e"
    using beval_cong[OF Bassign_trans(2)] by auto
  have tau1: "\<tau>1' = trans_post sig x \<tau>1 (t + dly)"
    using Bassign_trans(1)  using x_def by auto
  have tau2:  "\<tau>2' = trans_post sig x \<tau>2 (t + dly)"
    using Bassign_trans(4) using `x = beval t \<sigma> \<gamma> \<theta>2 e`  by simp
  have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>1 s k"
    using signal_of_trans_post unfolding tau1 by metis
  moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
    using Bassign_trans(3) by auto
  ultimately have *: "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
    using signal_of_trans_post unfolding tau2 by metis
  have "t + dly \<le> k \<or> k < t + dly"
    by auto
  moreover
  { assume "t + dly \<le> k"
    from signal_of_trans_post3[OF this] have "signal_of2 (\<sigma> s) \<tau>1' sig k = x"
      unfolding tau1 by metis
    moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of2 (\<sigma> s) \<tau>2' sig k = x"
      unfolding tau2  by metis
    ultimately have "signal_of2 (\<sigma> s) \<tau>1' sig k = signal_of2 (\<sigma> s) \<tau>2' sig k"
      by auto
    with * have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
      by auto }
  moreover
  { assume "k < t + dly"
    from signal_of_trans_post2[OF this] have "signal_of2 (\<sigma> s) \<tau>1' sig k = signal_of2 (\<sigma> s) \<tau>1 sig k"
      and "signal_of2 (\<sigma> s) \<tau>2' sig k = signal_of2 (\<sigma> s) \<tau>2 sig k" unfolding tau1 tau2 by metis+
    with * have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
      using Bassign_trans(3) by auto }
  ultimately show ?case by auto
next
  case (Bassign_inert sig e dly)
  define x where "x = (beval t \<sigma> \<gamma> \<theta>1 e)"
  hence "x = beval t \<sigma> \<gamma> \<theta>2 e"
    using beval_cong[OF Bassign_inert(2)] by auto
  have tau1: "\<tau>1' = inr_post sig x (\<sigma> sig) \<tau>1 t dly"
    using Bassign_inert(1)  using x_def by auto
  have tau2:  "\<tau>2' = inr_post sig x (\<sigma> sig) \<tau>2 t dly"
    using Bassign_inert(4) using `x = beval t \<sigma> \<gamma> \<theta>2 e`  by simp
  have ci0: "\<And>n. n < t \<Longrightarrow> lookup \<tau>1 n = 0" and ci1: "\<And>s. s \<in> dom (lookup \<tau>1 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>1 t s)"
    using `context_invariant t \<sigma> \<gamma> \<theta>1 \<tau>1` unfolding context_invariant_def by auto
  have "is_stable dly \<tau>1 t sig (\<sigma> sig) \<or> \<not> is_stable dly \<tau>1 t sig (\<sigma> sig)"
    by auto
  moreover
  { assume stab1: "is_stable dly \<tau>1 t sig (\<sigma> sig)" hence stab2:"is_stable dly \<tau>2 t sig (\<sigma> sig)"
      using signal_of2_eq_is_stable[OF _ Bassign_inert(3) ci0 ci1] by auto
    have tau1': "\<tau>1' = trans_post sig x \<tau>1 (t + dly)"
      using stab1 tau1 unfolding inr_post_def by auto
    moreover have tau2': "\<tau>2' = trans_post sig x \<tau>2 (t + dly)"
      using stab2 tau2 unfolding inr_post_def by auto
    have "t + dly \<le> k \<or> k < t + dly"
      by auto
    have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>1 s k"
      using signal_of_trans_post unfolding tau1' by metis
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
      using Bassign_inert(3) by auto
    ultimately have *: "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
      using signal_of_trans_post unfolding tau2' by metis
    have "t + dly \<le> k \<or> k < t + dly"
      by auto
    moreover
    { assume "t + dly \<le> k"
      from signal_of_trans_post3[OF this] have "signal_of2 (\<sigma> s) \<tau>1' sig k = x"
        unfolding tau1' by metis
      moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of2 (\<sigma> s) \<tau>2' sig k = x"
        unfolding tau2'  by metis
      ultimately have "signal_of2 (\<sigma> s) \<tau>1' sig k = signal_of2 (\<sigma> s) \<tau>2' sig k"
        by auto
      with * have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
        by auto }
    moreover
    { assume "k < t + dly"
      from signal_of_trans_post2[OF this] have "signal_of2 (\<sigma> s) \<tau>1' sig k = signal_of2 (\<sigma> s) \<tau>1 sig k"
        and "signal_of2 (\<sigma> s) \<tau>2' sig k = signal_of2 (\<sigma> s) \<tau>2 sig k" unfolding tau1' tau2' by metis+
      with * have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
        using Bassign_inert(3) by auto }
    ultimately have ?case by auto }
  moreover
  { assume nstable1: "\<not> is_stable dly \<tau>1 t sig (\<sigma> sig)"
    have ci2: "\<And>n. n < t \<Longrightarrow> lookup \<tau>2 n = 0" and ci3: "\<And>s. s \<in> dom (lookup \<tau>2 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>2 t s)"
      using `context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2` unfolding context_invariant_def by auto
    have nstable2: "\<not> is_stable dly \<tau>2 t sig (\<sigma> sig)"
      using signal_of2_eq_is_stable_eq[OF ci0 ci1 ci2 ci3 Bassign_inert(3)]
      `\<not> is_stable dly \<tau>1 t sig (\<sigma> sig)` by auto
    have tau1': "\<tau>1' = trans_post sig x (purge dly \<tau>1 t sig (\<sigma> sig)) (t + dly)"
      using tau1 nstable1 unfolding inr_post_def by auto
    have tau2': "\<tau>2' = trans_post sig x (purge dly \<tau>2 t sig (\<sigma> sig)) (t + dly)"
      using tau2 nstable2 unfolding inr_post_def by auto
    have "t + dly \<le> k \<or> k < t + dly"
      by auto
    have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) (purge dly \<tau>1 t sig (\<sigma> sig)) s k"
      using signal_of_trans_post unfolding tau1' by metis
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) (purge dly \<tau>1 t sig (\<sigma> sig)) s k = signal_of2 (\<sigma> s) \<tau>1 s k"
      using signal_of2_purge_not_affected  by fastforce
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
      using Bassign_inert(3) by auto
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>2 s k = signal_of2 (\<sigma> s) (purge dly \<tau>2 t sig (\<sigma> sig)) s k"
      using signal_of2_purge_not_affected by fastforce
    ultimately have *: "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
      using signal_of_trans_post unfolding tau2' by metis
    have "t + dly \<le> k \<or> k < t + dly"
      by auto
    moreover
    { assume "t + dly \<le> k"
      from signal_of_trans_post3[OF this] have "signal_of2 (\<sigma> s) \<tau>1' sig k = x"
        unfolding tau1' by metis
      moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of2 (\<sigma> s) \<tau>2' sig k = x"
        unfolding tau2'  by metis
      ultimately have "signal_of2 (\<sigma> s) \<tau>1' sig k = signal_of2 (\<sigma> s) \<tau>2' sig k"
        by auto
      with * have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
        by auto }
    moreover
    { assume "k < t + dly"
      from signal_of_trans_post2[OF this] have "signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) (purge dly \<tau>1 t sig (\<sigma> sig)) sig k"
        and "signal_of2 (\<sigma> sig) \<tau>2' sig k = signal_of2 (\<sigma> sig) (purge dly \<tau>2 t sig (\<sigma> sig)) sig k" unfolding tau1' tau2' by metis+
      moreover have "signal_of2 (\<sigma> sig) (purge dly \<tau>1 t sig (\<sigma> sig)) sig k = \<sigma> sig"
        using signal_of2_purged[OF `k < t + dly` `\<And>n. n < t \<Longrightarrow> get_trans \<tau>1 n = 0`
        `\<And>s. s \<in> dom (get_trans \<tau>1 t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau>1 t s)`] by auto
      moreover have "signal_of2 (\<sigma> sig) (purge dly \<tau>2 t sig (\<sigma> sig)) sig k = \<sigma> sig"
        using signal_of2_purged[OF `k < t + dly` `\<And>n. n < t \<Longrightarrow> get_trans \<tau>2 n = 0`
        `\<And>s. s \<in> dom (get_trans \<tau>2 t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau>2 t s)`] by auto
      ultimately have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
        using "*" by blast }
    ultimately have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
      by auto }
  ultimately show "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
    by auto
next
  case Bnull
  then show ?case by auto
qed

lemma helper:
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<And>k s. signal_of2 False \<theta>1 s k = signal_of2 False \<theta>2 s k"
  assumes "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
  assumes "context_invariant t \<sigma> \<gamma> \<theta>1 \<tau>1" and "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2"
  assumes "nonneg_delay ss"
  shows "\<exists>\<tau>2'. (t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2') \<and> (\<forall>k s. signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k)"
  using helper'[OF assms(1-3) _ assms(4-5) `nonneg_delay ss`] by auto

lemma Bcomp_hoare_valid':
  assumes "\<Turnstile>\<^sub>t [P] s1 [Q]" and "\<Turnstile>\<^sub>t [Q] s2 [R]"
  assumes "nonneg_delay (Bcomp s1 s2)"
  shows "\<Turnstile>\<^sub>t [P] Bcomp s1 s2 [R]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix w w'
  have "nonneg_delay s1" and "nonneg_delay s2"
    using assms(3) by auto
  assume "P w \<and> (w, t, Bcomp s1 s2 \<Rightarrow>\<^sub>s w')"
  hence "P w" and "w, t, Bcomp s1 s2 \<Rightarrow>\<^sub>s w'" by auto
  then obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>')" and "w'= worldline2 t \<sigma> \<theta> \<tau>'"
    unfolding world_seq_exec_def Let_def using destruct_worldline_exist by fastforce
  then obtain \<tau>'' where tau1: "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'')" and tau2: "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>')"
    by auto
  define w'' where "w'' = worldline2 t \<sigma> \<theta> \<tau>''"
  hence "w, t, s1 \<Rightarrow>\<^sub>s w''"
    using des tau1 unfolding world_seq_exec_def Let_def by auto
  with assms(1) have "Q w''"
    unfolding seq_hoare_valid2_def using `P w` by auto
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF des] by auto
  hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF _ tau1] assms(3) by auto
  obtain \<theta>''' \<tau>''' where des2: "destruct_worldline w'' t = (\<sigma>, \<gamma>, \<theta>''', \<tau>''')" and
    sig_beh: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False \<theta>''' s k" and
    sig_trans: "\<And>k s. signal_of2 (\<sigma> s) \<tau>'' s k = signal_of2 (\<sigma> s) \<tau>''' s k"
    unfolding w''_def using destruct_worldline_correctness[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>''`]
    by (metis destruct_worldline_exist)
  have "context_invariant t \<sigma> \<gamma> \<theta>''' \<tau>'''"
    using worldline2_constructible[OF des2] by auto
  then obtain \<tau>4 where tau3: "t, \<sigma>, \<gamma>, \<theta>''' \<turnstile> <s2, \<tau>'''> \<longrightarrow>\<^sub>s \<tau>4" and
    sig_trans: "\<And>k s. signal_of2 (\<sigma> s) \<tau>4 s k = signal_of2 (\<sigma> s) \<tau>' s k"
    using helper[OF tau2 sig_beh sig_trans `context_invariant t \<sigma> \<gamma> \<theta> \<tau>''`]  \<open>nonneg_delay s2\<close> by blast
  have "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta>''' \<tau>4"
    using sig_beh sig_trans
  proof transfer'
    fix \<theta>  \<theta>''' :: "'a transaction"
    fix \<sigma> :: "'a state"
    fix \<tau>'' \<tau>''' \<tau>4 t \<tau>'
    assume 1: "\<And>s k. signal_of2 False \<theta> s k = signal_of2 False \<theta>''' s k"
    assume  "\<And>s k. signal_of2 (\<sigma> s) \<tau>4 s k = signal_of2 (\<sigma> s) \<tau>' s k"
    thus " worldline t \<sigma> \<theta> \<tau>' = worldline t \<sigma> \<theta>''' \<tau>4"
      unfolding worldline_def using 1 by auto
  qed
  hence "w'', t, s2 \<Rightarrow>\<^sub>s w'"
    unfolding world_seq_exec_def using des2 tau3 `w'= worldline2 t \<sigma> \<theta> \<tau>'` by auto
  with `Q w''` show "R w'"
    using assms(2) unfolding seq_hoare_valid2_def by auto
qed

lemma Bnull_sound_hoare2:
  "\<turnstile>\<^sub>t [P] Bnull [Q] \<Longrightarrow> \<Turnstile>\<^sub>t [P] Bnull [Q]"
  by (auto dest!: BnullE'_hoare2 worldline2_constructible  simp add: seq_hoare_valid2_def world_seq_exec_def
      split: prod.splits)

lemma Bguarded_hoare_valid2:
  assumes "\<Turnstile>\<^sub>t [\<lambda>a. P a \<and> beval_world2 a t g] s1 [Q]" and "\<Turnstile>\<^sub>t [\<lambda>a. P a \<and> \<not> beval_world2 a t g] s2 [Q]"
  shows "\<Turnstile>\<^sub>t [P] Bguarded g s1 s2 [Q]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix w w'
  assume "P w \<and> (w, t, Bguarded g s1 s2 \<Rightarrow>\<^sub>s w')"
  hence "P w" and "w, t, Bguarded g s1 s2 \<Rightarrow>\<^sub>s w'" by auto
  obtain \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "w = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "w' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `w, t, Bguarded g s1 s2 \<Rightarrow>\<^sub>s w'` `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def by auto
  have "beval t \<sigma> \<gamma> \<theta> g \<or> \<not> beval t \<sigma> \<gamma> \<theta> g"
    by auto
  moreover
  { assume "beval t \<sigma> \<gamma> \<theta> g"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` by auto
    hence "beval_world2 w t g"
      using `beval t \<sigma> \<gamma> \<theta> g` `w = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      by (transfer', simp add: beval_beval_world_ci)
    have "w, t , s1 \<Rightarrow>\<^sub>s w'"
      using `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)` `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `w' = worldline2 t \<sigma> \<theta> \<tau>'` unfolding world_seq_exec_def Let_def by auto
    with assms(1) and `P w` have "Q w'"
      using `beval_world2 w t g` unfolding seq_hoare_valid2_def by auto }
  moreover
  { assume "\<not> beval t \<sigma> \<gamma> \<theta> g"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` by auto
    hence "\<not> beval_world2 w t g"
      using `\<not> beval t \<sigma> \<gamma> \<theta> g` `w = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      by (transfer', simp add: beval_beval_world_ci)
    have "w, t, s2 \<Rightarrow>\<^sub>s w'"
      using `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)` `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `w' = worldline2 t \<sigma> \<theta> \<tau>'` unfolding world_seq_exec_def Let_def by auto
    with assms(2) and `P w` have "Q w'"
      using `\<not> beval_world2 w t g` unfolding seq_hoare_valid2_def by auto }
  ultimately show "Q w'"
    by auto
qed

lemma lift_world_trans_worldline_upd2:
  assumes "w, t, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w'"
  shows "w' = w[sig, t + dly :=\<^sub>2 beval_world2 w t exp]"
  using assms
proof transfer'
  fix w t sig
  fix exp :: "'a bexp"
  fix dly w'
  assume "w, t , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w'"
  obtain \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence w_def: "w = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> exp) \<tau> (t + dly)"
    by auto
  moreover have "beval t \<sigma> \<gamma> \<theta> exp = beval_world2 w t exp"
    using `w = worldline2 t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (transfer', simp add: beval_beval_world_ci)
  ultimately have \<tau>'_def: "\<tau>' = trans_post sig (beval_world2 w t exp) \<tau> (t + dly)"
      by auto
  have "w' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `w, t , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w'` `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by auto
  also have "... = w[sig, t + dly:=\<^sub>2 beval_world2 w t exp]"
    using w_def \<tau>'_def by (transfer', meson lift_trans_post_worldline_upd)
  finally show "w' = w[sig, t + dly:=\<^sub>2 beval_world2 w t exp]"
    by auto
qed

lemma Bassign_trans_sound_hoare2:
  "\<turnstile>\<^sub>t [P] Bassign_trans sig exp dly [Q] \<Longrightarrow> \<Turnstile>\<^sub>t [P] Bassign_trans sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix w w'
  assume "\<turnstile>\<^sub>t [P] Bassign_trans sig exp dly [Q]"
  hence imp: "\<forall>w. P w \<longrightarrow> Q(w[sig, t + dly :=\<^sub>2 beval_world2 w t exp])"
    by (auto dest!: BassignE_hoare2)
  assume " P w \<and> (w, t , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w')"
  hence "P w" and "w, t, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w'" by auto
  obtain \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "w' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `w, t , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w'` `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  have "w' = w[sig, t + dly :=\<^sub>2 beval_world2 w t exp]"
    unfolding `w' = worldline2 t \<sigma> \<theta> \<tau>'`
    by (simp add: \<open>w' = worldline2 t \<sigma> \<theta> \<tau>'\<close> \<open>w, t , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s w'\<close> lift_world_trans_worldline_upd2)
  with imp and `P w` have "Q(w[sig, t + dly :=\<^sub>2 beval_world2 w t exp])"
    by auto
  thus "Q w'"
    using `Q(w[sig, t + dly :=\<^sub>2 beval_world2 w t exp])` `w' = w[sig, t + dly :=\<^sub>2 beval_world2 w t exp]`
    by auto
qed

lemma lift_world_inert_worldline_upd2:
  assumes "w, t, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s w'"
  assumes "0 < dly"
  shows "w' = w[sig, t, dly :=\<^sub>2 beval_world2 w t exp]"
  using assms
proof transfer'
  fix w t sig
  fix exp :: "'a bexp"
  fix dly w'
  assume "w, t , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s w'"
  assume "0 < dly"
  obtain \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence w_def: "w = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = inr_post sig (beval t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    by auto
  moreover have "beval t \<sigma> \<gamma> \<theta> exp = beval_world2 w t exp"
    using `w = worldline2 t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (transfer', simp add: beval_beval_world_ci)
  ultimately have \<tau>'_def: "\<tau>' = inr_post sig (beval_world2 w t exp) (\<sigma> sig) \<tau> t dly"
    by auto
  have "w' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `w, t , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s w'` `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by auto
  also have "... = w[sig, t, dly:=\<^sub>2 beval_world2 w t exp]"
    using `w = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` `0 < dly`
    by (transfer', simp add: lift_inr_post_worldline_upd)
  finally show "w' = w[sig, t, dly:=\<^sub>2 beval_world2 w t exp]"
    by auto
qed

lemma Bassign_inert_sound_hoare2:
  assumes "0 < dly"
  shows "\<turnstile>\<^sub>t [P] Bassign_inert sig exp dly [Q] \<Longrightarrow> \<Turnstile>\<^sub>t [P] Bassign_inert sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix w w'
  assume "\<turnstile>\<^sub>t [P] Bassign_inert sig exp dly [Q]"
  hence imp: "\<forall>w. P w \<longrightarrow> Q(w[sig, t, dly :=\<^sub>2 beval_world2 w t exp])"
    by (auto dest!: Bassign_inertE_hoare2)
  assume "P w \<and> (w, t , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s w')"
  hence "P w" and "w, t , (Bassign_inert sig exp dly) \<Rightarrow>\<^sub>s w'" by auto
  obtain \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "w' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `w, t , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s w'` `destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  have "w' = w[sig, t, dly :=\<^sub>2 beval_world2 w t exp]"
    by (simp add: \<open>w, t , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s w'\<close> assms lift_world_inert_worldline_upd2)
  with imp and `P w` have "Q(w[sig, t, dly :=\<^sub>2 beval_world2 w t exp])"
    by auto
  thus "Q w'"
    using `Q(w[sig, t,  dly :=\<^sub>2 beval_world2 w t exp])` `w' = w[sig, t, dly :=\<^sub>2 beval_world2 w t exp]`
    by auto
qed

subsubsection \<open>Soundness and completeness\<close>

lemma soundness_hoare2:
  assumes "\<turnstile>\<^sub>t [P] s [R]"
  assumes "nonneg_delay s"
  shows "\<Turnstile>\<^sub>t [P] s [R]"
  using assms
proof (induction rule:seq_hoare2.induct)
  case (AssignI2 t P sig dly exp)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound_hoare2[OF `0 < dly`]  using seq_hoare2.AssignI2 by fastforce
next
  case (Conseq2 P' P t s Q Q')
  then show ?case  by (auto simp add: seq_hoare_valid2_def)
qed (auto simp add: Bnull_sound_hoare2 Bassign_trans_sound_hoare2 Bcomp_hoare_valid' Bguarded_hoare_valid2)

lemma  world_seq_exec_bnull:
  "w, t, Bnull \<Rightarrow>\<^sub>s w"
  unfolding world_seq_exec_def Let_def
  by (metis (mono_tags, lifting) b_seq_exec.simps(1) destruct_worldline_exist old.prod.case
      worldline2_constructible)

lemma world_seq_exec_comp:
  assumes "nonneg_delay (Bcomp ss1 ss2)"
  shows "w, t, (Bcomp ss1 ss2) \<Rightarrow>\<^sub>s (world_seq_exec (world_seq_exec w t ss1) t ss2)"
proof -
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by blast
  then obtain \<tau>'' where "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and exec1: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    and ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''" using b_seq_exec_preserves_context_invariant
    using assms by fastforce
  hence *: "worldline2 t \<sigma> \<theta> \<tau>'' = world_seq_exec w t ss1"
    unfolding world_seq_exec_def Let_def using des1 by auto

  obtain \<theta>2 \<tau>2 \<tau>3 where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>'') t = (\<sigma>, \<gamma>, \<theta>2, \<tau>2)" and
    beh_same:"\<And>s k. signal_of2 False \<theta> s k = signal_of2 False \<theta>2 s k" and
    trans_same: "\<And>s k. signal_of2 (\<sigma> s) \<tau>'' s k = signal_of2 (\<sigma> s) \<tau>2 s k" and
    exec2: "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3"
    using destruct_worldline_correctness[OF ci2]  by (metis prod.exhaust_sel)
  have ci3: "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2"
    using worldline2_constructible[OF des2] by auto
  have "\<And>s k. signal_of2 (\<sigma> s) \<tau>' s k = signal_of2 (\<sigma> s) \<tau>3 s k"
    using helper'[OF exec1 beh_same trans_same exec2 ci2 ci3] assms by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta>2 \<tau>3"
    using beh_same
  proof (transfer')
    fix \<sigma> :: "'a state"
    fix \<tau>' \<tau>3
    fix \<theta> \<theta>2 :: "'a transaction"
    fix t
    assume 1: "\<And>s k. signal_of2 (\<sigma> s) \<tau>' s k = signal_of2 (\<sigma> s) \<tau>3 s k"
    assume "\<And>s k. signal_of2 False \<theta> s k = signal_of2 False \<theta>2 s k"
    thus " worldline t \<sigma> \<theta> \<tau>' = worldline t \<sigma> \<theta>2 \<tau>3 "
      unfolding worldline_def  using 1 by auto
  qed
  also have "... = world_seq_exec (worldline2 t \<sigma> \<theta> \<tau>'') t ss2"
    using des2 `t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3` unfolding world_seq_exec_def Let_def
    by auto
  finally have "worldline2 t \<sigma> \<theta> \<tau>' = world_seq_exec (worldline2 t \<sigma> \<theta> \<tau>'') t ss2"
    by auto
  thus ?thesis
    using des1 `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` unfolding  *
    world_seq_exec_def Let_def by auto
qed

lemma world_seq_exec_guarded:
  assumes "beval_world2 w t g"
  shows "world_seq_exec w t (Bguarded g ss1 ss2) = world_seq_exec w t ss1"
proof -
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and
    "w = worldline2 t \<sigma> \<theta> \<tau>" using destruct_worldline_exist worldline2_constructible by blast
  moreover have "beval t \<sigma> \<gamma> \<theta> g"
    using assms `w = worldline2 t \<sigma> \<theta> \<tau>` ci1  apply transfer' using beval_beval_world_ci by metis
  ultimately have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  thus ?thesis
    by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> case_prod_conv
        des1 world_seq_exec_def)
qed

lemma world_seq_exec_guarded_not:
  assumes "\<not> beval_world2 w t g"
  shows "world_seq_exec w t (Bguarded g ss1 ss2) = world_seq_exec w t ss2"
proof -
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and
    "w = worldline2 t \<sigma> \<theta> \<tau>" using destruct_worldline_exist worldline2_constructible by blast
  moreover have "\<not> beval t \<sigma> \<gamma> \<theta> g"
    using assms `w = worldline2 t \<sigma> \<theta> \<tau>` ci1  apply transfer' using beval_beval_world_ci by metis
  ultimately have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  thus ?thesis
    by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> case_prod_conv
        des1 world_seq_exec_def)
qed

definition wp :: "'signal seq_stmt \<Rightarrow> nat \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp ss t Q = (\<lambda>w. \<forall>w'. (w, t, ss \<Rightarrow>\<^sub>s w') \<longrightarrow> Q w')"

lemma wp_bnull:
  "wp Bnull t Q = Q"
  by (rule ext)(auto simp add: wp_def world_seq_exec_bnull)

lemma wp_bcomp:
  "nonneg_delay (Bcomp ss1 ss2) \<Longrightarrow> wp (Bcomp ss1 ss2) t Q = wp ss1 t (wp ss2 t Q)"
  by (rule ext) (auto simp add: wp_def world_seq_exec_comp)

lemma wp_guarded:
  "wp (Bguarded g ss1 ss2) t Q =
  (\<lambda>w. if beval_world2 w t g then wp ss1 t Q w else wp ss2 t Q w)"
  by (rule ext) (auto simp add: wp_def world_seq_exec_guarded world_seq_exec_guarded_not)

lemma wp_trans:
  "wp (Bassign_trans sig exp dly) t Q =
  (\<lambda>w. Q(w[sig, t + dly :=\<^sub>2 beval_world2 w t exp]))"
  by (rule ext, metis VHDL_Hoare_Complete.wp_def lift_world_trans_worldline_upd2)

lemma wp_inert:
  "0 < dly \<Longrightarrow> wp (Bassign_inert sig exp dly) t Q =
  (\<lambda>w. Q(w[sig, t, dly :=\<^sub>2 beval_world2 w t exp]))"
  by (rule ext, metis VHDL_Hoare_Complete.wp_def lift_world_inert_worldline_upd2)

lemma wp_is_pre: "nonneg_delay ss \<Longrightarrow> \<turnstile>\<^sub>t [wp ss t Q] ss [Q]"
proof (induction ss arbitrary: Q)
case (Bcomp ss1 ss2)
  then show ?case by (auto simp add: wp_bcomp)
next
  case (Bguarded x1 ss1 ss2)
  then show ?case by (auto intro:Conseq2 simp add: wp_guarded)
next
  case (Bassign_trans x1 x2 x3)
  then show ?case by (auto simp add: wp_trans)
next
  case (Bassign_inert x1 x2 x3)
  moreover have "0 < x3" using Bassign_inert by auto
  ultimately show ?case  using AssignI2 by (auto simp add: wp_inert)
next
  case Bnull
  then show ?case by (auto simp add: wp_bnull)
qed

lemma hoare_complete:
  assumes "nonneg_delay ss" assumes "\<Turnstile>\<^sub>t [P] ss [Q]" shows "\<turnstile>\<^sub>t [P] ss [Q]"
proof (rule strengthen_pre_hoare2)
  show "\<forall>w. P w \<longrightarrow> wp ss t Q w" using assms
    by (auto simp add:  seq_hoare_valid2_def wp_def)
  show " \<turnstile>\<^sub>t [VHDL_Hoare_Complete.wp ss t Q] ss [Q]"
    using assms by (intro wp_is_pre)
qed

corollary hoare_sound_complete:
  assumes "nonneg_delay ss"
  shows "\<turnstile>\<^sub>t [P] ss [Q] \<longleftrightarrow> \<Turnstile>\<^sub>t [P] ss [Q]"
  using hoare_complete soundness_hoare2 assms by auto

subsection \<open>A sound and complete Hoare logic for VHDL's concurrent statement\<close>

definition event_of :: "'signal worldline2  \<Rightarrow> nat \<Rightarrow> 'signal event" where
  "event_of w t = (fst o snd) (destruct_worldline w t)"

inductive
  conc_hoare :: "nat \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile>\<^sub>_ (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
Single:  "\<turnstile>\<^sub>t [\<lambda>w. P w \<and> \<not> disjnt sl (event_of w t)] ss [Q] \<Longrightarrow> \<forall>w. P w \<and> disjnt sl (event_of w t) \<longrightarrow> Q w
    \<Longrightarrow> \<turnstile>\<^sub>t \<lbrace>P\<rbrace> process sl : ss \<lbrace>Q\<rbrace>"
| Parallel:  "\<turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile>\<^sub>t \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Parallel2: "\<turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile>\<^sub>t \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Conseq': "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile>\<^sub>t \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t \<lbrace>P'\<rbrace> c \<lbrace>Q\<rbrace>"

lemma strengthen_pre_conc_hoare:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile>\<^sub>t \<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace>"
  shows "\<turnstile>\<^sub>t \<lbrace>P'\<rbrace> s \<lbrace>Q\<rbrace>"
  using assms by (blast intro: Conseq')

definition world_conc_exec :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal worldline2"
  where
  "world_conc_exec w t c = (let (\<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline w t;
                                          \<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c \<tau>
                           in worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_conc_exec_abb :: "'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal worldline2 \<Rightarrow> bool"
  ("(_, _ , _) \<Rightarrow>\<^sub>c _")
  where "world_conc_exec_abb w t s w' \<equiv> (world_conc_exec w t s = w')"

(* Diagram for lifting the concurrent execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>c          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>>    \<longrightarrow>\<^sub>c          \<tau>'
 *
 *)

lemma world_conc_exec_commute:
  assumes "w, t, (cs1 || cs2) \<Rightarrow>\<^sub>c w1"
  assumes "w, t, (cs2 || cs1) \<Rightarrow>\<^sub>c w2"
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "w1 = w2"
proof -
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> \<tau>' = w1"
    using assms(1) unfolding world_conc_exec_def Let_def by (auto split:prod.splits)
  hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_comp_commute'[OF assms(3)] by auto
  thus ?thesis
    using assms(2) unfolding world_conc_exec_def Let_def
    using \<open>destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> \<tau>' = w1\<close> by auto
qed

lemma world_conc_exec_disjnt:
  assumes "disjnt sl (event_of w t)" shows "w, t, (process sl : ss) \<Rightarrow>\<^sub>c w"
proof -
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist by blast
  moreover have "disjnt sl \<gamma>"
    using assms unfolding event_of_def des by auto
  ultimately have "\<tau>' = \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = w"
    using des  worldline2_constructible by blast
  with des ex show ?thesis
    by (simp add: world_conc_exec_def)
qed

lemma world_conc_exec_not_disjnt:
  assumes "\<not> disjnt sl (event_of w t)" and "w, t, ss \<Rightarrow>\<^sub>s w'"
  shows "w, t, (process sl : ss) \<Rightarrow>\<^sub>c w'"
proof -
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist by blast
  moreover have "\<not> disjnt sl \<gamma>"
    using assms unfolding event_of_def des by auto
  ultimately have "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = w'"
    using assms(2) des by (simp add: world_seq_exec_def)
  thus ?thesis
    using des ex by (simp add: world_conc_exec_def)
qed

definition
conc_hoare_valid :: "nat \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile>\<^sub>_ \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Turnstile>\<^sub>t \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>w w'.  P w \<and> (w, t, c \<Rightarrow>\<^sub>c w') \<longrightarrow> Q w')"

lemma helper_b_conc:
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <cs, \<tau>1> \<longrightarrow>\<^sub>c \<tau>1'"
  assumes "\<And>k s. signal_of2 False \<theta>1 s k = signal_of2 False \<theta>2 s k"
  assumes "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <cs, \<tau>2> \<longrightarrow>\<^sub>c \<tau>2'"
  assumes "context_invariant t \<sigma> \<gamma> \<theta>1 \<tau>1" and "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2"
  assumes "nonneg_delay_conc cs"
  shows "\<And>k s. signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
  using assms
proof (induction cs arbitrary: \<tau>1 \<tau>2 \<tau>1' \<tau>2')
  case (Bpar cs1 cs2)
  define \<tau>11 where "\<tau>11 = b_conc_exec t \<sigma> \<gamma> \<theta>1 cs1 \<tau>1"
  define \<tau>12 where "\<tau>12 = b_conc_exec t \<sigma> \<gamma> \<theta>1 cs2 \<tau>1"
  hence \<tau>1'_def: "\<tau>1' = clean_zip \<tau>1 (\<tau>11, set (signals_from cs1)) (\<tau>12, set (signals_from cs2))"
    using \<tau>11_def using Bpar by auto
  define \<tau>21 where "\<tau>21 = b_conc_exec t \<sigma> \<gamma> \<theta>2 cs1 \<tau>2"
  define \<tau>22 where "\<tau>22 = b_conc_exec t \<sigma> \<gamma> \<theta>2 cs2 \<tau>2"
  hence \<tau>2'_def: "\<tau>2' = clean_zip \<tau>2 (\<tau>21, set (signals_from cs1)) (\<tau>22, set (signals_from cs2))"
    using \<tau>21_def using Bpar by auto
  hence ind1: "\<And>s k. signal_of2 (\<sigma> s) \<tau>11 s k = signal_of2 (\<sigma> s) \<tau>21 s k"
    using Bpar(1)[OF _ Bpar(4-5) _ Bpar(7-8), of "\<tau>11" "\<tau>21"] Bpar(9) \<tau>11_def \<tau>21_def by auto
  hence ind2: "\<And>s k. signal_of2 (\<sigma> s) \<tau>12 s k = signal_of2 (\<sigma> s) \<tau>22 s k"
    using Bpar(2)[OF _ Bpar(4-5) _ Bpar(7-8), of "\<tau>12" "\<tau>22"] Bpar(9) \<tau>12_def \<tau>22_def by auto
  have "s \<in> set (signals_from cs1) \<or> s \<notin> set (signals_from cs1) \<and> s \<in> set (signals_from cs2) \<or>
        s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence "\<And>n. lookup (to_transaction2 \<tau>1' s) = lookup (to_transaction2 \<tau>11 s)"
      using \<tau>1'_def apply transfer'
      unfolding to_trans_raw2_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n. lookup (to_transaction2 \<tau>2' s) = lookup (to_transaction2 \<tau>21 s)"
      using `s \<in> set (signals_from cs1)` \<tau>2'_def apply transfer'
      unfolding to_trans_raw2_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using signal_of2_lookup_sig_same ind1 ind2 by metis }
  moreover
  { assume *: "s \<notin> set (signals_from cs1) \<and> s \<in> set (signals_from cs2)"
    hence "\<And>n. lookup (to_transaction2 \<tau>1' s) = lookup (to_transaction2 \<tau>12 s)"
      using \<tau>1'_def apply transfer'
      unfolding to_trans_raw2_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n. lookup (to_transaction2 \<tau>2' s) = lookup (to_transaction2 \<tau>22 s)"
      using * \<tau>2'_def apply transfer'
      unfolding to_trans_raw2_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using signal_of2_lookup_sig_same ind1 ind2 by metis }
  moreover
  { assume *: "s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    hence "\<And>n. lookup (to_transaction2 \<tau>1' s) = lookup (to_transaction2 \<tau>1 s)"
      using \<tau>1'_def apply transfer'
      unfolding to_trans_raw2_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    moreover have "\<And>n. lookup (to_transaction2 \<tau>2' s) = lookup (to_transaction2 \<tau>2 s)"
      using * \<tau>2'_def apply transfer'
      unfolding to_trans_raw2_def clean_zip_raw_def Let_def by (auto split:prod.splits)
    ultimately have  ?case
      using signal_of2_lookup_sig_same ind1 ind2 Bpar(5) by metis }
  ultimately show ?case by auto
next
  case (Bsingle sl ss)
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence "\<tau>1' = \<tau>1" and "\<tau>2' = \<tau>2"
      using Bsingle by auto
    with Bsingle(3) have ?case by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence tau1': "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'" and tau2': "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
      using Bsingle by auto
    have "nonneg_delay ss"
      using Bsingle by auto
    hence ?case
      using helper'[OF tau1' Bsingle(2-3) tau2' Bsingle(5-6)] by auto }
  ultimately show ?case by auto
qed

lemma world_conc_exec_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "w, t, (cs1 || cs2) \<Rightarrow>\<^sub>c (world_conc_exec (world_conc_exec w t cs1) t cs2)"
proof -
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by blast
  have ci': "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ci ex `nonneg_delay_conc cs1`] by auto
  hence wcs1: "world_conc_exec w t cs1 = worldline2 t \<sigma> \<theta> \<tau>'"
    using des ex by (simp add: world_conc_exec_def)
  obtain theta tau' where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>') t = (\<sigma>, \<gamma>, theta, tau')"
    and beh_same: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False theta s k" and
        trans_same: "\<And>k s. signal_of2 (\<sigma> s) \<tau>' s k = signal_of2 (\<sigma> s) tau' s k"
    using destruct_worldline_correctness[OF ci'] by (metis prod_cases4)
  have ci2: "context_invariant t \<sigma> \<gamma> theta tau'" and "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> theta tau'"
    using worldline2_constructible[OF des2] by auto
  have "\<And>k s. signal_of2 (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>') s  k =
              signal_of2  (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> theta cs2 tau') s k"
    using helper_b_conc[OF _ beh_same trans_same _ ci' ci2 `nonneg_delay_conc cs2`]
    by auto
  hence *: "worldline2 t \<sigma> theta (b_conc_exec t \<sigma> \<gamma> theta cs2 tau') =
        worldline2 t \<sigma> \<theta> (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>')"
    using beh_same apply transfer' unfolding worldline_def by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =  b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>'"
    using b_conc_exec_sequential[OF assms(1)] ex by auto
  hence "world_conc_exec w t (cs1 || cs2) = worldline2 t \<sigma> \<theta> (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>')"
    using des ex by (auto simp add: world_conc_exec_def)
  hence "(world_conc_exec w t cs1), t , cs2 \<Rightarrow>\<^sub>c (world_conc_exec w t (cs1 || cs2))"
    using des2 wcs1 *  by (simp add: world_conc_exec_def)
  thus ?thesis
    by simp
qed

lemma world_conc_exec_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "w, t, (cs1 || cs2) \<Rightarrow>\<^sub>c (world_conc_exec (world_conc_exec w t cs2) t cs1)"
proof -
  have wf: "conc_stmt_wf (cs2 || cs1)" and nd: "nonneg_delay_conc (cs2 || cs1)"
    using assms unfolding conc_stmt_wf_def by auto
  have "w , t, (cs1 || cs2) \<Rightarrow>\<^sub>c world_conc_exec w t (cs2 || cs1)"
    using world_conc_exec_commute[OF _ _ assms(1)] by blast
  with world_conc_exec_parallel[OF wf nd] show ?thesis
    by auto
qed

lemma parallel_valid:
  assumes "\<Turnstile>\<^sub>t \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Turnstile>\<^sub>t \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)"
  shows "\<Turnstile>\<^sub>t \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding conc_hoare_valid_def
proof rule+
  fix w w'
  assume "P w \<and> w, t , c1 || c2 \<Rightarrow>\<^sub>c w'"
  hence "P w" and "w, t, c1 || c2 \<Rightarrow>\<^sub>c w'"
    by auto
  then obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and
    *: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c1 || c2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and w'_def: "worldline2 t \<sigma> \<theta> \<tau>' = w'" and
    ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding world_conc_exec_def Let_def  using destruct_worldline_exist
    by (metis (mono_tags, lifting) old.prod.case worldline2_constructible)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> c1 \<tau>"
  hence ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>1"
    using b_conc_exec_preserves_context_invariant[OF ci] assms(4) by auto
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>"
  hence ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>2"
    using b_conc_exec_preserves_context_invariant[OF ci] assms(4) by auto
  have \<tau>'_def: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>1"
    using b_conc_exec_sequential[OF assms(3)] * unfolding \<tau>1_def by auto
  define w1 where "w1 = worldline2 t \<sigma> \<theta> \<tau>1"
  have "w, t, c1 \<Rightarrow>\<^sub>c w1"
    using des \<tau>1_def unfolding world_conc_exec_def Let_def by (simp add: w1_def)
  hence "R w1"
    using assms(1) `P w` unfolding conc_hoare_valid_def by auto
  obtain theta1 tau1 where des2: "destruct_worldline w1 t = (\<sigma>, \<gamma>, theta1, tau1)" and
    beh_same: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False theta1 s k" and
    trans_same: "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) tau1 s k"
    using destruct_worldline_exist[of "worldline2 t \<sigma> \<theta> \<tau>1" "t"] unfolding w1_def
    using destruct_worldline_correctness[OF ci1] by metis
  have "context_invariant t \<sigma> \<gamma> theta1 tau1"
    using des2 worldline2_constructible by blast
  moreover have "nonneg_delay_conc c2"
    using assms(4) by auto
  ultimately have "worldline2 t \<sigma> theta1 (b_conc_exec t \<sigma> \<gamma> theta1 c2 tau1) = worldline2 t \<sigma> \<theta> \<tau>'"
    using beh_same trans_same \<tau>'_def ci1
  proof (transfer')
    fix \<sigma> :: "'a state"
    fix \<theta> theta1 :: "'a transaction"
    fix \<tau>1 tau1 \<tau>'
    fix t \<gamma> c2
    assume bs: "\<And>s k. signal_of2 False \<theta> s k = signal_of2 False theta1 s k"
    assume ts: "\<And>s k. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) tau1 s k"
    assume \<tau>'_def': "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>1"
    assume ci1': " context_invariant t \<sigma> \<gamma> \<theta> \<tau>1"
    assume ci2': "context_invariant t \<sigma> \<gamma> theta1 tau1"
    assume "nonneg_delay_conc c2"
    hence "\<And>k s. signal_of2 (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> theta1 c2 tau1) s k =
          signal_of2 (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>1) s k"
      using helper_b_conc[OF _ bs ts _ ci1' ci2'] \<tau>'_def' by metis
    thus "worldline t \<sigma> theta1 (b_conc_exec t \<sigma> \<gamma> theta1 c2 tau1) = worldline t \<sigma> \<theta> \<tau>'"
      unfolding worldline_def \<tau>'_def' using bs by auto
  qed
  hence "w1, t , c2 \<Rightarrow>\<^sub>c w'"
    using des2 by (simp add: w'_def world_conc_exec_def)
  with `R w1` show "Q w'"
    using assms(2) using conc_hoare_valid_def by metis
qed

lemma soundness_conc_hoare:
  assumes "\<turnstile>\<^sub>t \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_stmt_wf c" and "nonneg_delay_conc c"
  shows "\<Turnstile>\<^sub>t \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:conc_hoare.induct)
  case (Single t P sl ss Q)
  { fix w w'
    assume as: "P w \<and> (w, t ,  process sl : ss \<Rightarrow>\<^sub>c w')"
    then obtain \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)" and "P w" and
      ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> \<tau>' = w'"
      unfolding world_seq_exec_def Let_def
      by (smt case_prod_conv destruct_worldline_exist world_conc_exec_def)
    have "nonneg_delay ss"
      using Single by auto
    have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
      by auto
    moreover
    { assume "disjnt sl \<gamma>"
      hence "\<tau>' = \<tau>" using ex by auto
      hence "w' = w"
        using \<open>destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> \<tau>' = w'\<close> worldline2_constructible
        by blast
      with Single have "Q w'"
        unfolding event_of_def  using \<open>P w \<and> w, t , process sl : ss \<Rightarrow>\<^sub>c w'\<close>
        \<open>destruct_worldline w t = (\<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>disjnt sl \<gamma>\<close>  disjnt_sym by fastforce }
    moreover
    { assume "\<not> disjnt sl \<gamma>"
      hence "\<not> disjnt sl (event_of w t)"
        unfolding event_of_def using des by auto
      moreover have "w, t, ss \<Rightarrow>\<^sub>s w'"
        using as `\<not> disjnt sl \<gamma>`
      proof -
        have "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
          using \<open>\<not> disjnt sl \<gamma>\<close> ex by force
        then show ?thesis
          by (simp add: \<open>worldline2 t \<sigma> \<theta> \<tau>' = w'\<close> des world_seq_exec_def)
      qed
      ultimately have "Q w'"
        using soundness_hoare2[OF Single(1) `nonneg_delay ss`] `P w` unfolding seq_hoare_valid2_def
        by auto }
    ultimately have "Q w'" by auto }
  then show ?case
    unfolding conc_hoare_valid_def by auto
next
  case (Parallel t P cs\<^sub>1 R cs\<^sub>2 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel by auto
  ultimately have " \<Turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace>" and " \<Turnstile>\<^sub>t \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace>"
    using Parallel by auto
  then show ?case
    using parallel_valid Parallel by blast
next
  case (Parallel2 t P cs\<^sub>2 R cs\<^sub>1 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel2 by auto
  ultimately have cs2: " \<Turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>" and cs1: " \<Turnstile>\<^sub>t \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using Parallel2 by auto
  have "conc_stmt_wf (cs\<^sub>2 || cs\<^sub>1)"
    using Parallel2(3) unfolding conc_stmt_wf_def by auto
  moreover have " nonneg_delay_conc (cs\<^sub>2 || cs\<^sub>1) "
    using Parallel2(7) by auto
  ultimately have "\<Turnstile>\<^sub>t \<lbrace>P\<rbrace> cs\<^sub>2 || cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using parallel_valid[OF cs2 cs1]   by auto
  thus ?case
    using world_conc_exec_commute[OF _ _ Parallel2(3)]  by (metis conc_hoare_valid_def)
next
  case (Conseq' P' P t c Q Q')
  then show ?case by (auto simp add: conc_hoare_valid_def)
qed

definition wp_conc :: "'signal conc_stmt \<Rightarrow> nat \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp_conc cs t Q = (\<lambda>w. \<forall>w'. (w, t, cs \<Rightarrow>\<^sub>c w') \<longrightarrow> Q w')"

lemma wp_conc_single:
  "wp_conc (process sl : ss) t Q =
  (\<lambda>w. if disjnt sl (event_of w t) then Q w else wp ss t Q w)"
  by (rule ext) (auto simp add: wp_conc_def wp_def world_conc_exec_disjnt world_conc_exec_not_disjnt)

lemma wp_conc_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) t Q =  wp_conc cs1 t (wp_conc cs2 t Q)"
  by (rule ext)(auto simp add: wp_conc_def world_conc_exec_parallel[OF assms])

lemma wp_conc_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) t Q =  wp_conc cs2 t (wp_conc cs1 t Q)"
  by (rule ext)(auto simp add: wp_conc_def world_conc_exec_parallel2[OF assms])

lemma wp_conc_is_pre:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "\<turnstile>\<^sub>t \<lbrace>wp_conc cs t Q\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction cs arbitrary:Q)
  case (Bpar cs1 cs2)
  hence "conc_stmt_wf cs1" and "conc_stmt_wf cs2" and "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    by auto
  hence "\<And>Q.  \<turnstile>\<^sub>t \<lbrace>wp_conc cs1 t Q\<rbrace> cs1 \<lbrace>Q\<rbrace>" and "\<And>Q.  \<turnstile>\<^sub>t \<lbrace>wp_conc cs2 t Q\<rbrace> cs2 \<lbrace>Q\<rbrace>"
    using Bpar(1-2) by auto
  then show ?case
    unfolding wp_conc_parallel[OF Bpar(3-4)]
    by (auto intro!: Parallel simp add: Bpar)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  then show ?case  unfolding wp_conc_single
    by (auto intro!: Single simp add: hoare_complete seq_hoare_valid2_def wp_def)
qed

lemma conc_hoare_complete:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  assumes "\<Turnstile>\<^sub>t \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>" shows "\<turnstile>\<^sub>t \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
proof (rule strengthen_pre_conc_hoare)
  show " \<forall>w. P w \<longrightarrow> wp_conc cs t Q w" using assms
    by (auto simp add: conc_hoare_valid_def wp_conc_def)
next
  show "\<turnstile>\<^sub>t \<lbrace>wp_conc cs t Q\<rbrace> cs \<lbrace>Q\<rbrace>"
    using assms by (intro wp_conc_is_pre)
qed

corollary conc_hoare_sound_and_complete:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "\<turnstile>\<^sub>t \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Turnstile>\<^sub>t \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  using conc_hoare_complete soundness_conc_hoare assms by auto

end