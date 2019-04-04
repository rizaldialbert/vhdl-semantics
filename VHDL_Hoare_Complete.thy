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

subsection \<open>A sound and complete Hoare logic for VHDL's sequential statements\<close>

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

lemma property_of_degree':
  fixes w :: "'signal worldline2"
  defines "d \<equiv> worldline_deg w"
  shows "\<forall>t > d. \<forall>s. Rep_worldline w s t = Rep_worldline w s d"
  using LeastI_ex[OF existence_of_degree] unfolding d_def worldline_deg_def by auto

lemma property_of_degree:
  fixes w :: "'signal worldline2"
  defines "d \<equiv> worldline_deg w"
  shows "\<forall>t \<ge> d. \<forall>s. Rep_worldline w s t = Rep_worldline w s d"
proof (rule, rule)
  fix t
  assume "d \<le> t"
  hence "d < t \<or> d = t"
    by auto
  moreover
  { assume "d < t"
    hence "\<forall>s. Rep_worldline w s t = Rep_worldline w s d"
      using property_of_degree'  using d_def by blast }
  moreover
  { assume "d = t"
    hence "\<forall>s. Rep_worldline w s t = Rep_worldline w s d"
      by auto }
  ultimately show "\<forall>s. Rep_worldline w s t = Rep_worldline w s d"
    by auto
qed

lift_definition worldline_upd2 ::
  "nat \<times> 'signal worldline2 \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> nat \<times> 'signal worldline2" ("_[ _, _ :=\<^sub>2 _]")
  is "\<lambda>tw sig dly val. (fst tw, worldline_upd (snd tw) sig (fst tw + dly) val)"
proof
  fix tw :: "nat \<times> ('signal \<Rightarrow> nat \<Rightarrow> val)"
  show "top (fst tw)"
    by auto
next
  fix tw :: "nat \<times> ('signal \<Rightarrow> nat \<Rightarrow> val)"
  fix sig dly v
  assume " pred_prod top (\<lambda>w. \<exists>t. \<forall>t'>t. (\<lambda>s. w s t') = (\<lambda>s. w s t)) tw"
  hence "\<exists>t. \<forall>t'>t. (\<lambda>s'. snd tw s' t') = (\<lambda>s'. snd tw s' t)"
    by (auto simp add: prod.pred_set intro!:snds.intros)
  then obtain tcurr :: "nat" where *: "\<forall>t' > tcurr. (\<lambda>s'. snd tw s' t') = (\<lambda>s'. snd tw s' tcurr)"
    by auto
  hence **: "\<And>t' s'. t' > tcurr \<Longrightarrow> snd tw s' t' = snd tw s' tcurr"
    by meson
  have "fst tw + dly < tcurr \<or> tcurr \<le> fst tw + dly"
    by auto
  moreover
  { assume "fst tw + dly < tcurr"
    hence "\<forall>t'> tcurr. (\<lambda>s. snd tw[sig, fst tw + dly := v] s t') = (\<lambda>s. snd tw[sig, fst tw + dly := v] s tcurr)"
      unfolding worldline_upd_def using ** by auto
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. snd tw[sig, fst tw + dly := v] s t') = (\<lambda>s. snd tw[sig, fst tw + dly := v] s t'')"
      by auto }
  moreover
  { assume "tcurr \<le> fst tw + dly"
    hence "\<forall>t'> fst tw + dly. (\<lambda>s. (snd tw)[sig, fst tw + dly:= v] s t') = (\<lambda>s. (snd tw)[sig, fst tw + dly := v] s (fst tw + dly))"
      unfolding worldline_upd_def using **
      by (metis (no_types, hide_lams) "*" add_less_mono1 le_antisym le_eq_less_or_eq le_neq_implies_less le_trans less_irrefl_nat)
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. (snd tw)[sig, fst tw + dly := v] s t') = (\<lambda>s. (snd tw)[sig, fst tw + dly := v] s t'')"
      by auto }
  ultimately show "\<exists>t''. \<forall>t'>t''. (\<lambda>s. (snd tw)[sig, fst tw + dly := v] s t') = (\<lambda>s. (snd tw)[sig, fst tw + dly := v] s t'')"
    by auto
qed

lift_definition worldline_inert_upd2 ::
  "nat \<times> 'signal worldline2 \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> nat \<times> 'signal worldline2" ("_\<lbrakk> _, _ :=\<^sub>2 _\<rbrakk>")
  is "\<lambda>tw sig dly v. (fst tw, worldline_inert_upd (snd tw) sig (fst tw) dly v)"
proof
  fix tw :: "nat \<times> ('signal \<Rightarrow> nat \<Rightarrow> val)"
  show "top (fst tw)"
    by auto
next
  fix tw :: "nat \<times> ('signal \<Rightarrow> nat \<Rightarrow> val)"
  fix sig v
  fix dly :: nat
  assume "pred_prod top (\<lambda>w. \<exists>t. \<forall>t'>t. (\<lambda>s. w s t') = (\<lambda>s. w s t)) tw"
  hence "\<exists>t. \<forall>t'>t. (\<lambda>s'. snd tw s' t') = (\<lambda>s'. snd tw s' t)"
    by (auto simp add: prod.pred_set intro!:snds.intros)
  then obtain tcurr :: "nat" where *: "\<forall>t' > tcurr. (\<lambda>s'. snd tw s' t') = (\<lambda>s'. snd tw s' tcurr)"
    by auto
  hence **: "\<And>t' s'. t' > tcurr \<Longrightarrow> snd tw s' t' = snd tw s' tcurr"
    by meson
  have "fst tw + dly < tcurr \<or> tcurr \<le> fst tw + dly"
    by auto
  moreover
  { assume "fst tw + dly < tcurr"
    hence "\<forall>t'> tcurr. (\<lambda>s. (snd tw)[sig, fst tw, dly := v] s t') = (\<lambda>s. (snd tw)[sig, fst tw, dly := v] s tcurr)"
      unfolding worldline_inert_upd_def using ** by auto
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. (snd tw)[sig, fst tw, dly:= v] s t') = (\<lambda>s. (snd tw)[sig, fst tw, dly:= v] s t'')"
      by auto }
  moreover
  { assume "tcurr \<le> fst tw + dly"
    have "\<forall>t'> fst tw + dly. (\<lambda>s. (snd tw)[sig, fst tw, dly := v] s t') = (\<lambda>s. (snd tw)[sig, (fst tw), dly := v] s (fst tw + dly))"
    proof (rule, rule)
      fix t'
      assume "t' > fst tw + dly" hence "t' > tcurr" using `fst tw + dly \<ge> tcurr` by auto
      { fix s
        have "s \<noteq> sig \<or> s = sig" by auto
        moreover
        { assume "s \<noteq> sig"
          hence "(snd tw)[sig, fst tw, dly:= v] s t' = (snd tw)[sig, fst tw, dly := v] s (fst tw + dly)"
            by (metis "*" \<open>tcurr < t'\<close> \<open>tcurr \<le> fst tw + dly\<close> le_less worldline_inert_upd_def) }
        moreover
        { assume "s = sig"
          hence "(snd tw)[sig, fst tw, dly := v] s t' = (snd tw)[sig, fst tw, dly := v] s (fst tw + dly)"
            by (metis \<open>fst tw + dly < t'\<close> not_less_iff_gr_or_eq trans_less_add1 worldline_inert_upd_def) }
        ultimately have "(snd tw)[sig, fst tw, dly := v] s t' = (snd tw)[sig, fst tw, dly := v] s (fst tw + dly)"
          by auto }
      thus " (\<lambda>s. (snd tw)[sig, fst tw, dly := v] s t') = (\<lambda>s. (snd tw)[sig, fst tw, dly := v] s (fst tw + dly))"
        by auto
    qed
    hence "\<exists>t''. \<forall>t'> t''. (\<lambda>s. (snd tw)[sig, fst tw, dly:= v] s t') = (\<lambda>s. (snd tw)[sig, fst tw, dly:= v] s t'')"
      by auto }
  ultimately show "\<exists>t''. \<forall>t'> t''. (\<lambda>s. (snd tw)[sig, fst tw, dly:= v] s t') = (\<lambda>s. (snd tw)[sig, fst tw, dly:= v] s t'')"
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

lift_definition beval_world2 :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal bexp \<Rightarrow> val"
  is "\<lambda>tw exp. beval_world (snd tw) (fst tw) exp" .

type_synonym 'signal assn2 = "nat \<times> 'signal worldline2 \<Rightarrow> bool"

inductive
  seq_hoare2 :: "'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<turnstile> ([(1_)]/ (_)/ [(1_)])" 50)
  where
Null2: "\<turnstile> [P] Bnull [P]" |
Assign2: "\<turnstile> [\<lambda>tw. P(  tw[sig, dly :=\<^sub>2 beval_world2 tw exp] )] Bassign_trans sig exp dly [P]" |

AssignI2: "\<turnstile> [\<lambda>tw. P( tw\<lbrakk>sig, dly :=\<^sub>2 (beval_world2 tw exp)\<rbrakk>  )] Bassign_inert sig exp dly [P]" |

Comp2: "\<lbrakk> \<turnstile> [P] s1 [Q]; \<turnstile> [Q] s2 [R]\<rbrakk> \<Longrightarrow> \<turnstile> [P] Bcomp s1 s2 [R]" |

If2: "\<lbrakk>\<turnstile> [\<lambda>tw. P tw \<and> beval_world2 tw g] s1 [Q]; \<turnstile> [\<lambda>tw. P tw \<and> \<not> beval_world2 tw g] s2 [Q]\<rbrakk>
        \<Longrightarrow>  \<turnstile> [P] Bguarded g s1 s2 [Q]" |

Conseq2: "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile> [P] s [Q]; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile> [P'] s [Q']"

inductive_cases seq_hoare2_ic: "\<turnstile> [P] s [Q]"

lemma BnullE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bnull"
  shows "\<forall>tw. P tw \<longrightarrow> Q tw"
  using assms
  by (induction rule:seq_hoare2.induct, auto)

lemma BnullE'_hoare2:
  "\<turnstile> [P] Bnull [Q] \<Longrightarrow> \<forall>tw. P tw \<longrightarrow> Q tw"
  using BnullE_hoare2 by blast

lemma BassignE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bassign_trans sig exp dly"
  shows "\<forall>tw. P tw \<longrightarrow> Q(tw[sig, dly :=\<^sub>2 beval_world2 tw exp])"
  using assms
proof (induction rule: seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case by blast
qed auto

lemma Bassign_inertE_hoare2:
  assumes "\<turnstile> [P] s [Q]"
  assumes "s = Bassign_inert sig exp dly"
  shows "\<forall>tw. P tw \<longrightarrow> Q(tw \<lbrakk> sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk> )"
  using assms
proof (induction rule: seq_hoare2.induct)
  case (Conseq2 P' P s Q Q')
  then show ?case by blast
qed auto

lemma BcompE_hoare2:
  assumes "\<turnstile> [P] s [R]"
  assumes "s = Bcomp s1 s2"
  shows "\<exists>Q. \<turnstile> [P] s1 [Q] \<and> \<turnstile> [Q] s2 [R]"
  using assms Conseq2
  by (induction rule:seq_hoare2.induct, auto) (blast)

lemmas [simp] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2
lemmas [intro!] = seq_hoare2.Null2 seq_hoare2.Assign2 seq_hoare2.Comp2 seq_hoare2.If2

lemma strengthen_pre_hoare2:
  assumes "\<forall>tw. P' tw \<longrightarrow> P tw" and "\<turnstile> [P] s [Q]"
  shows "\<turnstile> [P'] s [Q]"
  using assms by (blast intro: Conseq2)

lemma weaken_post_hoare2:
  assumes "\<forall>tw. Q tw \<longrightarrow> Q' tw" and "\<turnstile> [P] s [Q]"
  shows "\<turnstile> [P] s [Q']"
  using assms by (blast intro: Conseq2)

lemma Assign'_hoare2:
  assumes "\<forall>tw. P tw \<longrightarrow> Q (worldline_upd2 tw sig dly (beval_world2 tw exp))"
  shows "\<turnstile> [P] Bassign_trans sig exp dly [Q]"
  using assms by (metis (no_types, lifting) Assign2 strengthen_pre_hoare2)

subsubsection \<open>Validity of Hoare proof rules\<close>

lift_definition worldline2 ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> nat \<times> 'signal worldline2"
  is "\<lambda>t \<sigma> \<theta> \<tau>. (t, worldline t \<sigma> \<theta> \<tau>)"
proof
  fix t :: nat
  show "top t"
    by auto
next
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
      using property_of_degree' unfolding d_def by auto
    hence "\<forall>n > d. Rep_worldline w s n = Rep_worldline w s (n - 1)"
      by (metis (full_types) diff_Suc_1 gr0_implies_Suc less_add_same_cancel2 less_imp_Suc_add
      less_linear not_add_less1 trans_less_add1) }
  thus ?thesis
    unfolding difference_def unfolding zero_fun_def by (simp add: zero_option_def)
qed

(* Why is this derivative not used and we used derivative_raw instead? *)
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
  "nat \<times> 'signal worldline2 \<Rightarrow> (nat \<times> 'signal state \<times> 'signal event \<times> 'signal transaction \<times> 'signal transaction)"
  where
  "destruct_worldline tw = (let  t = fst tw; w = snd tw;
                                 \<sigma> = (\<lambda>s. Rep_worldline w s t);
                                 \<theta> = derivative_hist_raw (Rep_worldline w) t;
                                 \<comment> \<open>\<theta> = poly_mapping_of_fun (\<lambda>t. Some o (\<lambda>s. (Rep_worldline w) s t)) 0 t;\<close>
                                 \<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)};
                                 \<tau> = derivative_raw (Rep_worldline w) (worldline_deg w) t
                             in (t, \<sigma>, \<gamma>, \<theta>, \<tau>))"

text \<open>One might concern about the event @{term "\<gamma> :: 'signal event"} obtained from the destruction
@{term "destruct_worldline tw"} above. What happens if @{term "t = 0"}? This is a valid concern
since we have the expression @{term "t - 1"} in the definition of @{term "\<gamma>"} above.

Note that, we impose the requirement of @{term "context_invariant"} here. When this is the case,
history @{term "\<theta> :: 'signal transaction"} is empty when @{term "t = 0"}. Hence the expression
@{term "signal_of2 False \<theta> s (t - 1)"} is equal to @{term "signal_of2 False empty_trans s 0"} and,
subsequently, equals to @{term "False"}. Hence, when @{term "t = 0"}, the @{term "\<gamma>"} enumerates the
signals which are different with the default value @{term "False :: val"}.\<close>

lemma destruct_worldline_no_trans_at_t:
  "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>) \<Longrightarrow> lookup \<tau> t = 0"
proof -
  assume "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  hence "\<tau> = derivative_raw (Rep_worldline (snd tw)) (worldline_deg (snd tw)) (fst tw)" and "fst tw = t"
    unfolding destruct_worldline_def Let_def by auto
  thus ?thesis
    unfolding worldline_deg_def by (transfer', auto simp add: zero_map)
qed

lemma fst_destruct_worldline:
  "fst (destruct_worldline tw) = fst tw"
  unfolding destruct_worldline_def Let_def by auto

lemma destruct_worldline_exist:
  "\<exists>t \<sigma> \<gamma> \<theta> \<tau>. destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  unfolding destruct_worldline_def Let_def by auto

lemma worldline2_constructible:
  fixes tw :: "nat \<times> 'signal worldline2"
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  shows "tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
proof -
  have "\<exists>t. \<forall>t'>t. (\<lambda>s. Rep_worldline (snd tw) s t') = (\<lambda>s. Rep_worldline (snd tw) s t)"
    by transfer auto
  thus ?thesis
    using assms unfolding destruct_worldline_def Let_def worldline_deg_def
  proof transfer'
    fix tw :: "nat \<times> 'signal worldline"
    fix t \<sigma> \<gamma>
    fix \<theta> \<tau> :: "'signal transaction"
    let ?w = "snd tw"
    assume *: "\<exists>t. \<forall>t'>t. (\<lambda>s. ?w s t') = (\<lambda>s. ?w s t)"
    then obtain d where d_def: "d = (LEAST t. \<forall>t'>t. (\<lambda>s. ?w s t') = (\<lambda>s. ?w s t))"
      by auto
    have d_prop: "\<forall>t'>d. (\<lambda>s. ?w s t') = (\<lambda>s. ?w s d)"
      using LeastI_ex[OF *] unfolding d_def  by blast
    hence d_prop': "\<And>n s. d < n \<Longrightarrow> ?w s n = ?w s d"
      by meson
    have d_def': "d = (LEAST n. \<forall>t>n. \<forall>s. ?w s t = ?w s n)"
      unfolding d_def  by metis
    assume **:
      "(fst tw,
        \<lambda>s. snd tw s (fst tw),
        {s. snd tw s (fst tw) \<noteq> signal_of2 False (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)},
        derivative_hist_raw (snd tw) (fst tw),
        derivative_raw (snd tw) (LEAST n. \<forall>t>n. \<forall>s. snd tw s t = snd tw s n) (fst tw)) =
        (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    hence \<sigma>_def: "\<sigma> = (\<lambda>s. ?w s t)" and
          \<gamma>_def: "\<gamma> = {s. ?w s t \<noteq> signal_of2 False (derivative_hist_raw (snd tw) (fst tw)) s (fst tw - 1)}" and
          \<theta>_def: "\<theta> = derivative_hist_raw ?w t" and
          "fst tw = t"
      by auto
    have \<tau>_def: "\<tau> = derivative_raw ?w d t"
      using ** unfolding d_def' by auto
    have "?w = worldline t \<sigma> \<theta> \<tau>"
    proof (rule ext, rule ext, cases "t \<le> d")
      case True
      fix s' t'
      have "snd tw s' t = \<sigma> s'"
        unfolding \<sigma>_def by auto
      have "t' < t \<or> t \<le> t'" by auto
      moreover
      { assume "t' < t"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' =  signal_of2 False \<theta> s' t'"
          unfolding worldline_def by auto
        also have "... = ?w s' t'"
          using signal_of2_derivative_hist_raw[OF `t' < t`] unfolding \<theta>_def  by metis
        finally have "?w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      moreover
      { assume "t \<le> t'"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 (\<sigma> s') \<tau> s' t'"
          unfolding worldline_def by auto
        also have "... = ?w s' t'"
          unfolding \<tau>_def using signal_of2_derivative_raw'[OF `t \<le> t'` True] d_prop' `snd tw s' t = \<sigma> s'`
          by metis
        finally have "?w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      ultimately show "?w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
        by auto
    next
      case False
      fix s' t'
      have "t' < t \<or> t \<le> t'" by auto
      moreover
      { assume "t' < t"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' =  signal_of2 False \<theta> s' t'"
          unfolding worldline_def by auto
        also have "... = ?w s' t'"
          using signal_of2_derivative_hist_raw[OF `t' < t`] unfolding \<theta>_def by metis
        finally have "?w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      moreover
      { assume "t \<le> t'"
        hence "worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 (\<sigma> s') \<tau> s' t'"
          unfolding worldline_def by auto
        also have "... = signal_of2 (\<sigma> s') 0 s' t'"
          unfolding \<tau>_def using derivative_raw_zero False   by (metis (mono_tags) linear)
        also have "... = \<sigma> s'"
          using signal_of2_empty by fastforce
        also have "... = ?w s' t"
          unfolding \<sigma>_def by auto
        also have "... = ?w s' t'"
          using d_prop'[of "t"] d_prop'[of "t'"] False `t \<le> t'` by auto
        finally have "?w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
          by auto }
      ultimately show "?w s' t' = worldline t \<sigma> \<theta> \<tau> s' t'"
        by auto
    qed
    have "\<forall>n. t \<le> n \<longrightarrow> lookup \<theta> n = 0"
      unfolding \<theta>_def apply transfer' by (auto simp add: zero_map)
    moreover have "\<forall>n. n < t \<longrightarrow> lookup \<tau> n = 0"
      unfolding \<tau>_def by (transfer')(auto simp add:zero_fun_def zero_option_def)
    moreover have "\<forall>s. s \<in> dom (lookup \<tau> t) \<longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
      unfolding \<tau>_def \<sigma>_def by transfer' auto
    ultimately have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
      unfolding \<gamma>_def context_invariant_def \<sigma>_def \<theta>_def `fst tw = t` by auto
    thus " tw = (t, worldline t \<sigma> \<theta> \<tau>) \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
      using `?w = worldline t \<sigma> \<theta> \<tau>` `fst tw = t` surjective_pairing[of "tw"] by auto
  qed
qed

lemma worldline2_constructible':
  fixes tw :: "nat \<times> 'signal worldline2"
  shows "\<exists>t \<sigma> \<gamma> \<theta> \<tau>. tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  using destruct_worldline_exist worldline2_constructible by blast

lemma state_worldline2:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  shows "(\<lambda>s. (Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>) s t) = \<sigma>"
  using assms
proof (intro ext, transfer')
  fix s t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> :: "'a transaction"
  assume ci: "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  hence "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
    unfolding context_invariant_weaker_def by auto
  have "lookup \<tau> t s = 0 \<or> lookup \<tau> t s \<noteq> 0" by auto
  moreover
  { assume "lookup \<tau> t s \<noteq> 0"
    hence "s \<in> dom (lookup \<tau> t)"
      by (metis domIff zero_fun_def zero_map)
    hence "\<sigma> s = the (lookup \<tau> t s)"
      using ci unfolding context_invariant_weaker_def by auto
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
  ultimately show "((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s t = \<sigma> s"
    by auto
qed

lemma history_worldline2:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  shows "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. (Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>) s ta)) 0 t) s (t - 1) =
         signal_of2 False \<theta> s (t - 1)"
  using assms
proof transfer'
  fix t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> :: "'a transaction"
  fix s
  assume "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  hence "lookup \<theta> t = 0"
    unfolding context_invariant_weaker_def by auto
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
  ultimately show "signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s ta)) 0 t) s (t - 1) = signal_of2 False \<theta> s (t - 1)"
    by auto
qed

lemma beh_of_worldline:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  shows "\<And>k. signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. (Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>) s ta)) 0 t) s k =
             signal_of2 False \<theta> s k"
  using assms
proof transfer'
  fix k t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> :: "'a transaction"
  fix s
  assume "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  hence "lookup \<theta> t = 0"
    unfolding context_invariant_weaker_def by auto
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
        using `context_invariant_weaker t \<sigma> \<theta> \<tau>` unfolding context_invariant_weaker_def by auto
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
        using `context_invariant_weaker t \<sigma> \<theta> \<tau>` unfolding context_invariant_weaker_def by auto
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
  ultimately show " signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s ta)) 0 t) s k = signal_of2 False \<theta> s k"
    by auto
qed

lemma hist_of_worldline:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  shows "\<And>k. signal_of2 False (derivative_hist_raw ((Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>)) t) s k = signal_of2 False \<theta> s k"
  using assms
proof transfer'
  fix k t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> :: "'a transaction"
  fix s
  assume "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  have *: "signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k =
        signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s k" by auto
  have "\<forall>n\<ge>t. lookup \<theta> n = 0"
    using `context_invariant_weaker t \<sigma> \<theta> \<tau>` unfolding context_invariant_weaker_def by auto
  hence "lookup \<theta> t = 0"
    by auto
  have "k < t \<or> t \<le> k"
    by auto
  moreover
  { assume "k < t"
    have "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s k = worldline t \<sigma> \<theta> \<tau> s k"
      using signal_of2_derivative_hist_raw[OF `k < t`] by metis
    also have "... = signal_of2 False \<theta> s k"
      using `k < t` unfolding worldline_def by auto
    finally have " signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k = signal_of2 False \<theta> s k "
      using * by auto }
  moreover
  { assume "t \<le> k"
    hence "t < k \<or> t = k" by auto
    moreover
    { assume "t < k"
      moreover have "\<And>n. t < n \<Longrightarrow> n \<le> k \<Longrightarrow> lookup (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) n s = None"
        by transfer' auto
      ultimately have "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s k =
                       signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s t"
        by (intro signal_of2_less_ind')( auto simp add: zero_option_def) }
    moreover
    { assume "t = k"
      hence "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s k =
             signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s t"
        by auto }
    ultimately have **: "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s k =
                         signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s t" by auto
    have "lookup (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) t = Map.empty"
      by transfer' auto
    hence ***: "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s t =
                signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1)"
      using signal_of2_less_sig zero_option_def by force
    have "0 < t \<or> t = 0"
      by auto
    moreover
    { assume "0 < t"
      hence "t - 1 < t"
        by linarith
      hence "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1) = worldline t \<sigma> \<theta> \<tau> s (t - 1)"
        using signal_of2_derivative_hist_raw[of "t-1" "t"] by metis
      also have "... = signal_of2 False \<theta> s (t- 1)"
        using `t- 1 < t`unfolding worldline_def by auto
      also have "... = signal_of2 False \<theta> s t"
        using signal_of2_less[OF `lookup \<theta> t = 0`] by auto
      also have "... = signal_of2 False \<theta> s k"
        by (metis \<open>\<forall>n\<ge>t. get_trans \<theta> n = 0\<close> \<open>t < k \<or> t = k\<close> order.strict_implies_order
        signal_of2_less_ind)
      finally have "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1) = signal_of2 False \<theta> s k"
        by auto
      hence "signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k = signal_of2 False \<theta> s k"
        using * ** *** by blast }
    moreover
    { assume "t = 0"
      have  "lookup (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) t = Map.empty"
        unfolding `t = 0` by transfer' auto
      hence "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s t =  False"
        using signal_of2_zero unfolding `t = 0` by (metis zero_option_def)
      also have "... = signal_of2 False \<theta> s 0"
        using `lookup \<theta> t = 0` unfolding `t = 0` using signal_of2_zero by (metis zero_fun_def)
      also have "... = signal_of2 False \<theta> s k"
        by (metis \<open>\<forall>n\<ge>t. get_trans \<theta> n = 0\<close> \<open>t < k \<or> t = k\<close> \<open>t = 0\<close> le0 signal_of2_less_ind)
      finally have "signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s t = signal_of2 False \<theta> s k"
        by auto
      hence "signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k = signal_of2 False \<theta> s k"
        using * ** by auto }
    ultimately have "signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k = signal_of2 False \<theta> s k"
      by auto }
  ultimately show "signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k = signal_of2 False \<theta> s k"
    by auto
qed

lemma event_worldline2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "{s. (Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>) s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. (Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>) s ta)) 0 t) s (t - 1)} = \<gamma>"
  using assms state_worldline2[OF ci_implies_ci_weaker[OF assms]]
proof transfer'
  fix t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau>
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assume *: "(\<lambda>s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s t) = \<sigma>"
  have **: "\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
    using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
  have "{s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)} =
        {s. \<sigma> s \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)}"
    using * by (metis comp_apply snd_conv)
  moreover have "\<And>s. signal_of2 False \<theta> s (t - 1) =
            signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)"
    using history_worldline2[OF ci_implies_ci_weaker[OF \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close>]] by transfer' auto
  ultimately have "{s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. worldline t \<sigma> \<theta> \<tau> s ta)) 0 t) s (t - 1)} =
                   {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
    by auto
  thus " {s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s t \<noteq> signal_of2 False (poly_mapping_of_fun (\<lambda>ta. Some \<circ> (\<lambda>s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s ta)) 0 t) s (t - 1)} = \<gamma>"
    using ** by auto
qed

lemma event_worldline2':
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "{s. (Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>) s t \<noteq> signal_of2 False  (derivative_hist_raw ((Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>)) t) s (t - 1)} = \<gamma>"
  using assms state_worldline2[OF ci_implies_ci_weaker[OF assms]]
proof transfer'
  fix t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau>
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assume *: "(\<lambda>s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s t) = \<sigma>"
  have **: "\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
    using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
  have "{s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1)} =
        {s. \<sigma> s \<noteq> signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1)}"
    using * by (metis comp_apply snd_conv)
  moreover have "\<And>s. signal_of2 False \<theta> s (t - 1) =
                      signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1)"
    using hist_of_worldline[OF ci_implies_ci_weaker[OF \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>\<close>]]  by transfer' auto
  ultimately have "{s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1)} =
                   {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}"
    by auto
  thus "{s. ((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>) s t \<noteq> signal_of2 False (derivative_hist_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s (t - 1)} = \<gamma>"
    using ** by auto
qed

lemma transaction_worldline2:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  shows "\<And>k s . signal_of2 (\<sigma> s) (derivative_raw ((Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>)) ((worldline_deg o snd) (worldline2 t \<sigma> \<theta> \<tau>)) t) s k =
                signal_of2 (\<sigma> s) \<tau> s k"
  using assms unfolding worldline_deg_def
proof transfer'
  fix k s t \<sigma>
  fix \<gamma> :: "'a event"
  fix \<theta> \<tau> :: "'a transaction"
  assume "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  define deg where "deg = (LEAST n. \<forall>ta>n. \<forall>s. worldline t \<sigma> \<theta> \<tau> s ta = worldline t \<sigma> \<theta> \<tau> s n)"
  have deg_prop: "\<forall>ta > deg. \<forall>s. worldline t \<sigma> \<theta> \<tau> s ta = worldline t \<sigma> \<theta> \<tau> s deg"
    using LeastI_ex[OF exists_quiesce_worldline[OF `context_invariant_weaker t \<sigma> \<theta> \<tau>`]] unfolding deg_def
    by blast
  have "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0" and sdom: "(\<And>s. s \<in> dom (get_trans \<tau> t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau> t s))"
    using `context_invariant_weaker t \<sigma> \<theta> \<tau>` unfolding context_invariant_weaker_def by auto
  have "worldline t \<sigma> \<theta> \<tau> s t = signal_of2 (\<sigma> s) \<tau> s t"
    unfolding worldline_def by auto
  have "lookup \<tau> t s = 0 \<or> lookup \<tau> t s \<noteq> 0" by auto
  moreover
  { assume "lookup \<tau> t s = 0"
    hence "\<And>n. n \<le> t \<Longrightarrow> lookup \<tau> n s = 0"
      using `\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0` le_neq_implies_less  by (metis zero_fun_def)
    hence "signal_of2 (\<sigma> s) \<tau> s t = signal_of2 (\<sigma> s) \<tau> s 0"
      by (metis neq0_conv signal_of2_less_ind')
    also have "... = \<sigma> s"
      using `\<And>n. n \<le> t \<Longrightarrow> lookup \<tau> n s = 0` by (metis le0 signal_of2_zero)
    finally have "signal_of2 (\<sigma> s) \<tau> s t = \<sigma> s"
      by auto
    hence "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
      using `worldline t \<sigma> \<theta> \<tau> s t = signal_of2 (\<sigma> s) \<tau> s t` by auto }
  moreover
  { assume "lookup \<tau> t s \<noteq> 0"
    hence "s \<in> dom (lookup \<tau> t)"
      by (transfer', simp add: dom_def zero_option_def)
    hence "Some (\<sigma> s) = lookup \<tau> t s"
      using sdom by auto
    hence "signal_of2 (\<sigma> s) \<tau> s t = \<sigma> s"
      using lookup_some_signal_of2' by metis
    hence "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
      using `worldline t \<sigma> \<theta> \<tau> s t = signal_of2 (\<sigma> s) \<tau> s t` by auto }
  ultimately have "worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s"
    by auto
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
          using `context_invariant_weaker t \<sigma> \<theta> \<tau>` unfolding context_invariant_weaker_def using `k < t`
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
      using signal_of2_derivative_raw `worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s` by metis
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
        using signal_of2_derivative_raw2[OF _ order.strict_implies_order[OF `deg < k`]]
        `worldline t \<sigma> \<theta> \<tau> s t = \<sigma> s` by metis
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
        by (simp add: derivative_raw_zero)
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
              using `context_invariant_weaker t \<sigma> \<theta> \<tau>` unfolding context_invariant_weaker_def using `k < t`
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
            using calculation state_worldline2[OF `context_invariant_weaker t \<sigma> \<theta> \<tau>`]
            by (transfer', metis fun.map_ident snd_conv)
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
  thus "signal_of2 (\<sigma> s) (derivative_raw (((\<lambda>x. x) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) (((\<lambda>w. LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) \<circ> snd) (t, worldline t \<sigma> \<theta> \<tau>)) t) s k =
        signal_of2 (\<sigma> s) \<tau> s k"
    unfolding deg_def by auto
qed

text \<open>The following definition is an attempt to define a condition such that the derivative @{term
"derivative_raw"} and @{term "derivative_hist_raw"} are the inverses of the integral (@{term
"signal_of2"}). The predicate non-stuttering below indicates that, in each signal, there are no two
successive posting which has the same value. For example, if @{term "t1"} and @{term "t2"} are
elements of @{term "keys (to_transaction2 \<tau> sig)"}, then the value of posted at @{term "t1"} and
@{term "t2"} are different. That is, @{term "the (lookup (to_transaction2 \<tau> sig) t1) \<noteq>
the (lookup (to_transaction2 \<tau> sig) t2)"}.

We must pay a special attention for the first key
@{term "k = hd (sorted_list_of_set (keys ((\<tau> :: 'a transaction2) s)))"}. The first key must be
different from the default state @{term "\<sigma> s"}.\<close>

definition non_stuttering :: "'signal transaction2 \<Rightarrow> 'signal state \<Rightarrow> 'signal \<Rightarrow> bool" where
  "non_stuttering \<tau> \<sigma> s = (let ks = sorted_list_of_set (keys (\<tau> s)) in
                        (\<forall>i. Suc i < length ks \<longrightarrow> lookup (\<tau> s) (ks ! i) \<noteq> lookup (\<tau> s) (ks ! Suc i)) \<and> (ks \<noteq> [] \<longrightarrow> \<sigma> s \<noteq> the (lookup (\<tau> s) (ks ! 0))))"

lemma hd_of_keys:
  fixes \<tau> :: "'signal transaction2"
  fixes s :: "'signal"
  assumes "\<And>n. n < t \<Longrightarrow> lookup (\<tau> s) n = 0"
  assumes "lookup (\<tau> s) t \<noteq> None"
  defines "ks \<equiv> sorted_list_of_set (keys (\<tau> s))"
  shows "ks ! 0 = t"
proof (rule ccontr)
  have "sorted ks"
    unfolding ks_def by auto
  have "t \<in> keys (\<tau> s)"
    using `lookup (\<tau> s) t \<noteq> None` apply transfer' unfolding to_trans_raw2_def by (simp add: zero_option_def)
  hence "t \<in> set ks" and "ks \<noteq> []"
    unfolding ks_def by auto
  have *: "\<And>k. k \<in> keys (\<tau> s) \<Longrightarrow> t \<le> k"
    using assms(1) by (metis in_keys_iff le_less_linear)
  assume "ks ! 0 \<noteq> t"
  then obtain t' where "ks ! 0 = t'" and "t' \<noteq> t" using `ks \<noteq> []` by auto
  hence "t' \<in> keys (\<tau> s)"
    unfolding ks_def by (metis \<open>ks \<noteq> []\<close> \<open>t \<in> set ks\<close> ks_def length_pos_if_in_set nth_mem
    sorted_list_of_set(1) sorted_list_of_set.infinite)
  hence "t < t'"
    using * `t' \<noteq> t`  using nat_less_le by blast
  have "t' \<in> set ks"
    using `ks ! 0 = t'`  using \<open>ks \<noteq> []\<close> by auto
  with `t \<in> set ks` and `t < t'` obtain i j :: nat where "i < 0" and "ks ! i = t" and "ks ! 0 = t'"
    using `ks ! 0 = t'` by (metis \<open>sorted ks\<close> in_set_conv_nth leD leI sorted_iff_nth_mono)
  thus False by auto
qed

lemma no_mapping_at_t_if_non_stuttering:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  shows "lookup \<tau> t s = 0"
proof (rule ccontr)
  assume "lookup \<tau> t s \<noteq> 0"
  then obtain val where "lookup (to_transaction2 \<tau> s) t = Some val"
    apply transfer' unfolding to_trans_raw2_def using zero_option_def by fastforce
  moreover have "\<And>s. s \<in> dom (lookup \<tau> t) \<Longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
    using assms(1) unfolding context_invariant_weaker_def by auto
  ultimately have "val = \<sigma> s"
    apply transfer' unfolding to_trans_raw2_def by (simp add: domI)
  have "t \<in> keys (to_transaction2 \<tau> s)"
    using `lookup (to_transaction2 \<tau> s) t = Some val`
    by (metis lookup_not_eq_zero_eq_in_keys option.distinct(1) zero_fun_def zero_map)
  define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
  hence "sorted ks"
    by auto
  have "ks \<noteq> []"
    using `t \<in> keys (to_transaction2 \<tau> s)` unfolding ks_def by auto
  have "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
    using assms(1) unfolding context_invariant_weaker_def by auto
  hence "\<And>n. n < t \<Longrightarrow> lookup (to_transaction2 \<tau> s) n = 0"
    apply transfer' unfolding to_trans_raw2_def  by (simp add: zero_fun_def)
  have "ks ! 0 = t"
    using hd_of_keys [where \<tau>= "to_transaction2 \<tau>", OF `\<And>n. n < t \<Longrightarrow> lookup (to_transaction2 \<tau> s) n = 0`]
    `lookup (to_transaction2 \<tau> s) t = Some val` unfolding ks_def by auto
  hence "the (lookup (to_transaction2 \<tau> s) (ks ! 0)) = \<sigma> s"
    using `val = \<sigma> s` `lookup (to_transaction2 \<tau> s) t = Some val` by auto
  thus False
    using assms(2) `ks \<noteq> []` unfolding non_stuttering_def ks_def Let_def by blast
qed

lemma no_mapping_at_t_if_non_stuttering2:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  shows "lookup \<tau> t = 0"
proof -
  have "\<forall>s. lookup \<tau> t s = 0"
    using no_mapping_at_t_if_non_stuttering[OF assms(1)] assms(2) by fastforce
  thus ?thesis
    apply transfer' by (transfer', auto simp add: zero_fun_def)
qed

lemma two_successive_keys_diff_value:
  fixes \<tau> :: "'a transaction2"
  assumes "non_stuttering \<tau> \<sigma> s"
  assumes "t1 \<in> keys (\<tau> s)" and "t2 \<in> keys (\<tau> s)"
  defines "v1 \<equiv> the (lookup (\<tau> s) t1)"
  defines "v2 \<equiv> the (lookup (\<tau> s) t2)"
  assumes "\<forall>n>t1. n < t2 \<longrightarrow> lookup (\<tau> s) n = 0"
  assumes "t1 < t2"
  shows "v1 \<noteq> v2"
proof -
  define ks where "ks = sorted_list_of_set (keys (\<tau> s))"
  have "ks \<noteq> []" and "sorted ks" and "distinct ks"
    using `t1 \<in> keys (\<tau> s)` unfolding ks_def by auto
  obtain idx1 where "ks ! idx1 = t1" and "idx1 < length ks"
    using `t1 \<in> keys (\<tau> s)` unfolding ks_def
    by (metis finite_keys in_set_conv_nth set_sorted_list_of_set)
  have "idx1 + 1 < length ks"
  proof (rule ccontr)
    assume "\<not> idx1 + 1 < length ks"
    hence " length ks \<le> idx1 + 1"
      by auto
    with `idx1 < length ks` have "idx1 + 1 = length ks"
      by auto
    hence "last ks = t1"
      using `ks ! idx1 = t1` by (metis \<open>ks \<noteq> []\<close> add_diff_cancel_right' last_conv_nth)
    hence "\<forall>n > t1. n \<notin> set ks"
      using `sorted ks` `distinct ks` by (metis Suc_eq_plus1 \<open>idx1 + 1 = length ks\<close> \<open>idx1 < length ks\<close>
      \<open>ks ! idx1 = t1\<close> in_set_conv_nth leD less_Suc_eq_le sorted_nth_mono)
    hence "t2 \<notin> set ks"
      using `t1 < t2` by auto
    with `t2 \<in> keys (\<tau> s)` show False
      unfolding ks_def  by auto
  qed
  have "ks ! (idx1 + 1) = t2"
  proof (rule ccontr)
    assume "ks ! (idx1 + 1) \<noteq> t2"
    hence "ks ! (idx1 + 1) < t2 \<or> ks ! (idx1 + 1) > t2" by auto
    moreover
    { assume "ks ! (idx1 + 1) < t2"
      have "ks ! idx1 \<le> ks ! (idx1 + 1)"
        using `sorted ks` `idx1 + 1 < length ks` unfolding sorted_iff_nth_mono_less
        by auto
      hence "ks ! idx1 < ks ! (idx1 + 1)"
        using `distinct ks` by (metis Suc_eq_plus1 Suc_n_not_n \<open>idx1 + 1 < length ks\<close> \<open>idx1 < length ks\<close>
        distinct_conv_nth dual_order.strict_iff_order)
      have "ks ! (idx1 + 1) \<in> set ks"
        using `idx1 + 1 < length ks` nth_mem by blast
      hence "lookup (\<tau> s) (ks ! (idx1 + 1)) \<noteq> 0"
        unfolding ks_def by auto
      moreover have "lookup (\<tau> s) (ks ! (idx1 + 1)) = 0"
        using `ks ! idx1 < ks ! (idx1 + 1)` `ks ! idx1 = t1` `ks ! (idx1 + 1) < t2` assms(6)
        by auto
      ultimately have False by auto }
    moreover
    { assume "ks ! (idx1 + 1) > t2"
      then obtain idx where "idx \<le> idx1" and "ks ! idx = t2"
        using `t2 \<in> keys (\<tau> s)` `sorted ks` `distinct ks` unfolding ks_def
        by (metis \<open>ks \<noteq> []\<close> discrete in_set_conv_nth ks_def not_le set_sorted_list_of_set
        sorted_list_of_set.infinite sorted_nth_mono)
      moreover hence "idx \<noteq> idx1"
        using `ks ! idx1 = t1` `t1 < t2` by auto
      ultimately have "idx < idx1"
        by auto
      hence False
        using `ks ! idx = t2` `ks ! idx1 = t1` `t1 < t2` `sorted ks` `idx1 < length ks`
        by (meson not_le sorted_iff_nth_mono_less) }
    ultimately show False by auto
  qed
  thus ?thesis
    using assms ks_def `idx1 + 1 < length ks` unfolding non_stuttering_def
    by (smt One_nat_def \<open>ks ! idx1 = t1\<close> add.right_neutral add_Suc_right
    lookup_not_eq_zero_eq_in_keys option.expand zero_option_def)
qed


lemma derivative_raw_of_worldline_specific:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  defines "w \<equiv> worldline t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  defines "d \<equiv> (LEAST n. \<forall>k>n. \<forall>s. w s k = w s n)"
  assumes "t \<le> d"
  shows "derivative_raw w (LEAST n. \<forall>k>n. \<forall>s. w s k = w s n) t = \<tau>"
proof (intro poly_mapping_eqI)
  fix k
  have "lookup \<tau> t = 0"
    using no_mapping_at_t_if_non_stuttering2[OF _ assms(3)] assms(1) ci_implies_ci_weaker by blast
  have "k \<le> t \<or> t < k \<and> k \<le> d \<or> t < k \<and> d < k"
    using `t \<le> d` by auto
  moreover
  { assume "k \<le> t"
    hence "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = 0"
      unfolding d_def by (transfer', auto simp add: zero_fun_def zero_option_def)
    also have "... = lookup \<tau> k"
      using assms(1) `k \<le> t` unfolding context_invariant_weaker_def
      by (metis \<open>get_trans \<tau> t = 0\<close> order.not_eq_order_implies_strict)
    finally have "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = lookup \<tau> k"
      by auto }
  moreover
  { assume "t < k \<and> k \<le> d"
    hence "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = difference_raw w k"
      unfolding d_def apply transfer' by auto
    also have "... = lookup \<tau> k"
    proof (rule ext)
      fix s
      have "w s k \<noteq> w s (k - 1) \<or> w s k = w s (k - 1)"
        by auto
      moreover
      { assume "w s k \<noteq> w s (k - 1)"
        hence "signal_of2 (\<sigma> s) \<tau> s k \<noteq> signal_of2 (\<sigma> s) \<tau> s (k - 1)"
          unfolding w_def worldline_def using `t < k \<and> k \<le> d` by auto
        have lnone: "lookup (to_transaction2 \<tau> s) k \<noteq> 0"
        proof (rule ccontr)
          assume "\<not> lookup (to_transaction2 \<tau> s) k \<noteq> 0"
          hence "lookup (to_transaction2 \<tau> s) k = 0"
            by auto
          hence "lookup \<tau> k s = 0"
            apply transfer' unfolding to_trans_raw2_def by auto
          hence "signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau> s (k - 1)"
            by (intro signal_of2_less_sig)
          with `signal_of2 (\<sigma> s) \<tau> s k \<noteq> signal_of2 (\<sigma> s) \<tau> s (k - 1)` show False
            by auto
        qed
        then obtain val where "lookup (to_transaction2 \<tau> s) k = Some val"
          by (metis not_None_eq zero_fun_def zero_map)
        hence "get_trans \<tau> k s = Some val"
          by (transfer', auto simp add: to_trans_raw2_def)
        hence inf: "inf_time (to_transaction2 \<tau>) s k = Some k"
          by (auto intro!: lookup_some_inf_time'[where \<sigma>="(\<lambda>x. False)(s := val)"])
        have "difference_raw w k s = Some (w s k)"
          unfolding difference_raw_def using `w s k \<noteq> w s (k - 1)`
          using \<open>t < k \<and> k \<le> d\<close> by auto
        also have "... = lookup (to_transaction2 \<tau> s) k"
          unfolding w_def worldline_def using `t < k \<and> k \<le> d` unfolding to_signal2_def comp_def
          using inf \<open>lookup (to_transaction2 \<tau> s) k = Some val\<close> by auto
        also have "... = lookup \<tau> k s"
          by (transfer', auto simp add: to_trans_raw2_def)
        finally have "difference_raw w k s = get_trans \<tau> k s"
          by auto }
      moreover
      { assume "w s k = w s (k - 1)"
        hence sig_same: "signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau> s (k - 1)"
          unfolding w_def worldline_def using `t < k \<and> k \<le> d` by auto
        have lnone: "lookup (to_transaction2 \<tau> s) k = None"
        proof (rule ccontr)
          assume "lookup (to_transaction2 \<tau> s) k \<noteq> None"
          then obtain val where "lookup (to_transaction2 \<tau> s) k = Some val"
            by blast
          hence "get_trans \<tau> k s = Some val"
            by (transfer', auto simp add: to_trans_raw2_def)
          hence "inf_time (to_transaction2 \<tau>) s k = Some k"
            by (auto intro!: lookup_some_inf_time'[where \<sigma>="(\<lambda>x. False)(s := val)"])
          hence "signal_of2 (\<sigma> s) \<tau> s k = val"
            unfolding to_signal2_def comp_def by (simp add: \<open>lookup (to_transaction2 \<tau> s) k = Some val\<close>)
          with sig_same have "signal_of2 (\<sigma> s) \<tau> s (k - 1) = val"
            by auto
          from signal_of2_elim[OF this]
          have "(\<exists>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = Some val) \<or>
                (\<forall>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = None \<and> val = \<sigma> s)" by auto
          moreover
          { assume "(\<exists>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = Some val)"
            then obtain m where "inf_time (to_transaction2 \<tau>) s (k-1) = Some m" and "lookup (to_transaction2 \<tau> s) m = Some val"
              using `signal_of2 (\<sigma> s) \<tau> s (k - 1) = val` unfolding to_signal2_def comp_def
              using inf_time_noneE_iff
              by (smt domIff inf_time_neq_t_choice inf_time_someE2 option.case_eq_if option.discI option.expand option.sel)
            define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
            then obtain idx_m where "ks ! idx_m = m" and "idx_m < length ks"
              using `inf_time (to_transaction2 \<tau>) s (k - 1) = Some m`
              by (metis in_set_conv_nth inf_key_in_list inf_time_def)
            have "m \<le> k - 1"
              using inf_time_at_most[OF `inf_time (to_transaction2 \<tau>) s (k-1) = Some m`] by auto
            have "k \<in> set ks"
              using inf_key_in_list `inf_time (to_transaction2 \<tau>) s k = Some k`
              by (metis inf_time_def ks_def)
            then obtain idx where "ks ! idx = k" and "idx < length ks"
              by (meson in_set_conv_nth)
            have "idx_m < idx"
            proof (rule ccontr)
              assume "\<not> idx_m < idx" hence "idx \<le> idx_m" by auto
              have "sorted ks" and "distinct ks"
                unfolding ks_def by auto
              hence "ks ! idx \<le> ks ! idx_m"
                using `idx_m < length ks` sorted_iff_nth_mono `idx \<le> idx_m` by auto
              hence "k \<le> m"
                using `ks ! idx = k` and `ks ! idx_m = m` by auto
              with `m \<le> k - 1` show False using \<open>t < k \<and> k \<le> d\<close> by linarith
            qed
            moreover have "idx \<le> idx_m + 1"
            proof (rule ccontr)
              assume "\<not> idx \<le> idx_m + 1" hence "idx_m + 1 < idx" by auto
              moreover have "sorted ks" and "distinct ks"
                unfolding ks_def by auto
              ultimately have "ks ! (idx_m + 1) \<le> ks ! idx"
                using `idx < length ks` sorted_iff_nth_mono_less by auto
              hence "ks ! (idx_m + 1) < ks ! idx"
                using `idx_m + 1 < idx` `distinct ks` by (metis \<open>idx < length ks\<close>
                le_neq_implies_less less_not_refl2 nth_eq_iff_index_eq order.strict_trans)
              also have "... = k"
                using `ks ! idx = k` by auto
              finally have "ks ! (idx_m + 1) < k" by auto
              have "set (sorted_list_of_set (keys (to_transaction2 \<tau> s))) =  dom (lookup (to_transaction2 \<tau> s))"
                unfolding set_keys_dom_lookup by auto
              moreover have "idx_m + 1 < length ks"
                using `idx_m + 1 < idx` `idx < length ks` by auto
              ultimately have "ks ! (idx_m + 1) \<in> dom (lookup (to_transaction2 \<tau> s))"
                unfolding ks_def using nth_mem[where n = "idx_m + 1"] by blast
              hence "ks ! (idx_m + 1) \<le> m"
                using inf_time_someE[OF `inf_time (to_transaction2 \<tau>) s (k - 1) = Some m`]
                `ks ! (idx_m + 1) < k` by auto
              with `ks ! idx_m = m` show "False"
                using distinct_sorted_list_of_set sorted_sorted_list_of_set
                unfolding ks_def  by (metis \<open>idx_m + 1 < length ks\<close> add_lessD1 antisym_conv1 ks_def
                leD less_add_one nth_eq_iff_index_eq order.strict_implies_not_eq sorted_iff_nth_mono_less)
              qed
            ultimately have "idx = idx_m + 1"
              by auto
            with assms(3) have "lookup (to_transaction2 \<tau> s) m \<noteq>  lookup (to_transaction2 \<tau> s) k"
              unfolding non_stuttering_def using `idx < length ks` `ks ! idx = k` `ks ! idx_m = m`
              by (metis Suc_eq_plus1 ks_def)
            hence "Some val \<noteq> Some val"
              using `lookup (to_transaction2 \<tau> s) m = Some val` `get_trans \<tau> k s = Some val`
              by (transfer', auto simp add: to_trans_raw2_def)
            hence "False" by auto }
          moreover
          { assume "(\<forall>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = None \<and> val = \<sigma> s)"
            hence "\<And>m. m < k \<Longrightarrow> lookup (to_transaction2 \<tau> s) m = 0" and "val = \<sigma> s"
              by (auto simp add: zero_option_def)
            define ks  where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
            hence "ks ! 0 = k"
              using hd_of_keys[where \<tau>="to_transaction2 \<tau>" and s="s", OF
              `\<And>m. m < k \<Longrightarrow> lookup (to_transaction2 \<tau> s) m = 0` `lookup (to_transaction2 \<tau> s) k \<noteq> None`]
              by auto
            with `lookup (to_transaction2 \<tau> s) k = Some val` have "the (lookup (to_transaction2 \<tau> s) (ks ! 0)) = \<sigma> s"
              using `val = \<sigma> s` by auto
            moreover have "ks \<noteq> []"
            proof -
              have "k \<in> keys (to_transaction2 \<tau> s)"
                using `lookup (to_transaction2 \<tau> s) k \<noteq> None`  by (simp add: in_keys_iff zero_option_def)
              thus ?thesis
                unfolding ks_def by auto
            qed
            ultimately  have "False"
              using assms(3) unfolding non_stuttering_def ks_def Let_def by auto }
          ultimately show False by auto
        qed
        hence "difference_raw w k s = get_trans \<tau> k s"
          unfolding difference_raw_def using `w s k = w s (k - 1)` `t < k \<and> k \<le> d`
          by (transfer', auto simp add:to_trans_raw2_def) }
      ultimately show "difference_raw w k s = get_trans \<tau> k s"
        by auto
    qed
    finally have "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = lookup \<tau> k"
      by auto }
  moreover
  { assume "t < k \<and> d < k"
    hence "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = 0"
      unfolding d_def by (transfer', auto simp add: zero_fun_def zero_option_def)
    also have "... = lookup \<tau> k"
    proof (rule ext)
      fix s
      have *: "\<exists>n. \<forall>t>n. \<forall>s. w s t = w s n"
        using exists_quiesce_worldline[OF assms(1)] unfolding assms(2) by auto
      have **: "\<forall>k'\<ge> d. w s k' = w s d"
        using `t < k \<and> d < k` unfolding d_def using LeastI_ex[OF *]  using antisym_conv2 by blast
      have sig_same: "\<And>k'. d \<le> k' \<Longrightarrow> signal_of2 (\<sigma> s) \<tau> s k' = signal_of2 (\<sigma> s) \<tau> s d"
          using ** `t \<le> d` unfolding w_def worldline_def  by (meson dual_order.trans leD)
      have "lookup (to_transaction2 \<tau> s) k = None"
      proof (rule ccontr)
        assume "lookup (to_transaction2 \<tau> s) k \<noteq> None"
        then obtain val where "lookup (to_transaction2 \<tau> s) k = Some val"
          by blast
        hence "get_trans \<tau> k s = Some val"
          by (transfer', auto simp add: to_trans_raw2_def)
        hence "inf_time (to_transaction2 \<tau>) s k = Some k"
          by (auto intro!: lookup_some_inf_time'[where \<sigma>="(\<lambda>x. False)(s := val)"])
        hence "signal_of2 (\<sigma> s) \<tau> s k = val"
          unfolding to_signal2_def comp_def by (simp add: \<open>lookup (to_transaction2 \<tau> s) k = Some val\<close>)
        with sig_same have "signal_of2 (\<sigma> s) \<tau> s (k - 1) = val"
          by (metis \<open>t < k \<and> d < k\<close> diff_Suc_1 le_add1 less_imp_Suc_add nat_le_linear not_le)
        from signal_of2_elim[OF this]
        have "(\<exists>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = Some val) \<or>
              (\<forall>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = None \<and> val = \<sigma> s)" by auto
        moreover
        { assume "(\<exists>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = Some val)"
          then obtain m where "inf_time (to_transaction2 \<tau>) s (k-1) = Some m" and "lookup (to_transaction2 \<tau> s) m = Some val"
            using `signal_of2 (\<sigma> s) \<tau> s (k - 1) = val` unfolding to_signal2_def comp_def
            using inf_time_noneE_iff
            by (smt domIff inf_time_neq_t_choice inf_time_someE2 option.case_eq_if option.discI option.expand option.sel)
          define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
          then obtain idx_m where "ks ! idx_m = m" and "idx_m < length ks"
            using `inf_time (to_transaction2 \<tau>) s (k - 1) = Some m`
            by (metis in_set_conv_nth inf_key_in_list inf_time_def)
          have "m \<le> k - 1"
            using inf_time_at_most[OF `inf_time (to_transaction2 \<tau>) s (k-1) = Some m`] by auto
          have "k \<in> set ks"
            using inf_key_in_list `inf_time (to_transaction2 \<tau>) s k = Some k`
            by (metis inf_time_def ks_def)
          then obtain idx where "ks ! idx = k" and "idx < length ks"
            by (meson in_set_conv_nth)
          have "idx_m < idx"
          proof (rule ccontr)
            assume "\<not> idx_m < idx" hence "idx \<le> idx_m" by auto
            have "sorted ks" and "distinct ks"
              unfolding ks_def by auto
            hence "ks ! idx \<le> ks ! idx_m"
              using `idx_m < length ks` sorted_iff_nth_mono `idx \<le> idx_m` by auto
            hence "k \<le> m"
              using `ks ! idx = k` and `ks ! idx_m = m` by auto
            with `m \<le> k - 1` show False using \<open>t < k \<and> d < k\<close> by linarith
          qed
          moreover have "idx \<le> idx_m + 1"
          proof (rule ccontr)
            assume "\<not> idx \<le> idx_m + 1" hence "idx_m + 1 < idx" by auto
            moreover have "sorted ks" and "distinct ks"
              unfolding ks_def by auto
            ultimately have "ks ! (idx_m + 1) \<le> ks ! idx"
              using `idx < length ks` sorted_iff_nth_mono_less by auto
            hence "ks ! (idx_m + 1) < ks ! idx"
              using `idx_m + 1 < idx` `distinct ks` by (metis \<open>idx < length ks\<close>
              le_neq_implies_less less_not_refl2 nth_eq_iff_index_eq order.strict_trans)
            also have "... = k"
              using `ks ! idx = k` by auto
            finally have "ks ! (idx_m + 1) < k" by auto
            have "set (sorted_list_of_set (keys (to_transaction2 \<tau> s))) =  dom (lookup (to_transaction2 \<tau> s))"
              unfolding set_keys_dom_lookup by auto
            moreover have "idx_m + 1 < length ks"
              using `idx_m + 1 < idx` `idx < length ks` by auto
            ultimately have "ks ! (idx_m + 1) \<in> dom (lookup (to_transaction2 \<tau> s))"
              unfolding ks_def using nth_mem[where n = "idx_m + 1"] by blast
            hence "ks ! (idx_m + 1) \<le> m"
              using inf_time_someE[OF `inf_time (to_transaction2 \<tau>) s (k - 1) = Some m`]
              `ks ! (idx_m + 1) < k` by auto
            with `ks ! idx_m = m` show "False"
              using distinct_sorted_list_of_set sorted_sorted_list_of_set
              unfolding ks_def  by (metis \<open>idx_m + 1 < length ks\<close> add_lessD1 antisym_conv1 ks_def
              leD less_add_one nth_eq_iff_index_eq order.strict_implies_not_eq sorted_iff_nth_mono_less)
          qed
          ultimately have "idx = idx_m + 1"
            by auto
          with assms(3) have "lookup (to_transaction2 \<tau> s) m \<noteq>  lookup (to_transaction2 \<tau> s) k"
            unfolding non_stuttering_def using `idx < length ks` `ks ! idx = k` `ks ! idx_m = m`
            by (metis Suc_eq_plus1 ks_def)
          hence "Some val \<noteq> Some val"
            using `lookup (to_transaction2 \<tau> s) m = Some val` `get_trans \<tau> k s = Some val`
            by (transfer', auto simp add: to_trans_raw2_def)
          hence "False" by auto }
          moreover
          { assume "(\<forall>m\<le>k - 1. lookup (to_transaction2 \<tau> s) m = None \<and> val = \<sigma> s)"
            hence "\<And>m. m < k \<Longrightarrow> lookup (to_transaction2 \<tau> s) m = 0" and "val = \<sigma> s"
              by (auto simp add: zero_option_def)
            define ks  where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
            hence "ks ! 0 = k"
              using hd_of_keys[where \<tau>="to_transaction2 \<tau>" and s="s", OF
              `\<And>m. m < k \<Longrightarrow> lookup (to_transaction2 \<tau> s) m = 0` `lookup (to_transaction2 \<tau> s) k \<noteq> None`]
              by auto
            with `lookup (to_transaction2 \<tau> s) k = Some val` have "the (lookup (to_transaction2 \<tau> s) (ks ! 0)) = \<sigma> s"
              using `val = \<sigma> s` by auto
            moreover have "ks \<noteq> []"
            proof -
              have "k \<in> keys (to_transaction2 \<tau> s)"
                by (simp add: \<open>lookup (to_transaction2 \<tau> s) k \<noteq> None\<close> in_keys_iff zero_option_def)
              thus ?thesis
                unfolding ks_def by auto
            qed
            ultimately  have "False"
              using assms(3) unfolding non_stuttering_def ks_def Let_def by auto }
          ultimately show False by auto
      qed
      thus "0 s = get_trans \<tau> k s"
        apply transfer' unfolding to_trans_raw2_def zero_fun_def zero_option_def by auto
    qed
    finally have "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = lookup \<tau> k"
      by auto }
  ultimately show "lookup (derivative_raw w (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n) t) k = lookup \<tau> k"
    by auto
qed

lemma current_sig_and_prev_same:
  assumes "signal_of2 def \<theta> s k = signal_of2 def \<theta> s (k - 1)"
  assumes "0 < k"
  assumes "non_stuttering (to_transaction2 \<theta>) state s"
  assumes "state s = def"
  shows "lookup \<theta> k s = 0"
proof (rule ccontr)
  assume "lookup \<theta> k s \<noteq> 0"
  then obtain val where "lookup \<theta> k s = Some val"
    by (metis not_None_eq zero_fun_def zero_map)
  hence "signal_of2 def \<theta> s k = val"
    using lookup_some_signal_of2'[of "\<theta>" "k" "s" "def_state(s := val)" "def"] by auto
  have "the (lookup (to_transaction2 \<theta> s) k) = val"
    using `lookup \<theta> k s = Some val` by (transfer', auto simp add: to_trans_raw2_def)
  have "k \<in> dom (lookup (to_transaction2 \<theta> s))"
    using `lookup \<theta> k s = Some val`
    by (transfer', auto simp add: to_trans_raw2_def)
  hence "k \<in> keys (to_transaction2 \<theta> s)"
    by (transfer', auto simp add:to_trans_raw2_def zero_option_def)
  define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<theta> s))"
  obtain k' where "inf_time (to_transaction2 \<theta>) s (k - 1) = None \<or> inf_time (to_transaction2 \<theta>) s (k - 1) = Some k'"
    using option.exhaust_sel by blast
  moreover
  { assume inf_none: "inf_time (to_transaction2 \<theta>) s (k - 1) = None"
    hence noneE: "\<forall>t\<in>dom (lookup (to_transaction2 \<theta> s)). (k - 1) < t"
      by (auto dest!: inf_time_noneE)
    have *: "\<forall>n. n < k \<longrightarrow> lookup (to_transaction2 \<theta> s) n = 0"
    proof (rule ccontr)
      assume "\<not> (\<forall>n. n < k \<longrightarrow> lookup (to_transaction2 \<theta> s) n = 0)"
      then obtain n where "n < k" and "lookup (to_transaction2 \<theta> s) n \<noteq> 0"
        by auto
      hence "n \<in> dom (lookup (to_transaction2 \<theta> s))"
        by (simp add: domIff zero_option_def)
      hence "k - 1 < n" using noneE by auto
      with `n < k` show False by auto
    qed
    have "signal_of2 def \<theta> s (k - 1) = def"
      using inf_none unfolding to_signal2_def comp_def by auto
    have "ks ! 0 = k" unfolding ks_def
    proof (rule hd_of_keys)
      show "\<And>n. n < k \<Longrightarrow> lookup (to_transaction2 \<theta> s) n = 0"
        using * by auto
    next
      show "lookup (to_transaction2 \<theta> s) k \<noteq> None"
        using `lookup \<theta> k s \<noteq> 0` unfolding zero_option_def
        by transfer' (auto simp add: to_trans_raw2_def)
    qed
    have "k \<in> keys (to_transaction2 \<theta> s)"
      using `lookup \<theta> k s = Some val`   \<open>signal_of2 def \<theta> s (k - 1) = def\<close>
      \<open>signal_of2 def \<theta> s k = signal_of2 def \<theta> s (k - 1)\<close> inf_none inf_time_less
      lookup_some_inf_time' by fastforce
    hence "ks \<noteq> []"
      unfolding ks_def by auto
    moreover have "the (lookup (to_transaction2 \<theta> s) (ks ! 0)) = val"
      unfolding `ks ! 0 = k` using `lookup \<theta> k s = Some val`
      by transfer' (auto simp add: to_trans_raw2_def)
    ultimately have "val \<noteq> def"
      using assms(3-4) unfolding non_stuttering_def ks_def by auto
    hence "signal_of2 def \<theta> s k \<noteq> signal_of2 def \<theta> s (k - 1)"
      using `signal_of2 def \<theta> s k = val` `signal_of2 def \<theta> s (k - 1) = def`
      by auto
    with `signal_of2 def \<theta> s k = signal_of2 def \<theta> s (k - 1)` have "False" by auto }
  moreover
  { assume inf_some: "inf_time (to_transaction2 \<theta>) s (k - 1) = Some k'"
    have "\<forall>t\<in>dom (lookup (to_transaction2 \<theta> s)). t \<le> k-1 \<longrightarrow> t \<le> k'"
      using inf_time_someE[OF inf_some] by auto
    hence "\<forall>n>k'. n < k \<longrightarrow> lookup (to_transaction2 \<theta> s) n = None"
      by (metis diff_Suc_1 domIff le_add1 less_imp_Suc_add not_le)
    have "k' < k"
      using inf_time_at_most[OF inf_some] \<open>0 < k\<close> by linarith
    have "k' \<in> dom (lookup (to_transaction2 \<theta> s))"
      using inf_time_someE2[OF inf_some] by auto
    hence "k' \<in> keys (to_transaction2 \<theta> s)"
      by (transfer', auto simp add: to_trans_raw2_def zero_option_def)
    obtain val' where "lookup (to_transaction2 \<theta> s) k' = Some val'"
      using `k' \<in> dom (lookup (to_transaction2 \<theta> s))` by auto
    hence "the (lookup (to_transaction2 \<theta> s) k') = val'"
      by (transfer', auto simp add: to_trans_raw2_def)
    hence "val \<noteq> val'"
      using two_successive_keys_diff_value[OF `non_stuttering (to_transaction2 \<theta>) state s`
      `k' \<in> keys (to_transaction2 \<theta> s)` `k \<in> keys (to_transaction2 \<theta> s)` _ `k' < k`]
      `\<forall>n>k'. n < k \<longrightarrow> lookup (to_transaction2 \<theta> s) n = None` `the (lookup (to_transaction2 \<theta> s) k) = val`
      unfolding zero_option_def by auto
    hence "signal_of2 def \<theta> s (k - 1) = val'"
      using inf_some `the (lookup (to_transaction2 \<theta> s) k') = val'`
      unfolding to_signal2_def comp_def by auto
    with `signal_of2 def \<theta> s k = val` have "False"
      using `val \<noteq> val'` `signal_of2 def \<theta> s k = signal_of2 def \<theta> s (k - 1)` by auto }
  ultimately show False by auto
qed

text \<open>Here is an important result. In case that the history @{term "\<theta> :: 'a transaction"} is
non-stuttering, the derivative raw of the worldline @{term "w = worldline t \<sigma> \<theta> \<tau>"} is exactly the
history @{term "\<theta>"}.\<close>

lemma derivative_is_history:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  defines "w \<equiv> worldline t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<theta>) def_state s"
  shows "derivative_hist_raw w t = \<theta>"
proof (intro poly_mapping_eqI)
  fix k
  have *: "\<forall>n\<ge>t. lookup \<theta> n = 0"
    using assms(1) unfolding context_invariant_weaker_def by auto
  have "k = 0 \<or> 0 < k \<and> k < t \<or> t < k \<or> t = k"
    by auto
  moreover
  { assume "t < k"
    hence "lookup (derivative_raw w t 0) k = Map.empty"
      apply transfer' by auto
    also have "... = lookup \<theta> k"
      using * `t < k` apply transfer' unfolding zero_fun_def zero_option_def by auto
    finally have "lookup (derivative_hist_raw w t) k = lookup \<theta> k"
      using `t < k` by transfer' auto }
  moreover
  { assume "0 < k \<and> k < t"
    hence "lookup (derivative_raw w t 0) k = difference_raw w k"
      apply transfer' by auto
    also have "... = lookup \<theta> k"
      unfolding difference_raw_def
    proof (rule ext)
      fix s
      have "non_stuttering (to_transaction2 \<theta>) def_state s"
        using assms(3) by auto
      have "w s k = w s (k - 1) \<or> w s k \<noteq> w s (k - 1)"
        by auto
      moreover
      { assume "w s k = w s (k - 1)"
        have "signal_of2 False \<theta> s k = signal_of2 False \<theta> s (k - 1)"
          using `0 < k \<and> k < t` `w s k = w s (k - 1)` unfolding w_def worldline_def by auto
        have "lookup \<theta> k s = 0"
          using current_sig_and_prev_same \<open>0 < k \<and> k < t\<close> \<open>non_stuttering (to_transaction2 \<theta>)
          def_state s\<close> \<open>signal_of2 False \<theta> s k = signal_of2 False \<theta> s (k - 1)\<close> by fastforce
        hence "(if w s k \<noteq> w s (k - 1) then Some (w s k) else None) = get_trans \<theta> k s"
          using `w s k = w s (k-1)` by (auto simp add: zero_option_def) }
      moreover
      { assume "w s k \<noteq> w s (k - 1)"
        have "signal_of2 False \<theta> s k \<noteq> signal_of2 False \<theta> s (k - 1)"
          using `0 < k \<and> k < t` `w s k \<noteq> w s (k - 1)` unfolding w_def worldline_def by auto
        hence "lookup \<theta> k s \<noteq> 0"
          using signal_of2_less_sig  by fastforce
        have "the (lookup \<theta> k s) = signal_of2 False \<theta> s k "
          using lookup_some_signal_of2'
          by (metis \<open>get_trans \<theta> k s \<noteq> 0\<close> \<open>non_stuttering (to_transaction2 \<theta>) def_state s\<close>
          option.exhaust_sel zero_option_def)
        also have "... = w s k"
          unfolding w_def worldline_def using `0 < k \<and> k < t` by auto
        finally have "(if w s k \<noteq> w s (k - 1) then Some (w s k) else None) = get_trans \<theta> k s"
          using `w s k \<noteq> w s (k - 1)`  by (smt \<open>get_trans \<theta> k s \<noteq> 0\<close> option.collapse zero_option_def) }
      ultimately show "(if k = 0 then \<lambda>s. if w s k then Some True else None else (\<lambda>s. if w s k \<noteq> w s (k - 1) then Some (w s k) else None)) s = get_trans \<theta> k s"
        using `0 < k \<and> k < t` by auto
    qed
    finally have "lookup (derivative_hist_raw w t) k = lookup \<theta> k"
      using `0 < k \<and> k < t` by transfer' auto }
  moreover
  { assume "t = k"
    hence "lookup \<theta> k = 0"
      using * by auto
    hence "lookup (derivative_hist_raw w t) k = lookup \<theta> k"
      using `t = k` by transfer' (auto simp add: zero_map) }
  moreover
  { assume "k = 0"
    have "t = 0 \<or> 0 < t" by auto
    moreover
    { assume "t = 0"
      hence "get_trans (derivative_hist_raw w t) k = get_trans \<theta> k"
        using * apply transfer' by (auto simp add: zero_map) }
    moreover
    { assume "0 < t"
      hence "lookup (derivative_hist_raw w t) k = difference_raw w 0"
        unfolding `k = 0` apply transfer' by auto
      also have "... = lookup \<theta> 0"
      proof (rule ext)
        fix s
        have "non_stuttering (to_transaction2 \<theta>) def_state s"
          using assms(3) by auto
        define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<theta> s))"
        obtain val where "lookup \<theta> 0 s = None \<or> lookup \<theta> 0 s = Some val"
          by (meson not_None_eq)
        moreover
        { assume "lookup \<theta> 0 s = None"
          have "w s 0 = signal_of2 False \<theta> s 0"
            unfolding w_def worldline_def using `0 < t` by auto
          also have "... = False"
            using `lookup \<theta> 0 s = None` signal_of2_empty by (metis signal_of2_zero zero_option_def)
          finally have "w s 0 = False"
            by auto
          hence "difference_raw w 0 s = None"
            unfolding difference_raw_def by auto
          also have "... = lookup \<theta> 0 s"
            using `lookup \<theta> 0 s = None` by auto
          finally have "difference_raw w 0 s = lookup \<theta> 0 s"
            by auto }
        moreover
        { assume "lookup \<theta> 0 s = Some val"
          hence "lookup (to_transaction2 \<theta> s) 0 \<noteq> None"
            by transfer' (auto simp add: to_trans_raw2_def)
          hence "ks ! 0 = 0"
            using hd_of_keys[of "0" "to_transaction2 \<theta>" "s"] unfolding ks_def by auto
          have "0 \<in> keys (to_transaction2 \<theta> s)"
            using `lookup \<theta> 0 s = Some val`
            by (simp add: \<open>lookup (to_transaction2 \<theta> s) 0 \<noteq> None\<close> in_keys_iff zero_option_def)
          hence "ks \<noteq> []"
            unfolding ks_def by auto
          hence "val = True"
            using `non_stuttering (to_transaction2 \<theta>) def_state s` ks_def `ks ! 0 = 0`
            unfolding non_stuttering_def by (metis \<open>get_trans \<theta> 0 s = Some val\<close> option.sel
            to_trans_raw2_def to_transaction2.rep_eq)
          hence "w s 0 = signal_of2 False \<theta> s 0"
            unfolding w_def worldline_def using `0 < t` by auto
          also have "... = True"
            using `lookup \<theta> 0 s = Some val` unfolding `val = True`  using lookup_some_signal_of2'
            by fastforce
          finally have "w s 0 = True"
            by auto
          hence "difference_raw w 0 s = Some True"
            unfolding difference_raw_def by auto
          also have "... = lookup \<theta> 0 s"
            using `lookup \<theta> 0 s = Some val` unfolding `val = True` by auto
          finally have "difference_raw w 0 s = lookup \<theta> 0 s"
            by auto }
        ultimately show "difference_raw w 0 s = lookup \<theta> 0 s"
          by auto
      qed
      finally have "lookup (derivative_hist_raw w t) k = lookup \<theta> k"
        unfolding `k = 0` by auto }
    ultimately have "lookup (derivative_hist_raw w t) k = lookup \<theta> k"
      by auto }
  ultimately show "lookup (derivative_hist_raw w t) k = lookup \<theta> k"
    by auto
qed

lemma curr_time_lt_deg:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  defines "w \<equiv> worldline t \<sigma> \<theta> \<tau>"
  assumes "\<tau> \<noteq> 0"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  defines "d \<equiv> (LEAST n. \<forall>t>n. \<forall>s. w s t = w s n)"
  shows "t < d"
proof -
  have "lookup \<tau> t = 0"
    using no_mapping_at_t_if_non_stuttering2[OF _ assms(4)]
    using assms(1) ci_implies_ci_weaker by blast
  moreover have "\<forall>n < t. lookup \<tau> n = 0"
    using assms(1) unfolding context_invariant_weaker_def by auto
  ultimately have "\<forall>n \<le> t. lookup \<tau> n = 0"
    by (simp add: le_less)
  have "\<exists>t'>t. lookup \<tau> t' \<noteq> 0 \<and> (\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0)"
  proof -
    obtain t' where "lookup \<tau> t' \<noteq> 0" and "t' > t"
      using `\<tau> \<noteq> 0` `\<forall>n \<le> t. lookup \<tau> n = 0`  by (meson aux leI)
    have "(\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0) \<or> \<not> (\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0)"
      by auto
    moreover
    { assume "(\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0)"
      hence ?thesis
        using `lookup \<tau> t' \<noteq> 0` and `t' > t` by auto }
    moreover
    { assume "\<not> (\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0)"
      hence ?thesis
      proof (induction t')
        case 0
        then show ?case by auto
      next
        case (Suc t)
        then show ?case using less_Suc_eq by blast
      qed }
    ultimately show ?thesis by auto
  qed
  then obtain t' where "lookup \<tau> t' \<noteq> 0" and "t' > t" and "\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0"
    by auto
  then obtain m where "lookup \<tau> t' = m" and "m \<noteq> Map.empty"
    by (simp add: zero_option_def zero_fun_def)
  then obtain s val where "lookup \<tau> t' s = Some val"
    by (meson not_None_eq)
  hence the_lookup: "the (lookup (to_transaction2 \<tau> s) t') = val"
    by (transfer', auto simp add: to_trans_raw2_def)
  have "val \<noteq> \<sigma> s"
  proof -
    define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
    have "t' \<in> keys (to_transaction2 \<tau> s)"
      using `lookup \<tau> t' s = Some val` by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
    hence "ks \<noteq> []"
      unfolding ks_def by auto
    have "ks ! 0 = t'"
      unfolding ks_def
    proof(auto intro!: hd_of_keys)
      show "\<And>n. n < t' \<Longrightarrow> lookup (to_transaction2 \<tau> s) n = 0"
        using `\<forall>n \<le> t. lookup \<tau> n = 0` `\<forall>n > t. n < t' \<longrightarrow> lookup \<tau> n = 0`
        by (transfer', metis not_less to_trans_raw2_def zero_fun_def)
    next
      show "\<exists>y. lookup (to_transaction2 \<tau> s) t' = Some y"
        using `lookup \<tau> t' s = Some val` by (transfer', auto simp add: to_trans_raw2_def)
    qed
    thus ?thesis
      using assms(4) the_lookup `ks \<noteq> []`
      unfolding non_stuttering_def Let_def ks_def by auto
  qed
  have "signal_of2 (\<sigma> s) \<tau> s t' = val"
    using lookup_some_signal_of2'[where \<sigma>="(\<lambda>x. _)(s := val)"] `lookup \<tau> t' s = Some val` by auto
  have "signal_of2 (\<sigma> s) \<tau> s (t' - 1) = signal_of2 (\<sigma> s) \<tau> s t"
    using signal_of2_less_ind[OF _ `t < t'`] `\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0`
    by (smt \<open>t < t'\<close> diff_Suc_1 less_Suc_eq_le less_imp_Suc_add not_le not_less_iff_gr_or_eq signal_of2_less_ind)
  also have "... = \<sigma> s"
  proof (cases "t = 0")
    case True
    then show ?thesis
      using `lookup \<tau> t = 0` signal_of2_zero by (metis zero_fun_def)
  next
    case False
    hence "signal_of2 (\<sigma> s) \<tau> s t = signal_of2 (\<sigma> s) \<tau> s 0"
      using signal_of2_less_ind `\<forall>n < t. lookup \<tau> n = 0`
      by (metis \<open>\<forall>n\<le>t. get_trans \<tau> n = 0\<close> diff_is_0_eq' diff_le_self le_antisym not_less)
    also have "... = \<sigma> s"
      using signal_of2_zero `\<forall>n < t. lookup \<tau> n = 0` False
      by (metis \<open>\<forall>n\<le>t. get_trans \<tau> n = 0\<close> le0 zero_fun_def)
    finally show ?thesis
      by auto
  qed
  finally have "signal_of2 (\<sigma> s) \<tau> s (t' - 1) = \<sigma> s"
    by auto
  hence "signal_of2 (\<sigma> s) \<tau> s t' \<noteq> signal_of2 (\<sigma> s) \<tau> s (t'-1)"
    using `val \<noteq> \<sigma> s` `signal_of2 (\<sigma> s) \<tau> s t' = val` by metis
  hence " w s t' \<noteq> w s (t' - 1)"
    unfolding w_def worldline_def using `t' > t` by auto
  have "t' \<le> d"
  proof (rule ccontr)
    assume "\<not> t' \<le> d"
    hence "d < t'"
      by auto
    have *: "\<exists>n. \<forall>k>n. \<forall>s. w s k = w s n"
      using exists_quiesce_worldline[OF assms(1)] w_def by auto
    have "\<forall>k>d. \<forall>s. w s k = w s d"
      using LeastI_ex[OF *] unfolding d_def  by blast
    hence "\<forall>s. w s t' = w s d"
      using `d < t'` by auto
    have "d = t' - 1 \<or> d < t' - 1"
      using `d < t'` by auto
    moreover
    { assume "d = t' - 1"
      hence "w s t' \<noteq> w s d"
        using `w s t' \<noteq> w s (t' - 1)` by auto
      with `\<forall>s. w s t' = w s d` have "False"
        by auto }
    moreover
    { assume "d < t' - 1"
      hence "w s (t' - 1) = w s d"
        using `\<forall>k>d. \<forall>s. w s k = w s d` by auto
      also have "... = w s t'"
        using `\<forall>s. w s t' = w s d` by auto
      finally have "w s t' = w s (t' - 1)"
        by auto
      with `w s t' \<noteq> w s (t' - 1)` have "False" by auto }
    ultimately show False by auto
  qed
  with `t < t'` show "t < d" by auto
qed

text \<open>Similar to @{thm "derivative_is_history"}, the derivative of a worldline constructed by the
constructor @{term "worldline t \<sigma> \<theta> \<tau>"} is exactly the transaction @{term "\<tau>"} provided that the
transaction @{term "\<tau>"} is non-stuttering with respect to the initial state @{term "\<sigma> :: 'a
state"}.\<close>

lemma derivative_raw_of_worldline:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  defines "w \<equiv> worldline t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  defines "d \<equiv> (LEAST n. \<forall>k>n. \<forall>s. w s k = w s n)"
  shows "derivative_raw w (LEAST n. \<forall>k>n. \<forall>s. w s k = w s n) t = \<tau>"
proof (cases "\<tau> = 0")
  case True
  have "d \<le> t"
    using empty_transaction_deg_lt_t[OF True assms(1)] unfolding d_def w_def by auto
  have "derivative_raw w (LEAST n. \<forall>k>n. \<forall>s. w s k = w s n) t = 0"
    using derivative_raw_zero `d \<le>t`  unfolding d_def by auto
  then show ?thesis
    using True by auto
next
  case False
  with curr_time_lt_deg have "t < d"
    using assms by auto
  with derivative_raw_of_worldline_specific show ?thesis
    using assms nat_less_le by blast
qed

lemma derivative_raw_of_worldline2:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  shows "derivative_raw ((Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>)) ((worldline_deg o snd) (worldline2 t \<sigma> \<theta> \<tau>)) t = \<tau>"
proof -
  have "derivative_raw (worldline t \<sigma> \<theta> \<tau>) (LEAST n. \<forall>ta>n. \<forall>s. (worldline t \<sigma> \<theta> \<tau>) s ta = (worldline t \<sigma> \<theta> \<tau>) s n) t = \<tau>"
    using derivative_raw_of_worldline[OF assms(1-2)]  by auto
  thus ?thesis
    unfolding worldline_deg_def apply transfer' by auto
qed

lemma derivative_is_history2:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<theta>) def_state s"
  shows "derivative_hist_raw ((Rep_worldline o snd) (worldline2 t \<sigma> \<theta> \<tau>)) t = \<theta>"
proof -
  have "derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t = \<theta>"
    using derivative_is_history[OF assms(1-2)] by auto
  thus ?thesis
    by transfer' auto
qed

lemma preempted_trans_sub_keys:
  assumes "lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)"
  assumes "keys (to_transaction2 \<tau>' sig) \<noteq> {}"
  defines "ks'\<equiv> (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
  defines "ks \<equiv> (sorted_list_of_set (keys (to_transaction2 \<tau>  sig)))"
  shows "ks' = take (length ks') ks"
proof -
  have "\<And>n. n < t + dly \<Longrightarrow> lookup (to_transaction2 \<tau>' sig) n = lookup (to_transaction2 \<tau> sig) n"
    using `lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)`
    by (transfer', auto simp add : to_trans_raw2_def preempt_nonstrict_def)
  hence "takeWhile (\<lambda>n. n < t + dly) (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) =
         takeWhile (\<lambda>n. n < t + dly) (sorted_list_of_set (keys (to_transaction2 \<tau>  sig)))"
    using takeWhile_lookup_same_strict by blast
  moreover have "takeWhile (\<lambda>n. n < t + dly) (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) =
                 (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
  proof (rule takeWhile_last_strict )
    obtain las where las_def: "las = last (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
      using assms(2) by auto
    show "last (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly"
    proof (rule ccontr)
      assume "\<not> last (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly"
      hence "t + dly \<le> las"
        unfolding las_def by auto
      have "las \<in> keys (to_transaction2 \<tau>' sig)"
        unfolding las_def by (metis finite_keys_to_transaction2 assms(2) last_in_set
        list.set(1) set_sorted_list_of_set)
      hence "lookup (to_transaction2 \<tau>' sig) las \<noteq> 0"
        by (transfer', auto simp add: to_trans_raw2_def)
      moreover have "lookup (to_transaction2 \<tau>' sig) las = 0"
        using `lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)` `t + dly \<le> las`
        by (transfer', auto simp add:zero_option_def to_trans_raw2_def preempt_nonstrict_def)
      ultimately show "False" by auto
    qed
  qed (auto simp add: assms(2))
  moreover have "takeWhile (\<lambda>n. n < t + dly) (sorted_list_of_set (keys (to_transaction2 \<tau>  sig))) =
                             take (length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))) (sorted_list_of_set (keys (to_transaction2 \<tau>  sig)))"
  proof (rule takeWhile_eq_take_P_nth)
    fix idx
    assume idx_less: "idx < length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
    assume idx_less': "idx < length (sorted_list_of_set (keys (to_transaction2 \<tau> sig)))"
    show "sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! idx < t + dly"
    proof (rule ccontr)
      assume "\<not> sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! idx < t + dly"
      hence "sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! idx \<ge> t + dly"
        by auto
      let ?k = "sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! idx"
      have "lookup (to_transaction2 \<tau>' sig) ?k = 0"
        using `lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)` `?k \<ge> t + dly`
        apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def by (auto simp add:zero_option_def)
      hence "?k \<notin> dom (lookup (to_transaction2 \<tau>' sig))"
        apply transfer' by (auto simp add: to_trans_raw2_def zero_option_def)
      hence "?k \<notin> set (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
        unfolding set_keys_dom_lookup by auto
      hence "\<forall>i < length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))).
                         (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) ! i \<noteq> ?k"
        using in_set_conv_nth  by metis
      with idx_less show False
        using calculation(1) calculation(2) takeWhile_nth by auto
    qed
  next
    assume len_le_len: " length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < length (sorted_list_of_set (keys (to_transaction2 \<tau> sig)))"
    show "\<not> sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly"
    proof (rule ccontr)
      assume "\<not> \<not> sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly"
      hence "sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly"
        by auto
      let ?k = "sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
      have "lookup (to_transaction2 \<tau> sig) ?k \<noteq> 0"
        apply transfer' unfolding to_trans_raw2_def using \<open>sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly\<close>
        calculation(1) calculation(2) len_le_len nth_length_takeWhile by auto
      hence "?k \<in> dom (lookup (to_transaction2 \<tau> sig))"
        apply transfer' by (auto simp add: to_trans_raw2_def zero_option_def)
      with `?k < t + dly` have "?k \<in> dom (lookup (to_transaction2 \<tau>' sig))"
        using `lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)` apply transfer'
        unfolding preempt_nonstrict_def to_trans_raw2_def  by (simp add: domIff)
      hence "?k \<in> set (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
        unfolding set_keys_dom_lookup by auto
      hence "?k < length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
        by (metis calculation(1) calculation(2) len_le_len nth_length_takeWhile set_takeWhileD)
      thus False
        using \<open>\<not> \<not> sorted_list_of_set (keys (to_transaction2 \<tau> sig)) ! length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) < t + dly\<close>
        calculation(1) calculation(2) len_le_len nth_length_takeWhile by auto
    qed
  qed
  ultimately show ?thesis
    unfolding ks'_def ks_def by auto
qed

lemma trans_post_raw_sub_keys:
  assumes "lookup \<tau>' = trans_post_raw sig val (lookup \<tau>) t"
  defines "ks'\<equiv> (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))"
  defines "ks \<equiv> (sorted_list_of_set (keys (to_transaction2 \<tau>  sig)))"
  shows "ks' = take (length ks' - 1) ks @ [t]"
proof -
  have "\<And>n. n < t  \<Longrightarrow> lookup (to_transaction2 \<tau>' sig) n = lookup (to_transaction2 \<tau> sig) n"
    using assms(1)  by (transfer', auto simp add : to_trans_raw2_def trans_post_raw_def)
  hence takeWhile_eq: "takeWhile (\<lambda>n. n < t) ks' =  takeWhile (\<lambda>n. n < t) ks"
    unfolding ks_def ks'_def using takeWhile_lookup_same_strict by blast
  have "t \<in> keys (to_transaction2 \<tau>' sig)"
    using assms(1) by (transfer', auto simp add:zero_option_def trans_post_raw_def to_trans_raw2_def)
  hence "t \<in> set ks'"
    unfolding ks'_def set_keys_dom_lookup
    by (transfer', auto simp add: zero_fun_def zero_option_def to_trans_raw2_def)
  have "\<forall>k \<in> keys (to_transaction2 \<tau>' sig). k \<le> t"
  proof (rule ccontr)
    assume "\<not> (\<forall>k\<in>keys (to_transaction2 \<tau>' sig). k \<le> t)"
    then obtain k where "k \<in> keys (to_transaction2 \<tau>' sig)" and "t < k"
      by auto
    hence "lookup (to_transaction2 \<tau>' sig) k \<noteq> 0"
      apply transfer' by (auto simp add: to_trans_raw2_def)
    moreover have "lookup (to_transaction2 \<tau>' sig) k = 0"
      using assms(1) `t < k` by (transfer', auto simp add: to_trans_raw2_def trans_post_raw_def zero_option_def)
    ultimately show False by auto
  qed
  hence at_most_t: "\<forall>k \<in> set ks'. k \<le> t"
    unfolding ks'_def set_keys_dom_lookup apply transfer' unfolding to_trans_raw2_def
    by (auto simp add: zero_fun_def zero_option_def)
  hence "last ks' = t"
    by (metis \<open>t \<in> set ks'\<close> assms(2) last.simps last_appendR last_in_set le_antisym
        length_greater_0_conv length_pos_if_in_set list.distinct(1) sorted.simps(2) sorted_append
        sorted_sorted_list_of_set split_list)
  hence "ks' = butlast ks' @ [t]"
    by (metis \<open>t \<in> set ks'\<close> append_butlast_last_id empty_iff empty_set)
  have "takeWhile (\<lambda>n. n \<noteq> last ks') ks' = takeWhile (\<lambda>n. n < t) ks'"
  proof (rule takeWhile_cong)
    fix x
    assume "x \<in> set ks'"
    hence "x \<le> t" using at_most_t by auto
    thus "(x \<noteq> last ks') = (x < t) "
      unfolding `last ks' = t` by auto
  qed (auto)
  have "distinct ks'"
    unfolding ks'_def by (auto)
  hence "takeWhile (\<lambda>n. n \<noteq> last ks') ks' = butlast ks'"
    using takeWhile_not_last by metis
  hence "takeWhile (\<lambda>n. n < t) ks' = butlast ks'"
    using `takeWhile (\<lambda>n. n \<noteq> last ks') ks' = takeWhile (\<lambda>n. n < t) ks'` by auto
  hence "ks' = takeWhile (\<lambda>n. n < t) ks @ [t]"
    using \<open>ks' = butlast ks' @ [t]\<close> takeWhile_eq by auto
  have "takeWhile (\<lambda>n. n < t) ks = take (length ks' - 1) ks"
    by (metis \<open>takeWhile (\<lambda>n. n < t) ks' = butlast ks'\<close> length_butlast takeWhile_eq takeWhile_eq_take)
  thus ?thesis
    using \<open>ks' = takeWhile (\<lambda>n. n < t) ks @ [t]\<close> by blast
qed

text \<open>Several lemmas about preserving non_stuttering property.\<close>

lemma trans_post_preserves_non_stuttering:
  assumes "non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "nonneg_delay cs"
  assumes "cs = Bassign_trans sig e dly"
  shows "non_stuttering (to_transaction2 \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bassign_trans sig e dly)
  hence \<tau>'_def: "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
    by auto
  have prev_zero: "\<And>n. n < t \<Longrightarrow> lookup (to_transaction2 \<tau> s) n = 0"
    using Bassign_trans(3) apply transfer' unfolding to_trans_raw2_def
    by (auto simp add: zero_fun_def zero_option_def)
  have "0 < dly"
    using Bassign_trans by auto
  have "sig \<noteq> s \<or> sig = s" by auto
  moreover
  { assume "sig \<noteq> s"
    hence "to_transaction2 \<tau>' s = to_transaction2 \<tau> s"
      using \<tau>'_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def preempt_nonstrict_def  by auto
    hence ?case
      using Bassign_trans(1) unfolding non_stuttering_def Let_def by auto }
  moreover
  { assume "sig = s"
    have "post_necessary_raw (dly-1) (lookup \<tau>) t sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)\<or>
          \<not> post_necessary_raw (dly-1) (lookup \<tau>) t sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)" by auto
    moreover
    { assume notnec: "\<not> post_necessary_raw (dly-1) (lookup \<tau>) t sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)"
      then obtain i where "(t \<le> i \<and> i \<le> t + (dly-1) \<and> lookup \<tau> i sig = Some (beval t \<sigma> \<gamma> \<theta> e) \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None))
                          \<or> (\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None) \<and>  beval t \<sigma> \<gamma> \<theta> e = \<sigma> sig"
        using post_necessary_raw_correctness[of "dly-1" "lookup \<tau>" "t" "sig" "beval t \<sigma> \<gamma> \<theta> e" "\<sigma> sig"]
        by auto
      moreover
      { assume "(t \<le> i \<and> i \<le> t + (dly-1) \<and> lookup \<tau> i sig = Some (beval t \<sigma> \<gamma> \<theta> e) \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None))"
        hence "t \<le> i" and "i \<le> t + (dly-1)" and "lookup \<tau> i sig = Some (beval t \<sigma> \<gamma> \<theta> e)" and "\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None"
          by auto
        have look: "lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)"
          using notnec unfolding \<tau>'_def apply transfer' by auto
        define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
        define ks' where "ks' = sorted_list_of_set (keys (to_transaction2 \<tau>' s))"
        have "keys (to_transaction2 \<tau>' s) \<subseteq> keys (to_transaction2 \<tau> s)"
          using `lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)` apply transfer'
          unfolding to_trans_raw2_def preempt_nonstrict_def by (auto simp add: zero_option_def)
        hence "length ks' \<le> length ks"
          unfolding ks'_def ks_def
          using \<open>sig = s\<close> look preempted_trans_sub_keys sorted_list_of_set_eq_Nil_iff by fastforce
        have "0 < dly"
          using `nonneg_delay (Bassign_trans sig e dly)` by auto
        hence keys_not_empty: "keys (to_transaction2 \<tau>' sig) \<noteq> {}"
          using `lookup \<tau> i sig = Some (beval t \<sigma> \<gamma> \<theta> e)` `t \<le> i` `i \<le> t + (dly-1)` `lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)`
          apply transfer' unfolding to_trans_raw2_def preempt_nonstrict_def zero_fun_def zero_option_def
          by (metis One_nat_def Suc_pred add_le_cancel_left domIff dom_def empty_iff le_add_diff_inverse le_imp_less_Suc not_le option.distinct(1))
        hence "0 < length ks'"
          unfolding ks'_def `sig = s` using sorted_list_of_set_eq_Nil_iff[of "keys (to_transaction2 \<tau>' s)"]
          finite_keys by auto
        have "(sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) =
              take (length (sorted_list_of_set (keys (to_transaction2 \<tau>' sig)))) (sorted_list_of_set (keys (to_transaction2 \<tau>  sig)))"
          using preempted_trans_sub_keys[OF look keys_not_empty] by auto
        then obtain ys where "(sorted_list_of_set (keys (to_transaction2 \<tau>' sig))) @ ys = (sorted_list_of_set (keys (to_transaction2 \<tau>  sig)))"
          using append_eq_conv_conj by blast
        hence "ks' @ ys = ks"
          unfolding ks'_def ks_def `sig = s` by auto
        have *: "\<And>idx. idx < length ks' \<Longrightarrow> ks' ! idx = ks ! idx"
          using `ks' @ ys = ks` by (metis nth_append)
        moreover have "\<And>idx. idx < length ks' \<Longrightarrow> ks' ! idx < t + dly"
        proof -
          fix idx
          assume "idx < length ks'"
          hence "ks' ! idx \<in> dom (lookup (to_transaction2 \<tau>' s))"
            unfolding ks'_def  by (metis \<open>idx < length ks'\<close> ks'_def nth_mem set_keys_dom_lookup)
          { assume "ks' ! idx \<ge> t + dly"
            hence "lookup (to_transaction2 \<tau>' s) (ks' ! idx) = 0"
              using look `sig = s`   by (transfer', auto simp add: preempt_nonstrict_def to_trans_raw2_def zero_option_def)
            hence "ks' ! idx \<notin> dom (lookup (to_transaction2 \<tau>' s))"
              by (transfer', auto simp add: to_trans_raw2_def zero_option_def)
            with `ks' ! idx \<in> dom (lookup (to_transaction2 \<tau>' s))` have False by auto }
          thus "ks' ! idx < t + dly"
            using not_le by blast
        qed
        ultimately have "\<And>idx. idx < length ks' \<Longrightarrow> ks ! idx < t + dly"
          by auto
        hence **: "\<And>idx. idx < length ks' \<Longrightarrow> lookup (to_transaction2 \<tau> s) (ks ! idx) =
                                           lookup (to_transaction2 \<tau>' s) (ks' ! idx)"
          using * look apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def using not_le
          by auto
        have ***: "(\<forall>i. Suc i < length ks \<longrightarrow> lookup (to_transaction2 \<tau> s) (ks ! i) \<noteq> lookup (to_transaction2 \<tau> s) (ks ! Suc i)) \<and> (ks \<noteq> [] \<longrightarrow> \<sigma> s \<noteq> the (lookup (to_transaction2 \<tau> s) (ks ! 0)))"
          using `non_stuttering (to_transaction2 \<tau>) \<sigma> s` unfolding non_stuttering_def Let_def ks_def
          by auto
        have "(\<forall>i. Suc i < length ks' \<longrightarrow> lookup (to_transaction2 \<tau>' s) (ks' ! i) \<noteq> lookup (to_transaction2 \<tau>' s) (ks' ! Suc i)) \<and> (ks' \<noteq> [] \<longrightarrow> \<sigma> s \<noteq> the (lookup (to_transaction2 \<tau>' s) (ks' ! 0)))"
        proof (rule, rule, rule)
          fix i
          assume "Suc i < length ks'"
          hence "lookup (to_transaction2 \<tau>' s) (ks' ! i) = lookup (to_transaction2 \<tau> s) (ks ! i)"
            using ** by auto
          moreover have "lookup (to_transaction2 \<tau>' s) (ks' ! Suc i) = lookup (to_transaction2 \<tau> s) (ks ! Suc i)"
            using ** `Suc i < length ks'` by auto
          ultimately show "lookup (to_transaction2 \<tau>' s) (ks' ! i) \<noteq> lookup (to_transaction2 \<tau>' s) (ks' ! Suc i)"
            using *** `Suc i < length ks'` `length ks' \<le> length ks` by auto
        next
          have "ks \<noteq> [] \<longrightarrow> \<sigma> s \<noteq> the (lookup (to_transaction2 \<tau> s) (ks ! 0))"
            using `non_stuttering (to_transaction2 \<tau>) \<sigma> s` unfolding non_stuttering_def Let_def ks_def by auto
          moreover have "lookup (to_transaction2 \<tau> s) (ks ! 0) = lookup (to_transaction2 \<tau>' s) (ks' ! 0)"
            using ** `0 < length ks'` by auto
          ultimately show " ks'\<noteq> [] \<longrightarrow> \<sigma> s \<noteq> the (lookup (to_transaction2 \<tau>' s) (ks' ! 0))"
            using \<open>ks' @ ys = ks\<close> by auto
        qed
        hence ?case
          unfolding non_stuttering_def ks'_def by auto }
      moreover
      { assume "(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None) \<and>  beval t \<sigma> \<gamma> \<theta> e = \<sigma> sig"
        hence "(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None)" and "beval t \<sigma> \<gamma> \<theta> e = \<sigma> sig"
          by auto
        have look: "lookup \<tau>' = preempt_nonstrict sig (lookup \<tau>) (t + dly)"
          using notnec unfolding \<tau>'_def apply transfer' by auto
        hence "lookup (to_transaction2 \<tau>' sig) = 0"
          using Bassign_trans(3) `(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None)` `0 < dly`
          apply transfer' unfolding to_trans_raw2_def preempt_nonstrict_def
          by (rule ext, metis (no_types, lifting) One_nat_def Suc_pred add_Suc_right fun_upd_same not_le not_less_eq_eq zero_map)
        hence "keys (to_transaction2 \<tau>' s) = {}"
          unfolding `sig = s`  by (simp add: aux zero_fun_def)
        hence ?case
          unfolding non_stuttering_def Let_def `sig = s` by auto }
      ultimately have ?case by auto }
    moreover
    { assume nec: "post_necessary_raw (dly-1) (lookup \<tau>) t sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig)"
      hence lookup: "lookup \<tau>' = trans_post_raw sig (beval t \<sigma> \<gamma> \<theta> e) (lookup \<tau>) (t + dly)"
        unfolding \<tau>'_def by transfer' auto
      have "\<not> (\<exists>i\<ge>t. i \<le> t + (dly-1) \<and> lookup \<tau> i sig = Some (beval t \<sigma> \<gamma> \<theta> e) \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> lookup \<tau> j sig = None))"
          and imp: "(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None) \<Longrightarrow> beval t \<sigma> \<gamma> \<theta> e \<noteq> \<sigma> sig"
        using nec post_necessary_raw_correctness[of "dly-1" "lookup \<tau>" "t" "sig" "beval t \<sigma> \<gamma> \<theta> e" "\<sigma> sig"]
        by auto
      hence ind: "\<forall>i\<ge>t. i \<le> t + (dly-1) \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> lookup \<tau> j sig = None) \<longrightarrow> lookup \<tau> i sig \<noteq> Some (beval t \<sigma> \<gamma> \<theta> e) "
        by auto
      hence "(\<exists>i \<ge> t. i \<le> t + (dly-1) \<and> lookup \<tau> i sig \<noteq> Some (beval t \<sigma> \<gamma> \<theta> e) \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> lookup \<tau> j sig = None))"
        by (meson dual_order.strict_trans1 le_add1 le_refl less_irrefl_nat)
      then obtain i where "t \<le> i" and "i \<le> t + (dly-1)" and "lookup \<tau> i sig \<noteq> Some (beval t \<sigma> \<gamma> \<theta> e)"
          and "(\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None)" by auto
      hence ?case
      proof (induction "i - t" arbitrary: i)
        case 0
        hence "i = t" by auto
        define ks where ks_def: "ks = sorted_list_of_set (keys (to_transaction2 \<tau> sig))"
        define ks' where ks'_def: "ks' = sorted_list_of_set (keys (to_transaction2 \<tau>' sig))"
        have "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
          using Bassign_trans(3) lookup  by (simp add: trans_post_raw_preserve_trans_removal)
        have "ks' = take (length ks' - 1) ks @ [t + dly]"
          using trans_post_raw_sub_keys[OF lookup] unfolding ks_def ks'_def by auto
        hence "\<And>idx. idx < length ks' - 1 \<Longrightarrow> ks' ! idx = ks ! idx"
          by (metis butlast_snoc length_butlast nth_butlast nth_take)
        obtain v where "lookup \<tau> i sig = None \<or> lookup \<tau> i sig = Some v" and "v \<noteq> beval t \<sigma> \<gamma> \<theta> e"
          using 0(4)  by fastforce
        moreover
        { assume "lookup \<tau> i sig = Some v"
          hence " lookup (to_transaction2 \<tau> s) t \<noteq> None"
            using `i = t` `sig = s` apply transfer' unfolding to_trans_raw2_def by auto
          hence " ks ! 0 = i"
            unfolding ks_def using hd_of_keys[of "t" "to_transaction2 \<tau>", OF prev_zero] `sig = s` `i = t`
            by auto
          have "(LEAST n. \<forall>t\<ge>n. lookup (to_transaction2 \<tau>' sig) t = 0) = t + dly + 1"
          proof (rule Least_equality)
            show "\<forall>ta\<ge>t + dly + 1. lookup (to_transaction2 \<tau>' sig) ta = 0"
              using lookup apply transfer' unfolding to_trans_raw2_def trans_post_raw_def
              by (auto simp add: zero_option_def)
          next
            { fix y
              assume "\<not> t + dly + 1 \<le> y " hence "y < t + dly + 1" by auto
              hence "t + dly \<ge> y" by auto
              have "lookup (to_transaction2 \<tau>' sig) (t + dly) \<noteq> 0"
                using lookup apply transfer' unfolding to_trans_raw2_def trans_post_raw_def
                by (auto simp add: zero_option_def)
              hence "\<exists>t\<ge>y. lookup (to_transaction2 \<tau>' sig) t \<noteq> 0"
                using `t + dly \<ge> y` by (auto intro!: exI[where x="t+dly"]) }
            thus "\<And>y. \<forall>t\<ge>y. lookup (to_transaction2 \<tau>' sig) t = 0 \<Longrightarrow> t + dly + 1 \<le> y"
              by auto
          qed
          hence "Poly_Mapping.degree (to_transaction2 \<tau>' sig) = t + dly + 1"
            unfolding poly_mapping_degree[THEN sym] by auto
          have "ks' = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [0..<Poly_Mapping.degree (to_transaction2 \<tau>' sig)]"
            unfolding ks'_def sorted_list_of_set_keys by auto
          also have "... = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [0 ..< t+dly+1]"
            using `Poly_Mapping.degree (to_transaction2 \<tau>' sig) = t + dly + 1` by auto
          also have "... = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [0 ..< i] @
                           filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i ..< t+dly+1]"
            by (metis \<open>i = t\<close> add.assoc filter_append le_add2 le_add_same_cancel2 upt_add_eq_append)
          also have "... = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i ..< t+dly+1]"
            unfolding append_self_conv2  filter_empty_conv `i = t` using \<open>\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0\<close>
            apply transfer' unfolding to_trans_raw2_def by (auto simp add: zero_fun_def zero_option_def)
          also have "... = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i] @
                           filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i+1 ..< t+dly+1]"
            by (metis One_nat_def \<open>i = t\<close> add.right_neutral add_Suc_right append_Cons diff_add_zero
            diff_is_0_eq filter_append le_imp_less_Suc self_append_conv2 upt_rec)
          also have "... = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i] @
                           filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i+1 ..< t+dly] @
                           filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [t+dly]"
            by (smt \<open>0 < dly\<close> \<open>i = t\<close> add.commute add_diff_cancel_left' filter_append le_eq_less_or_eq
            length_upt less_add_same_cancel1 list.size(3) list.size(4) plus_1_eq_Suc upt_Suc_append upt_rec)
          also have "... = filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i]  @
                           filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [t+dly]"
          proof -
            have "filter (\<lambda>k. k \<in> keys (to_transaction2 \<tau>' sig)) [i + 1..<t + dly] = []"
              unfolding filter_empty_conv using `(\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None)`
              lookup apply transfer' unfolding to_trans_raw2_def trans_post_raw_def
              by (auto simp add: zero_option_def)
            thus ?thesis by auto
          qed
          also have "... = [i, t+dly]"
          proof -
            have "i \<in> keys (to_transaction2 \<tau>' sig)"
              using `lookup \<tau> i sig = Some v` lookup  by (metis \<open>0 < dly\<close> \<open>i = t\<close>
              \<open>lookup (to_transaction2 \<tau> s) t \<noteq> None\<close> \<open>sig = s\<close> \<tau>'_def less_add_same_cancel1
              lookup_trans_post_less not_in_keys_iff_lookup_eq_zero zero_option_def)
            moreover have "t + dly \<in> keys (to_transaction2 \<tau>' sig)"
              using lookup by (metis One_nat_def Suc_eq_plus1 \<open>Poly_Mapping.degree (to_transaction2 \<tau>' sig) = t + dly + 1\<close>
              degree_greater_zero_in_keys diff_Suc_Suc minus_nat.diff_0 zero_less_Suc)
            ultimately show ?thesis
              by auto
          qed
          finally have "ks' = [i, t+dly]"
            by auto
          have "lookup (to_transaction2 \<tau>' sig) i \<noteq> lookup (to_transaction2 \<tau>' sig) (t+dly)"
            using `lookup \<tau> i sig = Some v` `v \<noteq> beval t \<sigma> \<gamma> \<theta> e` lookup `i = t` `0 < dly`
            by (transfer', auto simp add: to_trans_raw2_def trans_post_raw_def)
          hence po1: "\<forall>i. Suc i < length ks' \<longrightarrow> lookup (to_transaction2 \<tau>' sig) (ks' ! i) \<noteq> lookup (to_transaction2 \<tau>' sig) (ks' ! Suc i)"
            using `ks' = [i, t+dly]` by auto
          have "\<sigma> s \<noteq> the (lookup (to_transaction2 \<tau> sig) (ks ! 0))"
            using Bassign_trans  unfolding `ks ! 0 = i` non_stuttering_def Let_def ks_def `sig = s`
            using \<open>ks' = [i, t + dly]\<close> \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close> \<open>sig = s\<close> ks_def by auto
          moreover have "lookup (to_transaction2 \<tau> sig) t = lookup (to_transaction2 \<tau>' sig) t"
            by (simp add: \<open>0 < dly\<close> \<tau>'_def lookup_trans_post_less)
          ultimately have "\<sigma> s \<noteq> the (lookup (to_transaction2 \<tau>' sig) (ks' ! 0))"
            unfolding `ks ! 0 = i` `ks' = [i, t+dly]` using lookup `i = t` by auto
          with po1 have " non_stuttering (to_transaction2 \<tau>') \<sigma> s"
            unfolding non_stuttering_def Let_def ks'_def `sig = s` by auto }
        moreover
        { assume "lookup \<tau> i sig = None"
          hence "(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None)"
            using `(\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None)` `i = t`  le_neq_trans by blast
          with imp have "beval t \<sigma> \<gamma> \<theta> e \<noteq> \<sigma> sig"
            by auto
          have single: "to_transaction2 \<tau>' sig = Poly_Mapping.single (t + dly) (Some (beval t \<sigma> \<gamma> \<theta> e))"
            unfolding \<tau>'_def using nec Bassign_trans(3) `(\<forall>i\<ge>t. i \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> i sig = None)`
            apply transfer' unfolding to_trans_raw2_def when_def trans_post_raw_def zero_option_def
            by (rule ext, smt One_nat_def Suc_pred add.right_neutral add_Suc_right fun_upd_same le_add1
            le_add_same_cancel1 le_neq_trans not_le not_less_eq_eq zero_map)
          have "ks' = [t + dly]"
            unfolding ks'_def single keys_single zero_option_def by auto
          hence "lookup (to_transaction2 \<tau>' sig) (ks' ! 0) = Some (beval t \<sigma> \<gamma> \<theta> e)"
            using single by simp
          with `beval t \<sigma> \<gamma> \<theta> e \<noteq> \<sigma> sig` have "non_stuttering (to_transaction2 \<tau>') \<sigma> s"
            using `ks' = [t + dly]` unfolding ks'_def non_stuttering_def Let_def `sig = s`
            by simp }
        ultimately show ?case by auto
      next
        case (Suc x)
        hence "x = (i - 1) - t"
          by auto
        have "\<forall>j>i. j < t + dly \<longrightarrow> get_trans \<tau>' j sig = None"
          using Suc(6) lookup by (transfer', auto simp add: trans_post_raw_def)
        define ks where ks_def: "ks = sorted_list_of_set (keys (to_transaction2 \<tau> sig))"
        define ks' where ks'_def: "ks' = sorted_list_of_set (keys (to_transaction2 \<tau>' sig))"
        have "sorted ks'" and "distinct ks'"
          unfolding ks'_def by auto
        have "\<forall>i k. ks' ! i < k \<and> k < ks' ! (i+1) \<and> i+1 < length ks' \<longrightarrow> lookup (to_transaction2 \<tau>' sig) k = 0"
        proof (rule, rule, rule, rule ccontr)
          fix i k
          assume "ks' ! i < k \<and> k < ks' ! (i+1) \<and> i+1 < length ks'"
          hence "ks' ! i < k" and "k < ks' ! (i+1)" and "i+1 < length ks'" by auto
          assume "lookup (to_transaction2 \<tau>' sig) k \<noteq> 0"
          hence "k \<in> keys (to_transaction2 \<tau>' sig)"
            apply transfer' unfolding to_trans_raw2_def by auto
          then obtain idx where "ks' ! idx = k" and "idx < length ks'"
            by (metis finite_keys_to_transaction2 in_set_conv_nth ks'_def sorted_list_of_set(1))
          hence "i < idx"
            by (metis \<open>ks' ! i < k \<and> k < ks' ! (i + 1) \<and> i + 1 < length ks'\<close> \<open>sorted ks'\<close>
            add_lessD1 leD leI sorted_nth_mono)
          moreover have "idx < i + 1"
            by (metis \<open>idx < length ks'\<close> \<open>k < ks' ! (i + 1)\<close> \<open>ks' ! idx = k\<close> \<open>sorted ks'\<close> leD le_less_linear sorted_nth_mono)
          ultimately show "False"
            by linarith
        qed
        have "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
          using Bassign_trans(3) lookup  by (simp add: trans_post_raw_preserve_trans_removal)
        have "ks' = take (length ks' - 1) ks @ [t + dly]"
          using trans_post_raw_sub_keys[OF lookup] unfolding ks_def ks'_def by auto
        hence "\<And>idx. idx < length ks' - 1 \<Longrightarrow> ks' ! idx = ks ! idx"
          by (metis butlast_snoc length_butlast nth_butlast nth_take)
        have "length ks' - 1 \<le> length ks"
          using `ks' = take (length ks' - 1) ks @ [t + dly]` take_all by fastforce
        have "i - 1 \<le> t + (dly-1)"
          using `i \<le> t + (dly-1)` by auto
        have "t \<le> i - 1"
          using Suc.hyps(2) by linarith
        have "get_trans \<tau> i sig = None \<or> get_trans \<tau> i sig \<noteq> None"
          by auto
        moreover
        { assume "lookup \<tau> i sig = None"
          have "\<forall>j>(i-1). j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None"
            using `\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None` `lookup \<tau> i sig = None`
            by (metis add.right_neutral le_add_diff_inverse less_Suc_eq_le nat_neq_iff not_less
            plus_1_eq_Suc zero_le)
          hence "get_trans \<tau> (i-1) sig \<noteq> Some (beval t \<sigma> \<gamma> \<theta> e)"
            using ind `t\<le> i-1` `i-1 \<le>t+(dly-1)` by auto
          hence ?case
            using Suc(1)[OF `x = (i-1)-t` `t \<le>i-1` `i-1\<le>t+(dly-1)` _ `\<forall>j>(i-1). j \<le> t + (dly-1) \<longrightarrow> get_trans \<tau> j sig = None`]
            by auto }
        moreover
        { assume "get_trans \<tau> i sig \<noteq> None"
          then obtain v where "lookup \<tau> i sig = Some v" and "v \<noteq> (beval t \<sigma> \<gamma> \<theta> e)"
            using `get_trans \<tau> i sig \<noteq> Some (beval t \<sigma> \<gamma> \<theta> e)` by auto
          have "\<forall>i. Suc i < length ks \<longrightarrow> lookup (to_transaction2 \<tau> sig) (ks ! i) \<noteq> lookup (to_transaction2 \<tau> sig) (ks ! Suc i)"
            using Bassign_trans(1) unfolding non_stuttering_def Let_def ks_def `sig = s` by auto
          hence "\<forall>i. Suc i < length ks' - 1 \<longrightarrow> lookup (to_transaction2 \<tau> sig) (ks' ! i) \<noteq> lookup (to_transaction2 \<tau> sig) (ks' ! Suc i)"
            using `length ks' - 1 \<le> length ks`  order.strict_trans2 `\<And>idx. idx < length ks' - 1 \<Longrightarrow> ks' ! idx = ks ! idx`
            by auto
          moreover have "\<forall>i. i < length ks' - 1 \<longrightarrow> ks' ! i < t + dly"
            using `ks' = take (length ks' - 1) ks @ [t + dly]` `sorted ks'` `distinct ks'`
            by (metis Nil_is_append_conv One_nat_def Suc_pred butlast_snoc length_butlast sorted_iff_nth_mono_less
            length_greater_0_conv less_Suc_eq nat_less_le not_Cons_self2 nth_append_length nth_eq_iff_index_eq)
          moreover have "\<forall>k < t + dly. lookup (to_transaction2 \<tau> sig) k = lookup (to_transaction2 \<tau>' sig) k"
            using lookup apply transfer' unfolding trans_post_raw_def to_trans_raw2_def by auto
          ultimately have IH: "\<forall>i. Suc i < length ks' - 1 \<longrightarrow> lookup (to_transaction2 \<tau>' sig) (ks' ! i) \<noteq> lookup (to_transaction2 \<tau>' sig) (ks' ! Suc i)"
            by auto
          have "i < t + dly"
            using `i \<le> t + (dly-1)` `0 < dly` by auto
          hence "i \<in> keys (to_transaction2 \<tau>' sig)"
            using lookup `lookup \<tau> i sig = Some v`
            by (transfer', auto simp add: to_trans_raw2_def trans_post_raw_def zero_option_def)
          moreover have "t + dly \<in> keys (to_transaction2 \<tau>' sig)"
            using lookup apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
            by (auto simp add: zero_option_def)
          ultimately have "2 \<le> length ks'"
            unfolding ks'_def using `i < t + dly`  by (metis (no_types, hide_lams)
            Nil_is_append_conv Suc_eq_plus1 \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close> \<open>sig = s\<close>
            append_Nil append_eq_conv_conj butlast_snoc cancel_comm_monoid_add_class.diff_cancel
            in_set_conv_nth ks'_def le_imp_less_or_eq length_0_conv length_butlast  less_imp_not_less
            less_one list.distinct(1) list.size(3) not_less_eq_eq nth_append_length one_add_one
            semiring_normalization_rules(24) set_sorted_list_of_set sorted_list_of_set.infinite zero_less_iff_neq_zero)
          have "last ks' = t + dly"
            using `ks' = take (length ks' - 1) ks @ [t + dly]` last_snoc[of "take (length ks' - 1) ks" "t + dly"]
            by auto
          have "lookup (to_transaction2 \<tau>' sig) (t + dly) = Some (beval t \<sigma> \<gamma> \<theta> e)"
            using lookup apply transfer'  unfolding to_trans_raw2_def trans_post_raw_def by auto
          hence "lookup (to_transaction2 \<tau>' sig) (ks' ! (length ks' - 1)) = Some (beval t \<sigma> \<gamma> \<theta> e)"
            using `last ks' = t + dly`
            by (metis Nil_is_append_conv \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close> last_conv_nth not_Cons_self2)
          moreover have "ks' ! (length ks' - 2) = i"
          proof (rule ccontr)
            assume " ks' ! (length ks' - 2) \<noteq> i"
            hence "ks' ! (length ks' - 2) > i \<or> ks' ! (length ks' - 2) < i" by auto
            moreover
            { assume "ks' ! (length ks' - 2) > i"
              have "ks' ! (length ks' - 2) < ks' ! (length ks' - 1)"
                using `sorted ks'` `distinct ks'` `2 \<le> length ks'`
                by (metis Suc_1 Suc_diff_Suc Suc_le_lessD \<open>\<forall>i<length ks' - 1. ks' ! i < t + dly\<close>
               \<open>last ks' = t + dly\<close> last_conv_nth less_Suc_eq list.size(3) not_less_eq_eq zero_le_one)
              also have "... = t + dly"
                using `last ks' = t + dly` by (metis Nil_is_append_conv \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close>
                last_conv_nth not_Cons_self2)
              finally have "ks' ! (length ks' - 2) < t + dly"
                by auto
              have in_keys: "ks' ! (length ks' - 2) \<in> keys (to_transaction2 \<tau>' sig)"
                using `2 \<le> length ks'` ks'_def
                by (metis Nil_is_append_conv Suc_1 \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close> diff_less
                le_imp_less_Suc length_greater_0_conv not_Cons_self2 nth_mem sorted_list_of_set(1)
                sorted_list_of_set.infinite zero_le_one)
              let ?last_two = "ks' ! (length ks' - 2)"
              have "lookup (to_transaction2 \<tau>' sig) ?last_two \<noteq> 0"
                using in_keys by (transfer', auto simp add:to_trans_raw2_def)
              moreover have "lookup (to_transaction2 \<tau>' sig) ?last_two = 0"
                using `i < ?last_two` `?last_two < t+ dly` `\<forall>j>i. j < t + dly \<longrightarrow> get_trans \<tau>' j sig = None`
                apply transfer' unfolding to_trans_raw2_def by (auto simp add: zero_option_def)
              ultimately have "False"
                by auto }
            moreover
            { assume "ks' ! (length ks' - 2) < i"
              let ?last_two = "ks' ! (length ks' - 2)"
              have "\<forall>j > ?last_two. j < last ks' \<longrightarrow> lookup (to_transaction2 \<tau>' sig) j = 0"
                by (metis Nil_is_append_conv One_nat_def Suc_1 Suc_diff_Suc Suc_le_lessD
                \<open>2 \<le> length ks'\<close> \<open>\<forall>i k. ks' ! i < k \<and> k < ks' ! (i + 1) \<and> i + 1 < length ks' \<longrightarrow> lookup (to_transaction2 \<tau>' sig) k = 0\<close>
                \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close> add.right_neutral add_Suc_right
                diff_less last_conv_nth length_greater_0_conv not_Cons_self2 zero_less_Suc)
              moreover have "lookup (to_transaction2 \<tau>' sig) i \<noteq> 0"
                using `lookup \<tau> i sig = Some v` `i < t + dly` lookup
                by (transfer', auto simp add: to_trans_raw2_def trans_post_raw_def zero_option_def)
              with `?last_two < i` have "False"
                using `i < t + dly` `last ks' = t + dly`  by (simp add: calculation) }
            ultimately show False by auto
          qed
          moreover have "lookup (to_transaction2 \<tau>' sig) i = Some v"
            using `lookup \<tau> i sig = Some v` lookup `i < t + dly` apply transfer' unfolding trans_post_raw_def
            to_trans_raw2_def by auto
          ultimately have "lookup (to_transaction2 \<tau>' sig) (ks' ! (length ks' - 2)) \<noteq> lookup (to_transaction2 \<tau>' sig) (ks' ! (length ks' - 1))"
            using `v \<noteq> (beval t \<sigma> \<gamma> \<theta> e)` by auto
          with IH have "\<forall>i. Suc i < length ks' \<longrightarrow> lookup (to_transaction2 \<tau>' sig) (ks' ! i) \<noteq> lookup (to_transaction2 \<tau>' sig) (ks' ! Suc i)"
            by (metis Suc_1 Suc_lessE Suc_lessI diff_Suc_1 diff_Suc_Suc)
          moreover have "\<sigma> s \<noteq> the (lookup (to_transaction2 \<tau>' s) (ks' ! 0))"
            using Bassign_trans(1) unfolding non_stuttering_def Let_def
            using \<open>2 \<le> length ks'\<close> \<open>\<And>idx. idx < length ks' - 1 \<Longrightarrow> ks' ! idx = ks ! idx\<close>
            \<open>\<forall>i<length ks' - 1. ks' ! i < t + dly\<close> \<open>\<forall>k<t + dly. lookup (to_transaction2 \<tau> sig) k = lookup (to_transaction2 \<tau>' sig) k\<close>
            \<open>sig = s\<close> ks_def \<open>ks' = take (length ks' - 1) ks @ [t + dly]\<close> by auto
          ultimately have "non_stuttering (to_transaction2 \<tau>') \<sigma> s"
            unfolding non_stuttering_def `sig = s` Let_def ks'_def by auto }
        ultimately show ?case by auto
      qed }
    ultimately have ?case by auto }
  ultimately show ?case by auto
next
  case (Bcomp cs1 cs2)
  have False
    using `Bcomp cs1 cs2 = Bassign_trans sig e dly` by auto
  then show ?case by auto
next
  case (Bguarded x1 cs1 cs2)
  have "False"
    using `Bguarded x1 cs1 cs2 = Bassign_trans sig e dly` by auto
  then show ?case by auto
next
  case (Bassign_inert x1 x2 x3)
  then show ?case by auto
next
  case Bnull
  then show ?case by auto
qed

lemma purge_trans_post_preserve_non_stuttering:
  fixes \<tau> sig t dly cur_val
  assumes "non_stuttering (to_transaction2 \<tau>) \<sigma> sig"
  defines "\<tau>'  \<equiv> purge \<tau> t dly sig"
  defines "\<tau>'' \<equiv> trans_post sig cur_val (\<sigma> sig) \<tau>' t dly"
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "0 < dly"
  shows "non_stuttering (to_transaction2 \<tau>'') \<sigma> sig"
proof (cases "cur_val = \<sigma> sig")
  case False
  have lookup: "lookup \<tau>' = override_on (lookup \<tau>) (\<lambda>n. (lookup \<tau> n)(sig := None)) {t <.. t + dly} "
    unfolding \<tau>'_def by transfer' auto
  have "context_invariant_weaker t \<sigma> \<theta> \<tau>"
    using ci_implies_ci_weaker assms by auto
  hence "lookup \<tau> t sig = None"
    using no_mapping_at_t_if_non_stuttering[OF _ assms(1)] by (auto simp add: zero_option_def)
  have "\<forall>n < t. lookup \<tau> n = 0"
    using assms(4) unfolding context_invariant_weaker_def by (auto simp add: zero_option_def)
  have "post_necessary_raw (dly - 1) (lookup \<tau>') t sig cur_val (\<sigma> sig)"
  proof -
    have *: "(\<forall>i>t. i \<le> t + (dly - 1) \<longrightarrow> get_trans \<tau>' i sig = None)"
      using lookup unfolding override_on_def by transfer' auto
    hence "lookup \<tau>' t sig = None"
      using lookup `lookup \<tau> t sig = None` unfolding override_on_def by transfer' auto
    hence "(\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> get_trans \<tau>' i sig = None)"
      using *  using le_eq_less_or_eq by blast
    thus ?thesis
      using post_necessary_raw_correctness2 False by metis
  qed
  hence lookup2: "lookup \<tau>'' = trans_post_raw sig cur_val (lookup \<tau>') (t + dly)"
    unfolding \<tau>''_def by transfer' auto
  have "to_transaction2 \<tau>'' sig = Poly_Mapping.single (t + dly) (Some cur_val)"
  proof (intro poly_mapping_eqI)
    fix k
    have "k \<le> t \<or> t < k \<and> k < t + dly \<or> k = t + dly \<or> t + dly < k"
      by auto
    moreover
    { assume "k \<le> t"
      hence "k < t + dly"
        using `0 < dly` by auto
      hence "lookup (to_transaction2 \<tau>'' sig) k = lookup (to_transaction2 \<tau>' sig) k"
        using lookup2 apply transfer' unfolding trans_post_raw_def to_trans_raw2_def by auto
      also have "... = lookup (to_transaction2 \<tau> sig) k"
        using lookup `k \<le> t` unfolding override_on_def apply transfer' unfolding to_trans_raw2_def by auto
      also have "... = 0"
        using `k \<le> t` `\<forall>n < t. lookup \<tau> n = 0` `lookup \<tau> t sig = None` apply transfer' unfolding to_trans_raw2_def
        by (metis le_eq_less_or_eq zero_map zero_option_def)
      also have "... = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        using `k < t + dly`  by (metis less_irrefl lookup_single_not_eq)
      finally have " lookup (to_transaction2 \<tau>'' sig) k = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        by auto }
    moreover
    { assume "t < k \<and> k < t + dly"
      hence "lookup (to_transaction2 \<tau>'' sig) k = lookup (to_transaction2 \<tau>' sig) k"
        using lookup2 apply transfer' unfolding trans_post_raw_def to_trans_raw2_def by auto
      also have "... = 0"
        using lookup `t < k \<and> k < t + dly` unfolding override_on_def apply transfer' unfolding to_trans_raw2_def
        by (auto simp add: zero_option_def)
      also have "... = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        using `t < k \<and> k < t + dly`  by (metis less_irrefl lookup_single_not_eq)
      finally have " lookup (to_transaction2 \<tau>'' sig) k = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        by auto }
    moreover
    { assume "k = t + dly"
      hence "lookup (to_transaction2 \<tau>'' sig) k = Some cur_val"
        using lookup2 apply transfer' unfolding trans_post_raw_def to_trans_raw2_def by auto
      also have "... = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        using `k = t + dly` apply transfer' by auto
      finally have " lookup (to_transaction2 \<tau>'' sig) k = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        by auto }
    moreover
    { assume "t + dly < k"
      hence "lookup (to_transaction2 \<tau>'' sig) k = 0"
        using lookup2 apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
        by (auto simp add: zero_option_def)
      also have "... = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        using `k > t + dly` apply transfer' by auto
      finally have " lookup (to_transaction2 \<tau>'' sig) k = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
        by auto }
    ultimately show " lookup (to_transaction2 \<tau>'' sig) k = lookup (Poly_Mapping.single (t + dly) (Some cur_val)) k "
      by auto
  qed
  with `cur_val \<noteq> \<sigma> sig` show ?thesis
    unfolding non_stuttering_def Let_def
    by (metis (no_types, lifting) Suc_lessD distinct_sorted_list_of_set finite_keys length_greater_0_conv
        lessI lookup_single_eq lookup_single_not_eq nat_less_le not_in_keys_iff_lookup_eq_zero nth_eq_iff_index_eq
        nth_mem option.sel sorted_list_of_set(1))
next
  case True
  have lookup: "lookup \<tau>' = override_on (lookup \<tau>) (\<lambda>n. (lookup \<tau> n)(sig := None)) {t <.. t + dly} "
    unfolding \<tau>'_def by transfer' auto
  have "context_invariant_weaker t \<sigma> \<theta> \<tau>"
    using ci_implies_ci_weaker assms by auto
  hence "lookup \<tau> t sig = None"
    using no_mapping_at_t_if_non_stuttering[OF _ assms(1)] by (auto simp add: zero_option_def)
  have "\<forall>n < t. lookup \<tau> n = 0"
    using assms(4) unfolding context_invariant_weaker_def by (auto simp add: zero_option_def)
  have "\<not> post_necessary_raw (dly - 1) (lookup \<tau>') t sig cur_val (\<sigma> sig)"
  proof -
    have *: "(\<forall>i>t. i \<le> t + (dly - 1) \<longrightarrow> get_trans \<tau>' i sig = None)"
      using lookup unfolding override_on_def by transfer' auto
    hence "lookup \<tau>' t sig = None"
      using lookup `lookup \<tau> t sig = None` unfolding override_on_def by transfer' auto
    hence "(\<forall>i\<ge>t. i \<le> t + (dly - 1) \<longrightarrow> get_trans \<tau>' i sig = None)"
      using *  using le_eq_less_or_eq by blast
    thus ?thesis
      using post_necessary_raw_correctness True by metis
  qed
  hence lookup2: "lookup \<tau>'' = preempt_nonstrict sig (lookup \<tau>') (t + dly)"
    unfolding \<tau>''_def  by transfer' auto
  hence "to_transaction2 \<tau>'' sig = 0"
    using `\<forall>n < t. lookup \<tau> n = 0` `lookup \<tau> t sig = None` lookup
    apply transfer' unfolding preempt_nonstrict_def to_trans_raw2_def
    by (rule ext, smt fun_upd_eqD fun_upd_triv greaterThanAtMost_iff le_neq_implies_less nat_le_linear
    override_on_apply_in override_on_apply_notin zero_map zero_option_def)
  with True show ?thesis
    unfolding non_stuttering_def Let_def by auto
qed

lemma b_seq_exec_preserves_non_stuttering:
  assumes "non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "nonneg_delay cs"
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  shows "non_stuttering (to_transaction2 \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  define \<tau>'' where "\<tau>'' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
  hence *: "non_stuttering (to_transaction2 \<tau>'') \<sigma> s"
    using Bcomp(1)[OF Bcomp(3)] Bcomp(4-) by auto
  have "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>''"
    unfolding \<tau>''_def using Bcomp.prems(2) by auto
  moreover have "\<And>n. n < t \<Longrightarrow> get_trans \<tau>'' n = 0"
    using b_seq_exec_preserve_trans_removal[OF Bcomp(5)] unfolding \<tau>''_def by auto
  moreover have " context_invariant_weaker t \<sigma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant_weaker[OF Bcomp(7)] \<tau>''_def Bcomp(5-) by auto
  ultimately show ?case
    using Bcomp(2)[OF *] Bcomp(6) by auto
next
  case (Bguarded x1 cs1 cs2)
  then show ?case by (metis b_seq_exec.simps(3) nonneg_delay.simps(3))
next
  case (Bassign_trans sig e dly)
  thus ?case by (meson trans_post_preserves_non_stuttering)
next
  case (Bassign_inert sig e dly)
  hence \<tau>'_def: "\<tau>' = inr_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  have "is_stable dly \<tau> t sig (\<sigma> sig) \<or> \<not> is_stable dly \<tau> t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable dly \<tau> t sig (\<sigma> sig)"
    hence "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
      using \<tau>'_def unfolding inr_post_def by auto
    hence ?case
      by (metis Bassign_inert.prems(1) Bassign_inert.prems(3) Bassign_inert.prems(4) b_seq_exec.simps(4)
      nonneg_delay.simps(4) nonneg_delay.simps(5) trans_post_preserves_non_stuttering) }
  moreover
  { assume "\<not> is_stable dly \<tau> t sig (\<sigma> sig)"
    hence \<tau>'_def': "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge \<tau> t dly sig) t dly"
      using \<tau>'_def unfolding inr_post_def by auto
    let ?\<tau> = "purge \<tau> t dly sig"
    have "s = sig \<or> s \<noteq> sig"
      by auto
    moreover
    { assume "s \<noteq> sig"
      hence "\<And>n. lookup (to_transaction2 \<tau>' s) n = lookup (to_transaction2 \<tau> s) n"
        using \<tau>'_def' lookup_trans_post by (metis purge_does_not_affect_other_sig to_trans_raw2_def
        to_transaction2.rep_eq)
      hence "to_transaction2 \<tau>' s = to_transaction2 \<tau> s"
        using poly_mapping_eqI by blast
      hence ?case
        using Bassign_inert(1) unfolding non_stuttering_def Let_def by auto }
    moreover
    { assume "s = sig"
      moreover have 3: "\<And>n. n < t \<Longrightarrow> lookup ?\<tau> n = 0"
        using Bassign_inert(3) by (simp add: purge_preserve_trans_removal)
      obtain cs2 where cs2_def: "cs2 = Bassign_trans sig e dly"
        by auto
      hence 2: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2, ?\<tau>> \<longrightarrow>\<^sub>s \<tau>'"
        using \<tau>'_def' by auto
      have 4: "nonneg_delay cs2"
        unfolding cs2_def using Bassign_inert(4) by auto
      have ?case
        using purge_trans_post_preserve_non_stuttering[OF Bassign_inert(1) Bassign_inert(5) `0 < dly`]
        unfolding \<tau>'_def' `s = sig` by auto }
    ultimately have ?case by auto }
  ultimately show ?case by auto
next
  case Bnull
  then show ?case by auto
qed

lemma b_conc_exec_preserves_non_stuttering:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "nonneg_delay_conc cs"
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "conc_stmt_wf cs"
  shows "non_stuttering (to_transaction2 \<tau>') \<sigma> s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  hence "nonneg_delay_conc cs1" and "conc_stmt_wf cs1" and "nonneg_delay_conc cs2" and "conc_stmt_wf cs2"
    by auto
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence "non_stuttering (to_transaction2 \<tau>1) \<sigma> s"
    using Bpar(1)[OF _ Bpar(4-5) _ `context_invariant_weaker t \<sigma> \<theta> \<tau>`]  `nonneg_delay_conc cs1` `conc_stmt_wf cs1`
    by metis
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence "non_stuttering (to_transaction2 \<tau>2) \<sigma> s"
    using Bpar(2)[OF _ Bpar(4-5) _ `context_invariant_weaker t \<sigma> \<theta> \<tau>`] `nonneg_delay_conc cs2` `conc_stmt_wf cs2`
    by auto
  have \<tau>'_def: "\<tau>' = clean_zip \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
    using Bpar unfolding \<tau>1_def \<tau>2_def by auto
  have "s \<in> set (signals_from cs1) \<or> s \<in> set (signals_from cs2) \<or> s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence "\<And>n. lookup \<tau>' n s = lookup \<tau>1 n s"
      using \<tau>'_def apply transfer' unfolding clean_zip_raw_def Let_def by auto
    hence " (to_transaction2 \<tau>' s) = (to_transaction2 \<tau>1 s)"
      by transfer' (auto simp add: to_trans_raw2_def)
    hence ?case
      using `non_stuttering (to_transaction2 \<tau>1) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  moreover
  { assume "s \<in> set (signals_from cs2)"
    hence "s \<notin> set (signals_from cs1)"
      using `conc_stmt_wf (cs1 || cs2)` unfolding conc_stmt_wf_def by auto
    hence "\<And>n. lookup \<tau>' n s = lookup \<tau>2 n s"
      using \<tau>'_def `s \<in> set (signals_from cs2)` apply transfer' unfolding clean_zip_raw_def Let_def
      by auto
    hence " (to_transaction2 \<tau>' s) = (to_transaction2 \<tau>2 s)"
      by transfer' (auto simp add: to_trans_raw2_def)
    hence ?case
      using `non_stuttering (to_transaction2 \<tau>2) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  moreover
  { assume "s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2)"
    hence "\<And>n. lookup \<tau>' n s = lookup \<tau> n s"
      unfolding \<tau>'_def apply transfer' unfolding clean_zip_raw_def Let_def by auto
    hence " (to_transaction2 \<tau>' s) = (to_transaction2 \<tau> s)"
      by transfer' (auto simp add: to_trans_raw2_def)
    hence ?case
      using `non_stuttering (to_transaction2 \<tau>) \<sigma> s` unfolding non_stuttering_def Let_def
      by auto }
  ultimately show ?case by auto
next
  case (Bsingle x1 x2)
  then show ?case
    using b_seq_exec_preserves_non_stuttering by force
qed

lemma [simp]:
  "fst (worldline2 t \<sigma> \<theta> \<tau>) = t"
  unfolding worldline2_def by auto

lemma destruct_worldline_correctness:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
  shows "t = t'"
    and "\<sigma> = \<sigma>'"
    and "\<gamma> = \<gamma>'"
    and "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False \<theta>' s k"
    and "\<And>k s. signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau>' s k"
  using assms(2) state_worldline2[OF ci_implies_ci_weaker[OF assms(1)]] event_worldline2'[OF assms(1)]
  hist_of_worldline[OF ci_implies_ci_weaker[OF assms(1)]]
  transaction_worldline2[OF ci_implies_ci_weaker[OF assms(1)]] unfolding destruct_worldline_def Let_def
  by auto

lemma destruct_worldline_correctness2:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  assumes " \<forall>s. non_stuttering (to_transaction2 \<theta>) def_state s"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
  shows "t = t'" and "\<sigma> = \<sigma>'" and "\<gamma> = \<gamma>'" and "\<tau> = \<tau>'" and "\<theta> = \<theta>'"
  using assms(4) destruct_worldline_correctness[OF assms(1) assms(4)]
  derivative_raw_of_worldline2[OF ci_implies_ci_weaker[OF assms(1)] assms(2)]
  derivative_is_history2[OF ci_implies_ci_weaker[OF assms(1)] assms(3)]
  unfolding destruct_worldline_def Let_def by auto

lemma destruct_worldline_correctness3:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  assumes "\<forall>s. non_stuttering (to_transaction2 \<theta>) def_state s"
  shows "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  using destruct_worldline_correctness[OF assms(1)]  derivative_raw_of_worldline2[OF ci_implies_ci_weaker[OF assms(1)] assms(2)]
  derivative_is_history2[OF ci_implies_ci_weaker[OF assms(1)] assms(3)] unfolding destruct_worldline_def Let_def
  by (metis (no_types, lifting) comp_apply)

lemma destruct_worldline_correctness_weaker:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>) = (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
  shows "t = t'"
    and "\<sigma> = \<sigma>'"
    and "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False \<theta>' s k"
    and "\<And>k s. signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) \<tau>' s k"
  using assms(2) state_worldline2[OF assms(1)]  hist_of_worldline[OF assms(1)]
  transaction_worldline2[OF assms(1)] unfolding destruct_worldline_def Let_def by auto

definition world_seq_exec :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> nat \<times> 'signal worldline2" where
  "world_seq_exec tw s = (let (t, \<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline tw;
                                           \<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> s \<tau>
                           in worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_seq_exec_abb :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> nat \<times> 'signal worldline2 \<Rightarrow> bool"
  ("(_ , _) \<Rightarrow>\<^sub>s _")
  where "world_seq_exec_abb tw s tw' \<equiv> (world_seq_exec tw s = tw')"

(* Diagram for lifting the sequential execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>s          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s, \<tau>>    \<longrightarrow>\<^sub>s          \<tau>'
 *
 *)

lemma time_invariant:
  assumes "tw, s \<Rightarrow>\<^sub>s tw'" shows "fst tw = fst tw'"
  using assms unfolding world_seq_exec_def Let_def
  by (auto dest!: worldline2_constructible split:prod.splits)

definition
seq_hoare_valid2 :: "'signal assn2 \<Rightarrow> 'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile> [(1_)]/ (_)/ [(1_)]" 50)
where "\<Turnstile> [P] s [Q] \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, s \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

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
  shows "signal_of2 (\<sigma> s) (purge \<tau>1 t dly sig) s k = signal_of2 (\<sigma> s) \<tau>1 s k"
proof -
  have "\<And>n. lookup (to_transaction2 (purge \<tau>1 t dly sig) s) n = lookup (to_transaction2 \<tau>1 s) n"
    using assms purge_does_not_affect_other_sig[of "\<tau>1" "t" "dly" "sig" "purge \<tau>1 t dly sig"]
    apply transfer' unfolding to_trans_raw2_def  by auto
  from signal_of2_lookup_sig_same[OF this] show ?thesis by auto
qed

lemma signal_of2_purged:
  assumes "k < t + dly"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau>1 n = 0"
  assumes "\<And>s. s \<in> dom (lookup \<tau>1 t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>1 t s)"
  shows "signal_of2 (\<sigma> sig) (purge \<tau>1 t dly sig) sig k = (\<sigma> sig)"
proof -
  have *: "\<And>k. k \<le> t \<Longrightarrow> lookup (purge \<tau>1 t dly sig) k = lookup \<tau>1 k"
    using purge_before_now_unchanged[of "\<tau>1" "t" "dly" "sig"] by auto
  have **: "\<And>k. k < t \<Longrightarrow> lookup (purge \<tau>1 t dly sig) k = 0"
    using assms(2) * by auto
  have "k < t \<or> k = t \<or> t < k"
    by auto
  moreover
  { assume "k < t "
    have ?thesis
    proof -
      have "\<forall>n\<in>dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig)). k < n"
      proof (rule ccontr)
        assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig)). k < n)"
        then obtain n where "n \<in> dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig))"
          and "n \<le> k"  using not_less by blast
        with `k < t` have "n < t" by auto
        hence " lookup (purge \<tau>1 t dly sig) n = lookup \<tau>1 n "
          using * by auto
        also have "... = 0"
          using assms(2) `n < t` by auto
        finally have "lookup (purge \<tau>1 t dly sig) n = 0"
          by auto
        hence "n \<notin> dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig))"
          apply transfer' unfolding to_trans_raw2_def
          by (simp add: domIff zero_fun_def zero_option_def)
        with `n \<in> dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig))`
        show False by auto
      qed
      hence "inf_time (to_transaction2 (purge \<tau>1 t dly sig)) sig k = None"
        by (rule inf_time_noneI)
      thus ?thesis
        unfolding to_signal2_def comp_def by auto
    qed }
  moreover
  { assume "k = t"
    hence "lookup (purge \<tau>1 t dly sig) k sig = lookup \<tau>1 k sig"
      using purge_before_now_unchanged by (simp add: "*")
    obtain x where "lookup \<tau>1 k sig = None \<or> lookup \<tau>1 k sig = Some x"
      by (meson not_None_eq)
    moreover
    { assume "lookup \<tau>1 k sig = None"
      have ?thesis
      proof -
        have "\<forall>n\<in>dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig)). k < n"
        proof (rule ccontr)
          assume "\<not> (\<forall>n\<in>dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig)). k < n)"
          then obtain n where "n \<in> dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig))"
            and "n \<le> k"  using not_less by blast
          with `k = t` have "n \<le> t" by auto
          hence " lookup (purge \<tau>1 t dly sig) n sig = lookup \<tau>1 n sig"
            using * by auto
          also have "... = 0"
            using assms(2) `n \<le> t` `lookup \<tau>1 k sig = None`
            by (metis \<open>k = t\<close> dual_order.order_iff_strict zero_fun_def zero_option_def)
          finally have "lookup (purge \<tau>1 t dly sig) n sig = 0"
            by auto
          hence "n \<notin> dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig))"
            apply transfer' unfolding to_trans_raw2_def
            by (simp add: domIff zero_fun_def zero_option_def)
          with `n \<in> dom (lookup (to_transaction2 (purge \<tau>1 t dly sig) sig))`
          show False by auto
        qed
        hence "inf_time (to_transaction2 (purge \<tau>1 t dly sig)) sig k = None"
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
        using \<open>get_trans (purge \<tau>1 t dly sig) k sig = get_trans \<tau>1 k sig\<close> lookup_some_signal_of2'
        by fastforce }
    ultimately have ?thesis by auto }
  moreover
  { assume "t < k"
    have "lookup (purge \<tau>1 t dly sig) k sig = None \<or>
          lookup (purge \<tau>1 t dly sig) k sig = Some (\<sigma> sig)"
      by (simp add: \<open>t < k\<close> assms(1) order.strict_implies_order purge_correctness')
    moreover
    { assume "lookup (purge \<tau>1 t dly sig) k sig = Some (\<sigma> sig)"
      hence ?thesis
        by (meson lookup_some_signal_of2') }
    moreover
    { assume "lookup (purge \<tau>1 t dly sig) k sig = None"
      define \<tau>1' where "\<tau>1' = purge \<tau>1 t dly sig"
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
          using `lookup (purge \<tau>1 t dly sig) k sig = None`
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
          using `lookup (purge \<tau>1 t dly sig) k sig = None` unfolding \<tau>1'_def
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
  assumes "context_invariant_weaker t \<sigma> \<theta>1 \<tau>1" and "context_invariant_weaker t \<sigma> \<theta>2 \<tau>2"
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
  moreover have "context_invariant_weaker t \<sigma> \<theta>1 \<tau>"
    using b_seq_exec_preserves_context_invariant_weaker[OF Bcomp(7) tau1 `nonneg_delay ss1`]
    by auto
  moreover have "context_invariant_weaker t \<sigma> \<theta>2 \<tau>'"
    using b_seq_exec_preserves_context_invariant_weaker[OF Bcomp(8) tau3 `nonneg_delay ss1`] .
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
  have tau1: "\<tau>1' = trans_post sig x (\<sigma> sig) \<tau>1 t dly"
    using Bassign_trans(1)  using x_def by auto
  have tau2:  "\<tau>2' = trans_post sig x (\<sigma> sig) \<tau>2 t dly"
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
    from signal_of_trans_post3[OF this] have "signal_of2 (\<sigma> sig) \<tau>1' sig k = x"
      using Bassign_trans(5-7) unfolding tau1 context_invariant_weaker_def
      by (metis (mono_tags, hide_lams) nonneg_delay.simps(4) tau1)
    moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of2 (\<sigma> sig) \<tau>2' sig k = x"
      using Bassign_trans(5-7) unfolding tau2 context_invariant_weaker_def
      by (metis (mono_tags, hide_lams) nonneg_delay.simps(4) tau2)
    ultimately have "signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) \<tau>2' sig k"
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
    using `context_invariant_weaker t \<sigma> \<theta>1 \<tau>1` unfolding context_invariant_weaker_def by auto
  have "is_stable dly \<tau>1 t sig (\<sigma> sig) \<or> \<not> is_stable dly \<tau>1 t sig (\<sigma> sig)"
    by auto
  moreover
  { assume stab1: "is_stable dly \<tau>1 t sig (\<sigma> sig)" hence stab2:"is_stable dly \<tau>2 t sig (\<sigma> sig)"
      using signal_of2_eq_is_stable[OF _ Bassign_inert(3) ci0 ci1] by auto
    have tau1': "\<tau>1' = trans_post sig x (\<sigma> sig) \<tau>1 t dly"
      using stab1 tau1 unfolding inr_post_def by auto
    moreover have tau2': "\<tau>2' = trans_post sig x (\<sigma> sig) \<tau>2 t dly"
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
      from signal_of_trans_post3[OF this] have "signal_of2 (\<sigma> sig) \<tau>1' sig k = x"
        using Bassign_inert(5-7) unfolding tau1' context_invariant_weaker_def
        by (smt nonneg_delay.simps(5))
      moreover from signal_of_trans_post3[OF `t + dly \<le> k`] have "signal_of2 (\<sigma> sig) \<tau>2' sig k = x"
        using Bassign_inert(5-7) unfolding tau2' context_invariant_weaker_def
        by (smt nonneg_delay.simps(5))
      ultimately have "signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) \<tau>2' sig k"
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
      using `context_invariant_weaker t \<sigma> \<theta>2 \<tau>2` unfolding context_invariant_weaker_def by auto
    have nstable2: "\<not> is_stable dly \<tau>2 t sig (\<sigma> sig)"
      using signal_of2_eq_is_stable_eq[OF ci0 ci1 ci2 ci3 Bassign_inert(3)]
      `\<not> is_stable dly \<tau>1 t sig (\<sigma> sig)` by auto
    have tau1': "\<tau>1' = trans_post sig x (\<sigma> sig) (purge \<tau>1 t dly sig) t dly"
      using tau1 nstable1 unfolding inr_post_def by auto
    have tau2': "\<tau>2' = trans_post sig x (\<sigma> sig) (purge \<tau>2 t dly sig) t dly"
      using tau2 nstable2 unfolding inr_post_def by auto
    have "t + dly \<le> k \<or> k < t + dly"
      by auto
    have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) (purge \<tau>1 t dly sig) s k"
      using signal_of_trans_post unfolding tau1' by metis
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) (purge \<tau>1 t dly sig) s k = signal_of2 (\<sigma> s) \<tau>1 s k"
      using signal_of2_purge_not_affected  by fastforce
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
      using Bassign_inert(3) by auto
    moreover have "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>2 s k = signal_of2 (\<sigma> s) (purge \<tau>2 t dly sig) s k"
      using signal_of2_purge_not_affected by fastforce
    ultimately have *: "s \<noteq> sig \<Longrightarrow> signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
      using signal_of_trans_post unfolding tau2' by metis
    have "t + dly \<le> k \<or> k < t + dly"
      by auto
    moreover
    { assume "t + dly \<le> k"
      have "signal_of2 (\<sigma> sig) \<tau>1' sig k = x"
        using Bassign_inert(5-7) unfolding tau1' context_invariant_weaker_def
        by (metis (no_types, lifting) \<open>t + dly \<le> k\<close> nonneg_delay.simps(5) signal_of_inr_post tau1 tau1')
      moreover have "signal_of2 (\<sigma> sig) \<tau>2' sig k = x"
        using Bassign_inert(5-7) unfolding tau2' context_invariant_weaker_def
        by (metis (no_types, lifting) \<open>t + dly \<le> k\<close> nonneg_delay.simps(5) signal_of_inr_post tau2 tau2')
      ultimately have "signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) \<tau>2' sig k"
        by auto
      with * have "signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k"
        by auto }
    moreover
    { assume "k < t + dly"
      from signal_of_trans_post2[OF this] have "signal_of2 (\<sigma> sig) \<tau>1' sig k = signal_of2 (\<sigma> sig) (purge \<tau>1 t dly sig) sig k"
        and "signal_of2 (\<sigma> sig) \<tau>2' sig k = signal_of2 (\<sigma> sig) (purge \<tau>2 t dly sig) sig k" unfolding tau1' tau2' by metis+
      moreover have "signal_of2 (\<sigma> sig) (purge \<tau>1 t dly sig) sig k = \<sigma> sig"
        using signal_of2_purged[OF `k < t + dly` `\<And>n. n < t \<Longrightarrow> get_trans \<tau>1 n = 0`
        `\<And>s. s \<in> dom (get_trans \<tau>1 t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau>1 t s)`] by auto
      moreover have "signal_of2 (\<sigma> sig) (purge \<tau>2 t dly sig) sig k = \<sigma> sig"
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
  assumes "context_invariant_weaker t \<sigma> \<theta>1 \<tau>1" and "context_invariant_weaker t \<sigma> \<theta>2 \<tau>2"
  assumes "nonneg_delay ss"
  shows "\<exists>\<tau>2'. (t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2') \<and> (\<forall>k s. signal_of2 (\<sigma> s) \<tau>1' s k = signal_of2 (\<sigma> s) \<tau>2' s k)"
  using helper'[OF assms(1-3) _ assms(4-5) `nonneg_delay ss`] by auto

lemma Bcomp_hoare_valid':
  assumes "\<Turnstile> [P] s1 [Q]" and "\<Turnstile> [Q] s2 [R]"
  assumes "nonneg_delay (Bcomp s1 s2)"
  shows "\<Turnstile> [P] Bcomp s1 s2 [R]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix tw tw' :: "nat \<times> 'a worldline2"
  have "nonneg_delay s1" and "nonneg_delay s2"
    using assms(3) by auto
  assume "P tw \<and> (tw, Bcomp s1 s2 \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bcomp s1 s2 \<Rightarrow>\<^sub>s tw'" by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>')" and "tw'= worldline2 t \<sigma> \<theta> \<tau>'"
    unfolding world_seq_exec_def Let_def using destruct_worldline_exist by fastforce
  then obtain \<tau>'' where tau1: "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'')" and tau2: "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>')"
    by auto
  define tw'' where "tw'' = worldline2 t \<sigma> \<theta> \<tau>''"
  hence "tw, s1 \<Rightarrow>\<^sub>s tw''"
    using des tau1 unfolding world_seq_exec_def Let_def by auto
  with assms(1) have "Q tw''"
    unfolding seq_hoare_valid2_def using `P tw` by fastforce
  have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF des] by auto
  hence "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''"
    using b_seq_exec_preserves_context_invariant[OF _ tau1] assms(3) by auto
  obtain \<theta>''' \<tau>''' where des2: "destruct_worldline tw'' = (t, \<sigma>, \<gamma>, \<theta>''', \<tau>''')" and
    sig_beh: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False \<theta>''' s k" and
    sig_trans: "\<And>k s. signal_of2 (\<sigma> s) \<tau>'' s k = signal_of2 (\<sigma> s) \<tau>''' s k"
    unfolding tw''_def using destruct_worldline_correctness[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>''`]
    by (metis destruct_worldline_exist)
  have "context_invariant t \<sigma> \<gamma> \<theta>''' \<tau>'''"
    using worldline2_constructible[OF des2] by auto
  obtain \<tau>4 where tau3: "t, \<sigma>, \<gamma>, \<theta>''' \<turnstile> <s2, \<tau>'''> \<longrightarrow>\<^sub>s \<tau>4" and
    sig_trans: "\<And>k s. signal_of2 (\<sigma> s) \<tau>4 s k = signal_of2 (\<sigma> s) \<tau>' s k"
    using helper[OF tau2 sig_beh sig_trans ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>''`]]  \<open>nonneg_delay s2\<close>
    ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta>''' \<tau>'''`] by auto
  have "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta>''' \<tau>4"
    using sig_beh sig_trans
  proof transfer'
    fix \<theta>  \<theta>''' :: "'a transaction"
    fix \<sigma> :: "'a state"
    fix \<tau>'' \<tau>''' \<tau>4 t \<tau>'
    assume 1: "\<And>s k. signal_of2 False \<theta> s k = signal_of2 False \<theta>''' s k"
    assume  "\<And>s k. signal_of2 (\<sigma> s) \<tau>4 s k = signal_of2 (\<sigma> s) \<tau>' s k"
    thus " (t, worldline t \<sigma> \<theta> \<tau>') = (t, worldline t \<sigma> \<theta>''' \<tau>4)"
      unfolding worldline_def using 1 by auto
  qed
  hence "tw'', s2 \<Rightarrow>\<^sub>s tw'"
    unfolding world_seq_exec_def using des2 tau3 `tw'= worldline2 t \<sigma> \<theta> \<tau>'`
    by (smt \<open>t, \<sigma> , \<gamma> , \<theta> \<turnstile> <Bcomp s1 s2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> \<open>tw , Bcomp s1 s2 \<Rightarrow>\<^sub>s tw'\<close> case_prod_conv
    des fst_conv world_seq_exec_def)
  with `Q tw''` show "R tw'"
    using assms(2) unfolding seq_hoare_valid2_def by blast
qed

lemma Bnull_sound_hoare2:
  "\<turnstile> [P] Bnull [Q] \<Longrightarrow> \<Turnstile> [P] Bnull [Q]"
  by (auto dest!: BnullE'_hoare2 worldline2_constructible  simp add: seq_hoare_valid2_def world_seq_exec_def
           split: prod.splits)

lemma Bguarded_hoare_valid2:
  assumes "\<Turnstile> [\<lambda>tw. P tw \<and> beval_world2 tw g] s1 [Q]" and "\<Turnstile> [\<lambda>tw. P tw \<and> \<not> beval_world2 tw g] s2 [Q]"
  shows "\<Turnstile> [P] Bguarded g s1 s2 [Q]"
  unfolding seq_hoare_valid2_def
proof (rule)+
  fix tw  tw':: "nat \<times> 'a worldline2"
  assume "P tw \<and> (tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and "tw = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "tw' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `tw, Bguarded g s1 s2 \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def by auto
  have "beval t \<sigma> \<gamma> \<theta> g \<or> \<not> beval t \<sigma> \<gamma> \<theta> g"
    by auto
  moreover
  { assume "beval t \<sigma> \<gamma> \<theta> g"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` by auto
    hence "beval_world2 tw g"
      using `beval t \<sigma> \<gamma> \<theta> g` `tw = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      by (transfer', simp add: beval_beval_world_ci)
    have "tw , s1 \<Rightarrow>\<^sub>s tw'"
      using `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)` `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `tw' = worldline2 t \<sigma> \<theta> \<tau>'` unfolding world_seq_exec_def Let_def  by simp
    with assms(1) and `P tw` have "Q tw'"
      using `beval_world2 tw g` `fst tw = t` unfolding seq_hoare_valid2_def by blast }
  moreover
  { assume "\<not> beval t \<sigma> \<gamma> \<theta> g"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g s1 s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` by auto
    hence "\<not> beval_world2 tw g"
      using `\<not> beval t \<sigma> \<gamma> \<theta> g` `tw = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
      by (transfer', simp add: beval_beval_world_ci)
    have "tw, s2 \<Rightarrow>\<^sub>s tw'"
      using `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)` `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <s2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`
      `tw' = worldline2 t \<sigma> \<theta> \<tau>'` unfolding world_seq_exec_def Let_def
      by simp
    with assms(2) and `P tw` have "Q tw'"
      using `\<not> beval_world2 tw g` `fst tw = t` unfolding seq_hoare_valid2_def by blast }
  ultimately show "Q tw'"
    by auto
qed

lemma lift_world_trans_worldline_upd2:
  assumes "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
  assumes "0 < dly"
  shows "tw' = tw[sig, dly :=\<^sub>2 beval_world2 tw exp]"
  using assms
proof transfer'
  fix tw tw' :: "nat \<times> 'a worldline2"
  fix sig
  fix exp :: "'a bexp"
  fix dly
  assume "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'"
  assume "0 < dly"
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and w_def: "tw = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  hence "\<forall>i<t. get_trans \<tau> i = 0"
    unfolding context_invariant_def by auto
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    by auto
  moreover have "beval t \<sigma> \<gamma> \<theta> exp = beval_world2 tw exp"
    using `tw = worldline2 t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (transfer', simp add: beval_beval_world_ci)
  ultimately have \<tau>'_def: "\<tau>' = trans_post sig (beval_world2 tw exp) (\<sigma> sig) \<tau> t dly"
    by auto
  have "tw' = (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by auto
  also have "... = tw[sig, dly:=\<^sub>2 beval_world2 tw exp]"
    using w_def \<tau>'_def `0 < dly` `\<forall>i<t. get_trans \<tau> i = 0`
    apply transfer'
    using lift_trans_post_worldline_upd  by (metis fst_conv fst_swap swap_simp)
  finally show "tw' = tw[sig, dly:=\<^sub>2 beval_world2 tw exp]"
    using `fst tw = t` by auto
qed

lemma Bassign_trans_sound_hoare2:
  "0 < dly \<Longrightarrow> \<turnstile> [P] Bassign_trans sig exp dly [Q] \<Longrightarrow> \<Turnstile> [P] Bassign_trans sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix tw tw' :: "nat \<times> 'a worldline2"
  assume "0 < dly"
  assume "\<turnstile> [P] Bassign_trans sig exp dly [Q]"
  hence imp: "\<forall>tw. P tw \<longrightarrow> Q( tw[sig, dly :=\<^sub>2 beval_world2 tw exp])"
    by (auto dest!: BassignE_hoare2)
  assume " P tw \<and> (tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "fst tw = t"
    by (metis (no_types, lifting) destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "tw' = worldline2 t \<sigma> \<theta> \<tau>'"
    using `tw, Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_trans sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  hence "fst tw' = t"
    by transfer'  auto
  have "tw' = tw[sig, dly :=\<^sub>2 beval_world2 tw exp]"
    unfolding `tw' = worldline2 t \<sigma> \<theta> \<tau>'` using `fst tw = t` `0 < dly`
    by (metis \<open>tw' = worldline2 t \<sigma> \<theta> \<tau>'\<close> \<open>tw , Bassign_trans sig exp dly \<Rightarrow>\<^sub>s tw'\<close>
    lift_world_trans_worldline_upd2)
  with imp and `P tw` have "Q(tw[sig, dly :=\<^sub>2 beval_world2 tw exp])"
    using `fst tw = t` by blast
  thus "Q tw'"
    using `tw' = tw[sig, dly :=\<^sub>2 beval_world2 tw exp]`
    `fst tw = t` surjective_pairing[of "tw'"]  `fst tw' = t` by auto
qed

lemma lift_world_inert_worldline_upd2:
  assumes "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
  assumes "0 < dly"
  shows "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk>"
  using assms
proof transfer'
  fix tw tw' :: "nat \<times> 'a worldline2"
  fix sig
  fix exp :: "'a bexp"
  fix dly
  assume "tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'"
  assume "0 < dly"
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    by (meson destruct_worldline_def)
  hence "fst tw = t" and w_def: "tw = worldline2 t \<sigma> \<theta> \<tau> " and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    by(auto dest!: worldline2_constructible)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    and "\<tau>' = inr_post sig (beval t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly"
    by auto
  moreover have "beval t \<sigma> \<gamma> \<theta> exp = beval_world2 tw exp"
    using `tw = worldline2 t \<sigma> \<theta> \<tau> ` and `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    by (transfer', simp add: beval_beval_world_ci)
  ultimately have \<tau>'_def: "\<tau>' = inr_post sig (beval_world2 tw exp) (\<sigma> sig) \<tau> t dly"
    by auto
  have "tw' = (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
    by auto
  also have "... = tw\<lbrakk>sig, dly:=\<^sub>2 beval_world2 tw exp\<rbrakk>"
    using `tw = worldline2 t \<sigma> \<theta> \<tau>` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`
    `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` `0 < dly`
    by (transfer', simp add: lift_inr_post_worldline_upd)
  finally show "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk>"
    using `fst tw = t` by auto
qed

lemma Bassign_inert_sound_hoare2:
  assumes "0 < dly"
  shows "\<turnstile> [P] Bassign_inert sig exp dly [Q] \<Longrightarrow> \<Turnstile> [P] Bassign_inert sig exp dly [Q]"
  unfolding seq_hoare_valid2_def
proof rule+
  fix tw tw' :: "nat \<times> 'a worldline2"
  assume "\<turnstile> [P] Bassign_inert sig exp dly [Q]"
  hence imp: "\<forall>tw. P tw \<longrightarrow> Q(tw \<lbrakk>sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk>)"
    by (auto dest!: Bassign_inertE_hoare2)
  assume "P tw \<and> (tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw')"
  hence "P tw" and "tw, (Bassign_inert sig exp dly) \<Rightarrow>\<^sub>s tw'" by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "fst tw = t"
    by (metis (no_types, lifting) destruct_worldline_def)
  obtain \<tau>' where "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "tw' = (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw, Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_seq_exec_def  using \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bassign_inert sig exp dly , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by auto
  hence "fst tw' = t"
    by transfer' auto
  have "tw' = tw\<lbrakk>sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk>"
    by (metis \<open>fst tw = t\<close> \<open>tw , Bassign_inert sig exp dly \<Rightarrow>\<^sub>s tw'\<close> assms lift_world_inert_worldline_upd2)
  with imp and `P tw` have "Q(tw\<lbrakk>sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk>)"
    using `fst tw = t` by blast
  thus "Q tw'"
    using `tw' = tw \<lbrakk> sig, dly :=\<^sub>2 beval_world2 tw exp\<rbrakk>` `fst tw = t` `fst tw' = t`
    surjective_pairing[of "tw'"] by auto
qed

subsubsection \<open>Soundness and completeness\<close>

lemma soundness_hoare2:
  assumes "\<turnstile> [P] s [R]"
  assumes "nonneg_delay s"
  shows "\<Turnstile> [P] s [R]"
  using assms
proof (induction rule:seq_hoare2.induct)
  case (AssignI2 P sig dly exp)
  hence "0 < dly" by auto
  then show ?case
    using Bassign_inert_sound_hoare2[OF `0 < dly`]  using seq_hoare2.AssignI2 by fastforce
next
  case (Conseq2 P' P s Q Q')
  then show ?case by (metis seq_hoare_valid2_def)
qed (auto simp add: Bnull_sound_hoare2 Bassign_trans_sound_hoare2 Bcomp_hoare_valid' Bguarded_hoare_valid2)

lemma  world_seq_exec_bnull:
  "tw, Bnull \<Rightarrow>\<^sub>s tw"
  unfolding world_seq_exec_def Let_def
  by (auto split:prod.splits dest!:worldline2_constructible)

lemma world_seq_exec_comp:
  assumes "nonneg_delay (Bcomp ss1 ss2)"
  shows "tw, (Bcomp ss1 ss2) \<Rightarrow>\<^sub>s (world_seq_exec (world_seq_exec tw ss1) ss2)"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by metis
  then obtain \<tau>'' where "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>''" and exec1: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss2, \<tau>''> \<longrightarrow>\<^sub>s \<tau>'"
    and ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>''" using b_seq_exec_preserves_context_invariant
    using assms by fastforce
  hence *: "worldline2 t \<sigma> \<theta> \<tau>'' = world_seq_exec tw ss1"
    unfolding world_seq_exec_def Let_def using des1 by auto
  obtain \<theta>2 \<tau>2 \<tau>3 where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>'') = (t, \<sigma>, \<gamma>, \<theta>2, \<tau>2)" and
    beh_same:"\<And>s k. signal_of2 False \<theta> s k = signal_of2 False \<theta>2 s k" and
    trans_same: "\<And>s k. signal_of2 (\<sigma> s) \<tau>'' s k = signal_of2 (\<sigma> s) \<tau>2 s k" and
    exec2: "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3"
    using destruct_worldline_correctness[OF ci2]  by (metis prod.exhaust_sel)
  have ci3: "context_invariant t \<sigma> \<gamma> \<theta>2 \<tau>2"
    using worldline2_constructible[OF des2] by auto
  have "\<And>s k. signal_of2 (\<sigma> s) \<tau>' s k = signal_of2 (\<sigma> s) \<tau>3 s k"
    using helper'[OF exec1 beh_same trans_same exec2 ci_implies_ci_weaker[OF ci2] ci_implies_ci_weaker[OF ci3]]
    assms by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta>2 \<tau>3"
    using beh_same
  proof (transfer')
    fix \<sigma> :: "'a state"
    fix \<tau>' \<tau>3
    fix \<theta> \<theta>2 :: "'a transaction"
    fix t
    assume 1: "\<And>s k. signal_of2 (\<sigma> s) \<tau>' s k = signal_of2 (\<sigma> s) \<tau>3 s k"
    assume "\<And>s k. signal_of2 False \<theta> s k = signal_of2 False \<theta>2 s k"
    thus " (t, worldline t \<sigma> \<theta> \<tau>') = (t, worldline t \<sigma> \<theta>2 \<tau>3) "
      unfolding worldline_def  using 1 by auto
  qed
  also have "... = world_seq_exec (worldline2 t \<sigma> \<theta> \<tau>'') ss2"
    using des2 `t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <ss2, \<tau>2> \<longrightarrow>\<^sub>s \<tau>3` unfolding world_seq_exec_def Let_def
    by auto
  finally have "worldline2 t \<sigma> \<theta> \<tau>' = world_seq_exec (worldline2 t \<sigma> \<theta> \<tau>'') ss2"
    by auto
  thus ?thesis
    using des1 `t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'` unfolding  *
    world_seq_exec_def Let_def by auto
qed

lemma world_seq_exec_guarded:
  fixes tw :: "nat \<times> 'a worldline2"
  assumes "beval_world2 tw g"
  shows "world_seq_exec tw (Bguarded g ss1 ss2) = world_seq_exec tw ss1"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> \<tau>" and "fst tw = t" using destruct_worldline_exist worldline2_constructible
    by (metis (no_types, lifting) destruct_worldline_def)
  moreover have "beval t \<sigma> \<gamma> \<theta> g"
    using assms `tw = worldline2 t \<sigma> \<theta> \<tau>` ci1  `fst tw = t`
    by (transfer', simp add: beval_beval_world_ci)
  ultimately have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  thus ?thesis
    by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> case_prod_conv
        des1 world_seq_exec_def)
qed

lemma world_seq_exec_guarded_not:
  fixes tw :: "nat \<times> 'a worldline2"
  assumes "\<not> beval_world2 tw g"
  shows "world_seq_exec tw (Bguarded g ss1 ss2) = world_seq_exec tw ss2"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des1: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <Bguarded g ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and
    "tw = worldline2 t \<sigma> \<theta> \<tau>" and "fst tw = t" using destruct_worldline_exist worldline2_constructible
    by (metis (no_types, lifting) destruct_worldline_def fst_def snd_def)
  moreover have "\<not> beval t \<sigma> \<gamma> \<theta> g"
    using assms `tw = worldline2 t \<sigma> \<theta> \<tau>` ci1  using `fst tw = t`
    by (transfer', auto simp add: beval_beval_world_ci)
  ultimately have "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  thus ?thesis
    by (metis (no_types, lifting) \<open>t , \<sigma> , \<gamma> , \<theta> \<turnstile> <Bguarded g ss1 ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> case_prod_conv
        des1 world_seq_exec_def)
qed

definition wp :: "'signal seq_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp ss Q = (\<lambda>tw. \<forall>tw'. (tw, ss \<Rightarrow>\<^sub>s tw') \<longrightarrow> Q tw')"

lemma wp_bnull:
  "wp Bnull Q = Q"
  by (rule ext)(auto simp add: wp_def world_seq_exec_bnull)

lemma wp_bcomp:
  "nonneg_delay (Bcomp ss1 ss2) \<Longrightarrow> wp (Bcomp ss1 ss2) Q = wp ss1 (wp ss2 Q)"
  by (rule ext) (auto simp add: wp_def world_seq_exec_comp)

lemma wp_guarded:
  "wp (Bguarded g ss1 ss2) Q =
  (\<lambda>tw. if beval_world2 tw g then wp ss1 Q tw else wp ss2 Q tw)"
  by (rule ext) (auto simp add: wp_def world_seq_exec_guarded world_seq_exec_guarded_not)

lemma wp_trans:
  "0 < dly \<Longrightarrow> wp (Bassign_trans sig exp dly) Q = (\<lambda>tw. Q(tw [sig, dly :=\<^sub>2 beval_world2 tw exp]))"
  by (rule ext, metis (full_types) lift_world_trans_worldline_upd2 wp_def)

lemma wp_inert:
  "0 < dly \<Longrightarrow> wp (Bassign_inert sig exp dly) Q = (\<lambda>tw. Q(tw \<lbrakk> sig, dly :=\<^sub>2 beval_world2 tw exp \<rbrakk>))"
  by (rule ext, metis lift_world_inert_worldline_upd2 wp_def)

lemma wp_is_pre: "nonneg_delay ss \<Longrightarrow> \<turnstile> [wp ss Q] ss [Q]"
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
  assumes "nonneg_delay ss" assumes "\<Turnstile> [P] ss [Q]" shows "\<turnstile> [P] ss [Q]"
proof (rule strengthen_pre_hoare2)
  show "\<forall>w. P w \<longrightarrow> wp ss Q w" using assms
    by (metis seq_hoare_valid2_def wp_def)
  show " \<turnstile> [VHDL_Hoare_Complete.wp ss Q] ss [Q]"
    using assms by (intro wp_is_pre)
qed

corollary hoare_sound_complete:
  assumes "nonneg_delay ss"
  shows "\<turnstile> [P] ss [Q] \<longleftrightarrow> \<Turnstile> [P] ss [Q]"
  using hoare_complete soundness_hoare2 assms by auto

subsection \<open>A sound and complete Hoare logic for VHDL's concurrent statement\<close>

definition event_of :: "nat \<times> 'signal worldline2  \<Rightarrow> 'signal event" where
  "event_of tw = (fst o snd o snd) (destruct_worldline tw)"

inductive
  conc_hoare :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile> (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
Single:  "\<turnstile> [\<lambda>tw. P tw \<and> \<not> disjnt sl (event_of tw)] ss [Q] \<Longrightarrow> \<forall>tw. P tw \<and> disjnt sl (event_of tw) \<longrightarrow> Q tw
    \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> process sl : ss \<lbrace>Q\<rbrace>"
| Parallel:  "\<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile> \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Parallel2: "\<turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace> \<Longrightarrow> \<turnstile> \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace> \<Longrightarrow> conc_stmt_wf (cs\<^sub>1 || cs\<^sub>2) \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 || cs\<^sub>2 \<lbrace>Q\<rbrace>"
| Conseq': "\<lbrakk>\<forall>w. P' w \<longrightarrow> P w; \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>; \<forall>w. Q w \<longrightarrow> Q' w\<rbrakk> \<Longrightarrow> \<turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q\<rbrace>"

lemma strengthen_pre_conc_hoare:
  assumes "\<forall>w. P' w \<longrightarrow> P w" and "\<turnstile> \<lbrace>P\<rbrace> s \<lbrace>Q\<rbrace>"
  shows "\<turnstile> \<lbrace>P'\<rbrace> s \<lbrace>Q\<rbrace>"
  using assms by (blast intro: Conseq')

definition world_conc_exec :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline2"
  where
  "world_conc_exec tw c = (let (t, \<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline tw;
                                          \<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c \<tau>
                           in worldline2 t \<sigma> \<theta> \<tau>')"

abbreviation world_conc_exec_abb :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline2 \<Rightarrow> bool"
  ("(_ , _) \<Rightarrow>\<^sub>c _")
  where "world_conc_exec_abb tw s w' \<equiv> (world_conc_exec tw s = w')"

(* Diagram for lifting the concurrent execution to the worldline level
 *
 *         w, t                    \<Rightarrow>\<^sub>c          w', t
 *           \<down>                                  \<up>
 *   destruct_worldline                      worldline2 t \<sigma> \<theta> \<tau>'
 *           \<down>                                  \<up>
 *         t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>>    \<longrightarrow>\<^sub>c          \<tau>'
 *
 *)

lemma fst_world_conc_exec:
  assumes "tw, cs \<Rightarrow>\<^sub>c tw'"
  shows "fst tw = fst tw'"
proof -
  have "tw' = world_conc_exec tw cs"
    using assms by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
    using destruct_worldline_exist by blast
  obtain \<tau>' where "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>"
    by auto
  have "fst tw = t"
    using fst_destruct_worldline `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`  by (metis fst_conv)
  have "fst tw' = fst (worldline2 t \<sigma> \<theta> \<tau>')"
    using `tw' = world_conc_exec tw cs` `destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)`
    unfolding world_conc_exec_def by auto
  also have "... = t"
    by transfer' auto
  also have "... = fst tw"
    using `fst tw = t` by auto
  finally show "fst tw = fst tw'"
    by auto
qed

lemma world_conc_exec_commute:
  assumes "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c tw1"
  assumes "tw, (cs2 || cs1) \<Rightarrow>\<^sub>c tw2"
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "tw1 = tw2"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "worldline2 t \<sigma> \<theta> \<tau>' = tw1"
    using assms(1) unfolding world_conc_exec_def Let_def by (auto split:prod.splits)
  hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_comp_commute'[OF assms(3)] by auto
  thus ?thesis
    using assms(2) unfolding world_conc_exec_def Let_def
    using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>worldline2 t \<sigma> \<theta> \<tau>' = tw1\<close>  by auto
qed

lemma world_conc_exec_disjnt:
  fixes tw :: "nat \<times> 'a worldline2"
  assumes "disjnt sl (event_of tw)" shows "tw, (process sl : ss) \<Rightarrow>\<^sub>c tw"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist by blast
  moreover have "disjnt sl \<gamma>"
    using assms unfolding event_of_def by (simp add: des)
  ultimately have "\<tau>' = \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = tw"
    using des  worldline2_constructible by fastforce
  with des ex show ?thesis
    by (auto simp add: world_conc_exec_def split:prod.splits)
qed

lemma world_conc_exec_not_disjnt:
  fixes tw :: "nat \<times> 'a worldline2"
  assumes "\<not> disjnt sl (event_of tw)" and "tw, ss \<Rightarrow>\<^sub>s tw'"
  shows "tw, (process sl : ss) \<Rightarrow>\<^sub>c tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using destruct_worldline_exist by blast
  moreover have "\<not> disjnt sl \<gamma>"
    using assms unfolding event_of_def des by (simp add: des)
  ultimately have "\<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>"
    by auto
  hence "worldline2 t \<sigma> \<theta> \<tau>' = tw'"
    using assms(2) des by (metis (no_types, lifting) old.prod.case snd_conv world_seq_exec_def)
  thus ?thesis
    using des ex
    by (simp add: world_conc_exec_def)
qed

definition
conc_hoare_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile> \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<longleftrightarrow>  (\<forall>tw tw'.  P tw \<and> (tw, c \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma helper_b_conc:
  assumes "t, \<sigma>, \<gamma>, \<theta>1 \<turnstile> <cs, \<tau>1> \<longrightarrow>\<^sub>c \<tau>1'"
  assumes "\<And>k s. signal_of2 False \<theta>1 s k = signal_of2 False \<theta>2 s k"
  assumes "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) \<tau>2 s k"
  assumes "t, \<sigma>, \<gamma>, \<theta>2 \<turnstile> <cs, \<tau>2> \<longrightarrow>\<^sub>c \<tau>2'"
  assumes "context_invariant_weaker t \<sigma> \<theta>1 \<tau>1" and "context_invariant_weaker t \<sigma> \<theta>2 \<tau>2"
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
  shows "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c (world_conc_exec (world_conc_exec tw cs1) cs2)"
proof -
  have "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    using assms by auto
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by (metis)
  have ci': "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ci ex `nonneg_delay_conc cs1`] by auto
  hence wcs1: "world_conc_exec tw cs1 = (worldline2 t \<sigma> \<theta> \<tau>')"
    using des ex by (simp add: world_conc_exec_def)
  obtain theta tau' where des2: "destruct_worldline (worldline2 t \<sigma> \<theta> \<tau>') = (t, \<sigma>, \<gamma>, theta, tau')"
    and beh_same: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False theta s k" and
        trans_same: "\<And>k s. signal_of2 (\<sigma> s) \<tau>' s k = signal_of2 (\<sigma> s) tau' s k"
    using destruct_worldline_correctness[OF ci'] by (metis prod_cases4)
  have ci2: "context_invariant t \<sigma> \<gamma> theta tau'" and "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> theta tau'"
    using worldline2_constructible[OF des2] by auto
  have "\<And>k s. signal_of2 (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>') s  k =
              signal_of2  (\<sigma> s) (b_conc_exec t \<sigma> \<gamma> theta cs2 tau') s k"
    using helper_b_conc[OF _ beh_same trans_same _ ci_implies_ci_weaker[OF ci'] ci_implies_ci_weaker[OF ci2]
    `nonneg_delay_conc cs2`] by auto
  hence *: "worldline2 t \<sigma> theta (b_conc_exec t \<sigma> \<gamma> theta cs2 tau') =
        worldline2 t \<sigma> \<theta> (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>')"
    using beh_same apply transfer' unfolding worldline_def by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =  b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>'"
    using b_conc_exec_sequential[OF assms(1)] ex by auto
  hence "world_conc_exec tw (cs1 || cs2) = worldline2 t \<sigma> \<theta> (b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>')"
    using des ex by (auto simp add: world_conc_exec_def)
  hence "(world_conc_exec tw cs1), cs2 \<Rightarrow>\<^sub>c (world_conc_exec tw (cs1 || cs2))"
    using des2 wcs1 *  by (simp add: world_conc_exec_def)
  thus ?thesis
    by simp
qed

lemma world_conc_exec_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c (world_conc_exec (world_conc_exec tw cs2) cs1)"
proof -
  have wf: "conc_stmt_wf (cs2 || cs1)" and nd: "nonneg_delay_conc (cs2 || cs1)"
    using assms unfolding conc_stmt_wf_def by auto
  have "tw, (cs1 || cs2) \<Rightarrow>\<^sub>c world_conc_exec tw (cs2 || cs1)"
    using world_conc_exec_commute[OF _ _ assms(1)] by blast
  with world_conc_exec_parallel[OF wf nd] show ?thesis
    by auto
qed

lemma parallel_valid:
  assumes "\<Turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace>" and "\<Turnstile> \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace>" and "conc_stmt_wf (c1 || c2)"
  assumes "nonneg_delay_conc (c1 || c2)"
  shows "\<Turnstile> \<lbrace>P\<rbrace> c1 || c2 \<lbrace>Q\<rbrace>"
  unfolding conc_hoare_valid_def
proof rule+
  fix tw tw':: "nat \<times> 'a worldline2"
  assume "P tw \<and> tw , c1 || c2 \<Rightarrow>\<^sub>c tw'"
  hence "P tw" and "tw, c1 || c2 \<Rightarrow>\<^sub>c tw'"
    by auto
  then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    *: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c1 || c2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and w'_def: "worldline2 t \<sigma> \<theta> \<tau>' = tw'" and
    ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding world_conc_exec_def Let_def  using destruct_worldline_exist
    by (auto simp add: worldline2_constructible split:prod.splits)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> c1 \<tau>"
  hence ci1: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>1"
    using b_conc_exec_preserves_context_invariant[OF ci] assms(4) by auto
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>"
  hence ci2: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>2"
    using b_conc_exec_preserves_context_invariant[OF ci] assms(4) by auto
  have \<tau>'_def: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c2 \<tau>1"
    using b_conc_exec_sequential[OF assms(3)] * unfolding \<tau>1_def by auto
  define tw1 where "tw1 = worldline2 t \<sigma> \<theta> \<tau>1"
  have "tw, c1 \<Rightarrow>\<^sub>c tw1"
    using des \<tau>1_def unfolding world_conc_exec_def Let_def by (simp add: tw1_def)
  hence "R tw1"
    using assms(1) `P tw` unfolding conc_hoare_valid_def by blast
  obtain theta1 tau1 where des2: "destruct_worldline tw1 = (t, \<sigma>, \<gamma>, theta1, tau1)" and
    beh_same: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False theta1 s k" and
    trans_same: "\<And>k s. signal_of2 (\<sigma> s) \<tau>1 s k = signal_of2 (\<sigma> s) tau1 s k"
    using destruct_worldline_exist[of "worldline2 t \<sigma> \<theta> \<tau>1"] unfolding tw1_def
    using destruct_worldline_correctness[OF ci1] by metis
  have "context_invariant t \<sigma> \<gamma> theta1 tau1"
    using des2 worldline2_constructible by fastforce
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
      using helper_b_conc[OF _ bs ts _ ci_implies_ci_weaker[OF ci1'] ci_implies_ci_weaker[OF ci2']] \<tau>'_def' by metis
    thus "(t, worldline t \<sigma> theta1 (b_conc_exec t \<sigma> \<gamma> theta1 c2 tau1)) = (t, worldline t \<sigma> \<theta> \<tau>')"
      unfolding worldline_def \<tau>'_def' using bs by auto
  qed
  hence "tw1, c2 \<Rightarrow>\<^sub>c tw'"
    using des2 by (simp add: w'_def world_conc_exec_def)
  with `R tw1` show "Q tw'"
    using assms(2) using conc_hoare_valid_def by metis
qed

lemma soundness_conc_hoare:
  assumes "\<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes "conc_stmt_wf c" and "nonneg_delay_conc c"
  shows "\<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:conc_hoare.induct)
  case (Single P sl ss Q)
  { fix tw  tw' :: "nat \<times> 'a worldline2"
    assume as: "P tw \<and> (tw ,  process sl : ss \<Rightarrow>\<^sub>c tw')"
    then obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and "P tw" and
      ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and "(worldline2 t \<sigma> \<theta> \<tau>') = tw'"
      unfolding world_seq_exec_def Let_def
      by (metis (mono_tags, lifting) case_prod_beta' prod.exhaust_sel world_conc_exec_def)
    have "fst tw = t"
      by (metis (no_types, lifting) des destruct_worldline_def fst_conv)
    have "nonneg_delay ss"
      using Single by auto
    have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
      by auto
    moreover
    { assume "disjnt sl \<gamma>"
      hence "\<tau>' = \<tau>" using ex by auto
      hence "tw' = tw"
        using \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>(worldline2 t \<sigma> \<theta> \<tau>') = tw'\<close> worldline2_constructible
        by (metis)
      with Single have "Q tw'"
        unfolding event_of_def  using \<open>P tw \<and> tw, process sl : ss \<Rightarrow>\<^sub>c tw'\<close>
        \<open>destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)\<close> \<open>disjnt sl \<gamma>\<close>  disjnt_sym by fastforce }
    moreover
    { assume "\<not> disjnt sl \<gamma>"
      hence "\<not> disjnt sl (event_of tw)"
        unfolding event_of_def using des `fst tw = t` by auto
      moreover have "tw, ss \<Rightarrow>\<^sub>s tw'"
        using as `\<not> disjnt sl \<gamma>`
      proof -
        have "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
          using \<open>\<not> disjnt sl \<gamma>\<close> ex by force
        then show ?thesis
          by (simp add: \<open>(worldline2 t \<sigma> \<theta> \<tau>') = tw'\<close> des world_seq_exec_def)
      qed
      ultimately have "Q tw'"
        using soundness_hoare2[OF Single(1) `nonneg_delay ss`] `P tw` `fst tw = t`
        unfolding seq_hoare_valid2_def by blast }
    ultimately have "Q tw'" by auto }
  then show ?case
    unfolding conc_hoare_valid_def by auto
next
  case (Parallel P cs\<^sub>1 R cs\<^sub>2 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel by auto
  ultimately have " \<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>1 \<lbrace>R\<rbrace>" and " \<Turnstile> \<lbrace>R\<rbrace> cs\<^sub>2 \<lbrace>Q\<rbrace>"
    using Parallel by auto
  then show ?case
    using parallel_valid Parallel by blast
next
  case (Parallel2 P cs\<^sub>2 R cs\<^sub>1 Q)
  hence "conc_stmt_wf cs\<^sub>1" and "conc_stmt_wf cs\<^sub>2"
    by (simp add: conc_stmt_wf_def)+
  moreover have "nonneg_delay_conc cs\<^sub>1" and "nonneg_delay_conc cs\<^sub>2"
    using Parallel2 by auto
  ultimately have cs2: " \<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 \<lbrace>R\<rbrace>" and cs1: " \<Turnstile> \<lbrace>R\<rbrace> cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using Parallel2 by auto
  have "conc_stmt_wf (cs\<^sub>2 || cs\<^sub>1)"
    using Parallel2(3) unfolding conc_stmt_wf_def by auto
  moreover have " nonneg_delay_conc (cs\<^sub>2 || cs\<^sub>1) "
    using Parallel2(7) by auto
  ultimately have "\<Turnstile> \<lbrace>P\<rbrace> cs\<^sub>2 || cs\<^sub>1 \<lbrace>Q\<rbrace>"
    using parallel_valid[OF cs2 cs1]   by auto
  thus ?case
    using world_conc_exec_commute[OF _ _ Parallel2(3)]  by (metis conc_hoare_valid_def)
next
  case (Conseq' P' P c Q Q')
  then show ?case by (metis conc_hoare_valid_def)
qed

definition wp_conc :: "'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> 'signal assn2" where
  "wp_conc cs Q = (\<lambda>tw. \<forall>tw'. (tw, cs \<Rightarrow>\<^sub>c tw') \<longrightarrow> Q tw')"

lemma wp_conc_single:
  "wp_conc (process sl : ss) Q =
  (\<lambda>tw. if disjnt sl (event_of tw) then Q tw else wp ss Q tw)"
  by (rule ext) (auto simp add: wp_conc_def wp_def world_conc_exec_disjnt world_conc_exec_not_disjnt)

lemma wp_conc_parallel:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) Q =  wp_conc cs1 (wp_conc cs2 Q)"
  by (rule ext)(auto simp add: wp_conc_def world_conc_exec_parallel[OF assms])

lemma wp_conc_parallel2:
  assumes "conc_stmt_wf (cs1 || cs2)" and "nonneg_delay_conc (cs1 || cs2)"
  shows "wp_conc (cs1 || cs2) Q =  wp_conc cs2 (wp_conc cs1 Q)"
  by (rule ext)(auto simp add: wp_conc_def world_conc_exec_parallel2[OF assms])

lemma wp_conc_is_pre:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "\<turnstile> \<lbrace>wp_conc cs Q\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction cs arbitrary:Q)
  case (Bpar cs1 cs2)
  hence "conc_stmt_wf cs1" and "conc_stmt_wf cs2" and "nonneg_delay_conc cs1" and "nonneg_delay_conc cs2"
    by auto
  hence "\<And>Q.  \<turnstile> \<lbrace>wp_conc cs1 Q\<rbrace> cs1 \<lbrace>Q\<rbrace>" and "\<And>Q.  \<turnstile> \<lbrace>wp_conc cs2 Q\<rbrace> cs2 \<lbrace>Q\<rbrace>"
    using Bpar(1-2) by auto
  then show ?case
    unfolding wp_conc_parallel[OF Bpar(3-4)]
    by (auto intro!: Parallel simp add: Bpar)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  then show ?case  unfolding wp_conc_single
    by (auto intro!: Single simp add: hoare_sound_complete seq_hoare_valid2_def wp_def)
qed

lemma conc_hoare_complete:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  assumes "\<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>" shows "\<turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
proof (rule strengthen_pre_conc_hoare)
  show " \<forall>tw. P tw \<longrightarrow> wp_conc cs Q tw" using assms
    by (metis conc_hoare_valid_def wp_conc_def)
next
  show "\<turnstile> \<lbrace>wp_conc cs Q\<rbrace> cs \<lbrace>Q\<rbrace>"
    using assms by (intro wp_conc_is_pre)
qed

corollary conc_hoare_sound_and_complete:
  assumes "conc_stmt_wf cs" and "nonneg_delay_conc cs"
  shows "\<turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow> \<Turnstile> \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  using conc_hoare_complete soundness_conc_hoare assms by auto

lemma push_rem_curr_trans_purge:
  "rem_curr_trans t (purge \<tau> t dly sig) = purge (rem_curr_trans t \<tau>) t dly sig"
  unfolding rem_curr_trans_def
  by transfer' (auto simp add: override_on_def)

lemma post_necessary_raw_rem_curr_trans:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s) \<longleftrightarrow> post_necessary_raw n (lookup (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
proof
  assume "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s)"
  hence "(\<exists>i\<ge>t. i \<le> t + n \<and> lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None))
                                      \<or>   (\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> lookup \<tau> i s = None) \<and> val \<noteq> (\<sigma> s)"
    (is "?case1 \<or> ?case2")
    by (simp add: post_necessary_raw_correctness2)
  moreover
  { assume "?case1"
    then obtain i where "i \<ge> t" and "i \<le> t + n" and "lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None) "
      by auto
    hence "t < i \<or> i = t" by auto
    moreover
    { assume "t < i"
      hence "(\<exists>i\<ge>t. i \<le> t + n \<and> lookup (rem_curr_trans t \<tau>) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) j s = None))"
        using `i \<le> t + n` `lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None)` unfolding rem_curr_trans_def
        apply transfer'  by (metis fun_upd_apply nat_less_le zero_map)
      hence "post_necessary_raw n (lookup (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
        by (simp add: post_necessary_raw_correctness2) }
    moreover
    { assume "i = t"
      hence "\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) i s = None"
        using `lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None)`
        unfolding rem_curr_trans_def apply transfer' by (auto simp add: zero_map)
      moreover have "(\<sigma> s) \<longleftrightarrow> \<not> val"
        using assms `lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None)`
        unfolding context_invariant_def `i = t` by auto
      ultimately have "post_necessary_raw n (lookup (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
        by (simp add: post_necessary_raw_correctness2) }
    ultimately have "post_necessary_raw n (lookup (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
      by auto }
  moreover
  { assume "?case2"
    hence "(\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) i s = None) \<and> val \<noteq> \<sigma> s"
      unfolding rem_curr_trans_def apply transfer' by (auto simp add: zero_map)
    hence "post_necessary_raw n (lookup (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
      by (simp add: post_necessary_raw_correctness2) }
  ultimately show "post_necessary_raw n (lookup (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
    by auto
next
  assume "post_necessary_raw n (get_trans (rem_curr_trans t \<tau>)) t s val (\<sigma> s)"
  hence "(\<exists>i\<ge>t. i \<le> t + n \<and> lookup (rem_curr_trans t \<tau>) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) j s = None))
                                      \<or>   (\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) i s = None) \<and> val \<noteq> (\<sigma> s)"
    (is "?case1 \<or> ?case2") by (simp add: post_necessary_raw_correctness2)
  moreover
  { assume "?case1"
    then obtain i where "i \<ge> t" and "i \<le> t + n" and "lookup (rem_curr_trans t \<tau>) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) j s = None) "
      by auto
    hence "i \<noteq> t"
      unfolding rem_curr_trans_def by (transfer', auto simp add:zero_map)
    hence "lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None)"
      using `lookup (rem_curr_trans t \<tau>) i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup (rem_curr_trans t \<tau>) j s = None)` `i \<ge> t`
      unfolding rem_curr_trans_def by transfer' auto
    with `i \<ge> t` and `i \<le> t + n` have "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s)"
      by(auto simp add: post_necessary_raw_correctness2) }
  moreover
  { assume "?case2"
    have "lookup \<tau> t s = None \<or> lookup \<tau> t s = Some (\<sigma> s)"
      using assms unfolding context_invariant_def  by (metis (full_types) domIff option.collapse)
    moreover
    { assume "lookup \<tau> t s = None"
      with `?case2` have "(\<forall>i\<ge>t. i \<le> t + n \<longrightarrow> get_trans \<tau> i s = None) \<and> val \<noteq> \<sigma> s"
        unfolding rem_curr_trans_def by (metis lookup_update)
      hence "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s)"
        by (auto simp add: post_necessary_raw_correctness2) }
    moreover
    { assume "lookup \<tau> t s = Some (\<sigma> s)"
      hence "(\<exists>i\<ge>t. i \<le> t + n \<and> lookup \<tau> i s = Some (\<not> val) \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> lookup \<tau> j s = None))"
        using `?case2`
        apply(intro exI[where x="t"])
        unfolding rem_curr_trans_def  apply transfer' using le_eq_less_or_eq by auto
      hence "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s)"
        unfolding post_necessary_raw_correctness2 by auto }
    ultimately have "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s)"
      by auto }
  ultimately show "post_necessary_raw n (lookup \<tau>) t s val (\<sigma> s)"
    by auto
qed

lemma context_invariant_purged:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "context_invariant t \<sigma> \<gamma> \<theta> (purge \<tau> t dly sig)"
proof -
  have "\<forall>n<t. get_trans \<tau> n = 0" and "\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}" and
    "\<forall>s. s \<in> dom (get_trans \<tau> t) \<longrightarrow> \<sigma> s = the (get_trans \<tau> t s)" and "\<forall>n\<ge>t. get_trans \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  hence "\<forall>n < t. lookup (purge \<tau> t dly sig) n = 0"
    by (simp add: purge_preserve_trans_removal)
  moreover have "\<forall>s. s \<in> dom (get_trans (purge \<tau> t dly sig) t) \<longrightarrow> \<sigma> s = the (get_trans (purge \<tau> t dly sig) t s)"
    using `\<forall>s. s \<in> dom (get_trans \<tau> t) \<longrightarrow> \<sigma> s = the (get_trans \<tau> t s)`
    by (metis order_refl purge_before_now_unchanged)
  ultimately show ?thesis
    unfolding context_invariant_def
    using \<open>\<forall>n\<ge>t. get_trans \<theta> n = 0\<close> \<open>\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)}\<close> by blast
qed

lemma b_seq_exec_mono_wrt_rem_curr_trans:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>s (rem_curr_trans t \<tau>')"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  then show ?case
    using b_seq_exec_preserves_context_invariant by fastforce
next
  case (Bguarded x1 ss1 ss2)
  then show ?case  by auto
next
  case (Bassign_trans sig e dly)
  hence "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  hence "rem_curr_trans t \<tau>' = rem_curr_trans t (trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly)"
    by auto
  also have "... = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (rem_curr_trans t \<tau>) t dly"
    using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
    unfolding rem_curr_trans_def
    by transfer' (auto simp add: zero_map zero_option_def trans_post_raw_def preempt_nonstrict_def)
  finally show ?case
    by auto
next
  case (Bassign_inert sig e dly)
  hence \<tau>'_def: "\<tau>' = inr_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  have "is_stable dly \<tau> t sig (\<sigma> sig) \<or> \<not> is_stable dly \<tau> t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable dly \<tau> t sig (\<sigma> sig)"
    hence *: "is_stable dly (rem_curr_trans t \<tau>) t sig (\<sigma> sig)"
      unfolding is_stable_correct unfolding rem_curr_trans_def
      by transfer' auto
    have "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly"
      using \<tau>'_def `is_stable dly \<tau> t sig (\<sigma> sig)` unfolding inr_post_def by auto
    hence "rem_curr_trans t \<tau>' = rem_curr_trans t (trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) \<tau> t dly)"
      by auto
    also have "... = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (rem_curr_trans t \<tau>) t dly"
      using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
      unfolding rem_curr_trans_def
      by (transfer', auto simp add: trans_post_raw_def preempt_nonstrict_def)
    also have "... = inr_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (rem_curr_trans t \<tau>) t dly"
      using * unfolding inr_post_def by auto
    finally have ?case
      by auto }
  moreover
  { assume "\<not> is_stable dly \<tau> t sig (\<sigma> sig)"
    hence *: "\<not> is_stable dly (rem_curr_trans t \<tau>) t sig (\<sigma> sig)"
      unfolding is_stable_correct unfolding rem_curr_trans_def
      by transfer' auto
    have "context_invariant t \<sigma> \<gamma> \<theta> (purge \<tau> t dly sig)"
      using context_invariant_purged `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` by metis
    have "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge \<tau> t dly sig) t dly"
      using `\<not> is_stable dly \<tau> t sig (\<sigma> sig)` \<tau>'_def unfolding inr_post_def by auto
    hence "rem_curr_trans t \<tau>' = rem_curr_trans t (trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge \<tau> t dly sig) t dly)"
      by auto
    also have "... = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (rem_curr_trans t (purge \<tau> t dly sig)) t dly"
      using `0 < dly` post_necessary_raw_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> (purge \<tau> t dly sig)`]
      unfolding rem_curr_trans_def
      by (transfer') (auto simp add: trans_post_raw_def preempt_nonstrict_def)
    also have "... = trans_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (purge (rem_curr_trans t \<tau>) t dly sig) t dly"
      unfolding push_rem_curr_trans_purge by auto
    also have "... = inr_post sig (beval t \<sigma> \<gamma> \<theta> e) (\<sigma> sig) (rem_curr_trans t \<tau>) t dly"
      using * unfolding inr_post_def by auto
    finally have ?case
      by auto }
  ultimately show ?case
    by auto
next
  case Bnull
  then show ?case by auto
qed

text \<open>The following lemma is based on the assumption (premise) that @{term "conc_stmt_wf cs"}. This
is because we want to employ the theorem @{thm "b_conc_exec_sequential"} where executing two parallel
processes can be seen as executing two sequential processes. This is, of course, relies on the
assumption that both processes do not modify the same signals.

A more fundamental question arises: can we prove this theorem without this well-formedness premise
and this theorem? We certainly would need to reason about @{term "clean_zip"} as this is the
primitive operation for handling parallel execution.\<close>

lemma b_conc_exec_mono_wrt_rem_curr_trans:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c (rem_curr_trans t \<tau>')"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence **: "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs1 , rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c rem_curr_trans t \<tau>1"
    using Bpar unfolding conc_stmt_wf_def by auto
  have *: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>1"
    using b_conc_exec_sequential[OF `conc_stmt_wf (cs1 || cs2)`] Bpar(3) \<tau>1_def by auto
  with Bpar have "t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs2 , rem_curr_trans t \<tau>1> \<longrightarrow>\<^sub>c rem_curr_trans t \<tau>'"
    unfolding conc_stmt_wf_def
    by (metis \<tau>1_def b_conc_exec_preserves_context_invariant distinct_append nonneg_delay_conc.simps(2) signals_from.simps(2))
  then show ?case
    using * Bpar(3)  by (metis Bpar.prems(3) ** b_conc_exec_sequential)
next
  case (Bsingle sl ss)
  hence "nonneg_delay ss"
    by auto
  have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>"
    by auto
  moreover
  { assume "disjnt sl \<gamma>"
    hence ?case
      using Bsingle.prems(1) by auto }
  moreover
  { assume "\<not> disjnt sl \<gamma>"
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      using Bsingle by auto
    hence "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>s rem_curr_trans t \<tau>'"
      using b_seq_exec_mono_wrt_rem_curr_trans[OF _ `nonneg_delay ss`]  by (simp add: Bsingle.prems(4))
    hence ?case
      using `\<not> disjnt sl \<gamma>` by auto }
  ultimately show ?case by auto
qed

lemma worldline_rem_curr_trans_eq:
  assumes "\<And>s. s \<in> dom (get_trans \<tau> t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau> t s)"
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "worldline2 t \<sigma> \<theta> \<tau> = worldline2 t \<sigma> \<theta> (rem_curr_trans t \<tau>)"
  using assms signal_of2_rem_curr_trans_at_t[OF assms]
  by (transfer', auto simp add: worldline_def)

lemma worldline2_constructible_rem_curr_trans:
  fixes tw :: "nat \<times> 'signal worldline2"
  assumes "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  defines "\<tau>' \<equiv> rem_curr_trans t \<tau>"
  shows "tw = worldline2 t \<sigma> \<theta> \<tau>' \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
proof -
  have "fst tw = t" and "tw = worldline2 t \<sigma> \<theta> \<tau> \<and> context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF assms(1)] by auto
  hence "\<And>s. s \<in> dom (get_trans \<tau> t) \<Longrightarrow> \<sigma> s = the (get_trans \<tau> t s)"
    and "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
    and " tw = worldline2 t \<sigma> \<theta> \<tau>"
    and " context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    unfolding context_invariant_def by auto
  hence "tw = worldline2 t \<sigma> \<theta> \<tau>'"
    unfolding \<tau>'_def using worldline_rem_curr_trans_eq by  metis
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    unfolding \<tau>'_def using context_invariant_rem_curr_trans[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
    by auto
  ultimately show ?thesis
    by auto
qed

definition world_conc_exec2 :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline2"
  where
  "world_conc_exec2 tw c = (let (t, \<sigma>, \<gamma>, \<theta>, \<tau>) = destruct_worldline tw;
                                             \<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> c (rem_curr_trans t \<tau>)
                             in worldline2 t \<sigma> \<theta> \<tau>')"

lemma world_conc_exec_rem_curr_trans_eq:
  assumes "nonneg_delay_conc c" and "conc_stmt_wf c"
  shows "world_conc_exec2 tw c = world_conc_exec tw c"
proof -
  let ?w = "snd tw"
  obtain t \<sigma> \<gamma> \<theta> \<tau> \<tau>' where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and  ex: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    and ci: "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using destruct_worldline_exist worldline2_constructible by (metis)
  hence ex2: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <c, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c (rem_curr_trans t \<tau>')"
    using b_conc_exec_mono_wrt_rem_curr_trans[OF _ assms] by auto
  moreover have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
    using b_conc_exec_preserves_context_invariant[OF ci ex assms(1)] by auto
  ultimately have "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> \<theta> (rem_curr_trans t \<tau>')"
    using worldline_rem_curr_trans_eq unfolding context_invariant_def by auto
  thus ?thesis
    unfolding world_conc_exec2_def world_conc_exec_def Let_def using des ex ex2
    by auto
qed

subsection \<open>A sound and complete Hoare logic for VHDL's simulation\<close>

lift_definition worldline_of_history :: "'signal transaction \<Rightarrow> 'signal worldline2" is
  "signal_of2 False"
proof -
  fix \<theta> :: "nat \<Rightarrow>\<^sub>0 'signal \<Rightarrow> bool option"
  define d where "d = Poly_Mapping.degree \<theta> - 1"
  have "\<And>n. d < n \<Longrightarrow> lookup \<theta> n = 0"
    using beyond_degree_lookup_zero unfolding d_def by (simp add: beyond_degree_lookup_zero)
  hence "\<And>n s. n > d \<Longrightarrow> signal_of2 False \<theta> s n = signal_of2 False \<theta> s d"
    by(intro signal_of2_less_ind)
  thus "\<exists>t. \<forall>t'>t. (\<lambda>s. signal_of2 False \<theta> s t') = (\<lambda>s. signal_of2 False \<theta> s t)"
    by (auto intro: exI[where x="d"])
qed

inductive world_sim_fin :: "nat \<times> 'signal worldline2 \<Rightarrow> nat \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal worldline2 \<Rightarrow> bool"
  (" _, _, _ \<Rightarrow>\<^sub>S _") where
  "    destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)
   \<Longrightarrow> T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res
   \<Longrightarrow> worldline_of_history res = w'
   \<Longrightarrow> tw, T, cs \<Rightarrow>\<^sub>S w'"

inductive_cases world_sim_fin: "tw, T, cs \<Rightarrow>\<^sub>S w'"

lemma premises_of_world_sim_fin:
  assumes "tw, T, cs \<Rightarrow>\<^sub>S w'"
  shows "\<exists>t \<sigma> \<gamma> \<theta> \<tau> res. destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>) \<and> T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res
                          \<and> worldline_of_history res = w' \<and> fst tw = t"
  using world_sim_fin[OF assms] by (metis (no_types) fst_conv fst_destruct_worldline)

lemma premises_of_world_sim_fin':
  assumes "tw, T, cs \<Rightarrow>\<^sub>S w'"
  obtains t \<sigma> \<gamma> \<theta> \<tau> res where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "T, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res" and   "worldline_of_history res = w'" and "fst tw = t"
  using premises_of_world_sim_fin[OF assms] by auto

text \<open>Simulation without considering time. It is assumed that eventually the simulation will terminate.
We cannot use this to simulate the oscillator which oscillates infinitely.\<close>

inductive b_simulate_inf :: "nat \<Rightarrow> 'signal  state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                            'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> nat \<times> 'signal trace \<Rightarrow> bool"
  ("_ , _ , _ , _ \<turnstile> <_ , _> \<leadsto> _") where

  "    (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')
   \<Longrightarrow> (next_time t \<tau>', next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>, add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, rem_curr_trans (next_time t \<tau>') \<tau>'> \<leadsto> tres)
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres)"

| "    (quiet \<tau> \<gamma>)
   \<Longrightarrow> Poly_Mapping.update t (Some o \<sigma>) \<theta> = res
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> (t, res))"

inductive world_sim :: "nat \<times> 'signal worldline2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> nat \<times> 'signal worldline2 \<Rightarrow> bool"
  (" _, _ \<Rightarrow>\<^sub>S _") where
  "    destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)
   \<Longrightarrow> t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres
   \<Longrightarrow> worldline_of_history (snd tres) = w'
   \<Longrightarrow> tw, cs \<Rightarrow>\<^sub>S (fst tres, w')"

inductive_cases world_sim: "tw, cs \<Rightarrow>\<^sub>S tw'"

lemma premises_of_world_sim:
  assumes "tw, cs \<Rightarrow>\<^sub>S tw'"
  shows "\<exists>t \<sigma> \<gamma> \<theta> \<tau> tres. tw' = (fst tres, worldline_of_history (snd tres)) \<and>
                         destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>) \<and> t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres \<and> fst tw = t"
  using world_sim[OF assms] by (smt fst_conv fst_destruct_worldline)

lemma premises_of_world_sim':
  assumes "tw, cs \<Rightarrow>\<^sub>S tw'"
  obtains t \<sigma> \<gamma> \<theta> \<tau> tres where "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
    "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres" and   "tw' = (fst tres, worldline_of_history (snd tres))" and "fst tw = t"
  using premises_of_world_sim[OF assms] by auto

definition
sim_hoare_valid :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool" ("\<Turnstile>\<^sub>s \<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>" 50)
where "\<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<forall>tw tw'. P tw \<and> (tw, cs \<Rightarrow>\<^sub>S tw') \<longrightarrow> Q tw')"

definition world_quiet :: "nat \<times> 'signal worldline2 \<Rightarrow> bool" where
  "world_quiet tw \<longleftrightarrow> fst tw > worldline_deg (snd tw)"

lemma derivative_raw_ensure_non_stuttering:
  "\<forall>s. non_stuttering (to_transaction2 (derivative_raw w d t)) (\<lambda>s. w s t) s"
proof
  fix s
  define ks where "ks = sorted_list_of_set (keys (to_transaction2 (derivative_raw w d t) s))"
  thus "non_stuttering (to_transaction2 (derivative_raw w d t)) (\<lambda>s. w s t) s"
  proof (induction ks)
    case Nil
    then show ?case
      unfolding non_stuttering_def by auto
  next
    case (Cons x xs)
    have "xs = [] \<or> xs \<noteq> []" by auto
    moreover
    { assume "xs = []"
      with Cons have li: "sorted_list_of_set (keys (to_transaction2 (derivative_raw w d t) s)) = [x]"
        by auto
      hence x_keys: "x \<in> keys (to_transaction2 (derivative_raw w d t) s)"
        by (metis empty_subsetI insert_subset list.simps(15) set_empty set_eq_subset
        set_sorted_list_of_set sorted_list_of_set.infinite)
      have "t < x \<and> x \<le> d"
      proof (rule ccontr)
        assume "\<not> (t < x \<and> x \<le> d)"
        hence "x \<le> t \<or> d < x" by auto
        hence "lookup (derivative_raw w d t) x = Map.empty"
          by transfer' auto
        with x_keys show False
          by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
      qed
      have "w s x \<noteq> w s (x - 1)"
      proof (rule ccontr)
        assume "\<not> w s x \<noteq> w s (x - 1)"
        with `t < x \<and> x \<le> d` have "lookup (to_transaction2 (derivative_raw w d t) s) x = None"
          by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
        hence "x \<notin> keys (to_transaction2 (derivative_raw w d t) s)"
          unfolding in_keys_iff zero_option_def by auto
        with x_keys show False by auto
      qed
      hence **: "lookup (to_transaction2 (derivative_raw w d t) s) x = Some (w s x)"
        using `t < x \<and> x \<le> d` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
      have *: "\<forall>i. t < i \<and> i < x \<longrightarrow> w s i = w s (i-1)"
      proof (rule ccontr)
        assume "\<not> (\<forall>i. t < i \<and> i < x \<longrightarrow> w s i = w s (i-1))"
        then obtain i where "t < i" and "i < x" and "w s i \<noteq> w s (i-1)"
          by auto
        hence "i \<in> keys (to_transaction2 (derivative_raw w d t) s)"
          using `t < x \<and> x \<le> d`
          by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
        with li have "i = x"
          by (metis finite_keys_to_transaction2 list.set(1) list.simps(15) set_sorted_list_of_set
          singletonD)
        with `i < x` show False by auto
      qed
      { fix i
        assume "t < i \<and> i < x"
        hence "w s i = w s t"
        proof (induction i)
          case 0
          then show ?case by auto
        next
          case (Suc i)
          with * have " w s (Suc i) = w s i"
            by auto
          have "t = i \<or> t < i"
            using Suc by auto
          moreover
          { assume "t = i"
            hence ?case
              using `w s (Suc i) = w s i` by auto }
          moreover
          { assume "t < i"
            moreover have "i < x"
              using Suc by auto
            ultimately have "w s i = w s t"
              using Suc(1) by auto
            with `w s (Suc i) = w s i` have ?case by auto }
          ultimately show ?case by auto
        qed }
      hence "\<forall>i. t < i \<and> i < x \<longrightarrow> w s i =  w s t"
        by auto
      hence "w s (x - 1) = w s t"
        using `t < x \<and> x \<le> d`
        by (metis Suc_pred' dual_order.order_iff_strict less_Suc_eq_le less_imp_Suc_add zero_less_Suc)
      with `w s x \<noteq> w s (x - 1)` have "w s x \<noteq> w s t"
        by auto
      hence ?case
        using li ** unfolding non_stuttering_def  by auto }
    moreover
    { assume "xs \<noteq> []"
      hence "1 < length ks"
        using Cons(2) unfolding ks_def by (metis One_nat_def Suc_less_eq length_Cons
        length_greater_0_conv)
      { fix i
        assume "Suc i < length ks"
        hence k_keys: "ks ! Suc i \<in> keys (to_transaction2 (derivative_raw w d t) s)"
          unfolding ks_def  using nth_mem by force
        let ?k = "ks ! Suc i"
        have "t < ?k \<and> ?k \<le> d"
        proof (rule ccontr)
          assume "\<not> (t < ?k \<and> ?k \<le> d)"
          hence "?k \<le> t \<or> d < ?k" by auto
          hence "lookup (derivative_raw w d t) ?k = Map.empty"
            by transfer' auto
          with k_keys show False
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
        qed
        have "w s ?k \<noteq> w s (?k - 1)"
        proof (rule ccontr)
          assume "\<not> w s ?k \<noteq> w s (?k - 1)"
          with `t < ?k \<and> ?k \<le> d` have "lookup (to_transaction2 (derivative_raw w d t) s) ?k = None"
            by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
          hence "?k \<notin> keys (to_transaction2 (derivative_raw w d t) s)"
            unfolding in_keys_iff zero_option_def by auto
          with k_keys show False by auto
        qed
        hence **: "lookup (to_transaction2 (derivative_raw w d t) s) ?k = Some (w s ?k)"
          using `t < ?k \<and> ?k \<le> d` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
        let ?k' = "ks ! i"
        have k'_keys: "?k' \<in> keys (to_transaction2 (derivative_raw w d t) s)"
          unfolding ks_def  using `Suc i < length ks`
          by (metis (no_types, lifting) Cons.prems Suc_lessD ks_def list.distinct(1) nth_mem
          sorted_list_of_set(1) sorted_list_of_set.infinite)
        hence "?k' < ?k"
          using k_keys unfolding ks_def
          by (metis Suc_lessD \<open>Suc i < length ks\<close> distinct_sorted_list_of_set ks_def le_add2
          n_not_Suc_n nat_less_le nth_eq_iff_index_eq plus_1_eq_Suc sorted_nth_mono
          sorted_sorted_list_of_set)
        hence "?k' < ?k \<and> ?k \<le> d" using `t < ?k \<and> ?k \<le> d` by auto
        have "t < ?k' \<and> ?k' \<le> d"
        proof (rule ccontr)
          assume "\<not> (t < ?k' \<and> ?k' \<le> d)"
          hence "?k' \<le> t \<or> d < ?k'" by auto
          hence "lookup (derivative_raw w d t) ?k' = Map.empty"
            by transfer' auto
          with k'_keys show False
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
        qed
        have "w s ?k' \<noteq> w s (?k' - 1)"
        proof (rule ccontr)
          assume "\<not> w s ?k' \<noteq> w s (?k' - 1)"
          with `t < ?k' \<and> ?k' \<le> d` have "lookup (to_transaction2 (derivative_raw w d t) s) ?k' = None"
            by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
          hence "?k' \<notin> keys (to_transaction2 (derivative_raw w d t) s)"
            unfolding in_keys_iff zero_option_def by auto
          with k'_keys show False by auto
        qed
        hence ***: "lookup (to_transaction2 (derivative_raw w d t) s) ?k' = Some (w s ?k')"
          using `t < ?k' \<and> ?k' \<le> d` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
        have *: "\<forall>i. ?k'< i \<and> i < ?k \<longrightarrow> w s i = w s (i-1)"
        proof (rule ccontr)
          assume "\<not> (\<forall>i. ?k'< i \<and> i < ?k \<longrightarrow> w s i = w s (i-1))"
          then obtain k'' where "?k'< k''" and "k'' < ?k" and "w s k'' \<noteq> w s (k''-1)"
            by auto
          hence "k'' \<in> keys (to_transaction2 (derivative_raw w d t) s)"
            using `?k'< ?k \<and> ?k \<le> d` `t < ?k' \<and> ?k' \<le> d`
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
          hence "k'' \<in> set ks"
            unfolding ks_def by auto
          then obtain idx where "ks ! idx = k''" and "idx < length ks"
            by (meson in_set_conv_nth)
          hence "i < idx"
            using `?k' < k''` `Suc i < length ks` unfolding ks_def
            by (meson Suc_lessD leD leI sorted_iff_nth_mono sorted_sorted_list_of_set)
          moreover have "idx < Suc i"
            using `ks ! idx = k''` `k'' < ?k` `idx < length ks` unfolding ks_def
            by (meson Suc_lessD leD leI sorted_iff_nth_mono sorted_sorted_list_of_set)
          ultimately show False
            by auto
        qed
        { fix i
          assume "?k'< i \<and> i < ?k"
          hence "w s i = w s ?k'"
          proof (induction i)
            case 0
            then show ?case by auto
          next
            case (Suc i)
            with * have " w s (Suc i) = w s i"
              by auto
            have "?k'= i \<or> ?k'< i"
              using Suc by auto
            moreover
            { assume "?k'= i"
              hence ?case
                using `w s (Suc i) = w s i` by auto }
            moreover
            { assume "?k'< i"
              moreover have "i < ?k"
                using Suc by auto
              ultimately have "w s i = w s ?k'"
                using Suc(1) by auto
              with `w s (Suc i) = w s i` have ?case by auto }
            ultimately show ?case by auto
          qed }
        hence "\<forall>i. ?k' < i \<and> i < ?k \<longrightarrow> w s i =  w s ?k'"
          by auto
        hence "w s (?k - 1) = w s ?k'"
          using `?k' < ?k` and `t < ?k' \<and> ?k' \<le> d`
          by (metis Suc_pred' diff_less less_SucE less_Suc_eq_0_disj less_imp_Suc_add zero_less_one)
        with `w s ?k \<noteq> w s (?k - 1)` have "w s ?k \<noteq> w s ?k'" and
          "lookup (to_transaction2 (derivative_raw w d t) s) (ks ! Suc i) = Some (w s (ks ! Suc i))" and
          "lookup (to_transaction2 (derivative_raw w d t) s) (ks ! i) = Some (w s (ks ! i))"
          using ** *** by auto }
      hence conj1: "(\<forall>i. Suc i < length ks \<longrightarrow>
              lookup (to_transaction2 (derivative_raw w d t) s) (ks ! i) \<noteq>
              lookup (to_transaction2 (derivative_raw w d t) s) (ks ! Suc i))"
        by auto
      have x_keys: "x \<in> keys (to_transaction2 (derivative_raw w d t) s)"
        using Cons(2) by (metis finite_keys insert_iff list.simps(15) sorted_list_of_set(1))
      have "t < x \<and> x \<le> d"
      proof (rule ccontr)
        assume "\<not> (t < x \<and> x \<le> d)"
        hence "x \<le> t \<or> d < x" by auto
        hence "lookup (derivative_raw w d t) x = Map.empty"
          by transfer' auto
        with x_keys show False
          by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
      qed
      have "w s x \<noteq> w s (x - 1)"
      proof (rule ccontr)
        assume "\<not> w s x \<noteq> w s (x - 1)"
        with `t < x \<and> x \<le> d` have "lookup (to_transaction2 (derivative_raw w d t) s) x = None"
          by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
        hence "x \<notin> keys (to_transaction2 (derivative_raw w d t) s)"
          unfolding in_keys_iff zero_option_def by auto
        with x_keys show False by auto
      qed
      hence **: "lookup (to_transaction2 (derivative_raw w d t) s) x = Some (w s x)"
        using `t < x \<and> x \<le> d` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
      have *: "\<forall>i. t < i \<and> i < x \<longrightarrow> w s i = w s (i-1)"
      proof (rule ccontr)
        assume "\<not> (\<forall>i. t < i \<and> i < x \<longrightarrow> w s i = w s (i-1))"
        then obtain i where "t < i" and "i < x" and "w s i \<noteq> w s (i-1)"
          by auto
        hence "i \<in> keys (to_transaction2 (derivative_raw w d t) s)"
          using `t < x \<and> x \<le> d`
          by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
        with Cons(2) have "i = x"
          by (metis \<open>i < x\<close> finite_keys_to_transaction2 leD set_ConsD set_sorted_list_of_set
          sorted.simps(2) sorted_sorted_list_of_set)
        with `i < x` show False by auto
      qed
      { fix i
        assume "t < i \<and> i < x"
        hence "w s i = w s t"
        proof (induction i)
          case 0
          then show ?case by auto
        next
          case (Suc i)
          with * have " w s (Suc i) = w s i"
            by auto
          have "t = i \<or> t < i"
            using Suc by auto
          moreover
          { assume "t = i"
            hence ?case
              using `w s (Suc i) = w s i` by auto }
          moreover
          { assume "t < i"
            moreover have "i < x"
              using Suc by auto
            ultimately have "w s i = w s t"
              using Suc(1) by auto
            with `w s (Suc i) = w s i` have ?case by auto }
          ultimately show ?case by auto
        qed }
      hence "\<forall>i. t < i \<and> i < x \<longrightarrow> w s i =  w s t"
        by auto
      hence "w s (x - 1) = w s t"
        using `t < x \<and> x \<le> d`
        by (metis Suc_pred' dual_order.order_iff_strict less_Suc_eq_le less_imp_Suc_add zero_less_Suc)
      with `w s x \<noteq> w s (x - 1)` have "w s x \<noteq> w s t"
        by auto
      hence "ks \<noteq> [] \<longrightarrow> w s t \<noteq> the (lookup (to_transaction2 (derivative_raw w d t) s) (ks ! 0))"
        using Cons(2) ks_def **  by (metis nth_Cons_0 option.sel)
      hence ?case
        using conj1 ks_def unfolding non_stuttering_def Let_def by auto }
    ultimately show ?case by auto
  qed
qed

lemma derivative_hist_raw_ensure_non_stuttering:
  "\<forall>s. non_stuttering (to_transaction2 (derivative_hist_raw w t)) def_state s"
proof
  fix s
  define ks where "ks = sorted_list_of_set (keys (to_transaction2 (derivative_hist_raw w t) s))"
  thus "non_stuttering (to_transaction2 (derivative_hist_raw w t)) def_state s"
  proof (induction ks)
    case Nil
    then show ?case
      unfolding non_stuttering_def by auto
  next
    case (Cons x xs)
    have "xs = [] \<or> xs \<noteq> []" by auto
    moreover
    { assume "xs = []"
      with Cons have li: "sorted_list_of_set (keys (to_transaction2 (derivative_hist_raw w t) s)) = [x]"
        by auto
      hence x_keys: "x \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
        by (metis empty_subsetI insert_subset list.simps(15) set_empty set_eq_subset
        set_sorted_list_of_set sorted_list_of_set.infinite)
      have "x < t"
      proof (rule ccontr)
        assume "\<not> (x < t)"
        hence "t \<le> x" by auto
        hence "lookup (derivative_hist_raw w t) x = Map.empty"
          by transfer' auto
        with x_keys show False
          by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
      qed
      have "0 < x \<or> x = 0"
        by auto
      moreover
      { assume "0 < x"
        have "w s x \<noteq> w s (x - 1)"
        proof (rule ccontr)
          assume "\<not> w s x \<noteq> w s (x - 1)"
          with `x < t` `0 < x` have "lookup (to_transaction2 (derivative_hist_raw w t) s) x = None"
            by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
          hence "x \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
            unfolding in_keys_iff zero_option_def by auto
          with x_keys show False by auto
        qed
        hence **: "lookup (to_transaction2 (derivative_hist_raw w t) s) x = Some (w s x)"
          using `0 < x` `x < t` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
        have *: "\<forall>i. 0 < i \<and> i < x \<longrightarrow> w s i = w s (i-1)"
        proof (rule ccontr)
          assume "\<not> (\<forall>i. 0 < i \<and> i < x \<longrightarrow> w s i = w s (i-1))"
          then obtain i where "0 < i" and "i < x" and "w s i \<noteq> w s (i-1)"
            by auto
          hence "i \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
            using `0 < x` `x < t`
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
          with li have "i = x"
            by (metis finite_keys_to_transaction2 list.set(1) list.simps(15) set_sorted_list_of_set
            singletonD)
          with `i < x` show False by auto
        qed
        { fix i
          assume "0 < i \<and> i < x"
          hence "w s i = w s 0"
          proof (induction i)
            case 0
            then show ?case by auto
          next
            case (Suc i)
            with * have " w s (Suc i) = w s i"
              by auto
            have "0 = i \<or> 0 < i"
              using Suc by auto
            moreover
            { assume "0 = i"
              hence ?case
                using `w s (Suc i) = w s i` by auto }
            moreover
            { assume "0 < i"
              moreover have "i < x"
                using Suc by auto
              ultimately have "w s i = w s 0"
                using Suc(1) by auto
              with `w s (Suc i) = w s i` have ?case by auto }
            ultimately show ?case by auto
          qed }
        hence "\<forall>i. 0 < i \<and> i < x \<longrightarrow> w s i =  w s 0"
          by auto
        hence "w s (x - 1) = w s 0"
          using `0 < x`  `x < t`
          by (metis Suc_pred' dual_order.order_iff_strict less_Suc_eq_le  zero_less_Suc)
        with `w s x \<noteq> w s (x - 1)` have "w s x \<noteq> w s 0"
          by auto
        moreover have "w s 0 = False"
        proof (rule ccontr)
          assume "w s 0 \<noteq> False" hence "w s 0 = True" by auto
          have "0 < t"
            using `0 < x` `x < t` by auto
          hence "lookup (to_transaction2 (derivative_hist_raw w t) s) 0 = Some True"
            using `w s 0 = True` apply transfer' unfolding to_trans_raw2_def difference_raw_def
            by auto
          hence "0 \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
            by (metis lookup_not_eq_zero_eq_in_keys option.distinct(1) zero_fun_def zero_map)
          with `0 < x` show False
            using li by (metis empty_set finite_keys list.set(2) neq0_conv singletonD sorted_list_of_set(1))
        qed
        ultimately have ?case
          using li ** unfolding non_stuttering_def by auto }
      moreover
      { assume "x = 0"
        have "0 < t"
          using `x < t` unfolding `x = 0` by auto
        have "w s x = True"
        proof (rule ccontr)
          assume "w s x \<noteq> True" hence " w s x = False" by auto
          hence "lookup (to_transaction2 (derivative_hist_raw w t) s) x = None"
            using `0 < t` unfolding `x = 0`
            by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
          with x_keys show False
            by (metis not_in_keys_iff_lookup_eq_zero zero_option_def)
        qed
        hence **: "lookup (to_transaction2 (derivative_hist_raw w t) s) x = Some (w s x)"
          using `x = 0` `x < t` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
        hence ?case
          using li `w s x = True` unfolding non_stuttering_def by auto }
      ultimately have ?case by auto }
    moreover
    { assume "xs \<noteq> []"
      hence "1 < length ks"
        using Cons(2) unfolding ks_def by (metis One_nat_def Suc_less_eq length_Cons
        length_greater_0_conv)
      { fix i
        assume "Suc i < length ks"
        hence k_keys: "ks ! Suc i \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
          unfolding ks_def using nth_mem by force
        let ?k = "ks ! Suc i"
        have "?k < t"
        proof (rule ccontr)
          assume "\<not> (?k < t)"
          hence "t \<le> ?k" by auto
          hence "lookup (derivative_hist_raw w t) ?k = Map.empty"
            by transfer' auto
          with k_keys show False
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
        qed
        let ?k' = "ks ! i"
        have k'_keys: "?k' \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
          unfolding ks_def  using `Suc i < length ks`
          by (metis (no_types, lifting) Cons.prems Suc_lessD ks_def list.distinct(1) nth_mem
          sorted_list_of_set(1) sorted_list_of_set.infinite)
        hence "?k' < ?k"
          using k_keys unfolding ks_def
          by (metis Suc_lessD \<open>Suc i < length ks\<close> distinct_sorted_list_of_set ks_def le_add2
          n_not_Suc_n nat_less_le nth_eq_iff_index_eq plus_1_eq_Suc sorted_nth_mono
          sorted_sorted_list_of_set)
        have "?k' < t"
        proof (rule ccontr)
          assume "\<not> (?k' < t)"
          hence "t \<le> ?k'" by auto
          hence "lookup (derivative_hist_raw w t) ?k' = Map.empty"
            by transfer' auto
          with k'_keys show False
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
        qed
        have "?k' = 0 \<or> 0 < ?k'" by auto
        moreover
        { assume "0 < ?k'"
          hence "0 < ?k"
            using `?k' < ?k` by auto
          have "w s ?k \<noteq> w s (?k - 1)"
          proof (rule ccontr)
            assume "\<not> w s ?k \<noteq> w s (?k - 1)"
            with `?k < t` have "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k = None"
              using `0 < ?k` by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
            hence "?k \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
              unfolding in_keys_iff zero_option_def by auto
            with k_keys show False by auto
          qed
          hence **: "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k = Some (w s ?k)"
            using `0 < ?k` `?k < t` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
          have "w s ?k' \<noteq> w s (?k' - 1)"
          proof (rule ccontr)
            assume "\<not> w s ?k' \<noteq> w s (?k' - 1)"
            with `?k' < t` have "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k' = None"
              using `0 < ?k' `by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
            hence "?k' \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
              unfolding in_keys_iff zero_option_def by auto
            with k'_keys show False by auto
          qed
          hence ***: "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k' = Some (w s ?k')"
            using `0 < ?k'` `?k' < t` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
          have *: "\<forall>i. ?k'< i \<and> i < ?k \<longrightarrow> w s i = w s (i-1)"
          proof (rule ccontr)
            assume "\<not> (\<forall>i. ?k'< i \<and> i < ?k \<longrightarrow> w s i = w s (i-1))"
            then obtain k'' where "?k'< k''" and "k'' < ?k" and "w s k'' \<noteq> w s (k''-1)"
              by auto
            hence "k'' \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
              using `?k'< ?k` `?k < t` `0 < ?k'` `?k' < t`
              by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
            hence "k'' \<in> set ks"
              unfolding ks_def by auto
            then obtain idx where "ks ! idx = k''" and "idx < length ks"
              by (meson in_set_conv_nth)
            hence "i < idx"
              using `?k' < k''` `Suc i < length ks` unfolding ks_def
              by (meson Suc_lessD leD leI sorted_iff_nth_mono sorted_sorted_list_of_set)
            moreover have "idx < Suc i"
              using `ks ! idx = k''` `k'' < ?k` `idx < length ks` unfolding ks_def
              by (meson Suc_lessD leD leI sorted_iff_nth_mono sorted_sorted_list_of_set)
            ultimately show False
              by auto
          qed
          { fix i
            assume "?k'< i \<and> i < ?k"
            hence "w s i = w s ?k'"
            proof (induction i)
              case 0
              then show ?case by auto
            next
              case (Suc i)
              with * have " w s (Suc i) = w s i"
                by auto
              have "?k'= i \<or> ?k'< i"
                using Suc by auto
              moreover
              { assume "?k'= i"
                hence ?case
                  using `w s (Suc i) = w s i` by auto }
              moreover
              { assume "?k'< i"
                moreover have "i < ?k"
                  using Suc by auto
                ultimately have "w s i = w s ?k'"
                  using Suc(1) by auto
                with `w s (Suc i) = w s i` have ?case by auto }
              ultimately show ?case by auto
            qed }
          hence "\<forall>i. ?k' < i \<and> i < ?k \<longrightarrow> w s i =  w s ?k'"
            by auto
          hence "w s (?k - 1) = w s ?k'"
            using `?k' < ?k` and `0 < ?k'` `?k' < t`
            by (metis Suc_pred' diff_less less_SucE less_Suc_eq_0_disj less_imp_Suc_add zero_less_one)
          with `w s ?k \<noteq> w s (?k - 1)` have "w s ?k \<noteq> w s ?k'" and
            "lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! Suc i) = Some (w s (ks ! Suc i))" and
            "lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! i) = Some (w s (ks ! i))"
            using ** *** by auto }
        moreover
        { assume "?k' = 0"
          hence "0 < ?k"
            using `?k' < ?k` by auto
          have "0 < t"
            using `?k' = 0` `?k' < ?k` `?k < t` by linarith
          have "w s ?k \<noteq> w s (?k - 1)"
          proof (rule ccontr)
            assume "\<not> w s ?k \<noteq> w s (?k - 1)"
            with `?k < t` have "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k = None"
              using `0 < ?k` by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
            hence "?k \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
              unfolding in_keys_iff zero_option_def by auto
            with k_keys show False by auto
          qed
          hence **: "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k = Some (w s ?k)"
            using `0 < ?k` `?k < t` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
          have "w s 0 = True"
          proof (rule ccontr)
            assume "w s 0 \<noteq> True" hence "w s 0 = False" by auto
            hence "lookup (to_transaction2 (derivative_hist_raw w t) s) 0 = None"
              using `0 < t` apply transfer' unfolding to_trans_raw2_def difference_raw_def by auto
            hence "0 \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
              by (simp add: zero_option_def)
            with `?k' = 0` show False
              using k'_keys by auto
          qed
          hence ***: "lookup (to_transaction2 (derivative_hist_raw w t) s) ?k' = Some True"
            using `0 < t` unfolding `?k' = 0` apply transfer' unfolding to_trans_raw2_def
            difference_raw_def by auto
          have *: "\<forall>i. ?k'< i \<and> i < ?k \<longrightarrow> w s i = w s (i-1)"
          proof (rule ccontr)
            assume "\<not> (\<forall>i. ?k'< i \<and> i < ?k \<longrightarrow> w s i = w s (i-1))"
            then obtain k'' where "?k'< k''" and "k'' < ?k" and "w s k'' \<noteq> w s (k''-1)"
              by auto
            hence "k'' \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
              using `?k'< ?k` `?k < t` `?k' = 0` `?k' < t`
              by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
            hence "k'' \<in> set ks"
              unfolding ks_def by auto
            then obtain idx where "ks ! idx = k''" and "idx < length ks"
              by (meson in_set_conv_nth)
            hence "i < idx"
              using `?k' < k''` `Suc i < length ks` unfolding ks_def
              by (meson Suc_lessD leD leI sorted_iff_nth_mono sorted_sorted_list_of_set)
            moreover have "idx < Suc i"
              using `ks ! idx = k''` `k'' < ?k` `idx < length ks` unfolding ks_def
              by (meson Suc_lessD leD leI sorted_iff_nth_mono sorted_sorted_list_of_set)
            ultimately show False
              by auto
          qed
          { fix i
            assume "?k'< i \<and> i < ?k"
            hence "w s i = w s ?k'"
            proof (induction i)
              case 0
              then show ?case by auto
            next
              case (Suc i)
              with * have " w s (Suc i) = w s i"
                by auto
              have "?k'= i \<or> ?k'< i"
                using Suc by auto
              moreover
              { assume "?k'= i"
                hence ?case
                  using `w s (Suc i) = w s i` by auto }
              moreover
              { assume "?k'< i"
                moreover have "i < ?k"
                  using Suc by auto
                ultimately have "w s i = w s ?k'"
                  using Suc(1) by auto
                with `w s (Suc i) = w s i` have ?case by auto }
              ultimately show ?case by auto
            qed }
          hence "\<forall>i. ?k' < i \<and> i < ?k \<longrightarrow> w s i =  w s ?k'"
            by auto
          hence "w s (?k - 1) = w s ?k'"
            using `?k' < ?k` and `?k' = 0` `?k' < t`
            by (metis Suc_pred' diff_less less_SucE zero_less_one)
          with `w s ?k \<noteq> w s (?k - 1)` have "w s ?k \<noteq> w s ?k'" and
            "lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! Suc i) = Some (w s (ks ! Suc i))" and
            "lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! i) = Some (w s (ks ! i))"
            using ** *** `w s 0 = True` `?k' = 0` by auto  }
        ultimately have "w s ?k \<noteq> w s ?k'" and
            "lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! Suc i) = Some (w s (ks ! Suc i))" and
            "lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! i) = Some (w s (ks ! i))"
          by auto }
      hence conj1: "(\<forall>i. Suc i < length ks \<longrightarrow>
              lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! i) \<noteq>
              lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! Suc i))"
        by auto
      have x_keys: "x \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
        using Cons(2) by (metis finite_keys insert_iff list.simps(15) sorted_list_of_set(1))
      have "x < t"
      proof (rule ccontr)
        assume "\<not> (x < t)"
        hence "t \<le> x" by auto
        hence "lookup (derivative_hist_raw w t) x = Map.empty"
          by transfer' auto
        with x_keys show False
          by (transfer', auto simp add: zero_option_def to_trans_raw2_def)
      qed
      have "0 < x \<or> x = 0" by auto
      moreover
      { assume "0 < x"
        have "w s x \<noteq> w s (x - 1)"
        proof (rule ccontr)
          assume "\<not> w s x \<noteq> w s (x - 1)"
          with `0 < x` `x < t` have "lookup (to_transaction2 (derivative_hist_raw w t) s) x = None"
            by (transfer', auto simp add : difference_raw_def to_trans_raw2_def)
          hence "x \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
            unfolding in_keys_iff zero_option_def by auto
          with x_keys show False by auto
        qed
        have **: "lookup (to_transaction2 (derivative_hist_raw w t) s) x = Some (w s x)"
          using `0 < x` `w s x \<noteq> w s (x - 1)` `x < t`
          by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
        have *: "\<forall>i. 0 < i \<and> i < x \<longrightarrow> w s i = w s (i-1)"
        proof (rule ccontr)
          assume "\<not> (\<forall>i. 0 < i \<and> i < x \<longrightarrow> w s i = w s (i-1))"
          then obtain i where "0 < i" and "i < x" and "w s i \<noteq> w s (i-1)"
            by auto
          hence "i \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
            using `0 < x` `x < t`
            by (transfer', auto simp add: zero_option_def to_trans_raw2_def difference_raw_def)
          with Cons(2) have "i = x"
            by (metis \<open>i < x\<close> finite_keys_to_transaction2 leD set_ConsD set_sorted_list_of_set
            sorted.simps(2) sorted_sorted_list_of_set)
          with `i < x` show False by auto
        qed
        { fix i
          assume "0 < i \<and> i < x"
          hence "w s i = w s 0"
          proof (induction i)
            case 0
            then show ?case by auto
          next
            case (Suc i)
            with * have " w s (Suc i) = w s i"
              by auto
            have "0 = i \<or> 0 < i"
              using Suc by auto
            moreover
            { assume "0 = i"
              hence ?case
                using `w s (Suc i) = w s i` by auto }
            moreover
            { assume "0 < i"
              moreover have "i < x"
                using Suc by auto
              ultimately have "w s i = w s 0"
                using Suc(1) by auto
              with `w s (Suc i) = w s i` have ?case by auto }
            ultimately show ?case by auto
          qed }
        hence "\<forall>i. 0 < i \<and> i < x \<longrightarrow> w s i =  w s 0"
          by auto
        hence "w s (x - 1) = w s 0"
          using `0 < x` `x < t`
          by (metis Suc_pred' dual_order.order_iff_strict less_Suc_eq_le  zero_less_Suc)
        with `w s x \<noteq> w s (x - 1)` have "w s x \<noteq> w s 0"
          by auto
        hence "ks \<noteq> [] \<longrightarrow> w s 0 \<noteq> the (lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! 0))"
          using Cons(2) ks_def **  by (metis nth_Cons_0 option.sel)
        moreover have "w s 0 = False"
        proof (rule ccontr)
          have "0 < t"
            using `0 < x` `x < t` by auto
          assume "w s 0 \<noteq> False" hence " w s 0 = True" by auto
          hence "lookup (to_transaction2 (derivative_hist_raw w t) s) 0 = Some True"
            using `0 < t` apply transfer' unfolding to_trans_raw2_def difference_raw_def by auto
          hence "0 \<in> keys (to_transaction2 (derivative_hist_raw w t) s)"
            by (metis not_in_keys_iff_lookup_eq_zero option.distinct(1) zero_fun_def zero_map)
          thus False
            using Cons `0 < x` by (metis finite_keys leD neq0_conv set_ConsD sorted.simps(2)
            sorted_list_of_set(1) sorted_sorted_list_of_set)
        qed
        ultimately have ?case
          using conj1 ks_def unfolding non_stuttering_def by auto }
      moreover
      { assume "x = 0"
        hence "0 < t"
          using `x < t` by auto
        have "w s 0 = True"
        proof (rule ccontr)
          assume "w s 0 \<noteq> True" hence "w s 0 = False" by auto
          hence "lookup (to_transaction2 (derivative_hist_raw w t) s) 0 = None"
            using `0 < t` by (transfer', auto simp add: to_trans_raw2_def difference_raw_def)
          hence "x \<notin> keys (to_transaction2 (derivative_hist_raw w t) s)"
            unfolding `x = 0` by (simp add: zero_option_def)
          with x_keys show False by auto
        qed
        hence "lookup (to_transaction2 (derivative_hist_raw w t) s) x = Some True"
          using `0 < t` unfolding `x = 0` apply transfer' unfolding to_trans_raw2_def difference_raw_def
          by auto
        hence "ks \<noteq> [] \<longrightarrow> False \<noteq> the (lookup (to_transaction2 (derivative_hist_raw w t) s) (ks ! 0))"
          using Cons(2) ks_def by (metis (full_types) nth_Cons_0 option.sel)
        hence ?case
          using conj1 ks_def unfolding non_stuttering_def by auto }
      ultimately have ?case by auto }
    ultimately show ?case by auto
  qed
qed

lemma worldline_deg_fixpoint_empty_trans:
  assumes "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "worldline_deg (snd (worldline2 t \<sigma> \<theta> \<tau>)) \<le> t"
  shows "\<tau> = 0"
proof (rule ccontr)
  let ?w = "worldline_deg (snd (worldline2 t \<sigma> \<theta> \<tau>))"
  assume "\<tau> \<noteq> 0"
  then obtain time sig val where "lookup \<tau> time sig = Some val"
    apply transfer' unfolding zero_fun_def zero_map zero_option_def
    by (meson not_None_eq)
  have " Rep_worldline (snd (worldline2 t \<sigma> \<theta> \<tau>)) = worldline t \<sigma> \<theta> \<tau>"
    by transfer' auto
  hence *: "\<forall>ta\<ge>?w. \<forall>s. worldline t \<sigma> \<theta> \<tau> s ta = worldline t \<sigma> \<theta> \<tau> s t"
    using property_of_degree[of "snd (worldline2 t \<sigma> \<theta> \<tau>)"] assms(3) by metis
  have "t \<le> time"
    using assms(2) unfolding context_invariant_weaker_def
    by (metis \<open>get_trans \<tau> time sig = Some val\<close> domI domIff le_less_linear zero_fun_def zero_option_def)
  have "lookup \<tau> t = 0"
    using no_mapping_at_t_if_non_stuttering2[OF assms(2) assms(1)] by auto
  hence "lookup \<tau> t sig = 0"
    by transfer' (auto simp add: zero_map zero_option_def)
  have "\<And>n. n < t \<Longrightarrow> lookup \<tau> n  = 0"
    using assms(2) unfolding context_invariant_weaker_def by auto
  hence "\<And>n. n < t \<Longrightarrow> lookup \<tau> n sig = 0"
    by (transfer', auto simp add: zero_map zero_option_def)
  define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> sig))"
  have "time \<in> keys (to_transaction2 \<tau> sig)"
    using `lookup \<tau> time sig = Some val` by (transfer', auto simp add: to_trans_raw2_def zero_option_def)
  hence "ks \<noteq> []"
    unfolding ks_def by auto
  have "ks ! 0 = time \<or> ks ! 0 \<noteq> time"
    by auto
  moreover
  { assume "ks ! 0 = time"
    hence "\<sigma> sig \<noteq> the (lookup (to_transaction2 \<tau> sig) (ks ! 0))"
      using `ks \<noteq> []` assms(1) unfolding ks_def non_stuttering_def Let_def by auto
    hence "val \<noteq> \<sigma> sig"
      using `ks ! 0 = time` `lookup \<tau> time sig = Some val` apply transfer' unfolding to_trans_raw2_def
      by auto
    hence "signal_of2 (\<sigma> sig) \<tau> sig time = val"
      using `lookup \<tau> time sig = Some val` by (meson lookup_some_signal_of2')
    hence "worldline t \<sigma> \<theta> \<tau> sig time = val"
      unfolding worldline_def using `t \<le> time` by auto
    have "t = 0 \<or> 0 < t" by auto
    moreover
    { assume "t = 0"
      hence "signal_of2 (\<sigma> sig) \<tau> sig t = signal_of2 (\<sigma> sig) \<tau> sig 0"
        by auto }
    moreover
    { assume "0 < t"
      hence " signal_of2 (\<sigma> sig) \<tau> sig t = signal_of2 (\<sigma> sig) \<tau> sig 0"
        using assms(2) unfolding context_invariant_weaker_def
        by (metis assms(1) assms(2) no_mapping_at_t_if_non_stuttering2 order.order_iff_strict signal_of2_less_ind) }
    ultimately have "signal_of2 (\<sigma> sig) \<tau> sig t = signal_of2 (\<sigma> sig) \<tau> sig 0"
      by auto
    have "lookup \<tau> 0 sig = 0"
      using `lookup \<tau> t sig = 0` \<open>\<And>n. n < t \<Longrightarrow> lookup \<tau> n sig = 0\<close>
      by (cases "t = 0") auto
    hence "signal_of2 (\<sigma> sig) \<tau> sig 0 = \<sigma> sig"
      using `lookup \<tau> t sig = 0` by (intro signal_of2_zero)
    hence "signal_of2 (\<sigma> sig) \<tau> sig t = \<sigma> sig"
      using \<open>signal_of2 (\<sigma> sig) \<tau> sig t = signal_of2 (\<sigma> sig) \<tau> sig 0\<close> by auto
    hence "worldline t \<sigma> \<theta> \<tau> sig t = \<sigma> sig"
      unfolding worldline_def by auto
    hence "worldline t \<sigma> \<theta> \<tau> sig time \<noteq> worldline t \<sigma> \<theta> \<tau> sig t"
      using `worldline t \<sigma> \<theta> \<tau> sig time = val` `val \<noteq> \<sigma> sig` by auto
    hence "False"
      using * `time \<ge> t` assms(3) le_trans by blast }
  moreover
  { assume "ks ! 0 \<noteq> time"
    then obtain itime where "ks ! itime = time" and "itime \<noteq> 0" and "itime < length ks"
      using `time \<in> keys (to_transaction2 \<tau> sig)` ks_def
      by (metis \<open>ks \<noteq> []\<close> in_set_conv_nth sorted_list_of_set(1) sorted_list_of_set.infinite)
    hence " lookup (to_transaction2 \<tau> sig) (ks ! (itime - 1)) \<noteq> lookup (to_transaction2 \<tau> sig) (ks ! itime)"
      using assms(1) unfolding non_stuttering_def ks_def Let_def
      by (metis less_one linordered_semidom_class.add_diff_inverse plus_1_eq_Suc)
    have at_least_t: "\<forall>k \<in> keys (to_transaction2 \<tau> sig). t \<le> k"
    proof (rule ccontr)
      assume "\<not> (\<forall>k \<in> keys (to_transaction2 \<tau> sig). t \<le> k)"
      then obtain k where "k \<in> keys (to_transaction2 \<tau> sig)" and "k < t"
        by auto
      with \<open>\<And>n. n < t \<Longrightarrow> lookup \<tau> n sig = 0\<close> have "lookup \<tau> k sig = None"
        by (auto simp add: zero_option_def)
      hence "k \<notin> keys (to_transaction2 \<tau> sig)"
        by (transfer', auto simp add: to_trans_raw2_def zero_option_def)
      with `k \<in> keys (to_transaction2 \<tau> sig)` show False by auto
    qed
    have "ks ! (itime - 1) \<in> keys (to_transaction2 \<tau> sig)"
      using `itime \<noteq> 0` `itime < length ks` ks_def
      by (metis Suc_lessD \<open>ks \<noteq> []\<close> less_one linordered_semidom_class.add_diff_inverse nth_mem
      plus_1_eq_Suc sorted_list_of_set(1) sorted_list_of_set.infinite)
    hence "t \<le> ks ! (itime - 1)"
      using at_least_t by auto
    obtain val and val' where "lookup (to_transaction2 \<tau> sig) (ks ! itime) = Some val" and
      "lookup (to_transaction2 \<tau> sig) (ks ! (itime - 1)) = Some val'" and "val \<noteq> val'"
    proof -
    assume a1: "\<And>val val'. \<lbrakk>lookup (to_transaction2 \<tau> sig) (ks ! itime) = Some val; lookup (to_transaction2 \<tau> sig) (ks ! (itime - 1)) = Some val'; val \<noteq> val'\<rbrakk> \<Longrightarrow> thesis"
      have f2: "ks ! (itime - 1) \<in> dom (lookup (to_transaction2 \<tau> sig))"
        by (metis (no_types) \<open>ks ! (itime - 1) \<in> keys (to_transaction2 \<tau> sig)\<close> domIff lookup_eq_zero_in_keys_contradict zero_option_def)
      have "time \<in> dom (lookup (to_transaction2 \<tau> sig))"
        by (metis \<open>time \<in> keys (to_transaction2 \<tau> sig)\<close> domIff lookup_eq_zero_in_keys_contradict zero_option_def)
      then show ?thesis
        using f2 a1 \<open>ks ! itime = time\<close> \<open>lookup (to_transaction2 \<tau> sig) (ks ! (itime - 1)) \<noteq> lookup (to_transaction2 \<tau> sig) (ks ! itime)\<close> by fastforce
    qed
    hence "get_trans \<tau> time sig = Some ((def_state(sig := val)) sig)"
      using `ks ! itime = time` apply transfer' unfolding to_trans_raw2_def by auto
    hence "signal_of2 (\<sigma> sig) \<tau> sig time = val"
      using lookup_some_signal_of2'[of "\<tau>" "time" "sig" "def_state (sig := val)" "\<sigma> sig"]
      by auto
    hence "worldline t \<sigma> \<theta> \<tau> sig time = val"
      unfolding worldline_def using `t \<le> time` by auto
    have "get_trans \<tau> (ks ! (itime - 1)) sig = Some ((def_state(sig := val')) sig)"
      using `lookup (to_transaction2 \<tau> sig) (ks ! (itime - 1)) = Some val'`
      by (transfer', auto simp add: to_trans_raw2_def)
    hence "signal_of2 (\<sigma> sig) \<tau> sig (ks ! (itime - 1)) = val'"
      using lookup_some_signal_of2'[of "\<tau>" "ks ! (itime - 1)" "sig" "def_state (sig := val')" "\<sigma> sig"]
      by auto
    hence "worldline t \<sigma> \<theta> \<tau> sig (ks ! (itime - 1)) = val'"
      unfolding worldline_def using `t \<le> ks ! (itime - 1)` by auto
    hence "worldline t \<sigma> \<theta> \<tau> sig (ks ! (itime - 1)) \<noteq> worldline t \<sigma> \<theta> \<tau> sig time"
      using `worldline t \<sigma> \<theta> \<tau> sig time = val` `val \<noteq> val'` by auto
    hence False
      using * `t \<le> time` `t \<le> ks ! (itime - 1)` assms(3)  le_trans by blast }
  ultimately show False by auto
qed

definition next_time_world :: "nat \<times> 'signal worldline2 \<Rightarrow> nat" where
  "next_time_world tw =  (let t  = fst tw; w = snd tw;
                              \<tau>  = derivative_raw (Rep_worldline w) (worldline_deg w) t
                          in
                              next_time t \<tau>)"

text \<open>In the definition of @{term "next_time_world"} above, note that after we ``differentiate''
--- perform @{term "derivative_raw"} operation which is a term borrowed from the domain of real
analysis --- the worldline, we need to remove the current transaction at time @{term "t"}. Why?

This is due to the nature of the derivative operation itself. By peeking into its definition,
there will always be a mapping posted at time @{term "t"}. If we do not remove this mapping, the
@{term "next_time"} operation performed next will always return time @{term "t"} --- because
of the @{term "Least"} operator inside the definition of @{term "next_time"} --- and we cannot
advance to the actual next time.\<close>

lemma exist_least_nonzero_sig:
  fixes t :: "nat"
  assumes "\<forall>n. n \<le> t \<longrightarrow> lookup \<tau> n = 0"
  assumes "\<tau> \<noteq> 0"
  shows "\<exists>t' sig val. t < t' \<and> lookup \<tau> t' sig = Some val \<and> (\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n sig = None)"
proof -
  obtain t' sig where *: "lookup \<tau> t' sig \<noteq> None"
    using assms(2) apply transfer' unfolding zero_fun_def zero_option_def by (metis)
  hence "t' > t"
    using assms(1) by (metis leI option.distinct(1) zero_map)
  hence **: "\<exists>t'>t . lookup \<tau> t' sig \<noteq> None"
    using * by auto
  define time where "time = (LEAST n. t < n \<and> lookup \<tau> n sig \<noteq> None)"
  hence "lookup \<tau> time sig \<noteq> None" and "time > t"
    using LeastI_ex[OF **] by auto
  have "\<forall>n > t. n < time \<longrightarrow> lookup \<tau> n sig = None"
    using not_less_Least time_def by blast
  thus ?thesis
    using `lookup \<tau> time sig \<noteq> None` `time > t`
    by blast
qed

lemma exist_least_nonzero:
  fixes \<tau> :: "'a transaction"
  assumes "\<forall>n\<le>t. lookup \<tau> n = 0"
  assumes "\<tau> \<noteq> 0"
  shows "\<exists>t'>t. lookup \<tau> t' \<noteq> 0 \<and> (\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0)"
proof -
  obtain t' where *: "lookup \<tau> t' \<noteq> 0"
    using assms(2) apply transfer' unfolding zero_fun_def zero_option_def by (metis)
  hence "t' > t"
    using assms(1)  using leI by auto
  hence **: "\<exists>t'>t. lookup \<tau> t' \<noteq> 0"
    using * by auto
  define time where "time = (LEAST n. t < n \<and> lookup \<tau> n \<noteq> 0)"
  hence "lookup \<tau> time \<noteq> 0" and "t < time"
    using LeastI_ex[OF **] by auto
  have "\<forall>n > t. n < time \<longrightarrow> lookup \<tau> n = 0"
    using not_less_Least time_def by blast
  thus ?thesis
    using `lookup \<tau> time \<noteq> 0` `time > t` by blast
qed


lemma next_time_at_most_degree:
  assumes "derivative_raw ((Rep_worldline o snd) tw) ((worldline_deg o snd) tw) (fst tw) \<noteq> 0"
  shows "next_time_world tw \<le> worldline_deg (snd tw)"
proof -
  define t where "t = fst tw"
  define w where "w = snd tw"
  define \<tau> where "\<tau> = derivative_raw (Rep_worldline w) (worldline_deg w) t"

  let ?\<sigma> = "\<lambda>s. Rep_worldline w s t"
  have "\<tau> \<noteq> 0"
    using assms unfolding \<tau>_def w_def t_def by auto
  hence "t < worldline_deg w"
    using \<tau>_def derivative_raw_zero leI by blast

  \<comment> \<open>finding explicit solution of next_time\<close>
  have *: "\<And>n. n \<le> t \<Longrightarrow> get_trans \<tau> n = 0"
    unfolding \<tau>_def apply transfer' by (auto simp add: zero_fun_def zero_option_def)
  have non_stut: "\<forall>s. non_stuttering (to_transaction2 \<tau>) ?\<sigma> s"
    using derivative_raw_ensure_non_stuttering unfolding \<tau>_def by metis
  obtain t' where "lookup \<tau> t' \<noteq> 0" and "\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0" and "t' > t"
    using exist_least_nonzero[OF _ `\<tau> \<noteq> 0`] * by blast
  obtain sig val where "lookup \<tau> t' sig = Some val"
    using `lookup \<tau> t' \<noteq> 0` apply transfer' unfolding zero_fun_def zero_map zero_option_def
    by force
  have "(LEAST n. dom (get_trans \<tau> n) \<noteq> {}) = t'"
  proof (rule Least_equality)
    show "dom (lookup \<tau> t') \<noteq> {}"
      using \<open>get_trans \<tau> t' sig = Some val\<close> by auto
  next
    { fix y
      assume "\<not> t' \<le> y" hence "y < t'" by auto
      hence "dom (lookup \<tau> y) = {}"
        using `t < t'` * `\<forall>n>t. n < t' \<longrightarrow> lookup \<tau> n = 0`
        by (metis dom_eq_empty_conv nat_less_le nat_neq_iff order_refl zero_fun_def zero_option_def) }
    thus "\<And>y. dom (get_trans \<tau> y) \<noteq> {} \<Longrightarrow> t' \<le> y "
      by auto
  qed
  hence "next_time t \<tau> = t'"
    using `\<tau> \<noteq> 0` unfolding next_time_def by auto
  hence "next_time_world tw = t'"
    unfolding next_time_world_def Let_def using t_def \<tau>_def w_def by auto
  have "t' \<le> worldline_deg w \<or> worldline_deg w < t'"
    by auto
  moreover
  { assume "t' \<le> worldline_deg w"
    hence ?thesis
      using `next_time_world tw = t'` w_def by auto }
  moreover
  { assume "worldline_deg w < t'"
    hence t'_worldline: "signal_of2 (?\<sigma> sig) (derivative_raw (Rep_worldline w) (worldline_deg w) t) sig t' = Rep_worldline w sig (worldline_deg w)"
      using signal_of2_derivative_raw2[OF order.strict_implies_order[OF `t < worldline_deg w`],
            where \<sigma>="?\<sigma>" and s'="sig" and w="Rep_worldline w" and t'="t'"]
      by auto
    have "t' - 1 < t'"
      using `worldline_deg w < t'` by linarith
    hence "worldline_deg w \<le> t' - 1"
      using `worldline_deg w  < t'` by auto
    hence "Rep_worldline w sig (t' - 1) = Rep_worldline w sig (worldline_deg w)"
      using property_of_degree by auto
    have "signal_of2 (?\<sigma> sig) \<tau> sig (t' - 1) = Rep_worldline w sig (worldline_deg w)"
      using signal_of2_derivative_raw2[where \<sigma>="?\<sigma>" and s'="sig" and w="Rep_worldline w" and d="worldline_deg w" and t'="t' - 1" and t="t"]
      \<tau>_def \<open>t < worldline_deg w\<close> \<open>worldline_deg w \<le> t' - 1\<close> order.strict_implies_order by blast
    with t'_worldline have "signal_of2 (?\<sigma> sig) \<tau> sig t' = signal_of2 (?\<sigma> sig) \<tau> sig (t' - 1)"
      using \<tau>_def by auto
    hence "lookup \<tau> t' sig = None"
      by (simp add: \<open>worldline_deg w < t'\<close> \<tau>_def derivative_raw.rep_eq)
    with `lookup \<tau> t' sig = Some val` have False by auto
    hence ?thesis
      by auto }
  ultimately show ?thesis
    by auto
qed

lemma signal_of2_not_default:
  assumes "lookup \<tau> t sig = Some (\<not> def)"
  shows "signal_of2 def \<tau> sig t \<noteq> def"
proof -
  have "inf_time (to_transaction2 \<tau>) sig t = Some t"
  proof (rule inf_time_someI)
    show "t \<in> dom (lookup (to_transaction2 \<tau> sig))"
      using assms(1) by (transfer', auto simp add: to_trans_raw2_def)
  qed auto
  hence "signal_of2 def \<tau> sig t = the (lookup (to_transaction2 \<tau> sig) t)"
    unfolding to_signal2_def comp_def by auto
  also have "... \<longleftrightarrow> \<not> def"
    using assms(1) by (transfer', auto simp add: to_trans_raw2_def)
  finally show ?thesis
    by auto
qed

lemma signal_of2_defaultE:
  assumes "signal_of2 def \<tau> sig t = def"
  shows "lookup \<tau> t sig = None \<or> lookup \<tau> t sig = Some def"
  using assms
proof (rule contrapos_pp)
  assume " \<not> (get_trans \<tau> t sig = None \<or> get_trans \<tau> t sig = Some def) "
  hence "lookup \<tau> t sig = Some (\<not> def)"
    by auto
  thus "signal_of2 def \<tau> sig t \<noteq> def"
    by (meson signal_of2_not_default)
qed

lemma next_time_world_alt_def1:
  assumes "derivative_raw ((Rep_worldline o snd) tw) ((worldline_deg o snd) tw) (fst tw) \<noteq> 0"
  shows "next_time_world tw = (LEAST n. n \<ge> fst tw \<and> (\<lambda>s. (Rep_worldline o snd) tw s (fst tw)) \<noteq> (\<lambda>s. (Rep_worldline o snd) tw s n))"
proof -
  define t where "t = fst tw"
  define w where "w = snd tw"
  define \<tau> where "\<tau> = derivative_raw (Rep_worldline w) (worldline_deg w) t"
  have non_stut: "\<forall>s. non_stuttering (to_transaction2 \<tau>) (\<lambda>s. Rep_worldline w s t) s"
    by (simp add: derivative_raw_ensure_non_stuttering \<tau>_def)
  have "\<tau> \<noteq> 0"
    using assms unfolding \<tau>_def w_def t_def by auto
  hence "next_time_world tw = next_time t \<tau>"
    unfolding next_time_world_def Let_def w_def t_def \<tau>_def by auto
  also have "... = (LEAST n. dom (get_trans \<tau> n) \<noteq> {})"
    unfolding next_time_def using `\<tau> \<noteq> 0` by auto
  finally have t'_def: "next_time_world tw = (LEAST n. dom (lookup \<tau> n) \<noteq> {})"
    by auto
  let ?t' = "next_time_world tw"
  have "\<And>n. n \<le> t \<Longrightarrow> get_trans \<tau> n = 0"
    unfolding \<tau>_def apply transfer' by (auto simp add: zero_fun_def zero_option_def)
  hence "t \<le> ?t'"
    unfolding `next_time_world tw = next_time t \<tau>`  by (simp add: next_time_at_least)
  have "\<exists>x. dom (get_trans \<tau> x) \<noteq> {}"
    using `\<tau> \<noteq> 0` apply transfer'
    by (metis dom_eq_empty_conv map_add_subsumed1 map_add_subsumed2 map_le_def zero_map)
  hence "dom (lookup \<tau> ?t') \<noteq> {}"
    unfolding `next_time_world tw = (LEAST n. dom (lookup \<tau> n) \<noteq> {})` by (rule LeastI_ex)
  hence "lookup \<tau> ?t' \<noteq> Map.empty"
    by simp
  then obtain sig val where "lookup \<tau> ?t' sig = Some val"
    by (meson not_Some_eq)
  hence non_stut_sig: "non_stuttering (to_transaction2 \<tau>) (\<lambda>s. Rep_worldline w s t) sig"
    using non_stut by auto
  have "t < worldline_deg w"
    using derivative_raw_zero[of "worldline_deg w" "t" "Rep_worldline w"] `\<tau> \<noteq> 0` \<tau>_def leI by blast
  have "(\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s (next_time_world tw))"
  proof
    let ?\<sigma> = "\<lambda>s. Rep_worldline w s t"
    assume " (\<lambda>s. Rep_worldline w s t) = (\<lambda>s. Rep_worldline w s (next_time_world tw))"
    hence "Rep_worldline w sig t = Rep_worldline w sig (next_time_world tw)"
      by metis
    moreover have helper1: "Rep_worldline w sig t = signal_of2 (?\<sigma> sig) \<tau> sig t"
    proof -
      have f1: "t \<le> worldline_deg w"
        by (meson \<open>t < worldline_deg w\<close> order.strict_implies_order)
      then have f2: "\<forall>p a. (Rep_worldline w a t \<or> p a) \<or> \<not> signal_of2 False \<tau> a t"
        by (metis (full_types) \<tau>_def signal_of2_derivative_raw_t)
      have "\<forall>a p. (signal_of2 (p a) \<tau> a t \<or> \<not> Rep_worldline w a t) \<or> \<not> p a"
        using f1 by (metis \<tau>_def signal_of2_derivative_raw_t)
      then have "(\<exists>b. b \<and> signal_of2 b \<tau> sig t) \<or> (\<exists>p. \<not> Rep_worldline w sig t \<and> \<not> p sig)"
        by auto
      then have "Rep_worldline w sig t = signal_of2 (Rep_worldline w sig t) \<tau> sig t \<or> (\<exists>p. \<not> Rep_worldline w sig t \<and> \<not> p sig)"
        by force
      then show ?thesis
        using f2 by (metis (full_types))
    qed
    moreover have " signal_of2 (?\<sigma> sig)  \<tau> sig ?t' = Rep_worldline w sig ?t'"
    proof (unfold \<tau>_def, intro signal_of2_derivative_raw)
      show "next_time_world tw \<le> worldline_deg w"
        using `\<tau> \<noteq> 0` unfolding \<tau>_def w_def t_def  by (simp add: next_time_at_most_degree)
    qed (auto simp add: `t \<le> ?t'`)
    ultimately have "signal_of2 (?\<sigma> sig) \<tau> sig t = signal_of2 (?\<sigma> sig) \<tau> sig ?t'"
      by auto
    have "t < ?t'"
    proof (rule ccontr)
      assume "\<not> t < ?t'" hence "?t' \<le> t" by auto
      hence "lookup \<tau> ?t' = 0"
        using `\<And>n. n \<le> t \<Longrightarrow> get_trans \<tau> n = 0` by auto
      with `lookup \<tau> ?t' sig = Some val` show False
        by (simp add: zero_fun_def zero_option_def)
    qed
    have "t < ?t' - 1 \<Longrightarrow> signal_of2 (?\<sigma> sig) \<tau> sig (?t' - 1) = signal_of2 (?\<sigma> sig) \<tau> sig t"
    proof (rule signal_of2_less_ind)
      have "\<forall>n. t < n \<and> n < ?t' \<longrightarrow> get_trans \<tau> n = 0"
        using t'_def \<open>next_time_world tw = next_time t \<tau>\<close> next_time_at_least2 by auto
      thus "\<And>n. t < n \<Longrightarrow> n \<le> next_time_world tw - 1 \<Longrightarrow> get_trans \<tau> n = 0"
        by auto
    qed auto
    with `t < ?t'` have "signal_of2 (?\<sigma> sig) \<tau> sig (?t' - 1) = signal_of2 (?\<sigma> sig) \<tau> sig t"
      by (metis \<tau>_def helper1 linorder_neqE_nat signal_of2_derivative_before_now)
    hence "signal_of2 (?\<sigma> sig) \<tau> sig (?t' - 1) = signal_of2 (?\<sigma> sig) \<tau> sig ?t'"
      using \<open>signal_of2 (Rep_worldline w sig t) \<tau> sig t = signal_of2 (Rep_worldline w sig t) \<tau> sig (next_time_world tw)\<close>
      by blast
    hence "lookup \<tau> ?t' sig = None"
      using \<open>t < next_time_world tw\<close> current_sig_and_prev_same non_stut_sig zero_option_def
      by fastforce
    with `lookup \<tau> ?t' sig = Some val` show False by auto
  qed
  have "(LEAST n. n \<ge> t \<and> (\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s n)) = next_time_world tw"
  proof (rule Least_equality)
    show "t \<le> next_time_world tw \<and> (\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s (next_time_world tw))"
      by (simp add: \<open>(\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s (next_time_world tw))\<close> \<open>t \<le> next_time_world tw\<close>)
  next
    { fix y
      let ?\<sigma> = "\<lambda>s. Rep_worldline w s t"
      assume "\<not> ?t' \<le> y" hence "y < ?t'" by auto
      have "y < t \<or> \<not> y < t" by auto
      moreover
      { assume "\<not> y < t" hence "t \<le> y" by auto
        have "\<And>n. t < n \<Longrightarrow> n \<le> y \<Longrightarrow> lookup \<tau> n = 0"
          using `y < ?t'` t'_def
          by (metis \<open>next_time_world tw = next_time t \<tau>\<close> le_less_trans  next_time_at_least2)
        have "\<And>s. Rep_worldline w s t = signal_of2 (?\<sigma> s) \<tau> s t"
          using `\<And>n. n \<le> t \<Longrightarrow> get_trans \<tau> n = 0`
          by (metis lookup_zero order_refl signal_of2_empty signal_of2_lookup_same)
        moreover have "\<And>s. signal_of2 (?\<sigma> s) \<tau> s y = Rep_worldline w s y"
        proof (unfold \<tau>_def, intro signal_of2_derivative_raw)
          show "y \<le> worldline_deg w"
            using \<open>\<tau> \<noteq> 0\<close> \<open>y < ?t'\<close> \<tau>_def next_time_at_most_degree t_def w_def by fastforce
        qed (auto simp add: `t \<le> y`)
        moreover have "\<And>s. signal_of2 (?\<sigma> s) \<tau> s y = signal_of2 (?\<sigma> s) \<tau> s t"
        proof (cases "t < y")
          case True
          thus "\<And>s. signal_of2 (?\<sigma> s) \<tau> s y = signal_of2 (?\<sigma> s) \<tau> s t"
            by (meson \<open>\<And>n. \<lbrakk>t < n; n \<le> y\<rbrakk> \<Longrightarrow> get_trans \<tau> n = 0\<close> signal_of2_less_ind)
        next
          case False
          with `t \<le> y` show "\<And>s. signal_of2 (?\<sigma> s) \<tau> s y = signal_of2 (?\<sigma> s) \<tau> s t"
            by auto
        qed
        ultimately have "(\<lambda>s. Rep_worldline w s t) = (\<lambda>s. Rep_worldline w s y)"
          by blast
        hence "\<not> (t \<le> y \<and> (\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s y))"
          by auto }
      moreover
      { assume "y < t"
        hence "\<not> (t \<le> y \<and> (\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s y))"
          by auto }
      ultimately have "\<not> (t \<le> y \<and> (\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s y))"
        by auto }
    thus "\<And>y. t \<le> y \<and> (\<lambda>s. Rep_worldline w s t) \<noteq> (\<lambda>s. Rep_worldline w s y) \<Longrightarrow> ?t' \<le> y"
      by auto
  qed
  thus ?thesis
    unfolding w_def t_def by auto
qed

lemma next_time_world_alt_def2:
  assumes "derivative_raw ((Rep_worldline o snd) tw) ((worldline_deg o snd) tw) (fst tw) = 0"
  shows "next_time_world tw = fst tw + 1"
  using assms  by (simp add: next_time_world_def)

lemma time_lt_degree_nonempty_trans:
  assumes "fst tw < worldline_deg (snd tw)"
  shows "derivative_raw ((Rep_worldline o snd) tw) ((worldline_deg o snd) tw) (fst tw) \<noteq> 0"
proof -
  define t where "t = fst tw"
  define w where "w = (Rep_worldline o snd) tw"
  have "\<not> (\<forall>k > t. \<forall>s. w s k = w s t)"
    using assms not_less_Least unfolding t_def w_def comp_def worldline_deg_def  by blast
  hence *: "\<exists>k. k > t \<and> (\<lambda>s. w s k) \<noteq> (\<lambda>s. w s t)"
    by meson
  define k where "k = (LEAST n. n > t \<and> (\<lambda>s. w s n) \<noteq> (\<lambda>s. w s t))"
  then obtain sig where "k > t" and "w sig k \<noteq> w sig t"
    using LeastI_ex[OF *] by auto
  have "\<forall>i>t. i < k \<longrightarrow> (\<forall>s. w s i = w s t)"
    using k_def  by (metis (mono_tags, lifting) not_less_Least)
  define d where "d = (worldline_deg o snd) tw"
  have "t < d"
    using assms unfolding t_def d_def by auto
  have "k \<le> d"
  proof (rule ccontr)
    assume "\<not> k \<le> d" hence "d < k" by auto
    hence " w sig k = w sig d"
      using property_of_degree' unfolding d_def  by (simp add: property_of_degree' w_def)
    also have "... = w sig t"
      using `t < d` \<open>\<forall>i>t. i < k \<longrightarrow> (\<forall>s. w s i = w s t)\<close> \<open>d < k\<close> by blast
    finally have " w sig k = w sig t"
      by auto
    with `w sig k \<noteq> w sig t` show False by auto
  qed
  hence "lookup (derivative_raw w d t) k = difference_raw w k"
    using lookup_derivative_in_between[OF `k > t`] by blast
  moreover have "w sig k \<noteq> w sig (k - 1)"
    by (metis Suc_diff_1 \<open>\<And>thesis. (\<And>sig. \<lbrakk>t < k; w sig k \<noteq> w sig t\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
    \<open>\<forall>i>t. i < k \<longrightarrow> (\<forall>s. w s i = w s t)\<close> \<open>w sig k \<noteq> w sig t\<close> leI le_neq_implies_less less_Suc_eq_le
    not_less_zero)
  hence "lookup (derivative_raw w d t) k sig = Some (w sig k)"
    by (smt \<open>t < k\<close> calculation difference_raw_def not_less_zero)
  hence "derivative_raw w d t \<noteq> 0"
    by (metis lookup_zero option.discI zero_fun_def zero_option_def)
  thus ?thesis
    unfolding w_def d_def t_def by auto
qed

lemma time_geq_degree_empty_trans:
  assumes "fst tw \<ge> worldline_deg (snd tw)"
  shows "derivative_raw ((Rep_worldline o snd) tw) ((worldline_deg o snd) tw) (fst tw) = 0"
  by (simp add: assms derivative_raw_zero)

lemma next_time_world_alt_def:
  "next_time_world tw = (let
                            t = fst tw; w2 = snd tw; w = Rep_worldline w2; d = worldline_deg w2
                         in
                            if t \<ge> d then t + 1 else (LEAST n. n \<ge> t \<and> (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n)))"
proof -
  define t where "t = fst tw"
  define w2 where "w2 = snd tw"
  define w where "w = Rep_worldline w2"
  define d where "d = worldline_deg w2"
  define \<tau> where "\<tau> = derivative_raw w d t"

  have "t \<ge> d \<or> t < d"
    by auto
  moreover
  { assume "t \<ge> d"
    hence "\<tau> = 0"
      by (simp add: \<tau>_def derivative_raw_zero)
    hence "next_time_world tw  = t + 1"
      by (metis \<tau>_def d_def next_time_def next_time_world_def t_def w2_def w_def)
    hence ?thesis
      using \<open>d \<le> t\<close> d_def t_def w2_def by auto }
  moreover
  { assume "t < d"
    hence "\<tau> \<noteq> 0"
      using \<tau>_def d_def time_lt_degree_nonempty_trans w_def by force
    hence "next_time_world tw = (LEAST n. n \<ge> t \<and> (\<lambda>s. w s t) \<noteq> (\<lambda>s. w s n))"
      by (simp add: \<tau>_def d_def next_time_world_alt_def1 t_def w2_def w_def)
    hence ?thesis
      using \<open>t < d\<close> d_def t_def w2_def w_def  by (metis (full_types) calculation(2)) }
  ultimately show ?thesis by auto
qed

inductive
  conc_sim :: "'signal assn2 \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal assn2 \<Rightarrow> bool"
  ("\<turnstile>\<^sub>s (\<lbrace>(1_)\<rbrace>/ (_)/ \<lbrace>(1_)\<rbrace>)" 50)
  where
While: "\<turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace> \<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>  \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>P\<rbrace>" |
Conseq_sim: "\<forall>tw. P' tw \<longrightarrow> P tw \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>tw. Q tw \<longrightarrow> Q' tw \<Longrightarrow> \<turnstile>\<^sub>s \<lbrace>P'\<rbrace> cs \<lbrace>Q'\<rbrace>"

lemma worldline_next_config:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "worldline t \<sigma> \<theta> \<tau>' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
proof (rule ext)+
  fix s' t'
  have "t' < t \<or> t \<le> t' \<and> t' < next_time t \<tau>' \<or> next_time t \<tau>' \<le> t'"
    by auto
  moreover
  { assume "t' < t"
    hence "t' < next_time t \<tau>'"
      using next_time_at_least assms unfolding context_invariant_def
      by (metis (full_types) dual_order.strict_trans leD less_linear)
    have "\<And>n. n \<le> t' \<Longrightarrow> lookup \<theta> n = lookup (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n"
      using `t' < t` unfolding add_to_beh_def
      by (cases "t < next_time t \<tau>'") (auto simp add: lookup_update)
    hence "signal_of2 False \<theta> s' t' = signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      using signal_of2_lookup_same[where maxtime="t'" and n="t'"] by (metis order_refl)
    hence "worldline t \<sigma> \<theta> \<tau>' s' t' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
      unfolding worldline_def using `t' < t` `t' < next_time t \<tau>'` by auto }
  moreover
  { assume "next_time t \<tau>' \<le> t'"
    moreover have "t \<le> next_time t \<tau>'"
      using next_time_at_least assms unfolding context_invariant_def  by auto
    ultimately have "t \<le> t'"
      by auto
    have "signal_of2 (\<sigma> s') \<tau>' s' t' =  signal_of2 (next_state t \<tau>' \<sigma> s') \<tau>' s' t'"
    proof (cases "inf_time (to_transaction2 \<tau>') s' t' = None")
      case True
      hence " \<forall>t\<in>dom (lookup (to_transaction2 \<tau>' s')). t' < t"
        by (auto elim!: inf_time_noneE)
      hence "\<forall>t. t \<le> t' \<longrightarrow> t \<notin> dom (lookup  (to_transaction2 \<tau>' s'))"
        using not_le by blast
      hence "next_time t \<tau>' \<notin> dom (lookup  (to_transaction2 \<tau>' s'))"
        using `next_time t \<tau>' \<le> t'` by auto
      hence "s' \<notin> dom (get_trans \<tau>' (next_time t \<tau>'))"
        unfolding next_time_def by (transfer', auto simp add: to_trans_raw2_def)
      hence "next_state t \<tau>' \<sigma> s' = \<sigma> s'"
        unfolding next_state_def Let_def by auto
      then show ?thesis
        using True unfolding to_signal2_def comp_def by auto
    next
      case False
      then show ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    hence "worldline t \<sigma> \<theta> \<tau>' s' t' =
         worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
      unfolding worldline_def using `t \<le> t'` and `next_time t \<tau>' \<le> t'` by auto }
  moreover
  { assume "t \<le> t' \<and> t' < next_time t \<tau>'"
    hence "t < next_time t \<tau>'"
      by auto
    have add_to_beh: "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = Poly_Mapping.update t (Some o \<sigma>) \<theta>"
      unfolding add_to_beh_def using `t < next_time t \<tau>'` by auto
    have "signal_of2 (\<sigma> s') \<tau>' s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'. get_trans \<tau>' n = 0"
        using `t < next_time t \<tau>'` next_time_at_least2 by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow> lookup \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "\<forall>t\<in>dom (lookup (to_transaction2 \<tau>' s')). t' < t"
      proof (rule ccontr)
        assume "\<not> (\<forall>t\<in>dom (lookup (to_transaction2 \<tau>' s')). t' < t)"
        then obtain time where "time \<in> dom (lookup (to_transaction2 \<tau>' s'))" and "time \<le> t'"
          using leI by blast
        hence "lookup \<tau>' time \<noteq> 0"
          by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_map zero_option_def)
        moreover have "lookup \<tau>' time = 0"
          using `\<forall>n. n \<le> t' \<longrightarrow> lookup \<tau>' n = 0` `time \<le> t'` by auto
        ultimately show False by auto
      qed
      hence "inf_time (to_transaction2 \<tau>') s' t' = None"
        by (intro inf_time_noneI)
      thus ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    moreover have "signal_of2 False (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'. get_trans \<tau>' n = 0"
        using next_time_at_least2 `t < next_time t \<tau>'` by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow> lookup \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "t \<in> dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s'))"
        by transfer' (auto simp add: to_trans_raw2_def)
      moreover have "t \<le> t'"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      moreover have "\<forall>ta\<in>dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s')). ta \<le> t' \<longrightarrow> ta \<le> t"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s')). ta \<le> t' \<longrightarrow> ta \<le> t)"
        then obtain ta where ta_dom: "ta\<in>dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s'))"  and  "ta \<le> t'" and "ta > t"
          using leI by blast
        have "lookup (to_transaction2 (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s') ta =  lookup (to_transaction2 \<theta> s') ta"
          using `ta > t` by transfer' (auto simp add: to_trans_raw2_def)
        hence "lookup \<theta> ta \<noteq> 0"
          using ta_dom by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_map zero_option_def)
        have "\<forall>n \<ge> t. lookup \<theta> n = 0"
          using assms(1) unfolding context_invariant_def by auto
        hence "lookup \<theta> ta = 0"
          using `ta > t` by auto
        with `lookup \<theta> ta \<noteq> 0` show False by auto
      qed
      ultimately have "inf_time (to_transaction2 (Poly_Mapping.update t (Some o \<sigma>) \<theta>)) s' t' = Some t"
        by (rule inf_time_someI)
      moreover have "the (lookup (to_transaction2 (Poly_Mapping.update t (\<lambda>x. Some (\<sigma> x)) \<theta>) s') t) = \<sigma> s'"
        by transfer' (auto simp add: to_trans_raw2_def)
      ultimately show ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    ultimately have "signal_of2 (\<sigma> s') \<tau>' s' t' = signal_of2 False (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s' t'"
      by auto
    hence "signal_of2 (\<sigma> s') \<tau>' s' t' = signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      unfolding add_to_beh by auto
    hence "worldline t \<sigma> \<theta> \<tau>' s' t' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
      unfolding worldline_def using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto }
  ultimately show "worldline t \<sigma> \<theta> \<tau>' s' t' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>' s' t'"
    by auto
qed

lemma worldline_next_config_next_time:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "worldline t \<sigma> \<theta> \<tau>' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')"
proof (rule ext)+
  fix s' t'
  have "t' < t \<or> t \<le> t' \<and> t' < next_time t \<tau>' \<or> next_time t \<tau>' \<le> t'"
    by auto
  moreover
  { assume "t' < t"
    hence "t' < next_time t \<tau>'"
      using next_time_at_least assms unfolding context_invariant_def
      by (metis (full_types) dual_order.strict_trans leD less_linear)
    have "\<And>n. n \<le> t' \<Longrightarrow> lookup \<theta> n = lookup (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n"
      using `t' < t` unfolding add_to_beh_def
      by (cases "t < next_time t \<tau>'") (auto simp add: lookup_update)
    hence "signal_of2 False \<theta> s' t' = signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      using signal_of2_lookup_same[where maxtime="t'" and n="t'"] by (metis order_refl)
    hence "worldline t \<sigma> \<theta> \<tau>' s' t' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>') s' t'"
      unfolding worldline_def using `t' < t` `t' < next_time t \<tau>'` by auto }
  moreover
  { assume "next_time t \<tau>' \<le> t'"
    moreover have "t \<le> next_time t \<tau>'"
      using next_time_at_least assms unfolding context_invariant_def  by auto
    ultimately have "t \<le> t'"
      by auto
    have "signal_of2 (\<sigma> s') \<tau>' s' t' =  signal_of2 (next_state t \<tau>' \<sigma> s') (rem_curr_trans (next_time t \<tau>') \<tau>') s' t'"
    proof (cases "inf_time (to_transaction2 \<tau>') s' t' = None")
      case True
      hence " \<forall>t\<in>dom (lookup (to_transaction2 \<tau>' s')). t' < t"
        by (auto elim!: inf_time_noneE)
      hence "\<forall>t. t \<le> t' \<longrightarrow> t \<notin> dom (lookup  (to_transaction2 \<tau>' s'))"
        using not_le by blast
      hence "next_time t \<tau>' \<notin> dom (lookup  (to_transaction2 \<tau>' s'))"
        using `next_time t \<tau>' \<le> t'` by auto
      hence "s' \<notin> dom (get_trans \<tau>' (next_time t \<tau>'))"
        unfolding next_time_def by (transfer', auto simp add: to_trans_raw2_def)
      hence "next_state t \<tau>' \<sigma> s' = \<sigma> s'"
        unfolding next_state_def Let_def by auto
      moreover have "inf_time (to_transaction2 (rem_curr_trans (next_time t \<tau>') \<tau>')) s' t' =
            inf_time (to_transaction2 \<tau>') s' t'"
        using True  by (simp add: inf_time_rem_curr_trans)
      ultimately show ?thesis
        using True unfolding to_signal2_def comp_def by auto
    next
      case False
      then obtain time where "inf_time (to_transaction2 \<tau>') s' t' = Some time"
        by auto
      have "time = next_time t \<tau>' \<or> time \<noteq> next_time t \<tau>'"
        by auto
      moreover
      { assume "time \<noteq> next_time t \<tau>'"
        hence "inf_time (to_transaction2 (rem_curr_trans (next_time t \<tau>') \<tau>')) s' t' =  inf_time (to_transaction2 \<tau>') s' t'"
          using `inf_time (to_transaction2 \<tau>') s' t' = Some time` by (simp add: inf_time_rem_curr_trans)
        hence ?thesis
          using `inf_time (to_transaction2 \<tau>') s' t' = Some time` `time \<noteq> next_time t \<tau>'`
          unfolding to_signal2_def comp_def  by (metis option.simps(5) trans_value_same_except_at_removed) }
      moreover
      { assume "time = next_time t \<tau>'"
        hence "inf_time (to_transaction2 \<tau>') s' t' = Some (next_time t \<tau>')"
          using `inf_time (to_transaction2 \<tau>') s' t' = Some time` by auto
        hence *: "signal_of2 (\<sigma> s') \<tau>' s' t' = the (lookup (to_transaction2 \<tau>' s') (next_time t \<tau>'))"
          unfolding to_signal2_def comp_def by auto
        have "next_time t \<tau>' \<in> dom (lookup (to_transaction2 \<tau>' s'))"
          using inf_time_someE2[OF `inf_time (to_transaction2 \<tau>') s' t' = Some (next_time t \<tau>')`]
          by auto
        hence "s' \<in> dom (get_trans \<tau>' (next_time t \<tau>'))"
          unfolding next_time_def by (transfer', auto simp add: to_trans_raw2_def)
        moreover have "the (lookup (to_transaction2 \<tau>' s') (next_time t \<tau>')) = the (get_trans \<tau>' (next_time t \<tau>') s')"
          unfolding next_time_def apply transfer' by (auto simp add: to_trans_raw2_def)
        ultimately have "the (lookup (to_transaction2 \<tau>' s') (next_time t \<tau>')) = next_state t \<tau>' \<sigma> s'"
          unfolding next_state_def Let_def by auto
        with * have "signal_of2 (\<sigma> s') \<tau>' s' t' = next_state t \<tau>' \<sigma> s'"
          by auto
        have "\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans \<tau>' n = 0"
          using next_time_at_least2 by auto
        hence "inf_time (to_transaction2 (rem_curr_trans (next_time t \<tau>') \<tau>')) s' t' = None"
          using inf_time_rem_curr_trans_at_t[OF `inf_time (to_transaction2 \<tau>') s' t' = Some (next_time t \<tau>')`]
          by auto
        hence ?thesis
          unfolding `signal_of2 (\<sigma> s') \<tau>' s' t' = next_state t \<tau>' \<sigma> s'` to_signal2_def by auto }
      ultimately show ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    hence "worldline t \<sigma> \<theta> \<tau>' s' t' =
         worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>') s' t'"
      unfolding worldline_def using `t \<le> t'` and `next_time t \<tau>' \<le> t'` by auto }
  moreover
  { assume "t \<le> t' \<and> t' < next_time t \<tau>'"
    hence "t < next_time t \<tau>'"
      by auto
    have add_to_beh: "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = Poly_Mapping.update t (Some o \<sigma>) \<theta>"
      unfolding add_to_beh_def using `t < next_time t \<tau>'` by auto
    have "signal_of2 (\<sigma> s') \<tau>' s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'. get_trans \<tau>' n = 0"
        using `t < next_time t \<tau>'` next_time_at_least2 by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow> lookup \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "\<forall>t\<in>dom (lookup (to_transaction2 \<tau>' s')). t' < t"
      proof (rule ccontr)
        assume "\<not> (\<forall>t\<in>dom (lookup (to_transaction2 \<tau>' s')). t' < t)"
        then obtain time where "time \<in> dom (lookup (to_transaction2 \<tau>' s'))" and "time \<le> t'"
          using leI by blast
        hence "lookup \<tau>' time \<noteq> 0"
          by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_map zero_option_def)
        moreover have "lookup \<tau>' time = 0"
          using `\<forall>n. n \<le> t' \<longrightarrow> lookup \<tau>' n = 0` `time \<le> t'` by auto
        ultimately show False by auto
      qed
      hence "inf_time (to_transaction2 \<tau>') s' t' = None"
        by (intro inf_time_noneI)
      thus ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    moreover have "signal_of2 False (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s' t' = \<sigma> s'"
    proof -
      have "\<forall>n<next_time t \<tau>'. get_trans \<tau>' n = 0"
        using next_time_at_least2 `t < next_time t \<tau>'` by auto
      hence "\<forall>n. n \<le> t' \<longrightarrow> lookup \<tau>' n = 0"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      have "t \<in> dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s'))"
        by transfer' (auto simp add: to_trans_raw2_def)
      moreover have "t \<le> t'"
        using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto
      moreover have "\<forall>ta\<in>dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s')). ta \<le> t' \<longrightarrow> ta \<le> t"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s')). ta \<le> t' \<longrightarrow> ta \<le> t)"
        then obtain ta where ta_dom: "ta\<in>dom (lookup (to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) s'))"  and  "ta \<le> t'" and "ta > t"
          using leI by blast
        have "lookup (to_transaction2 (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s') ta =  lookup (to_transaction2 \<theta> s') ta"
          using `ta > t` by transfer' (auto simp add: to_trans_raw2_def)
        hence "lookup \<theta> ta \<noteq> 0"
          using ta_dom by (transfer', auto simp add: to_trans_raw2_def zero_fun_def zero_map zero_option_def)
        have "\<forall>n \<ge> t. lookup \<theta> n = 0"
          using assms(1) unfolding context_invariant_def by auto
        hence "lookup \<theta> ta = 0"
          using `ta > t` by auto
        with `lookup \<theta> ta \<noteq> 0` show False by auto
      qed
      ultimately have "inf_time (to_transaction2 (Poly_Mapping.update t (Some o \<sigma>) \<theta>)) s' t' = Some t"
        by (rule inf_time_someI)
      moreover have "the (lookup (to_transaction2 (Poly_Mapping.update t (\<lambda>x. Some (\<sigma> x)) \<theta>) s') t) = \<sigma> s'"
        by transfer' (auto simp add: to_trans_raw2_def)
      ultimately show ?thesis
        unfolding to_signal2_def comp_def by auto
    qed
    ultimately have "signal_of2 (\<sigma> s') \<tau>' s' t' = signal_of2 False (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s' t'"
      by auto
    hence "signal_of2 (\<sigma> s') \<tau>' s' t' = signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s' t'"
      unfolding add_to_beh by auto
    hence "worldline t \<sigma> \<theta> \<tau>' s' t' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>') s' t'"
      unfolding worldline_def using `t \<le> t' \<and> t' < next_time t \<tau>'` by auto }
  ultimately show "worldline t \<sigma> \<theta> \<tau>' s' t' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>') s' t'"
    by auto
qed

lemma worldline2_next_config:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "(next_time t \<tau>', snd (worldline2 t \<sigma> \<theta> \<tau>')) = worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
  using assms
proof transfer
  fix t :: nat
  fix \<sigma> :: "'a \<Rightarrow> bool"
  fix \<gamma> :: "'a set"
  fix \<theta> \<tau>'
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  hence "worldline t \<sigma> \<theta> \<tau>' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
    using worldline_next_config by metis
  thus "(next_time t \<tau>', snd (t, worldline t \<sigma> \<theta> \<tau>')) = (next_time t \<tau>', worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>')"
    by auto
qed

lemma worldline2_next_config_next_time:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  shows "(next_time t \<tau>', snd (worldline2 t \<sigma> \<theta> \<tau>')) = worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')"
  using assms
proof transfer
  fix t :: nat
  fix \<sigma> :: "'a \<Rightarrow> bool"
  fix \<gamma> :: "'a set"
  fix \<theta> \<tau>'
  assume "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
  hence "worldline t \<sigma> \<theta> \<tau>' = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')"
    using worldline_next_config_next_time by metis
  thus "(next_time t \<tau>', snd (t, worldline t \<sigma> \<theta> \<tau>')) = (next_time t \<tau>', worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>'))"
    by auto
qed

lemma non_stuttering_preserved:
  assumes "context_invariant_weaker t \<sigma> \<theta> \<tau>"
  assumes "non_stuttering (to_transaction2 \<tau>) \<sigma> s"
  shows   "non_stuttering (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>)) (next_state t \<tau> \<sigma>) s"
proof (cases "\<tau> \<noteq> 0")
  case True
  define ks where "ks = sorted_list_of_set (keys (to_transaction2 \<tau> s))"
  have conj1: "\<forall>i. Suc i < length ks \<longrightarrow> lookup (to_transaction2 \<tau> s) (ks ! i) \<noteq> lookup (to_transaction2 \<tau> s) (ks ! Suc i)"
   and conj2: "ks \<noteq> [] \<longrightarrow> \<sigma> s \<noteq> the (lookup (to_transaction2 \<tau> s) (ks ! 0))"
    using assms(2) unfolding non_stuttering_def Let_def ks_def by auto
  define ks' where "ks' = sorted_list_of_set (keys (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s))"
  have keys_diff: "keys (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) =  keys (to_transaction2 \<tau> s) - {next_time t \<tau>}"
    unfolding rem_curr_trans_def to_transaction2_delete[where n="next_time t \<tau>"] keys_update by auto
  hence "ks' = remove1 (next_time t \<tau>) ks"
    unfolding ks'_def ks_def  by (simp add: sorted_list_of_set_remove)
  have exi: "\<exists>n. dom (lookup \<tau> n) \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> (\<exists>n. dom (lookup \<tau> n) \<noteq> {})" hence "\<forall>n. dom (lookup \<tau> n) = {}"
      by auto
    hence "\<tau> = 0"
      apply transfer' by (auto simp add: zero_fun_def zero_option_def)
    with `\<tau> \<noteq> 0` show False
      by auto
  qed
  have "\<forall>n < next_time t \<tau>. lookup \<tau> n = 0"
    using next_time_at_least2 by auto
  hence *: "\<And>n. n < next_time t \<tau> \<Longrightarrow> lookup (to_transaction2 \<tau> s) n = 0"
    unfolding next_time_def apply transfer' unfolding to_trans_raw2_def  by (simp add: zero_fun_def)
  have "lookup (to_transaction2 \<tau> s) (next_time t \<tau>) \<noteq> None \<or> lookup (to_transaction2 \<tau> s) (next_time t \<tau>) = None"
    by auto
  moreover
  { assume lookup: "lookup (to_transaction2 \<tau> s) (next_time t \<tau>) \<noteq> None"
    hence "next_time t \<tau> \<in> keys (to_transaction2 \<tau> s)"
      by (simp add: in_keys_iff zero_option_def)
    hence "s \<in> dom (get_trans \<tau> (next_time t \<tau>))"
      unfolding next_time_def apply transfer'
      unfolding to_trans_raw2_def by (auto simp add: zero_map zero_fun_def zero_option_def)
    have lookup_same: "the (lookup (to_transaction2 \<tau> s) (next_time t \<tau>)) = the (get_trans \<tau> (next_time t \<tau>) s)"
      unfolding next_time_def apply transfer'
      unfolding to_trans_raw2_def by (auto)
    have "ks \<noteq> []"
      using `next_time t \<tau> \<in> keys (to_transaction2 \<tau> s)` unfolding ks_def by fastforce
    moreover have "ks ! 0 = next_time t \<tau>"
      using lookup hd_of_keys[of "next_time t \<tau>" "to_transaction2 \<tau>", OF *] unfolding ks_def by auto
    ultimately have "hd ks = next_time t \<tau>"
      by (simp add:  hd_conv_nth)
    hence "ks' = tl ks"
      using `ks' = remove1 (next_time t \<tau>) ks` by (metis \<open>ks \<noteq> []\<close> hd_Cons_tl remove1.simps(2))
    hence conj1': "\<forall>i. Suc i < length ks' \<longrightarrow> lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! i) \<noteq> lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! Suc i)"
      using conj1
      by (metis Diff_iff Suc_lessD Suc_mono keys_diff hd_Cons_tl insertI1 ks'_def length_Cons
      list.sel(2) nth_mem nth_tl sorted_list_of_set(1) sorted_list_of_set.infinite
      trans_value_same_except_at_removed)
    { assume "ks' \<noteq> []"
      hence "ks' ! 0 = ks ! 1"
        using `ks' = tl ks`  using nth_tl by fastforce
      have "ks ! 0 \<noteq> ks ! 1"
        using `ks \<noteq> []` `ks' = tl ks` `ks' \<noteq> []` conj1
        by (metis One_nat_def length_greater_0_conv length_tl zero_less_diff)
      have "the (lookup (to_transaction2 \<tau> s) (next_time t \<tau>)) = next_state t \<tau> \<sigma> s"
        using lookup_same `s \<in> dom (get_trans \<tau> (next_time t \<tau>))` unfolding next_state_def Let_def
        by auto
      have "next_state t \<tau> \<sigma> s \<noteq> the (lookup (to_transaction2 \<tau> s) (ks' ! 0))"
        by (smt One_nat_def \<open>ks ! 0 = next_time t \<tau>\<close> \<open>ks \<noteq> []\<close> \<open>ks' ! 0 = ks ! 1\<close> \<open>ks' = tl ks\<close> \<open>ks' \<noteq> []\<close>
        \<open>the (lookup (to_transaction2 \<tau> s) (next_time t \<tau>)) = next_state t \<tau> \<sigma> s\<close> conj1 ks_def
        length_greater_0_conv length_tl not_in_keys_iff_lookup_eq_zero nth_mem option.expand
        sorted_list_of_set(1) sorted_list_of_set.infinite zero_less_diff zero_option_def)
      hence "next_state t \<tau> \<sigma> s \<noteq> the (lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! 0))"
        by (metis \<open>ks ! 0 = next_time t \<tau>\<close> \<open>ks ! 0 \<noteq> ks ! 1\<close> \<open>ks' ! 0 = ks ! 1\<close>
        trans_value_same_except_at_removed) }
    hence "ks' \<noteq> [] \<longrightarrow> next_state t \<tau> \<sigma> s \<noteq> the (lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! 0))"
      by auto
    with conj1' have ?thesis
      using ks'_def unfolding non_stuttering_def by auto }
  moreover
  { assume lookup: "lookup (to_transaction2 \<tau> s) (next_time t \<tau>) = None"
    hence "next_time t \<tau> \<notin> keys (to_transaction2 \<tau> s)"
      by (simp add: in_keys_iff zero_option_def)
    hence "s \<notin> dom (get_trans \<tau> (next_time t \<tau>))"
      unfolding next_time_def apply transfer'
      unfolding to_trans_raw2_def by (auto simp add: zero_map zero_fun_def zero_option_def)
    have "next_time t \<tau> \<notin> set ks"
      using `next_time t \<tau> \<notin> keys (to_transaction2 \<tau> s)` unfolding ks_def by simp
    hence "ks' = ks"
      using `ks' = remove1 (next_time t \<tau>) ks` by (simp add: remove1_idem)
    hence conj1': "(\<forall>i. Suc i < length ks' \<longrightarrow>
            lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! i) \<noteq> lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! Suc i))"
      using conj1 by (metis Suc_lessD \<open>next_time t \<tau> \<notin> set ks\<close> in_set_conv_nth trans_value_same_except_at_removed)
    have "next_state t \<tau> \<sigma> s = \<sigma> s"
      unfolding next_state_def Let_def using `s \<notin> dom (get_trans \<tau> (next_time t \<tau>))`
      by auto
    hence conj2': "ks' \<noteq> [] \<longrightarrow> next_state t \<tau> \<sigma> s \<noteq> the (lookup (to_transaction2 (rem_curr_trans (next_time t \<tau>) \<tau>) s) (ks' ! 0))"
      using conj2 `ks' = ks` by (metis \<open>next_time t \<tau> \<notin> keys (to_transaction2 \<tau> s)\<close> ks_def
      length_greater_0_conv nth_mem set_sorted_list_of_set sorted_list_of_set.infinite
      trans_value_same_except_at_removed)
    have ?thesis
      using conj1' conj2' ks'_def unfolding non_stuttering_def by auto }
  ultimately show ?thesis
    by auto
next
  case False hence "\<tau> = 0" by auto
  have "lookup \<tau> t = 0"
    using False by auto
  have ntime: "next_time t \<tau> = t + 1"
    using `\<tau> = 0` unfolding next_time_def by auto
  hence nstate: "next_state t \<tau> \<sigma> = \<sigma>"
    unfolding next_state_def Let_def using `\<tau> = 0` by auto
  hence nevent: "next_event t \<tau> \<sigma> = {}"
    unfolding next_event_alt_def by auto
  have nhist: "add_to_beh \<sigma> \<theta> t (next_time t \<tau>) = Poly_Mapping.update t (Some o \<sigma>) \<theta>"
    unfolding add_to_beh_def using `next_time t \<tau> = t + 1` by auto
  have ntrans: "rem_curr_trans (next_time t \<tau>) \<tau> = \<tau>"
    using `lookup \<tau> t = 0` `next_time t \<tau> = t + 1` unfolding rem_curr_trans_def
    by (metis `\<tau> = 0` aux lookup_update)
  show ?thesis
    unfolding ntrans nstate using assms by auto
qed

lemma while_soundness:
  assumes "\<Turnstile> \<lbrace>\<lambda>tw. P tw \<rbrace> cs \<lbrace> \<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>"
  assumes "tw, cs \<Rightarrow>\<^sub>S tw'"
  assumes "P tw"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows   "P tw'"
proof -
  obtain t \<sigma> \<gamma> \<theta> \<tau> tres where des: "destruct_worldline tw = (t, \<sigma>, \<gamma>, \<theta>, \<tau>)" and
  sim: "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> tres" and   woh: "tw' = (fst tres, worldline_of_history (snd tres))"
    using premises_of_world_sim[OF assms(2)] by blast
  have tau_def: "\<tau> = derivative_raw (Rep_worldline (snd tw)) (worldline_deg (snd tw)) (fst tw)" and
      sigma_def: "\<sigma> = (\<lambda>s. Rep_worldline (snd tw) s (fst tw))" and
      theta_def: "\<theta> = derivative_hist_raw (Rep_worldline (snd tw)) (fst tw)" and
      gamma_def: "\<gamma> = {s. Rep_worldline (snd tw) s (fst tw) \<noteq> signal_of2 False (derivative_hist_raw (Rep_worldline (snd tw)) (fst tw)) s (fst tw - 1)}"
    using des unfolding destruct_worldline_def Let_def by auto
  have non_stut: "\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s"
    using derivative_raw_ensure_non_stuttering unfolding tau_def sigma_def by metis
  have "tw = worldline2 t \<sigma> \<theta> \<tau>" and "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
    using worldline2_constructible[OF des] by auto
  with sim show ?thesis
    using woh assms(1) assms(3-5) non_stut gamma_def
  proof (induction arbitrary: tw rule:b_simulate_inf.induct)
    case (1 \<tau> \<gamma> t \<sigma> \<theta> cs \<tau>' tres)
    hence "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
      unfolding context_invariant_def by auto
    have "Rep_worldline (snd tw) = worldline t \<sigma> \<theta> \<tau>"
      using 1(5-6) by transfer' auto
    have "\<not> world_quiet tw \<or> world_quiet tw" by auto
    moreover
    { assume "\<not> world_quiet tw"
      obtain tw_conc where "tw, cs \<Rightarrow>\<^sub>c tw_conc" by auto
      with `P tw` `\<not> world_quiet tw` have "P (next_time_world tw_conc, snd tw_conc)"
        using 1(8) unfolding conc_hoare_valid_def by blast
      have "fst tw = fst tw_conc"
        using fst_world_conc_exec `tw, cs \<Rightarrow>\<^sub>c tw_conc` by metis
      have "world_conc_exec tw cs = tw_conc"
        using world_conc_exec_rem_curr_trans_eq[OF 1(10-11)] `tw, cs \<Rightarrow>\<^sub>c tw_conc` by auto
      have " get_trans \<tau> t = 0"
        using no_mapping_at_t_if_non_stuttering2[OF ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`] `\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s`]
        by auto
      hence "t < next_time t \<tau>'"
        using  nonneg_delay_conc_next_time_strict[OF _ `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` `nonneg_delay_conc cs` `conc_stmt_wf cs`]
        \<open>\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0\<close> dual_order.order_iff_strict by auto
      have ci: "context_invariant (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')"
        using context_invariant_new[OF 1(6) 1(2) 1(10-11) `lookup \<tau> t  = 0`] by auto
      obtain time sigma gamma theta tau where dw_def: "destruct_worldline tw = (time, sigma, gamma, theta, tau)"
        using destruct_worldline_exist by blast
      hence  "time = t" and "sigma = \<sigma>" and "gamma = \<gamma>" and
             same_beh: "\<And>k s. signal_of2 False \<theta> s k = signal_of2 False theta s k"  and
             same_trans: "\<And>k s. signal_of2 (\<sigma> s) \<tau> s k = signal_of2 (\<sigma> s) tau s k"
        using destruct_worldline_correctness[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]
        unfolding `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
      moreover have "tau = \<tau>"
        using dw_def unfolding destruct_worldline_def Let_def `tw = worldline2 t \<sigma> \<theta> \<tau>`
        using derivative_raw_of_worldline2[OF ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`] 1(12)]
        by auto
      ultimately have "destruct_worldline tw = (t, \<sigma>, \<gamma>, theta, \<tau>)"
        using dw_def by auto
      hence "context_invariant t \<sigma> \<gamma> theta \<tau>"
        using worldline2_constructible by blast
      hence "context_invariant_weaker t \<sigma> theta \<tau>"
        by (auto elim!: ci_implies_ci_weaker)
      obtain tau' where "t, \<sigma>, \<gamma>, theta \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c tau'"
        by auto
      hence "\<And>s' t'. signal_of2 (\<sigma> s') \<tau>' s' t' = signal_of2 (\<sigma> s') tau' s' t'"
        using helper_b_conc[OF 1(2) same_beh _ `t, \<sigma>, \<gamma>, theta \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c tau'`
        ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`] `context_invariant_weaker t \<sigma> theta \<tau>`
        `nonneg_delay_conc cs`]  by auto
      hence "worldline t \<sigma> \<theta> \<tau>' = worldline t \<sigma> theta tau'"
        unfolding worldline_def using same_beh by auto
      hence "worldline2 t \<sigma> \<theta> \<tau>' = worldline2 t \<sigma> theta tau'"
        by transfer' auto
      also have "... = tw_conc"
        using `world_conc_exec tw cs = tw_conc` unfolding world_conc_exec_def Let_def
        using `destruct_worldline tw = (t, \<sigma>, \<gamma> , theta, \<tau>)`
        by (simp add: \<open>t , \<sigma> , \<gamma> , theta \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c tau'\<close>)
      finally have "worldline2 t \<sigma> \<theta> \<tau>' = tw_conc"
        by auto
      hence "fst tw_conc = t"
        by transfer' auto
      have "Rep_worldline (snd tw_conc) = worldline t \<sigma> \<theta> \<tau>'"
        using `worldline2 t \<sigma> \<theta> \<tau>' = tw_conc` by transfer' auto
      have "context_invariant t \<sigma> \<gamma> \<theta> \<tau>'"
        using b_conc_exec_preserves_context_invariant[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` 1(2) `nonneg_delay_conc cs`]
        by auto
      hence "\<And>n. n < t \<Longrightarrow> lookup \<tau>' n = 0"
        unfolding context_invariant_def by auto
      have "\<forall>s. non_stuttering (to_transaction2 \<tau>') \<sigma> s"
        using b_conc_exec_preserves_non_stuttering[OF `t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`]
        rem_curr_trans_preserve_trans_removal[OF `\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0`]
        `nonneg_delay_conc cs` `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` `\<forall>s. non_stuttering (to_transaction2 \<tau>) \<sigma> s`
        `conc_stmt_wf cs` \<open>\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0\<close> ci_implies_ci_weaker
        by blast
      have "next_time_world tw_conc = next_time t \<tau>'"
        unfolding next_time_world_def Let_def `Rep_worldline (snd tw_conc) = worldline t \<sigma> \<theta> \<tau>'`
        using derivative_raw_of_worldline[OF ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'`]] `\<forall>s. non_stuttering (to_transaction2 \<tau>') \<sigma> s`
        unfolding world_quiet_def worldline_deg_def `fst tw = fst tw_conc` `Rep_worldline (snd tw_conc) = worldline t \<sigma> \<theta> \<tau>'`
        by (simp add: \<open>fst tw_conc = t\<close>)
      hence twc: "(next_time_world tw_conc, snd tw_conc) =
               worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')"
        using `worldline2 t \<sigma> \<theta> \<tau>' = tw_conc` worldline2_next_config_next_time[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'`]
        by auto
      moreover have " \<forall>s. non_stuttering (to_transaction2 (rem_curr_trans (next_time t \<tau>') \<tau>')) (next_state t \<tau>' \<sigma>) s"
        using non_stuttering_preserved[OF ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'`] _ ]
        `\<forall>s. non_stuttering (to_transaction2 \<tau>') \<sigma> s` by auto
      moreover have "next_event t \<tau>' \<sigma> = {s. Rep_worldline (snd (next_time_world tw_conc, snd tw_conc)) s (fst (next_time_world tw_conc, snd tw_conc)) \<noteq>
        signal_of2 False (derivative_hist_raw (Rep_worldline (snd (next_time_world tw_conc, snd tw_conc))) (fst (next_time_world tw_conc, snd tw_conc))) s
         (fst (next_time_world tw_conc, snd tw_conc) - 1)}" (is "_ = ?complex")
      proof -
        have "?complex = {s. Rep_worldline (snd tw_conc) s (next_time_world tw_conc) \<noteq>
        signal_of2 False (derivative_hist_raw (Rep_worldline (snd tw_conc)) (next_time_world tw_conc)) s
         (next_time_world tw_conc - 1)}"
          by auto
        also have "... = {s. worldline t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') \<noteq>
                             signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>') (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
          using `Rep_worldline (snd tw_conc) = worldline t \<sigma> \<theta> \<tau>'` `next_time_world tw_conc = next_time t \<tau>'`
          by auto
        also have "... = {s. worldline t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') \<noteq>  signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
        proof -
          have 0: "(Rep_worldline \<circ> snd) (worldline2 t \<sigma> \<theta> \<tau>') = worldline t \<sigma> \<theta> \<tau>'"
            by transfer' auto
          have *: "... = worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>') "
            using worldline_next_config_next_time[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'`] by auto
          have **: "(Rep_worldline \<circ> snd) (worldline2 (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')) =
                worldline (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (rem_curr_trans (next_time t \<tau>') \<tau>')"
            by transfer' auto
          have "\<And>s. signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>') (next_time t \<tau>')) s (next_time t \<tau>' - 1) =
                     signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)"
            using hist_of_worldline[OF ci_implies_ci_weaker[OF ci]]  unfolding ** sym[OF *] by auto
          thus ?thesis
            by auto
        qed
        also have "... = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1)}"
        proof -
          have "t \<le> next_time t \<tau>'"
            using next_time_at_least[OF `\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0`] by auto
          hence "\<And>s. worldline t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') = signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>')"
            unfolding worldline_def by auto
          moreover have "\<And>s. signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
          proof -
            fix s
            have "s \<in> (dom (get_trans \<tau>' (next_time t \<tau>'))) \<or> s \<notin> (dom (get_trans \<tau>' (next_time t \<tau>')))"
              by auto
            moreover
            { assume s_dom: "s \<in> dom (get_trans \<tau>' (next_time t \<tau>'))"
              then obtain val where lookup: "lookup \<tau>' (next_time t \<tau>') s = Some val"
                by auto
              hence "next_state t \<tau>' \<sigma> s = val"
                unfolding next_state_def Let_def using s_dom by auto
              also have "... = signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>')"
                using lookup_some_signal_of2' lookup by fastforce
              finally have "signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
                by auto }
            moreover
            { have "lookup \<tau> t s = 0"
                using `lookup \<tau> t  = 0` by transfer' (auto simp add: zero_map zero_option_def)
              have "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n  = 0"
                using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>'` unfolding context_invariant_def by auto
              assume s_not_dom: "s \<notin> dom (get_trans \<tau>' (next_time t \<tau>'))"
              hence "next_state t \<tau>' \<sigma> s = \<sigma> s"
                unfolding next_state_def Let_def by auto
              have "\<And>n. n < t \<Longrightarrow> lookup \<tau>' n s = 0"
                using s_not_dom \<open>\<And>n. n < t \<Longrightarrow> lookup \<tau>' n = 0\<close>  by (simp add: zero_fun_def)
              have "\<And>n. t < n \<Longrightarrow> n < next_time t \<tau>' \<Longrightarrow> lookup \<tau>' n = 0"
                using next_time_lookup_zero by auto
              hence "\<And>n. t < n \<Longrightarrow> n \<le> next_time t \<tau>' \<Longrightarrow> lookup \<tau>' n s = 0"
                using s_not_dom by (metis (full_types) domIff nat_less_le zero_fun_def zero_map)
              hence "signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>') = signal_of2 (\<sigma> s) \<tau>' s t"
                by (metis \<open>t \<le> next_time t \<tau>'\<close> le_neq_implies_less signal_of2_less_ind')
              also have "... = signal_of2 (\<sigma> s) \<tau>' s 0"
                by (metis \<open>\<forall>s. non_stuttering (to_transaction2 \<tau>') \<sigma> s\<close> \<open>context_invariant t \<sigma> \<gamma> \<theta> \<tau>'\<close>
                ci_implies_ci_weaker context_invariant_weaker_def le_neq_implies_less
                less_nat_zero_code linorder_neqE_nat no_mapping_at_t_if_non_stuttering2
                signal_of2_less_ind)
              also have "... = \<sigma> s"
                by (metis \<open>get_trans \<tau> t = 0\<close> \<open>get_trans \<tau> t s = 0\<close> domIff le0 le_neq_implies_less
                next_time_at_least2 s_not_dom signal_of2_zero zero_map)
              finally have "signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>') = \<sigma> s"
                by auto
              hence "signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
                using \<open>next_state t \<tau>' \<sigma> s = \<sigma> s\<close> by blast }
            ultimately show " signal_of2 (\<sigma> s) \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
              by auto
          qed
          ultimately have "\<And>s. worldline t \<sigma> \<theta> \<tau>' s (next_time t \<tau>') = next_state t \<tau>' \<sigma> s"
            by auto
          thus ?thesis by auto
        qed
        also have "... = {s. next_state t \<tau>' \<sigma> s \<noteq> \<sigma> s}"
        proof -
          have "t \<le> next_time t \<tau>'"
            using \<open>\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0\<close> next_time_at_least by blast
          moreover have "\<And>n. t \<le> n \<Longrightarrow> lookup \<theta> n = 0"
            using `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` unfolding context_invariant_def by auto
          ultimately have "\<And>s n. t < n \<Longrightarrow> n \<le> next_time t \<tau>' - 1 \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n s = 0"
            unfolding add_to_beh_def by (simp add: lookup_update zero_fun_def)
          hence "t \<le> next_time t \<tau>' - 1"
            using `t < next_time t \<tau>'` by auto
          { fix s
            have "signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) =
                  signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s t"
              using `t \<le> next_time t \<tau>' - 1`
              by (metis (full_types) \<open>\<And>s n. \<lbrakk>t < n; n \<le> next_time t \<tau>' - 1\<rbrakk> \<Longrightarrow> get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n s = 0\<close> le_neq_implies_less signal_of2_less_ind')
            also have "... =  signal_of2 False (Poly_Mapping.update t (Some o \<sigma>) \<theta>) s t"
              using `t < next_time t \<tau>'` unfolding add_to_beh_def by auto
            also have "... = \<sigma> s"
              by (meson lookup_some_signal_of2 lookup_update)
            finally have "signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) = \<sigma> s"
              by auto }
          hence "\<And>s. signal_of2 False (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s (next_time t \<tau>' - 1) = \<sigma> s"
            by auto
          thus ?thesis by auto
        qed
        also have "... = next_event t \<tau>' \<sigma>"
          unfolding next_event_alt_def by auto
        finally show ?thesis by auto
      qed
      ultimately have ?case
        using 1(4)[OF twc ci 1(7-8) _ 1(10-11)] `P (next_time_world tw_conc, snd tw_conc)`  by auto }
    moreover
    { assume "world_quiet tw"
      hence "fst tw > worldline_deg (snd tw)"
        unfolding world_quiet_def by auto
      hence "\<tau> = 0"
        using worldline_deg_fixpoint_empty_trans[OF `\<forall>a. non_stuttering (to_transaction2 \<tau>) \<sigma> a`
        ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]] `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
      have unfold1: "Rep_worldline (snd tw) = worldline t \<sigma> \<theta> \<tau>"
        using `tw = worldline2 t \<sigma> \<theta> \<tau>` by transfer' auto
      moreover have unfold2: "fst tw = t"
        using `tw = worldline2 t \<sigma> \<theta> \<tau>`  by transfer' auto
      ultimately have "\<gamma> = {s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1)}"
        using 1(13) by auto
      moreover have "\<And>s. signal_of2 False (derivative_hist_raw (worldline t \<sigma> \<theta> \<tau>) t) s (t - 1) = signal_of2 False \<theta> s (t - 1)"
        using hist_of_worldline[OF ci_implies_ci_weaker[OF `context_invariant t \<sigma> \<gamma> \<theta> \<tau>`]]
        unfold1 unfold2 "1.prems"(1) by auto
      ultimately have g_def: "\<gamma> = {s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> signal_of2 False \<theta> s (t - 1)}"
        by auto
      have "0 < t"
        using `fst tw = t` `fst tw > worldline_deg (snd tw)` by auto
      hence "\<And>s. signal_of2 False \<theta> s (t - 1) = worldline t \<sigma> \<theta> \<tau> s (t - 1)"
        unfolding worldline_def by auto
      hence "\<gamma> = {s. worldline t \<sigma> \<theta> \<tau> s t \<noteq> worldline t \<sigma> \<theta> \<tau> s (t - 1)}"
        unfolding g_def by auto
      moreover have "\<forall>k\<ge>worldline_deg (snd tw). \<forall>s. worldline t \<sigma> \<theta> \<tau> s k = worldline t \<sigma> \<theta> \<tau> s (worldline_deg (snd tw))"
        using property_of_degree unfold1 by fastforce
      ultimately have "\<gamma> = {}"
        using `fst tw = t` `fst tw > worldline_deg (snd tw)` by (smt Collect_cong diff_diff_cancel
        diff_le_mono2 empty_def le_cases3 less_imp_le_nat less_one zero_less_diff)
      hence "quiet \<tau> \<gamma>"
        using `\<tau> = 0` unfolding quiet_def by auto
      with `\<not> quiet \<tau> \<gamma>` have False by auto
      hence ?case by auto }
    ultimately show ?case by auto
  next
    case (2 \<tau> \<gamma> t \<sigma> \<theta> res cs)
    have "worldline2 t \<sigma> \<theta> \<tau> = (t, worldline_of_history res)"
    proof
      show "fst (worldline2 t \<sigma> \<theta> \<tau>) = fst (t, worldline_of_history res)"
        using `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
    next
      have "worldline t \<sigma> \<theta> \<tau> = signal_of2 False res"
      proof (intro ext)+
        fix s' t'
        have "t' < t \<or> t \<le> t'" by auto
        moreover
        { assume "t' < t"
          hence *: "\<And>n. n < t \<Longrightarrow> lookup (to_transaction2 (Poly_Mapping.update t (\<lambda>x. Some (\<sigma> x)) \<theta>) s') n =
                                lookup (to_transaction2 \<theta> s') n"
            by (transfer', auto simp add:to_trans_raw2_def)
          hence "inf_time (to_transaction2 (Poly_Mapping.update t (\<lambda>x. Some (\<sigma> x)) \<theta>)) s' t' =
                 inf_time (to_transaction2 \<theta>) s' t'"
            by (meson \<open>t' < t\<close> inf_time_when_lookups_same_strict)
          hence "signal_of2 False res s' t' = signal_of2 False \<theta> s' t'"
            unfolding 2(2)[THEN sym] to_signal2_def comp_def using `t' < t`
            by (smt * inf_time_at_most le_less_trans not_None_eq option.case_eq_if option.sel)
          hence " worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 False res s' t'"
            unfolding worldline_def using `t' < t` by auto }
        moreover
        { assume "t \<le> t'"
          have "\<tau> = 0"
            using `quiet \<tau> \<gamma>` unfolding quiet_def by meson
          hence inf_none: "inf_time (to_transaction2 \<tau>) s' t' = None"
            unfolding inf_time_def by (auto simp add: zero_fun_def)
          have *: "keys (to_transaction2 res s') = insert t (keys (to_transaction2 \<theta> s'))"
            unfolding 2(2)[THEN sym]  by (transfer', auto simp add: to_trans_raw2_def zero_option_def)
          have "(\<forall>n\<ge>t. get_trans \<theta> n = 0)"
            using 2(4) unfolding context_invariant_def by auto
          hence **: " \<forall>k\<in> (keys (to_transaction2 \<theta> s')). k < t"
            apply transfer' unfolding to_trans_raw2_def
            by (metis (mono_tags, lifting) le_less_linear mem_Collect_eq zero_fun_def)
          moreover have "finite (keys (to_transaction2 \<theta> s'))"
            using finite_keys by auto
          ultimately have "sorted_list_of_set (keys (to_transaction2 res s')) =
                           sorted_list_of_set (keys (to_transaction2 \<theta> s')) @ [t]"
            unfolding *  using sorted_list_insert by blast
          hence "inf_time (to_transaction2 res) s' t' = Some t"
            unfolding inf_time_def  using inf_key_snoc[OF `t \<le> t'`] **
            by (simp add: less_imp_le_nat)
          moreover have "the (lookup (to_transaction2 res s') t) = \<sigma> s'"
            using 2(2) apply transfer' unfolding to_trans_raw2_def by auto
          ultimately have "signal_of2 (\<sigma> s') \<tau> s' t' = signal_of2 False res s' t'"
            using inf_none unfolding to_signal2_def comp_def by auto
          hence " worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 False res s' t'"
            unfolding worldline_def using `t \<le> t'` by auto }
        ultimately show "worldline t \<sigma> \<theta> \<tau> s' t' = signal_of2 False res s' t'"
          by auto
      qed
      thus "snd (worldline2 t \<sigma> \<theta> \<tau>) = snd (t, worldline_of_history res)"
        by transfer' auto
    qed
    also have "... = tw'"
      using 2 by auto
    finally have "tw = tw'"
      using `tw = worldline2 t \<sigma> \<theta> \<tau>` by auto
    then show ?case
      using `P tw` by auto
  qed
qed

lemma conc_sim_soundness:
  assumes "\<turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows "\<Turnstile>\<^sub>s \<lbrace>P\<rbrace> cs \<lbrace>Q\<rbrace>"
  using assms
proof (induction rule:conc_sim.induct)
  case (While P cs)
  hence " \<Turnstile> \<lbrace>\<lambda>tw. P tw\<rbrace> cs \<lbrace>\<lambda>tw. P (next_time_world tw, snd tw)\<rbrace>"
    using soundness_conc_hoare[OF While(1)] by auto
  then show ?case
    unfolding sim_hoare_valid_def using while_soundness[OF _ _ _ While(2) While(3)] by auto
next
  case (Conseq_sim P' P cs Q Q')
  then show ?case by (metis (full_types) sim_hoare_valid_def)
qed

end