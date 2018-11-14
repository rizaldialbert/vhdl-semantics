(*
 * Copyright 2018, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore 
 *)

theory Femto_VHDL_Executable
  imports Femto_VHDL
          "Polynomials.Poly_Mapping_Finite_Map"
begin

datatype sig = A | B | C

notation (output) A  ("A")
notation (output) B  ("B")
notation (output) C  ("C")

lemma UNIV_sig:
  "UNIV = {A, B, C}"
  by (auto intro: sig.exhaust)

instantiation sig :: enum
begin

definition enum_sig where
  "enum_sig = [A, B, C]"

definition enum_all_sig where
  "enum_all_sig P \<longleftrightarrow> P A \<and> P B \<and> P C"

definition enum_ex_sig where
  "enum_ex_sig P \<longleftrightarrow> P A \<or> P B \<or> P C"

instance proof
qed (simp_all only: enum_sig_def enum_all_sig_def enum_ex_sig_def UNIV_sig, simp_all)
end

lemma zero_map:
  "(0 :: 'a \<rightharpoonup> 'b) x = None"
  by (auto simp add:zero_option_def zero_fun_def)

lemma zero_upd:
  "0 (sig := None) = 0"
  by (auto simp add:zero_map zero_option_def)

value [code] "signals_in (Bassign_trans C Btrue 0)"
value [code] "beval 0 def_state {} 0 (Bsig A)"
value [code] "beval 0 def_state {} 0 (Band (Bsig A) (Bsig B))"

definition
  "test_beh = Pm_fmap (fmap_of_list [(1 :: nat, [A \<mapsto> True, B \<mapsto> False, C \<mapsto> True])])"

lemma lookup0_fmdrop:
  "lookup0 (fmdrop x xa) = map_drop x (lookup0 xa)"
  by (auto simp add: fmlookup_default_def Finite_Map.map_filter_def map_drop_def zero_option_def  
              split: option.splits)

lemma lookup0_fmupd:
  "lookup0 (fmupd a b m) a' = (if a = a' then b else lookup0 m a')"
  by (simp add: fmlookup_default_def)

(* TODO : streamline this proof; applying auto in the middle is ugly *)
lemma lookup0_update_with_none:
  "(lookup0 xs)(time := (lookup0 xs time)(sig := None)) = 
    lookup0 (fmupd time (map_drop sig (lookup0 xs time)) xs)"
  apply (auto simp add: fmlookup_default_def Finite_Map.map_filter_def map_drop_def zero_option_def
              split: option.splits)
  unfolding lookup0_fmupd
proof (rule_tac[!] ext)
  fix a'
  assume "fmlookup xs time = None"
  thus "((lookup0 xs)(time := 0(sig := None))) a' = 
            (if time = a' then \<lambda>x. if x \<noteq> sig then 0 x else None else lookup0 xs a')"
    by auto
next
  fix x2 a'
  assume "fmlookup xs time = Some x2"
  thus "((lookup0 xs)(time := x2(sig := None))) a' = 
            (if time = a' then \<lambda>x. if x \<noteq> sig then x2 x else None else lookup0 xs a')"
    by auto
qed

lemma [code]:
  "purge 0 (Pm_fmap xs) now sig val = (Pm_fmap xs)"
  by (transfer, auto)

lemma [code]:
  "purge (Suc n) (Pm_fmap xs) now sig val = 
      (let f   = lookup0 xs (now + Suc n);
           f'  = map_drop sig f;
           xs' = fmupd (now + Suc n) f' xs 
       in 
          if f sig = Some val then purge n (Pm_fmap xs) now sig val 
          else purge n (Pm_fmap xs') now sig val)"
  by (transfer, auto simp add: lookup0_update_with_none Let_def) 
 
value "lookup (purge 1 (0 :: sig transaction) 1 C True) 1 C"

lemma [code]:
  "trans_post sig v (Pm_fmap xs) t = (let 
                                          current = lookup0 xs t;
                                          chopped = fmmap_keys (\<lambda>t'. if t < t' then map_drop sig else id);
                                          updated = fmupd t (current(sig \<mapsto> v)) xs  
                                      in 
                                          Pm_fmap (chopped updated))"
  by (transfer', unfold Let_def trans_post_raw_def)
     (rule ext, auto simp add: fmlookup_default_def zero_map map_drop_def map_filter_def 
                        split: option.splits)

value [code] "beval 2 def_state {} test_beh (Bsig_delayed A 1)"
value [code] "beval 2 def_state {} test_beh (Bsig_delayed B 1)"
value [code] "beval 2 def_state {} test_beh (Bsig_delayed C 1)"
value [code] "b_seq_exec 0 def_state {} 0 (Bnull :: sig seq_stmt) empty_trans"

definition
  "exp1 = Bsig C"

definition
  "exp2 = Bnand (Bsig A) (Bsig B)"

definition
  "exp3 = Bnot (Bor (Bsig C) (Bsig B))"

definition 
  "seq1 = Bassign_trans C exp2 1"

definition
  "seq2 = Bassign_inert B exp3 2"

definition                                                                
  "seq3 = Bguarded exp1 seq1 seq2"          

value [code] "lookup (b_seq_exec 0 def_state {} 0 (Bcomp seq1 seq2) empty_trans) 1 C"
value [code] "lookup (b_seq_exec 0 def_state {} 0 (Bguarded exp1 seq1 seq2) empty_trans) 2 C"
value [code] "lookup (b_seq_exec 0 def_state {} 0 seq1 empty_trans) 1 C"
value [code] "lookup (b_seq_exec 0 def_state {} 0 seq2 empty_trans) 2 C" 


term "fmmap_keys (\<lambda>x. fmadd)"

lemma [code]:
  "map_add_trans (Pm_fmap xs) (Pm_fmap ys) =  
                               Pm_fmap (fmmap_keys (\<lambda>k v. lookup0 xs k ++ lookup0 ys k) (xs ++\<^sub>f ys))"
  by (transfer') (rule ext, auto simp add:fmlookup_default_def map_add_subsumed1 split:option.splits)

lemma [code]:
  "map_diff_trans (Pm_fmap xs) (Pm_fmap ys) = 
                     Pm_fmap (fmmap_keys (\<lambda>k v. map_diff (lookup0 xs k) (lookup0 ys k)) (xs ++\<^sub>f ys))"
  by (transfer') (rule ext, auto simp add: fmlookup_default_def zero_map split:option.splits)

lemma clean_zip_alt_def [code]:
  "clean_zip \<tau> \<tau>1 \<tau>2 = (let \<tau>1_stripped = map_diff_trans \<tau>1 \<tau>;
                           \<tau>2_stripped = map_diff_trans \<tau>2 \<tau>;
                           zipped = map_add_trans \<tau>1_stripped \<tau>2_stripped
                        in 
                           map_add_trans \<tau> zipped)"
  by (transfer) (auto simp add:clean_zip_raw_def)


value [code] "clean_zip empty_trans empty_trans (empty_trans :: sig transaction)"
value [code] "lookup (b_conc_exec 1 def_state {A, B} test_beh (process {A} : seq1) empty_trans) 2 C"
value [code] "lookup (b_conc_exec 1 def_state {A, C} test_beh ((process {A} : seq1) || (process {C} : seq2)) empty_trans) 3 B"

value [code] "quiet (empty_trans :: sig transaction) {}"
                  

lemma [code]:
  "Poly_Mapping.update k v (Pm_fmap xs) = Pm_fmap (fmupd k v xs)"
  by (transfer, auto simp add:fmlookup_default_def)

value [code] "rem_curr_trans 0 (empty_trans :: sig transaction)"


lemma lookup0_zero_fun:
  "lookup0 xs = (\<lambda>k. 0) \<longleftrightarrow> clearjunk0 xs = fmempty" 
  by (metis PM_clearjunk0_cong Pm_fmap.rep_eq aux compute_keys_pp compute_zero_pp 
            fmap_exhaust fmdom'_fmupd insert_iff lookup_not_eq_zero_eq_in_keys)

lemma LEAST_ext:
  assumes "\<And>n. P n = Q n"
  shows "(LEAST n. P n) = (LEAST n. Q n)"
  using assms by auto

lemma clearjunk0_fmupd_with_0:
  "clearjunk0 (fmupd x 0 m) = fmdrop x (clearjunk0 m)"
proof -
  have "clearjunk0 (fmupd x 0 m) = fmfilter (\<lambda>k. fmlookup (fmupd x 0 m) k \<noteq> Some 0) (fmupd x 0 m)"
    unfolding clearjunk0_def by auto
  also have "... = fmfilter (\<lambda>k. fmlookup (fmupd x 0 m) k \<noteq> Some 0) m"
    by auto
  also have "... = fmfilter (\<lambda>k. k \<noteq> x \<and> fmlookup m k \<noteq> Some 0) m"
    by (metis fmupd_lookup)
  also have "... = fmfilter (\<lambda>k. k \<noteq> x) (fmfilter (\<lambda>k. fmlookup m k \<noteq> Some 0) m)"
    unfolding fmfilter_comp by auto
  also have "... = fmfilter (\<lambda>k. k \<noteq> x) (clearjunk0 m)"
    unfolding clearjunk0_def by auto
  also have "... = fmdrop x (clearjunk0 m)"
    by (simp add: fmfilter_alt_defs(1))
  finally show ?thesis by auto
qed


lemma sorted_list_fmdom_fmupd:
  "sorted_list_of_fset (fmdom (fmupd x y m)) = insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
proof -
  have "fmdom (fmupd x y m) = finsert x (fmdom m)"
    by auto
  hence "sorted_list_of_fset (fmdom (fmupd x y m)) = sorted_list_of_fset (finsert x (fmdom m))"
    by auto
  also have "... = insort x (sorted_list_of_fset (fmdom m - {|x|}))"
    by (auto simp add: sorted_list_of_fset.rep_eq)
  also have "... = insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
    by auto
  finally show "sorted_list_of_fset (fmdom (fmupd x y m)) = 
                   insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
    by auto
qed

lemma sorted_list_of_fmap_fmupd:
  "sorted_list_of_fmap (fmupd x y m) = 
   map (\<lambda>k. (k, the (fmlookup (fmupd x y m) k))) (insort x (sorted_list_of_fset (fmdom (fmdrop x m))))"
proof -               
  have "sorted_list_of_fset (fmdom (fmupd x y m)) = 
                   insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
    using sorted_list_fmdom_fmupd by auto
  thus "sorted_list_of_fmap (fmupd x y m) = 
    map (\<lambda>k. (k, the (fmlookup (fmupd x y m) k))) (insort x (sorted_list_of_fset (fmdom (fmdrop x m))))"
    unfolding sorted_list_of_fmap_def by auto
qed

lemma clearjunk0_fmupd_neq_0:
  "y \<noteq> 0 \<Longrightarrow> clearjunk0 (fmupd x y m) = fmupd x y (clearjunk0 m)"
  by (rule fmap_ext) (auto simp add: clearjunk0_def)

lemma fst_hd_list_is_hd_map:
  "xs \<noteq> [] \<Longrightarrow> fst (hd xs) = hd (map fst xs)"
  by (induction xs) auto

lemma dom_only:
  "m \<noteq> fmempty \<Longrightarrow> fst (hd (sorted_list_of_fmap m)) = hd (sorted_list_of_fset (fmdom m))"
proof -
  assume a1: "m \<noteq> fmempty"
  obtain aa :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> 'a" where
    "\<forall>f fa. fa = f \<or> map_of (sorted_list_of_fmap fa) (aa fa f) \<noteq> map_of (sorted_list_of_fmap f) (aa fa f)"
    by (metis fmap_ext map_of_sorted_list)
  then have " fst (hd (sorted_list_of_fmap m)) = hd (map fst (sorted_list_of_fmap m))"
    using a1 by (metis (no_types) bot_fset.rep_eq fmdom_empty list.map_sel(1) list.simps(8) 
                 map_of_sorted_list sorted_list_of_fmap_def sorted_list_of_fset.rep_eq 
                 sorted_list_of_set_empty)
  also have "... = hd (sorted_list_of_fset (fmdom m))"
    unfolding sorted_list_of_fmap_def by (simp add: o_def)
  finally show ?thesis by auto
qed



lemma obtain_neq_empty':
  fixes m :: "('a, 'b \<rightharpoonup> 'c) fmap"
  assumes "clearjunk0 m \<noteq> fmempty"
  shows  "\<exists>k. lookup0 m k \<noteq> Map.empty"
proof -
  have *: "\<And>k. fmlookup (clearjunk0 m) k \<noteq> Some (0 :: 'b \<rightharpoonup> 'c)"
    unfolding clearjunk0_def by auto
  obtain k where k_prop: "fmlookup (clearjunk0 m) k \<noteq> None"
    using assms by (metis fmap_ext fmempty_lookup)
  with * have "fmlookup (clearjunk0 m) k \<noteq> Some 0"
    by auto
  then obtain val where "fmlookup (clearjunk0 m) k = Some val" and "val \<noteq> 0"
    using k_prop by auto
  hence "val \<noteq> Map.empty"
    by (auto simp add:zero_map)
  hence "lookup0 (clearjunk0 m) k \<noteq> Map.empty"
    using `fmlookup (clearjunk0 m) k = Some val` unfolding fmlookup_default_def
    by auto
  hence "lookup0 m k \<noteq> Map.empty"
    unfolding clearjunk0_def 
    by (metis \<open>lookup0 (clearjunk0 m) k \<noteq> Map.empty\<close> lookup0_clearjunk0)
  thus ?thesis
    by (intro exI[where x="k"])
qed

lemma obtain_neq_empty:
  fixes m :: "('a, 'b \<rightharpoonup> 'c) fmap"
  assumes "clearjunk0 m \<noteq> fmempty"
  obtains k where "lookup0 m k \<noteq> Map.empty"
  using obtain_neq_empty'[OF assms] by blast

lemma hd_after_insert_larger_key:
  assumes "xs \<noteq> []"
  assumes "hd xs < x"
  shows "hd (insort x xs) = hd xs"
  by (metis assms insort_key.simps(2) leD list.collapse list.sel(1))


(* TODO : streamline this ugly proof! *)
lemma least_fst_hd_sorted:
  fixes xs :: "('a::wellorder, 'b \<Rightarrow> 'c option) fmap"
  assumes "clearjunk0 xs \<noteq> fmempty"
  shows "(LEAST n. lookup0 xs n \<noteq> Map.empty) = fst (hd (sorted_list_of_fmap (clearjunk0 xs)))"
  using assms
proof (induction xs rule: fmap_induct)
  case fmempty
  then show ?case by (auto simp add: clearjunk0_def)
next
  case (fmupd x y m)
  have "clearjunk0 m = fmempty \<or> clearjunk0 m \<noteq> fmempty" 
    by auto
  moreover
  { assume *: "clearjunk0 m = fmempty"
    have "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = x"
    proof (rule Least_equality) 
      have **: "x \<in> fmdom' (clearjunk0 (fmupd x y m))"
        using fmupd(3) *  by (metis (mono_tags, hide_lams) compute_keys_pp compute_lookup_pp 
                                    in_keys_iff  lookup0_fmupd lookup0_zero_fun)
      have " lookup0 (fmupd x y m) x = lookup0 (clearjunk0 (fmupd x y m)) x"
        using lookup0_clearjunk0 by metis
      moreover have "... \<noteq> Map.empty"
        using fmupd(3) 
        apply (auto simp add:fmlookup_default_def split:option.splits)
        apply (metis "*"calculation fmlookup_default_if(2) lookup0_fmupd lookup0_zero_fun)
        using clearjunk0_nonzero[OF **] zero_fun_def zero_option_def
        by (metis "**" PM_clearjunk0_cong calculation clearjunk0_map_of_SomeD clearjunk0_nonzero 
                       compute_keys_pp ext fmlookup_default_def fmupd_lookup option.simps(5))
      ultimately show "lookup0 (fmupd x y m) x \<noteq> Map.empty"
        by auto 
    next
      { fix ya
        assume "\<not> x \<le> ya" hence "ya <  x" by auto
        hence "lookup0 (fmupd x y m) ya = lookup0 m ya"
          unfolding lookup0_fmupd by auto
        moreover have "lookup0 m ya = Map.empty"
          using * lookup0_zero_fun zero_map by force
        ultimately have "lookup0 (fmupd x y m) ya =  Map.empty"
          by auto
      }
      thus "\<And>ya. lookup0 (fmupd x y m) ya \<noteq> Map.empty \<Longrightarrow> x \<le> ya "
        by blast
    qed
    moreover have " fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) = x"
    proof -
      have "fmlookup (fmupd x y m) x \<noteq> Some 0"
        using fmupd(3) by (metis "*" fmupd_lookup lookup0_fmupd lookup0_zero_fun option.sel)
      hence "fmdom (clearjunk0 (fmupd x y m)) =  finsert x (fmdom (clearjunk0 m))"
        by (auto simp add:clearjunk0_def)
      also have "... = {|x|}"
        using * by auto
      finally have "fmdom (clearjunk0 (fmupd x y m)) =  {|x|}"
        by auto
      moreover have "the (fmlookup (clearjunk0 (fmupd x y m)) x) = y"        
      proof -
        have "fmlookup (fmupd x y m) x \<noteq> Some 0"
          using \<open>fmlookup (fmupd x y m) x \<noteq> Some 0\<close> by blast
        then show ?thesis
          by (simp add: clearjunk0_def)
      qed
      ultimately have "sorted_list_of_fmap (clearjunk0 (fmupd x y m)) = [(x, y)]"
        unfolding sorted_list_of_fmap_def sorted_list_of_fset_def by auto
      thus ?thesis by auto
    qed
    ultimately have ?case by auto }

  moreover
  { assume "clearjunk0 m \<noteq> fmempty"
    with fmupd(1) have ind: "(LEAST n. lookup0 m n \<noteq> Map.empty) = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
      by auto
    obtain cur_least where cur_least_def: "cur_least = (LEAST n. lookup0 m n \<noteq> Map.empty) "
      by auto
    consider (new) "x < cur_least" | (old) "cur_least \<le> x" 
      using le_less_linear by blast
    hence ?case 
    proof (cases)
      case new
      have "lookup0 (fmupd x y m) x = Map.empty \<or> lookup0 (fmupd x y m) x \<noteq> Map.empty"
        by auto
      moreover
      { assume "lookup0 (fmupd x y m) x = Map.empty"
        hence "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = 
               (LEAST n. n \<noteq> x \<and> lookup0 (fmupd x y m) n \<noteq> Map.empty)"
          by metis
        also have "... = (LEAST n. lookup0 m n \<noteq> Map.empty)"
          apply (rule LEAST_ext)
          unfolding lookup0_fmupd using fmupd.hyps zero_map by force
        also have "... = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using ind by auto
        finally have lexpand: "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) =
                                                      fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          by auto
        have "y = 0"
          using `lookup0 (fmupd x y m) x = Map.empty` 
          by (auto simp add:zero_map)
        have "clearjunk0 (fmupd x y m) = fmdrop x (clearjunk0 m)"  
          using clearjunk0_fmupd_with_0 unfolding `y = 0` by metis
        also have "... = clearjunk0 m"
          using fmupd(2)  by (simp add: clearjunk0_def fmap_ext)
        finally have "clearjunk0 (fmupd x y m) = clearjunk0 m"
          by auto
        hence "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) = 
                                                      fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          by auto
        with lexpand have ?thesis by auto }
      moreover 
      { assume "lookup0 (fmupd x y m) x \<noteq> Map.empty"
        hence "y \<noteq> Map.empty" by auto
        have lexpand2: "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = x"
        proof (rule Least_equality)
          show "lookup0 (fmupd x y m) x \<noteq> Map.empty"
            using `lookup0 (fmupd x y m) x \<noteq> Map.empty` by auto
        next
          { fix ya
            assume "\<not> x \<le> ya" hence "ya < x" by auto
            hence "lookup0 (fmupd x y m) ya = lookup0 m ya"
              unfolding lookup0_fmupd by auto
            have "ya < cur_least"
              using `ya < x` and `x < cur_least` by auto
            hence "lookup0 m ya = Map.empty"
              unfolding cur_least_def using not_less_Least by auto 
            hence "lookup0 (fmupd x y m) ya = Map.empty"
              using `lookup0 (fmupd x y m) ya = lookup0 m ya` by auto }
          thus "\<And>ya. lookup0 (fmupd x y m) ya \<noteq> Map.empty \<Longrightarrow> x \<le> ya "
            by auto
        qed
        have push_clearjunk0: "clearjunk0 (fmupd x y m) = fmupd x y (clearjunk0 m)"
          by (metis \<open>y \<noteq> Map.empty\<close> clearjunk0_fmupd_neq_0 zero_map)
        hence swap_cj_fmupd: "sorted_list_of_fmap (clearjunk0 (fmupd x y m)) = 
               sorted_list_of_fmap (fmupd x y (clearjunk0 m))"
          by auto
        have "... = 
            map (\<lambda>k. (k, the (fmlookup (fmupd x y (clearjunk0 m)) k))) 
                                              (insort x (sorted_list_of_fset (fmdom (fmdrop x (clearjunk0 m)))))"
            (is "?simple = ?complex")
          using sorted_list_of_fmap_fmupd by auto
        have "fmdrop x (clearjunk0 m) = clearjunk0 m"
          by (simp add: fmupd clearjunk0_def fmap_ext)
        hence "sorted_list_of_fset (fmdom (fmdrop x (clearjunk0 m))) = 
               sorted_list_of_fset (fmdom (clearjunk0 m))"
          by auto
        moreover have "insort x (sorted_list_of_fset (fmdom (clearjunk0 m))) = 
            x # (sorted_list_of_fset (fmdom (clearjunk0 m)))"
          using new unfolding cur_least_def 
          using ind  unfolding dom_only[OF `clearjunk0 m \<noteq> fmempty`]
          by (metis (no_types, lifting) insort_key.simps(1) insort_key.simps(2) less_imp_le list.collapse)
        ultimately have x_as_hd: "insort x (sorted_list_of_fset (fmdom (fmdrop x (clearjunk0 m)))) = 
               x # sorted_list_of_fset (fmdom (clearjunk0 m))"
          by auto      
        have "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =  x"
          using swap_cj_fmupd `?simple = ?complex` x_as_hd by auto
        with lexpand2 have ?thesis by auto }    
      ultimately show ?thesis by auto
    next
      case old
      have "x \<noteq> cur_least"
      proof (rule ccontr)
        assume "\<not> x \<noteq> cur_least"
        hence "x = cur_least" by auto
        obtain k where k_not_emp: "lookup0 m k \<noteq> Map.empty" 
          using `clearjunk0 m \<noteq> fmempty`
          by (smt Pm_fmap.rep_eq clearjunk0_def compute_keys_pp fmdom'_filter fmdom'_notI 
                  fmfilter_false fmlookup_default_if(1) fmupd(2) in_keys_iff member_filter)
        hence "lookup0 m x \<noteq> Map.empty"
          using LeastI[where P = "\<lambda>x. lookup0 m x \<noteq> Map.empty", OF k_not_emp] `x = cur_least` 
          unfolding cur_least_def by auto
        thus "False"
          using fmupd(2) by (simp add: zero_fun_def zero_option_def)
      qed
      hence "cur_least < x" using old by auto
      have lexpand_old:"(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = cur_least"
      proof (rule Least_equality)
        have eqlookup0: "lookup0 (fmupd x y m) cur_least = lookup0 m cur_least"
          using `x \<noteq> cur_least` unfolding lookup0_fmupd by auto
        obtain k where wit: "lookup0 m k \<noteq> Map.empty"
          using obtain_neq_empty[OF `clearjunk0 m \<noteq> fmempty`] by auto
        hence "lookup0 m cur_least \<noteq> Map.empty"
          using LeastI[of "\<lambda>x. lookup0 m x \<noteq> Map.empty", OF wit] unfolding cur_least_def
          by auto
        thus "lookup0 (fmupd x y m) cur_least \<noteq> Map.empty"
          using eqlookup0 by auto
      next
        { fix ya
          assume "\<not> cur_least \<le> ya" hence "ya < cur_least" by auto
          hence "ya < x" using `cur_least < x` by auto
          hence "lookup0 (fmupd x y m) ya = lookup0 m ya"
            unfolding lookup0_fmupd by auto
          also have "...  = Map.empty"
            using `ya < cur_least` cur_least_def not_less_Least by auto
          finally have "lookup0 (fmupd x y m) ya = Map.empty"
            by auto }
        thus "\<And>ya. lookup0 (fmupd x y m) ya \<noteq> Map.empty \<Longrightarrow> cur_least \<le> ya "
          by blast
      qed
      have fi_rexpand: "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) = 
            hd (sorted_list_of_fset (fmdom (clearjunk0 (fmupd x y m))))"
        using dom_only[OF `clearjunk0 (fmupd x y m) \<noteq> fmempty`] by auto

      have "y = Map.empty \<or> y \<noteq> Map.empty" by auto
      moreover
      { assume "y = Map.empty"
        hence "clearjunk0 (fmupd x y m) = fmdrop x (clearjunk0 m)"
          using clearjunk0_fmupd_with_0[of "x" "m"]  by (simp add: zero_fun_def zero_option_def)
        also have "... = clearjunk0 m"
          using fmupd(2)  by (simp add: clearjunk0_def fmap_ext) 
        finally have "clearjunk0 (fmupd x y m) = clearjunk0 m"
          by auto
        hence " hd (sorted_list_of_fset (fmdom (clearjunk0 (fmupd x y m)))) =
                hd (sorted_list_of_fset (fmdom (clearjunk0 m)))"
          by auto
        also have "... = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using dom_only[OF `clearjunk0 m \<noteq> fmempty`] by auto
        finally have "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =
                       fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using fi_rexpand by auto
        also have "... = cur_least"
          using ind unfolding cur_least_def by auto
        finally have "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) = 
                      cur_least" by auto
        with lexpand_old have ?thesis by auto }
    
      moreover
      { assume "y \<noteq> Map.empty"
        have push_clearjunk0_old: "clearjunk0 (fmupd x y m) = fmupd x y (clearjunk0 m)"
          by (metis \<open>y \<noteq> Map.empty\<close> clearjunk0_fmupd_neq_0 zero_map)
        hence fmdom_clearjunk: "fmdom (clearjunk0 (fmupd x y m)) = fmdom (fmupd x y (clearjunk0 m))"
          by auto
        have "sorted_list_of_fset (fmdom (fmupd x y (clearjunk0 m))) = 
              insort x (sorted_list_of_fset (fmdom (fmdrop x (clearjunk0  m)))) "
          using sorted_list_fmdom_fmupd by auto
        moreover have "fmdrop x (clearjunk0 m) = clearjunk0 m"
          by (simp add: fmupd clearjunk0_def fmap_ext)
        ultimately have ****: "sorted_list_of_fset (fmdom (fmupd x y (clearjunk0 m))) =
                      insort x (sorted_list_of_fset (fmdom (clearjunk0  m)))"
          by auto
        hence "sorted_list_of_fset (fmdom (clearjunk0 (fmupd x y m))) = 
               insort x (sorted_list_of_fset (fmdom (clearjunk0 m)))"
          using push_clearjunk0_old by auto
        have "hd (insort x (sorted_list_of_fset (fmdom (clearjunk0 m)))) = 
                        hd (sorted_list_of_fset (fmdom (clearjunk0 m)))"
        proof (rule hd_after_insert_larger_key)
          show "sorted_list_of_fset (fmdom (clearjunk0 m)) \<noteq> []"
            by (metis \<open>clearjunk0 m \<noteq> fmempty\<close> fmrestrict_fset_dom fmrestrict_fset_null fset_of_list_simps(1) 
                      sorted_list_of_fset_simps(2))
        next
          show " hd (sorted_list_of_fset (fmdom (clearjunk0 m))) < x "
            using \<open>clearjunk0 m \<noteq> fmempty\<close> \<open>cur_least < x\<close> cur_least_def dom_only ind by force
        qed
        also have "... = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using dom_only[OF `clearjunk0 m \<noteq> fmempty`] by auto
        also have "... = cur_least"
          using ind unfolding cur_least_def by auto
        finally have "hd (insort x (sorted_list_of_fset (fmdom (clearjunk0 m)))) =
                         cur_least" by auto
        hence "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) = 
                cur_least"
          using  **** fi_rexpand push_clearjunk0_old by auto
        with lexpand_old have ?thesis by auto }
      ultimately show ?thesis by auto
    qed }
  ultimately show ?case by auto
qed

lemma [code]:
  "next_time t (Pm_fmap xs) = (if clearjunk0 xs = fmempty then t else (fst o hd) (sorted_list_of_fmap (clearjunk0 xs)))"
  unfolding next_time_def 
  by (transfer', auto simp add: least_fst_hd_sorted lookup0_zero_fun) 

value [code] "next_time 0 (empty_trans :: sig transaction)"
value [code] "next_state 0 (empty_trans :: sig transaction) def_state B"
value [code] "fmadd (fmap_of_list [(1::nat, True)]) (fmap_of_list [(1::nat, False)])"

definition fm_const_interval_open_right :: "'a :: zero \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) fmap" where
  "fm_const_interval_open_right v lo hi = fmap_of_list (zip [lo ..< hi] (replicate (hi - lo) v))"

lemma fmlookup_const_interval_if:
  "x \<in> {lo ..< hi} \<Longrightarrow> fmlookup (fm_const_interval_open_right v lo hi) x = Some v"
  "x \<notin> {lo ..< hi} \<Longrightarrow> fmlookup (fm_const_interval_open_right v lo hi) x = None"
  unfolding fm_const_interval_open_right_def fmlookup_of_list 
  by (metis distinct_upt in_set_impl_in_set_zip1 in_set_replicate length_replicate length_upt 
            map_fst_zip map_of_eq_Some_iff set_upt set_zip_rightD) (auto)


lemma [code]:
  "override_lookups_on_open_right (Pm_fmap xs) v lo hi = 
                                              Pm_fmap (xs  ++\<^sub>f fm_const_interval_open_right v lo hi)"
proof (transfer', rule ext)
  fix x lo hi :: nat
  fix xs :: "(nat, 'a ::zero) fmap"
  fix v :: 'a
  let ?le = "override_on (lookup0 xs) (\<lambda>n. v) {lo..<hi} x"
  let ?ri = "lookup0 (xs ++\<^sub>f fm_const_interval_open_right v lo hi) x"
  have "x \<in> {lo ..<hi} \<or> x \<notin> {lo..<hi}"
    by auto
  moreover
  { assume "x \<in> {lo ..< hi}"
    hence "override_on (lookup0 xs) (\<lambda>n. v) {lo..<hi} x = v"
      unfolding override_on_def by auto
    moreover have "lookup0 (xs ++\<^sub>f fm_const_interval_open_right v lo hi) x = v"
      by (metis \<open>x \<in> {lo..<hi}\<close> fmlookup_add fmlookup_const_interval_if(1) fmlookup_default_if(1) 
                fmlookup_dom_iff)  
    ultimately have "?le = ?ri"
      by auto }
  moreover
  { assume "x \<notin> {lo ..< hi}"
    hence "override_on (lookup0 xs) (\<lambda>n. v) {lo..<hi} x = lookup0 xs x"
      unfolding override_on_def by auto
    moreover have "lookup0 (xs ++\<^sub>f fm_const_interval_open_right v lo hi) x = lookup0 xs x"
      by (metis \<open>x \<notin> {lo..<hi}\<close> fmlookup_const_interval_if(2) fmlookup_default_add fmlookup_dom_iff 
                option.simps(3))
    ultimately have "?le = ?ri"
      by auto }
  ultimately show "?le = ?ri"
    by blast
qed
            
value [code] "add_to_beh (def_state :: sig state) {A, B, C}" 

code_thms add_to_beh

code_thms next_event

definition next_event_code :: "time \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal event" where
  "next_event_code t \<tau>' \<sigma> = (let m = get_trans \<tau>' (next_time t \<tau>') in  
                                       {sig. if sig \<in> dom m then (the o m) sig \<noteq> \<sigma> sig else False})"

lemma [code]:
  "next_event t \<tau>' \<sigma> = next_event_code t \<tau>' \<sigma>"
  unfolding next_event_def next_event_code_def Let_def  by auto

value [code] "next_event 0 (empty_trans :: sig transaction) def_state"

code_pred (modes : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) b_simulate_fin .

thm b_simulate_fin.equation

definition "functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> = 
            Predicate.the (b_simulate_fin_i_i_i_i_i_i_i_o maxtime t \<sigma> \<gamma> \<theta> cs \<tau>)"

theorem functional_simulate_fin_complete:
  assumes "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> beh"
  shows "functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> = beh"
  using assms unfolding functional_simulate_fin_def b_simulate_fin_i_i_i_i_i_i_i_o_def
  Predicate.the_def pred.sel
proof -
  have *: "(\<And>x. maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> x \<Longrightarrow> x = beh)"
    using b_simulate_fin_deterministic[OF assms] by auto
  thus  "(THE x. maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> x) = beh"
    by (auto intro: the_equality[where P="\<lambda>x. b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> x", OF assms])
qed

code_pred (modes : i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) b_simulate .

lemma functional_simulate_fin_sound:                      
  assumes "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
  assumes "\<forall>n. t \<le> n \<longrightarrow> Poly_Mapping.lookup \<theta> n = 0" 
  assumes "\<forall>n. n < t \<longrightarrow> get_trans \<tau> n = 0"
  assumes "functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> = beh"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> beh"
  using assms unfolding functional_simulate_fin_def b_simulate_fin_i_i_i_i_i_i_i_o_def
  Predicate.the_def pred.sel
proof -
  have *: "The (b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau>) = beh"
    using assms unfolding functional_simulate_fin_def b_simulate_fin_i_i_i_i_i_i_i_o_def
    Predicate.the_def pred.sel by auto
  obtain \<tau>' \<sigma>' \<gamma>' \<theta>' where ss: "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
    using assms(1) by auto
  have **: "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> (Poly_Mapping.update (maxtime + 1) 0 \<theta>')"
    using small_step_implies_big_step[OF ss assms(2) assms(3)] by auto
  hence "\<And>beh. b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> beh \<Longrightarrow> 
                                               beh = (Poly_Mapping.update (maxtime + 1) 0 \<theta>')"
    by (simp add: b_simulate_fin_deterministic)
  from * show "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> beh"
    by (metis ** b_simulate_fin_deterministic theI)  
qed

lemma functional_simulate_eq_b_simulate_fin:
  assumes "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
  assumes "\<forall>n. t  \<le> n \<longrightarrow> Poly_Mapping.lookup \<theta> n = 0"  
  assumes "\<forall>n. n < t \<longrightarrow> get_trans \<tau> n = 0"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> beh \<longleftrightarrow> (functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> = beh)"
  by (meson assms functional_simulate_fin_complete functional_simulate_fin_sound)

definition "functional_simulate maxtime cs = 
            Predicate.the (b_simulate_i_i_o maxtime cs)"

theorem functional_simulate_complete:         
  assumes "b_simulate maxtime cs beh"
  shows "functional_simulate maxtime cs = beh"
  using assms unfolding functional_simulate_def b_simulate_i_i_o_def
  Predicate.the_def pred.sel
proof -
  have *: "(\<And>x. b_simulate maxtime cs x \<Longrightarrow> x = beh)"
    using b_sim_init_deterministic[OF assms] by auto
  thus  "(THE x. b_simulate maxtime cs x) = beh"
    by (auto intro: the_equality[where P="\<lambda>x. b_simulate maxtime cs x", OF assms])
qed

theorem functional_simulate_sound:
  assumes "init' 0 def_state {} 0 cs empty_trans = \<tau>"
  assumes "update_config (0, def_state, {}, 0) \<tau> = (t, \<sigma>, \<gamma>, \<theta>)"
  assumes "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
  assumes "functional_simulate maxtime cs = beh"
  shows "b_simulate maxtime cs beh"
proof -
  have the_beh: "The (b_simulate maxtime cs) = beh"
    using assms unfolding functional_simulate_def b_simulate_i_i_o_def Predicate.the_def pred.sel
    by auto
  have "\<theta> = add_to_beh def_state {} 0 0 t"
    using assms(2) by (auto simp add: Let_def)
  also have "... = override_lookups_on_open_right empty_trans (Some o def_state) 0 t"
    unfolding add_to_beh_def by auto
  finally have *: "\<forall>n\<ge>t. lookup \<theta> n = 0"
    by transfer' auto
  have "t = next_time 0 \<tau>"
    using assms(2) by (auto simp add: Let_def)
  hence "\<forall>n. n < t \<longrightarrow> get_trans \<tau> n = 0"
    using next_time_at_least2 by auto
  hence "\<forall>n<t. lookup \<tau> n = 0 "
    by auto
  hence **: "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> (Poly_Mapping.update (maxtime + 1) 0 \<theta>')"
    using small_step_implies_big_step[OF assms(3)] * by auto
  have "b_simulate maxtime cs (Poly_Mapping.update (maxtime + 1) 0 \<theta>')"
    using b_simulate.intros[OF assms(1) _ _ _ _ **] assms(2) by (auto simp add: Let_def)
  thus "b_simulate maxtime cs beh"
    unfolding the_beh[THEN sym]   by (auto simp add: b_sim_init_deterministic intro: theI)
qed

theorem
  assumes "init' 0 def_state {} 0 cs empty_trans = \<tau>"
  assumes "update_config (0, def_state, {}, 0) \<tau> = (t, \<sigma>, \<gamma>, \<theta>)"
  assumes "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
  shows "functional_simulate maxtime cs = beh \<longleftrightarrow> b_simulate maxtime cs beh"
  using assms functional_simulate_sound functional_simulate_complete by metis

end