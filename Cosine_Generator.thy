(*
 * Copyright 2020, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Cosine_Generator
  imports VHDL_Hoare_Typed Bits_Int_Aux Cosine_Frac_Approx Fixed_Point Assertion
begin                

datatype signames = SINPUT | SOUTPUT | SINREADY | SOUTREADY | SOUTREADY_REG 
  | SNEXT_OUTREADYREG | SACCUM | SNEXT_ACCUM  | SCOUNTER | SNEXT_COUNTER | SFRAC | SNEXT_FRAC 
  | SCOMMON | SNEXT_COMMON  | SCTR_NEQ_0 | SCLK | SRST | SSTATE | SNEXT_STATE | SSQUARE_TEMP 
  | SCTR_MSB  | CTR_LSB
  | STERM1

abbreviation "INPUT \<equiv> Sname SINPUT"
abbreviation "OUTPUT \<equiv> Sname SOUTPUT"
abbreviation "INREADY \<equiv> Sname SINREADY"
abbreviation "OUTREADY \<equiv> Sname SOUTREADY"
abbreviation "OUTREADY_REG \<equiv> Sname SOUTREADY_REG"
abbreviation "NEXT_OUTREADYREG \<equiv> Sname SNEXT_OUTREADYREG"
abbreviation "ACCUM \<equiv> Sname SACCUM"
abbreviation "NEXT_ACCUM \<equiv> Sname SNEXT_ACCUM"
abbreviation "COUNTER \<equiv>  Sname SCOUNTER"
abbreviation "NEXT_COUNTER \<equiv> Sname SNEXT_COUNTER"
abbreviation "FRAC \<equiv> Sname SFRAC"
abbreviation "NEXT_FRAC \<equiv> Sname SNEXT_FRAC"
abbreviation "COMMON \<equiv> Sname SCOMMON"
abbreviation "NEXT_COMMON \<equiv> Sname SNEXT_COMMON"
abbreviation "CTR_NEQ_0 \<equiv> Sname SCTR_NEQ_0"
abbreviation "CLK \<equiv> Sname SCLK"
abbreviation "RST \<equiv> Sname SRST"
abbreviation "STATE \<equiv> Sname SSTATE"
abbreviation "NEXT_STATE \<equiv> Sname SNEXT_STATE"
abbreviation "SQUARE_TEMP \<equiv> Sname SSQUARE_TEMP"
abbreviation "TERM1 \<equiv> Sname STERM1"

text \<open>State encoding\<close>                                     

abbreviation "S_INIT \<equiv> Bliteral Neu [False, False, False]"
abbreviation "S_WAIT \<equiv> Bliteral Neu [False, False, True ]"
abbreviation "S_PRE  \<equiv> Bliteral Neu [False, True , False]"
abbreviation "S_PROC \<equiv> Bliteral Neu [False, True , True ]"
abbreviation "S_POST \<equiv> Bliteral Neu [True , False, False]"

abbreviation "V_INIT \<equiv> Lv Neu [False, False, False]" 
abbreviation "V_WAIT \<equiv> Lv Neu [False, False, True ]"
abbreviation "V_PRE  \<equiv> Lv Neu [False, True , False]"
abbreviation "V_PROC \<equiv> Lv Neu [False, True , True ]"
abbreviation "V_POST \<equiv> Lv Neu [True , False, False]" 

abbreviation "U_ZERO3  \<equiv>  [False, False, False]"
abbreviation "U_ZERO32 \<equiv>  replicate 32 False"

abbreviation "V_ZERO3   \<equiv> Lv Uns U_ZERO3"
abbreviation "V_ZERO32  \<equiv> Lv Sig U_ZERO32"

abbreviation "V_4       \<equiv> Lv Uns [True, False, False]"
abbreviation "V_3       \<equiv> Lv Uns [False, True, True]"
abbreviation "V_2       \<equiv> Lv Uns [False, True, False]"
abbreviation "V_1       \<equiv> Lv Uns [False, False, True]"
abbreviation "V_0       \<equiv> Lv Uns [False, False, False]"

abbreviation "ONE \<equiv> Bliteral Sig (to_bl (1 :: 32 word))"

type_synonym sig = "signames Assertion.sig"

locale cosine_locale = 
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> INREADY = Bty" and "\<Gamma> OUTREADY = Bty" and "\<Gamma> COUNTER = Lty Uns 3"
          "\<Gamma> CTR_NEQ_0 = Bty" and "\<Gamma> CLK = Bty" and "\<Gamma> RST = Bty" and 
          "\<Gamma> INPUT = Lty Sig 32" and  "\<Gamma> OUTPUT = Lty Sig 32" and "\<Gamma> ACCUM = Lty Sig 32" and 
          "\<Gamma> COMMON = Lty Sig 32" and "\<Gamma> FRAC   = Lty Sig 32" and 
          "\<Gamma> STATE  = Lty Neu 3" and  "\<Gamma> NEXT_STATE = Lty Neu 3" and "\<Gamma> SQUARE_TEMP = Lty Sig 64" and 
          "\<Gamma> TERM1 = Lty Sig 64" and "\<Gamma> OUTREADY_REG = Bty" and "\<Gamma> NEXT_OUTREADYREG = Bty" and 
          "\<Gamma> NEXT_ACCUM = Lty Sig 32" and "\<Gamma> NEXT_FRAC = Lty Sig 32" and "\<Gamma> NEXT_COMMON = Lty Sig 32" and 
          "\<Gamma> NEXT_COUNTER = Lty Uns 3"
begin


section \<open>Preliminaries\<close>

definition next_state :: "sig conc_stmt" where
" next_state \<equiv> (process {STATE, INREADY, CTR_NEQ_0} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_INIT), 
                   Bassign_trans NEXT_STATE (S_WAIT) 1)
         ,   (Explicit (S_WAIT),
                   Bguarded (Bsig INREADY) 
                            (Bassign_trans NEXT_STATE (S_PRE)  1)
                            (Bassign_trans NEXT_STATE (S_WAIT) 1))
         ,   (Explicit (S_PRE),
                   Bassign_trans NEXT_STATE (S_PROC) 1)
         ,   (Explicit (S_PROC),
                   Bguarded (Bsig CTR_NEQ_0) 
                       (Bassign_trans NEXT_STATE (S_PROC) 1) 
                       (Bassign_trans NEXT_STATE (S_POST) 1))
         ,   (Explicit (S_POST), 
                   Bassign_trans NEXT_STATE (S_WAIT) 1)
         ,   (Others, 
                   Bassign_trans NEXT_STATE (S_INIT) 1)])"

lemma conc_stmt_wf_next_state: "conc_stmt_wf next_state"
  unfolding next_state_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_state [simp]: "nonneg_delay_conc next_state"
  unfolding next_state_def by auto

lemma cwt_ns [simp]: "conc_wt \<Gamma> next_state"
  using cosine_locale_axioms
  unfolding next_state_def cosine_locale_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

definition next_common :: "sig conc_stmt" where
  "next_common \<equiv> (process {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_WAIT),
                   Bguarded (Bsig INREADY)   (Bassign_trans NEXT_COMMON (Bsig INPUT)  1) 
                                             (Bassign_trans NEXT_COMMON (Bsig COMMON) 1))
         ,   (Explicit (S_PRE),
                   Bassign_trans NEXT_COMMON (Badd (Bnot (Bslice SQUARE_TEMP 62 31)) ONE) 1)
         ,   (Explicit (S_PROC), 
                   Bassign_trans NEXT_COMMON (Badd (Bnot (Bsig COMMON)) ONE) 1)
         ,   (Explicit (S_INIT), 
                   Bassign_trans NEXT_COMMON (Bliteral Sig U_ZERO32) 1)
         ,   (Others, 
                   Bassign_trans NEXT_COMMON (Bsig COMMON) 1)])"

lemma conc_stmt_wf_next_common: "conc_stmt_wf next_common"
  unfolding next_common_def  conc_stmt_wf_def by auto

lemma cwt_nc [simp]: "conc_wt \<Gamma> next_common"
  using cosine_locale_axioms unfolding next_common_def cosine_locale_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)
  
lemma nonneg_delay_conc_next_common [simp]: "nonneg_delay_conc next_common"
  unfolding next_common_def by auto

lemma seq_wt_next_common:
  "seq_wt \<Gamma> (get_seq next_common)"
  using cwt_nc  by (metis conc_stmt.sel(4) conc_wt_cases(1) next_common_def)

lemma nonneg_delay_next_common:
  "nonneg_delay (get_seq next_common)"
  using nonneg_delay_conc_next_common  by (simp add: next_common_def)

definition squaring :: "sig conc_stmt" where     
  "squaring \<equiv> (process {COMMON} : 
      Bassign_trans SQUARE_TEMP (Bmult (Bsig COMMON) (Bsig COMMON)) 1)"

lemma conc_stmt_wf_squaring: "conc_stmt_wf squaring"
  unfolding squaring_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_squaring [simp]: "nonneg_delay_conc squaring"
  unfolding squaring_def by auto

lemma cwts [simp]: "conc_wt \<Gamma> squaring"
  using cosine_locale_axioms unfolding squaring_def cosine_locale_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_squaring: "seq_wt \<Gamma> (get_seq squaring)"
  using cwts  by (metis conc_stmt.sel(4) conc_wt_cases(1) squaring_def)

lemma nonneg_delay_squaring: "nonneg_delay (get_seq squaring)"
  using nonneg_delay_conc_squaring by (simp add: squaring_def)

definition next_counter :: "sig conc_stmt" where
  "next_counter \<equiv> (process {STATE, INREADY, CTR_NEQ_0, COUNTER} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_WAIT),
                   Bguarded (Bsig INREADY) 
                            (Bassign_trans NEXT_COUNTER (Bliteral Uns (to_bl (4 :: 3 word)))  1)
                            (Bassign_trans NEXT_COUNTER (Bsig COUNTER) 1))
         ,   (Explicit (S_PRE),
                   Bassign_trans NEXT_COUNTER (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 ::3 word)))) 1)
         ,   (Explicit (S_PROC),                       
                   Bguarded (Bsig CTR_NEQ_0)           
                       (Bassign_trans NEXT_COUNTER (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 :: 3 word)))) 1) 
                       (Bassign_trans NEXT_COUNTER (Bsig COUNTER) 1))  
         ,   (Explicit (S_INIT), 
                   Bassign_trans NEXT_COUNTER (Bliteral Uns (to_bl (0 :: 3 word))) 1)
         ,   (Others, 
                   Bassign_trans NEXT_COUNTER (Bsig COUNTER) 1)])"

lemma conc_stmt_wf_next_counter: "conc_stmt_wf next_counter"
  unfolding next_counter_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_counter [simp]: "nonneg_delay_conc next_counter"
  unfolding next_counter_def by auto

lemma cwt_ncnt [simp]: "conc_wt \<Gamma> next_counter"
  using cosine_locale_axioms unfolding next_counter_def cosine_locale_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto

lemma seq_wt_next_counter: "seq_wt \<Gamma> (get_seq next_counter)"
  using cwt_ncnt by (metis conc_stmt.sel(4) conc_wt_cases(1) next_counter_def)

lemma nonneg_delay_next_counter: "nonneg_delay (get_seq next_counter)"
  using nonneg_delay_conc_next_counter by (auto simp add: next_counter_def)

definition next_accum :: "sig conc_stmt" where
  "next_accum \<equiv> (process {STATE, ACCUM, FRAC, TERM1} : 
      Bcase (Bsig STATE)
         [   (Explicit (S_PRE),
                   Bassign_trans NEXT_ACCUM (Bliteral Sig (to_bl (0 :: 32 word))) 1)
         ,   (Explicit (S_PROC),
                   Bassign_trans NEXT_ACCUM (Badd (Bsig FRAC) (Bslice TERM1 62 31)) 1)
         ,   (Explicit (S_INIT), 
                   Bassign_trans NEXT_ACCUM (Bliteral Sig (to_bl (0 :: 32 word))) 1)
         ,   (Others,
                   Bassign_trans NEXT_ACCUM (Bsig ACCUM) 1)])"

lemma conc_stmt_wf_next_accum: "conc_stmt_wf next_accum"
  unfolding next_accum_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_accum [simp]: "nonneg_delay_conc next_accum"
  unfolding next_accum_def by auto

lemma cwt_na [simp]: "conc_wt \<Gamma> next_accum"
  using cosine_locale_axioms unfolding cosine_locale_def next_accum_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto

lemma seq_wt_next_accum: "seq_wt \<Gamma> (get_seq next_accum)"
  using cwt_na by (metis conc_stmt.sel(4) conc_wt_cases(1) next_accum_def)

lemma nonneg_delay_next_accum: "nonneg_delay (get_seq next_accum)"
  using nonneg_delay_conc_next_accum by (simp add: next_accum_def)
  
definition term1 :: "sig conc_stmt" where
  "term1 \<equiv> ( process {COMMON, ACCUM} : 
      Bassign_trans TERM1 (Bmult (Bsig COMMON) (Bsig ACCUM)) 1)"

lemma conc_stmt_wf_term1: "conc_stmt_wf term1"
  unfolding term1_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_term1 [simp]: "nonneg_delay_conc term1"
  unfolding term1_def by auto

lemma cwt_t1[simp]: "conc_wt \<Gamma> term1"
  using cosine_locale_axioms unfolding cosine_locale_def term1_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto

lemma seq_wt_term1: "seq_wt \<Gamma> (get_seq term1)"
  using cwt_t1 by (metis conc_stmt.sel(4) conc_wt_cases(1) term1_def)

lemma nonneg_delay_term1: "nonneg_delay (get_seq term1)"
  using nonneg_delay_conc_term1 by (simp add: term1_def)

definition next_frac :: "sig conc_stmt" where
  "next_frac \<equiv> (process {COUNTER} : 
      Bcase (Bsig COUNTER) 
         [   (Explicit (Bliteral Uns (to_bl (4 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_eighth :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (3 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_sixth  :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (2 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_fourth :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (1 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_half   :: 32 word))) 1)
         ,   (Explicit (Bliteral Uns (to_bl (0 :: 3 word))), 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (approx_one    :: 32 word))) 1)
         ,   (Others, 
                   Bassign_trans NEXT_FRAC (Bliteral Sig (to_bl (0 :: 32 word))) 1) ])"

lemma conc_stmt_wf_next_frac: "conc_stmt_wf next_frac"
  unfolding next_frac_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_frac [simp]: "nonneg_delay_conc next_frac"
  unfolding next_frac_def by auto

lemma cwt_nf [simp]: "conc_wt \<Gamma> next_frac"
  using cosine_locale_axioms unfolding cosine_locale_def next_frac_def
  by (intro conc_wt.intros seq_wt.intros bexp_wt.intros) auto 

lemma seq_wt_next_frac: "seq_wt \<Gamma> (get_seq next_frac)"
  using cwt_nf by (metis conc_stmt.sel(4) conc_wt_cases(1) next_frac_def)

lemma nonneg_delay_next_frac: "nonneg_delay (get_seq next_frac)"
  using nonneg_delay_conc_next_frac by (simp add: next_frac_def)

definition next_outready_reg :: "sig conc_stmt" where
  "next_outready_reg \<equiv> (process {STATE, CTR_NEQ_0, OUTREADY_REG} : 
      Bcase (Bsig STATE)    
         [   (Explicit (S_PROC), 
                    Bguarded (Bsig CTR_NEQ_0) 
                        (Bassign_trans NEXT_OUTREADYREG (Bfalse) 1) 
                        (Bassign_trans NEXT_OUTREADYREG (Btrue ) 1))
         ,   (Explicit (S_POST), 
                    Bassign_trans NEXT_OUTREADYREG (Bsig OUTREADY_REG) 1)
         ,   (Others, 
                    Bassign_trans NEXT_OUTREADYREG (Bfalse) 1)])"

lemma conc_stmt_wf_next_outready_reg: "conc_stmt_wf next_outready_reg"
  unfolding next_outready_reg_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_next_outready_reg [simp]: "nonneg_delay_conc next_outready_reg"
  unfolding next_outready_reg_def by auto

lemma cwt_no [simp]: "conc_wt \<Gamma> next_outready_reg"
  using cosine_locale_axioms unfolding cosine_locale_def next_outready_reg_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_next_outready_reg: "seq_wt \<Gamma> (get_seq next_outready_reg)"
  using cwt_no by (metis conc_stmt.sel(4) conc_wt_cases(1) next_outready_reg_def)

lemma nonneg_delay_next_outready_reg: "nonneg_delay (get_seq next_outready_reg)"
  using nonneg_delay_conc_next_outready_reg by (auto simp add: next_outready_reg_def)

definition "ctr_neq_0 \<equiv> (process {COUNTER} : 
  Bassign_trans CTR_NEQ_0 (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0))) 1)"

lemma conc_stmt_wf_ctr_neq_0: "conc_stmt_wf ctr_neq_0"
  unfolding ctr_neq_0_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_ctr_neq_0 [simp]: "nonneg_delay_conc ctr_neq_0"
  unfolding ctr_neq_0_def by auto

lemma cwt_n0 [simp]: "conc_wt \<Gamma> ctr_neq_0"
  using cosine_locale_axioms unfolding cosine_locale_def ctr_neq_0_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_ctr_neq_0: "seq_wt \<Gamma> (get_seq ctr_neq_0)"
  using cwt_n0 by (metis conc_stmt.sel(4) conc_wt_cases(1) ctr_neq_0_def)

lemma nonneg_delay_ctr_neq_0: "nonneg_delay (get_seq ctr_neq_0)"
  using nonneg_delay_conc_ctr_neq_0 by (auto simp add: ctr_neq_0_def)
                        
definition "output \<equiv> (process {ACCUM} : 
  Bassign_trans OUTPUT (Bsig ACCUM) 1)"

lemma conc_stmt_wf_output: "conc_stmt_wf output"
  unfolding output_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_output [simp]: "nonneg_delay_conc output"
  unfolding output_def by auto

lemma cwt_output[simp]: "conc_wt \<Gamma> output"
  using cosine_locale_axioms unfolding cosine_locale_def output_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_output: "seq_wt \<Gamma> (get_seq output)"
  using cwt_output by (metis conc_stmt.sel(4) conc_wt_cases(1) output_def)

lemma nonneg_delay_output: "nonneg_delay (get_seq output)"
  using nonneg_delay_conc_output  by (simp add: output_def)

definition "output_ready \<equiv> (process {OUTREADY_REG} : 
  Bassign_trans OUTREADY (Bsig OUTREADY_REG) 1)"

lemma conc_stmt_wf_output_ready: "conc_stmt_wf output_ready"
  unfolding output_ready_def  conc_stmt_wf_def by auto

lemma nonneg_delay_conc_output_ready [simp]: "nonneg_delay_conc output_ready"
  unfolding output_ready_def by auto

lemma cwt_outready[simp]: "conc_wt \<Gamma> output_ready"
  using cosine_locale_axioms unfolding cosine_locale_def output_ready_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma seq_wt_output_ready: "seq_wt \<Gamma> (get_seq output_ready)"
  using cwt_outready by (metis conc_stmt.sel(4) conc_wt_cases(1) output_ready_def)

lemma nonneg_delay_output_ready: "nonneg_delay (get_seq output_ready)"
  using nonneg_delay_conc_output_ready by (auto simp add: output_ready_def)

definition "registers \<equiv> (process {CLK} : 
              Bguarded (Band (Bsig CLK) (Bsig_event CLK)) 
                (Bguarded (Bsig RST) 
                    (Bcomp (Bassign_trans ACCUM        (Bliteral Sig U_ZERO32) 1)      
                    (Bcomp (Bassign_trans COUNTER      (Bliteral Uns U_ZERO3 ) 1)      
                    (Bcomp (Bassign_trans FRAC         (Bliteral Sig U_ZERO32) 1) 
                    (Bcomp (Bassign_trans COMMON       (Bliteral Sig U_ZERO32) 1) 
                    (Bcomp (Bassign_trans STATE        (S_INIT)                1)
                           (Bassign_trans OUTREADY_REG (Bfalse)                1))))))

                    (Bcomp (Bassign_trans ACCUM        (Bsig NEXT_ACCUM)       1)     
                    (Bcomp (Bassign_trans COUNTER      (Bsig NEXT_COUNTER)     1)     
                    (Bcomp (Bassign_trans FRAC         (Bsig NEXT_FRAC)        1) 
                    (Bcomp (Bassign_trans COMMON       (Bsig NEXT_COMMON)      1) 
                    (Bcomp (Bassign_trans STATE        (Bsig NEXT_STATE)       1)
                           (Bassign_trans OUTREADY_REG (Bsig NEXT_OUTREADYREG) 1))))))) 
                (Bnull))"

lemma nonneg_delay_conc_registers [simp]: "nonneg_delay_conc registers"
  unfolding registers_def by auto

lemma cwt_reg [simp]: "conc_wt \<Gamma> registers"
  using cosine_locale_axioms unfolding cosine_locale_def registers_def
  by (auto intro!: conc_wt.intros seq_wt.intros bexp_wt.intros)

lemma conc_stmt_wf_registers: "conc_stmt_wf registers"
  unfolding registers_def  conc_stmt_wf_def by auto

definition architecture :: "sig conc_stmt" where
  "architecture \<equiv>     
              (   ((((next_common || squaring) || next_accum || term1) || output) || output_ready)  
              ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))) 
              ||  registers"

lemma nonneg_delay_conc_architecture : "nonneg_delay_conc architecture"
  unfolding architecture_def by auto

lemmas circuit_defs = registers_def next_state_def next_common_def squaring_def next_counter_def
next_accum_def term1_def next_frac_def next_outready_reg_def ctr_neq_0_def 
output_def output_ready_def

lemma conc_stmt_wf_arch: "conc_stmt_wf architecture"
  unfolding architecture_def circuit_defs conc_stmt_wf_def by auto

lemma cwt_arch[simp]: "conc_wt \<Gamma> architecture"
  using cosine_locale_axioms unfolding cosine_locale_def architecture_def
  by (auto intro!: conc_wt.intros)
                                                           
abbreviation is_posedge2 :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow>  bool" where
  "is_posedge2 w s j \<equiv> (snd w s (j - 1) = Bv False \<and> snd w s j = Bv True)"

fun next_signal :: "sig \<Rightarrow> sig" where
  "next_signal ACCUM        = NEXT_ACCUM" |
  "next_signal COUNTER      = NEXT_COUNTER" |
  "next_signal FRAC         = NEXT_FRAC" |
  "next_signal COMMON       = NEXT_COMMON" |
  "next_signal STATE        = NEXT_STATE" |
  "next_signal OUTREADY_REG = NEXT_OUTREADYREG"

abbreviation "bof_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

fun zero_of :: "sig \<Rightarrow> val" where
  "zero_of ACCUM        = V_ZERO32" |
  "zero_of COUNTER      = V_ZERO3" |
  "zero_of FRAC         = V_ZERO32" |
  "zero_of COMMON       = V_ZERO32" |
  "zero_of STATE        = V_INIT" |
  "zero_of OUTREADY_REG = Bv False"

section \<open>Functional specification of @{term "registers"}\<close>

definition inv_reg :: "sig assn2" where
  "inv_reg   tw \<equiv> (\<forall>s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}. 
                 1 < fst tw \<longrightarrow> wline_of tw s (fst tw) = (if is_posedge2 (snd tw) CLK (fst tw - 1) then 
                                                            if bof_wline tw RST (fst tw - 1) then zero_of s else wline_of tw (next_signal s) (fst tw - 1) 
                                                          else wline_of tw s (fst tw - 1)))"

lemma inv_reg_alt_def:
  "inv_reg tw \<longleftrightarrow> (1 < fst tw \<longrightarrow> (if wline_of (tw) CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
                                   then if bof_wline tw RST (fst tw - 1)
                                        then wline_of tw ACCUM (fst tw) = V_ZERO32
                                        else wline_of tw ACCUM (fst tw) = wline_of tw (NEXT_ACCUM) (fst tw - 1)
                                   else wline_of tw ACCUM (fst tw) = wline_of tw ACCUM (fst tw - 1)) 
                              \<and> (if wline_of (tw) CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
                                   then if bof_wline tw RST (fst tw - 1)
                                        then wline_of tw COUNTER (fst tw) = V_ZERO3
                                        else wline_of tw COUNTER (fst tw) = wline_of tw (NEXT_COUNTER) (fst tw - 1)
                                   else wline_of tw COUNTER (fst tw) = wline_of tw COUNTER (fst tw - 1))
                              \<and> (if wline_of (tw) CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
                                   then if bof_wline tw RST (fst tw - 1)
                                        then wline_of tw FRAC (fst tw) = V_ZERO32
                                        else wline_of tw FRAC (fst tw) = wline_of tw (NEXT_FRAC) (fst tw - 1)
                                   else wline_of tw FRAC (fst tw) = wline_of tw FRAC (fst tw - 1))
                              \<and> (if wline_of (tw) CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
                                   then if bof_wline tw RST (fst tw - 1)
                                        then wline_of tw COMMON (fst tw) = V_ZERO32
                                        else wline_of tw COMMON (fst tw) = wline_of tw (NEXT_COMMON) (fst tw - 1)
                                   else wline_of tw COMMON (fst tw) = wline_of tw COMMON (fst tw - 1))
                              \<and> (if wline_of (tw) CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
                                   then if bof_wline tw RST (fst tw - 1)
                                        then wline_of tw STATE (fst tw) = V_INIT
                                        else wline_of tw STATE (fst tw) = wline_of tw (NEXT_STATE) (fst tw - 1)
                                   else wline_of tw STATE (fst tw) = wline_of tw STATE (fst tw - 1))
                              \<and> (if wline_of (tw) CLK ((fst tw - 1) - 1) = Bv False \<and> wline_of tw CLK (fst tw - 1) = Bv True
                                   then if bof_wline tw RST (fst tw - 1)
                                        then wline_of tw OUTREADY_REG (fst tw) = Bv False
                                        else wline_of tw OUTREADY_REG (fst tw) = wline_of tw (NEXT_OUTREADYREG) (fst tw - 1)
                                   else wline_of tw OUTREADY_REG (fst tw) = wline_of tw OUTREADY_REG (fst tw - 1)))"
  unfolding inv_reg_def
  by simp

schematic_goal inv_reg_concrete:
  "inv_reg tw \<longleftrightarrow> eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_reg_alt_def
  apply (reify eval_simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        (" (1 < get_time tw \<longrightarrow>
     (if wline_of tw CLK (get_time tw - 1 - 1) = Bv False \<and> wline_of tw CLK (get_time tw - 1) = Bv True
      then if bval_of (wline_of tw RST (get_time tw - 1)) then wline_of tw ACCUM (get_time tw) = V_ZERO32 else wline_of tw ACCUM (get_time tw) = wline_of tw NEXT_ACCUM (get_time tw - 1)
      else wline_of tw ACCUM (get_time tw) = wline_of tw ACCUM (get_time tw - 1)) \<and>
     (if wline_of tw CLK (get_time tw - 1 - 1) = Bv False \<and> wline_of tw CLK (get_time tw - 1) = Bv True
      then if bval_of (wline_of tw RST (get_time tw - 1)) then wline_of tw COUNTER (get_time tw) = V_0 else wline_of tw COUNTER (get_time tw) = wline_of tw NEXT_COUNTER (get_time tw - 1)
      else wline_of tw COUNTER (get_time tw) = wline_of tw COUNTER (get_time tw - 1)) \<and>
     (if wline_of tw CLK (get_time tw - 1 - 1) = Bv False \<and> wline_of tw CLK (get_time tw - 1) = Bv True
      then if bval_of (wline_of tw RST (get_time tw - 1)) then wline_of tw FRAC (get_time tw) = V_ZERO32 else wline_of tw FRAC (get_time tw) = wline_of tw NEXT_FRAC (get_time tw - 1)
      else wline_of tw FRAC (get_time tw) = wline_of tw FRAC (get_time tw - 1)) \<and>
     (if wline_of tw CLK (get_time tw - 1 - 1) = Bv False \<and> wline_of tw CLK (get_time tw - 1) = Bv True
      then if bval_of (wline_of tw RST (get_time tw - 1)) then wline_of tw COMMON (get_time tw) = V_ZERO32 else wline_of tw COMMON (get_time tw) = wline_of tw NEXT_COMMON (get_time tw - 1)
      else wline_of tw COMMON (get_time tw) = wline_of tw COMMON (get_time tw - 1)) \<and>
     (if wline_of tw CLK (get_time tw - 1 - 1) = Bv False \<and> wline_of tw CLK (get_time tw - 1) = Bv True
      then if bval_of (wline_of tw RST (get_time tw - 1)) then wline_of tw STATE (get_time tw) = V_INIT else wline_of tw STATE (get_time tw) = wline_of tw NEXT_STATE (get_time tw - 1)
      else wline_of tw STATE (get_time tw) = wline_of tw STATE (get_time tw - 1)) \<and>
     (if wline_of tw CLK (get_time tw - 1 - 1) = Bv False \<and> wline_of tw CLK (get_time tw - 1) = Bv True
      then if bval_of (wline_of tw RST (get_time tw - 1)) then wline_of tw OUTREADY_REG (get_time tw) = Bv False else wline_of tw OUTREADY_REG (get_time tw) = wline_of tw NEXT_OUTREADYREG (get_time tw - 1)
      else wline_of tw OUTREADY_REG (get_time tw) = wline_of tw OUTREADY_REG (get_time tw - 1)))"))
  by rule

definition inv_reg2 :: "sig assn2" where
  "inv_reg2 tw \<equiv> disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True) \<longrightarrow> 
                    (\<forall>i > fst tw. \<forall>s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}. wline_of tw s i = wline_of tw s (fst tw))"

lemma inv_reg2_alt_def:
  "inv_reg2 tw \<longleftrightarrow> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True) \<longrightarrow> 
                    (\<forall>i. i > fst tw \<longrightarrow> (\<forall>s. s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG} \<longrightarrow> wline_of tw s i = wline_of tw s (fst tw))))"
  unfolding inv_reg2_def by auto

schematic_goal inv_reg2_concrete:
  "inv_reg2 tw \<longleftrightarrow> eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_reg2_alt_def
  apply (reify eval_simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (get_time tw) \<noteq> Bv True \<longrightarrow> (\<forall>i>get_time tw. \<forall>s. s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG} \<longrightarrow> wline_of tw s i = wline_of tw s (get_time tw)))"))
  by rule

definition 
  "inv_reg_comb \<equiv> Rsepand 
(RImp (RNLT (NC 1) (NFst (Wvar 0)))
       (RAnd
         (RIfte (RAnd (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NDec (NFst (Wvar 0))))) (VC (Bv False))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (VC (Bv True))))
           (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))) (NFst (Wvar 0))) (VC V_ZERO32))
             (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))) (NFst (Wvar 0)))
               (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))) (NDec (NFst (Wvar 0))))))
           (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))) (NFst (Wvar 0)))
             (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))) (NDec (NFst (Wvar 0))))))
         (RAnd
           (RIfte (RAnd (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NDec (NFst (Wvar 0))))) (VC (Bv False))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (VC (Bv True))))
             (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) (NFst (Wvar 0))) (VC V_0))
               (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))) (NDec (NFst (Wvar 0))))))
             (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) (NDec (NFst (Wvar 0))))))
           (RAnd
             (RIfte (RAnd (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NDec (NFst (Wvar 0))))) (VC (Bv False))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (VC (Bv True))))
               (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) (NFst (Wvar 0))) (VC V_ZERO32))
                 (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))) (NDec (NFst (Wvar 0))))))
               (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) (NDec (NFst (Wvar 0))))))
             (RAnd
               (RIfte (RAnd (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NDec (NFst (Wvar 0))))) (VC (Bv False))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (VC (Bv True))))
                 (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NFst (Wvar 0))) (VC V_ZERO32))
                   (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) (NDec (NFst (Wvar 0))))))
                 (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NDec (NFst (Wvar 0))))))
               (RAnd
                 (RIfte (RAnd (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NDec (NFst (Wvar 0))))) (VC (Bv False))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (VC (Bv True))))
                   (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NFst (Wvar 0))) (VC V_INIT))
                     (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (NDec (NFst (Wvar 0))))))
                   (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NDec (NFst (Wvar 0))))))
                 (RIfte (RAnd (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NDec (NFst (Wvar 0))))) (VC (Bv False))) (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (VC (Bv True))))
                   (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC (Bv False)))
                     (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))))
                   (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))))))
     (RImp (ROr (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) LEmpty) (Wvar 0)) (Rnot (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (NFst (Wvar 0))) (VC (Bv True)))))
       (RNall
         (RImp (RNLT (NFst (Wvar 0)) (NVar 0))
           (RSigall
             (LCons (Svar (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))
               (LCons (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))))))
             (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))
"

definition
  "inv_reg_FV = [OUTREADY_REG, NEXT_OUTREADYREG, RST, CLK, STATE, NEXT_STATE, COMMON, NEXT_COMMON, FRAC, NEXT_FRAC, COUNTER, NEXT_COUNTER, ACCUM, NEXT_ACCUM, OUTREADY_REG, STATE, COMMON, FRAC, COUNTER, ACCUM, CLK]"

lemma inv_reg_comb_alt_def:
  "inv_reg tw \<and> inv_reg2 tw \<longleftrightarrow> eval inv_reg_comb [tw] [] inv_reg_FV"
  unfolding inv_reg_alt_def inv_reg2_alt_def inv_reg_comb_def inv_reg_FV_def
  by simp

lemma inv_reg2_next_time_rst:
  fixes tw v
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 V_ZERO32][ COUNTER, 1 :=\<^sub>2 V_ZERO3][ FRAC, 1 :=\<^sub>2 V_ZERO32][ COMMON, 1 :=\<^sub>2 V_ZERO32][ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]"
  shows   "inv_reg2 (fst tw' + 1, snd tw')"
  unfolding inv_reg2_def tw'_def fst_worldline_upd2 
  by  (auto simp add: worldline_upd2_def worldline_upd_def)  

lemma inv_reg_next_time_rst:
  fixes tw
  assumes "eval_world_raw2 tw (Bsig RST) = Bv True"
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 V_ZERO32][ COUNTER, 1 :=\<^sub>2 V_ZERO3][ FRAC, 1 :=\<^sub>2 V_ZERO32][ COMMON, 1 :=\<^sub>2 V_ZERO32][ STATE, 1 :=\<^sub>2 V_INIT][ OUTREADY_REG, 1 :=\<^sub>2 Bv False]"
  assumes "\<not> disjnt {CLK} (event_of tw)"
  assumes "eval_world_raw2 tw (Bsig CLK) = Bv True"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_reg (fst tw' + 1, snd tw')"
  unfolding inv_reg_def
proof (rule ballI, rule impI)
  fix s
  assume "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  have "bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1))"
    using assms(1) unfolding eval_world_raw.simps fst_worldline_upd2 tw'_def 
    worldline_upd2_def worldline_upd_def by auto
  hence "bof_wline (fst tw' + 1, snd tw') RST (fst tw')"
    by auto
  assume "1 < get_time (get_time tw' + 1, snd tw')"
  hence "0 < fst tw" 
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have *: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
    using assms(3) `0 < fst tw` unfolding event_of_alt_def by auto
  have **: "wline_of tw CLK (fst tw) = Bv True"
    using assms(4) by auto
  hence "wline_of tw CLK (fst tw - 1) = Bv False"
    using *  by (smt assms(5) comp_apply ty.distinct(1) type_of.elims type_of.simps(1) wityping_def wtyping_def)
  hence prev_false: "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False"
    unfolding snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def by auto
  have curr_true : "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True"
    using ** unfolding snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def by auto
  hence "is_posedge2 (snd tw') CLK (fst tw')"
    using prev_false by auto
  have "wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) = wline_of (fst tw + 1, snd tw') s (fst tw + 1)"
    unfolding tw'_def fst_worldline_upd2 by auto
  also have "... = zero_of s"
    using zero_of.simps `s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}`
    unfolding tw'_def  worldline_upd2_def worldline_upd_def by auto
  finally show "wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) =
         (if snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False \<and>
             snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True
          then if bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1)) then zero_of s
               else wline_of (get_time tw' + 1, snd tw') (next_signal s) (get_time (get_time tw' + 1, snd tw') - 1)
          else wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw') - 1))"
    using `bof_wline (fst tw' + 1, snd tw') RST (fst tw')` `is_posedge2 (snd tw') CLK (fst tw')` 
    unfolding snd_conv fst_conv by auto
qed

lemma inv_reg_next_time_clk:
  fixes tw
  assumes "\<not> disjnt {CLK} (event_of tw)"
  assumes "eval_world_raw2 tw (Bsig RST) \<noteq> Bv True"
  assumes "eval_world_raw2 tw (Bsig CLK) = Bv True"
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) NEXT_ACCUM (fst tw)]
                   [ COUNTER, 1 :=\<^sub>2 snd (snd tw) NEXT_COUNTER (fst tw)]
                   [ FRAC, 1 :=\<^sub>2 snd (snd tw) NEXT_FRAC (fst tw)]
                   [ COMMON, 1 :=\<^sub>2 snd (snd tw) NEXT_COMMON (fst tw)]
                   [ STATE, 1 :=\<^sub>2 snd (snd tw) NEXT_STATE (fst tw)]
                   [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) NEXT_OUTREADYREG (fst tw)]"
  assumes "wityping \<Gamma> (snd tw)"
  assumes "inv_reg tw"
  shows   "inv_reg (fst tw' + 1, snd tw')"
  unfolding inv_reg_def
proof (rule, rule)
  have tw'_alt_def: "tw' = tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) (next_signal ACCUM) (fst tw)]
                             [ COUNTER, 1 :=\<^sub>2 snd (snd tw) (next_signal COUNTER) (fst tw)]
                             [ FRAC, 1 :=\<^sub>2 snd (snd tw) (next_signal FRAC) (fst tw)]
                             [ COMMON, 1 :=\<^sub>2 snd (snd tw) (next_signal COMMON) (fst tw)]
                             [ STATE, 1 :=\<^sub>2 snd (snd tw) (next_signal STATE) (fst tw)]
                             [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) (next_signal OUTREADY_REG) (fst tw)]"
    unfolding tw'_def next_signal.simps by auto
  have "\<Gamma> RST = Bty"
    using cosine_locale_axioms unfolding cosine_locale_def by auto
  hence "type_of (snd (snd tw) RST (fst tw)) = Bty" 
    using assms(5) unfolding wityping_def wtyping_def by auto
  hence "snd (snd tw) RST (get_time tw) = Bv False"
    using assms(2) assms(5) unfolding eval_world_raw.simps  by (metis ty.distinct(1) type_of.elims)
  hence not_bval: "\<not> bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1))"
    unfolding fst_worldline_upd2 tw'_def fst_conv worldline_upd2_def worldline_upd_def by auto 
  assume "1 < get_time (get_time tw' + 1, snd tw')"
  hence "0 < fst tw" 
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have *: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
    using assms(1) `0 < fst tw` unfolding event_of_alt_def by auto
  have **: "wline_of tw CLK (fst tw) = Bv True"
    using assms(3) by auto
  hence "wline_of tw CLK (fst tw - 1) = Bv False"
    using *  by (smt assms(5) comp_apply ty.distinct(1) type_of.elims type_of.simps(1) wityping_def wtyping_def)
  hence prev_false: "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False"
    unfolding snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def by auto
  have curr_true : "snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True"
    using ** unfolding snd_conv fst_conv tw'_def worldline_upd2_def worldline_upd_def by auto
  fix s 
  assume s_set: " s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
  have " wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) = wline_of (fst tw + 1, snd tw') s (fst tw + 1)"
    unfolding tw'_def fst_worldline_upd2 by auto
  also have "... = (snd (snd tw) (next_signal s) (fst tw))"
    using s_set unfolding tw'_alt_def worldline_upd2_def worldline_upd_def by auto
  also have "... = wline_of (get_time tw' + 1, snd tw') (next_signal s) (get_time (get_time tw' + 1, snd tw') - 1)"
    unfolding fst_conv tw'_alt_def worldline_upd2_def worldline_upd_def by auto 
  finally show "         wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw')) =
         (if snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1 - 1) = Bv False \<and>
             snd (snd (get_time tw' + 1, snd tw')) CLK (get_time (get_time tw' + 1, snd tw') - 1) = Bv True
          then if bval_of (wline_of (get_time tw' + 1, snd tw') RST (get_time (get_time tw' + 1, snd tw') - 1)) then zero_of s
               else wline_of (get_time tw' + 1, snd tw') (next_signal s) (get_time (get_time tw' + 1, snd tw') - 1)
          else wline_of (get_time tw' + 1, snd tw') s (get_time (get_time tw' + 1, snd tw') - 1))"
    using prev_false curr_true not_bval by auto
qed

lemma inv_reg2_next_time_clk:
  fixes tw
  defines "tw' \<equiv> tw[ ACCUM, 1 :=\<^sub>2 snd (snd tw) NEXT_ACCUM (fst tw)]
                   [ COUNTER, 1 :=\<^sub>2 snd (snd tw) NEXT_COUNTER (fst tw)]
                   [ FRAC, 1 :=\<^sub>2 snd (snd tw) NEXT_FRAC (fst tw)]
                   [ COMMON, 1 :=\<^sub>2 snd (snd tw) NEXT_COMMON (fst tw)]
                   [ STATE, 1 :=\<^sub>2 snd (snd tw) NEXT_STATE (fst tw)]
                   [ OUTREADY_REG, 1 :=\<^sub>2 snd (snd tw) NEXT_OUTREADYREG (fst tw)]"
  shows   "inv_reg2 (fst tw' + 1, snd tw')"
  unfolding inv_reg2_def tw'_def fst_worldline_upd2
  by (auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_reg_preserved:
  "\<And>tw. inv_reg tw \<and> inv_reg2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)) \<Longrightarrow> inv_reg (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv_reg tw \<and> inv_reg2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True))"
  hence "inv_reg tw" "inv_reg2 tw" and *: "(disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True))"
    by auto
  { fix s
    assume s_set: "s \<in> {ACCUM, COUNTER, FRAC, COMMON, STATE, OUTREADY_REG}"
    assume "0 < fst tw"
    hence "\<not> is_posedge2 (snd tw) CLK (fst tw)"
      using * unfolding event_of_alt_def by auto
    have **: " wline_of tw s (fst tw + 1) = wline_of tw s (fst tw)"
      using `inv_reg2 tw` * s_set unfolding inv_reg2_def by auto
    hence "wline_of tw s (fst tw + 1) = (if is_posedge2 (snd tw) CLK (fst tw) then 
                                            if bof_wline tw RST (fst tw) then zero_of s  else wline_of tw (next_signal s) (fst tw) 
                                         else wline_of tw s (fst tw))"
      using `\<not> is_posedge2 (snd tw) CLK (fst tw)` by auto }
  thus "inv_reg (fst tw + 1, snd tw)"
    unfolding inv_reg_def comp_def fst_conv snd_conv by auto
qed

lemma inv_reg2_preserved:
  "\<And>tw. inv_reg2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)) \<Longrightarrow> inv_reg2 (fst tw + 1, snd tw)"
  unfolding inv_reg2_def by auto

lemma correctness_registers':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> registers \<lbrace>\<lambda>tw. inv_reg (Suc (fst tw), snd tw) \<and> inv_reg2 (Suc(fst tw), snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> registers (\<lambda>tw. inv_reg  (fst tw + 1, snd tw) \<and> 
                                                          inv_reg2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_registers, rule nonneg_delay_conc_registers, rule cwt_reg, simp)
  unfolding registers_def wp3_conc_single'[OF cwt_reg[unfolded registers_def] nonneg_delay_conc_registers[unfolded registers_def]]                                        
proof (rule, rule)
  fix w 
  assume *: " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  consider (case0) "disjnt {CLK} (event_of w)"
    | (case1)"\<not> disjnt {CLK} (event_of w) \<and> eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) = Bv True \<and>  eval_world_raw2 w (Bsig RST) = Bv True"
    | (case2)"\<not> disjnt {CLK} (event_of w) \<and> eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) = Bv True \<and>  eval_world_raw2 w (Bsig RST) \<noteq> Bv True"
    | (case3)"\<not> disjnt {CLK} (event_of w) \<and> eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) \<noteq> Bv True"
    by auto
  thus "(if disjnt {CLK} (event_of w) then (inv_reg (get_time w + 1, snd w) \<and> inv_reg2 (get_time w + 1, snd w)) \<and> wityping \<Gamma> (snd w)
         else wp3_fun \<Gamma>
               (Bguarded (Band (Bsig CLK) (Bsig_event CLK))
                 (Bguarded (Bsig RST)
                   (Bcomp (Bassign_trans ACCUM (Bliteral Sig U_ZERO32) 1)
                     (Bcomp (Bassign_trans COUNTER (Bliteral Uns U_ZERO3) 1)
                       (Bcomp (Bassign_trans FRAC (Bliteral Sig U_ZERO32) 1)
                         (Bcomp (Bassign_trans COMMON (Bliteral Sig U_ZERO32) 1) (Bcomp (Bassign_trans STATE S_INIT 1) (Bassign_trans OUTREADY_REG Bfalse 1))))))
                   (Bcomp (Bassign_trans ACCUM (Bsig NEXT_ACCUM) 1)
                     (Bcomp (Bassign_trans COUNTER (Bsig NEXT_COUNTER) 1)
                       (Bcomp (Bassign_trans FRAC (Bsig NEXT_FRAC) 1)
                         (Bcomp (Bassign_trans COMMON (Bsig NEXT_COMMON) 1) (Bcomp (Bassign_trans STATE (Bsig NEXT_STATE) 1) (Bassign_trans OUTREADY_REG (Bsig NEXT_OUTREADYREG) 1)))))))
                 Bnull)
               (\<lambda>tw. inv_reg (get_time tw + 1, snd tw) \<and> inv_reg2 (get_time tw + 1, snd tw)) w)"
  proof (cases)
    case case0
    then show ?thesis 
      unfolding wp3_fun.simps eval_world_raw2_suc using "*" inv_reg2_preserved inv_reg_preserved 
      by auto
  next
    case case1
    moreover have  tyclk: "type_of (snd (snd w) CLK (get_time w)) = Bty"
      using * cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def by auto
    moreover have a: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)])"
    and  b: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)])"
    and  c: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)])"
    and  d: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bliteral Sig U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)])"
    and  e: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bliteral Sig
                                             U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w
                                                                          (Bliteral Uns
                                                                            U_ZERO3)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ STATE, 1 :=\<^sub>2 eval_world_raw2 w S_INIT])"
      using cosine_locale_axioms * unfolding cosine_locale_def eval_world_raw2_suc
      by (auto intro!: worldline_upd_eval_world_raw_preserve_wityping2)
    ultimately show ?thesis 
      unfolding wp3_fun.simps eval_world_raw2_suc using "*" case1 inv_reg2_next_time_rst inv_reg_next_time_rst
      by (auto split:val.splits)
  next
    case case2
    moreover have tyclk: "type_of (snd (snd w) CLK (get_time w)) = Bty"
      using * cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def by auto
    moreover have a: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)])"
    and  b: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)])"
    and c: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)])"
    and  d: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COMMON)])"
    and  e: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COMMON)][ STATE, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_STATE)])"
      using cosine_locale_axioms * unfolding cosine_locale_def eval_world_raw2_suc
      by (smt eval_world_raw.simps(10) wityping_def worldline_upd_eval_world_raw_preserve_wityping2 wtyping_def)+      
    ultimately show ?thesis 
      unfolding wp3_fun.simps eval_world_raw2_suc using "*" case2 inv_reg_next_time_clk inv_reg2_next_time_clk
      by (auto split:val.splits)
  next
    case case3
    hence "wline_of w CLK (get_time w) \<noteq> Bv True"
      by (auto split:val.splits)
    hence "(inv_reg (get_time w + 1, snd w) \<and> inv_reg2 (get_time w + 1, snd w)) \<and> wityping \<Gamma> (snd w)"
      using * inv_reg_preserved inv_reg2_preserved by auto
    thus ?thesis
      using case3 by auto
  qed       
qed

lemma correctness_registers:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> registers \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_registers' by auto

section \<open>Functional specification of @{term "next_state"}\<close>

definition inv_nstate :: "sig assn2" where
  "inv_nstate tw = (wline_of tw NEXT_STATE (fst tw) = 
                   (case wline_of tw STATE (fst tw - 1) of 
                      V_INIT \<Rightarrow> V_WAIT | 
                      V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then V_PRE else V_WAIT) |
                      V_PRE  \<Rightarrow> V_PROC  |
                      V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then V_PROC else V_POST) |
                      V_POST \<Rightarrow> V_WAIT |
                      _      \<Rightarrow> V_INIT
                   ))"

lemma inv_nstate_alt_def:
  "inv_nstate tw \<longleftrightarrow> (if wline_of tw STATE (fst tw - 1) = V_INIT
                     then wline_of tw NEXT_STATE (fst tw) = V_WAIT
                     else if wline_of tw STATE (fst tw - 1) = V_WAIT 
                          then if bof_wline tw INREADY (fst tw - 1) 
                               then  wline_of tw NEXT_STATE (fst tw) = V_PRE
                               else  wline_of tw NEXT_STATE (fst tw) = V_WAIT
                          else if wline_of tw STATE (fst tw - 1) = V_PRE
                               then wline_of tw NEXT_STATE (fst tw) = V_PROC
                               else if wline_of tw STATE (fst tw - 1) = V_PROC 
                                    then if bof_wline tw CTR_NEQ_0 (fst tw - 1)
                                         then wline_of tw NEXT_STATE (fst tw) = V_PROC
                                         else wline_of tw NEXT_STATE (fst tw) = V_POST
                                    else if wline_of tw STATE (fst tw - 1) = V_POST 
                                         then wline_of tw NEXT_STATE (fst tw) = V_WAIT
                                         else wline_of tw NEXT_STATE (fst tw) = V_INIT)"
  unfolding inv_nstate_def 
  by (simp split:val.splits signedness.splits list.splits bool.splits)

schematic_goal inv_nstate_concrete:
  "inv_nstate tw \<longleftrightarrow> eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_nstate_alt_def 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(if wline_of tw STATE (get_time tw - 1) = V_INIT then wline_of tw NEXT_STATE (get_time tw) = V_WAIT
     else if wline_of tw STATE (get_time tw - 1) = V_WAIT
          then if bval_of (wline_of tw INREADY (get_time tw - 1)) then wline_of tw NEXT_STATE (get_time tw) = V_PRE else wline_of tw NEXT_STATE (get_time tw) = V_WAIT
          else if wline_of tw STATE (get_time tw - 1) = V_PRE then wline_of tw NEXT_STATE (get_time tw) = V_PROC
               else if wline_of tw STATE (get_time tw - 1) = V_PROC
                    then if bval_of (wline_of tw CTR_NEQ_0 (get_time tw - 1)) then wline_of tw NEXT_STATE (get_time tw) = V_PROC else wline_of tw NEXT_STATE (get_time tw) = V_POST
                    else if wline_of tw STATE (get_time tw - 1) = V_POST then wline_of tw NEXT_STATE (get_time tw) = V_WAIT else wline_of tw NEXT_STATE (get_time tw) = V_INIT)"))
  by rule
  
definition inv_nstate2 :: "sig assn2" where
  "inv_nstate2 tw \<equiv> disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_STATE i = wline_of tw NEXT_STATE (fst tw))"

schematic_goal inv_nstate2_concrete:
  "inv_nstate2 tw \<longleftrightarrow> eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_nstate2_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        (" (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. wline_of tw NEXT_STATE i = wline_of tw NEXT_STATE (get_time tw)))"))
  by rule

definition 
  "inv_nstate_comb \<equiv> Rsepand
(RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0)))) (VC V_INIT)) (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_WAIT))
       (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0)))) (VC V_WAIT))
         (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_PRE))
           (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_WAIT)))
         (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0)))) (VC V_PRE)) (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_PROC))
           (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0)))) (VC V_PROC))
             (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0))))) (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_PROC))
               (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_POST)))
             (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0)))) (VC V_POST)) (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_WAIT))
               (RVEq (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))) (VC V_INIT)))))))
(RImp (RDisevt (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))"

lemma [simp]:
  "highest_idx_form_sig inv_nstate_comb = 8"
  unfolding inv_nstate_comb_def by auto

definition
  "inv_nstate_FV = [NEXT_STATE, STATE, CTR_NEQ_0, INREADY, NEXT_STATE, CTR_NEQ_0, INREADY, STATE]"

lemma [simp]:
  "length inv_nstate_FV = 8"
  unfolding inv_nstate_FV_def by auto

lemma inv_nstate_comb_alt_def:
  "inv_nstate tw \<and> inv_nstate2 tw \<longleftrightarrow> eval inv_nstate_comb [tw] [] inv_nstate_FV"
  unfolding inv_nstate_alt_def inv_nstate2_def inv_nstate_comb_def inv_nstate_FV_def
  by auto

lemma inv_nstate2_preserved:
  "\<And>tw. inv_nstate2 tw \<and> (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw)) \<Longrightarrow> inv_nstate2 (fst tw + 1, snd tw)"
  unfolding inv_nstate2_def by auto

lemma inv_nstate_preserved:
  "\<And>tw. inv_nstate tw \<and> inv_nstate2 tw \<and>  (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw)) \<Longrightarrow> inv_nstate (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv_nstate tw \<and> inv_nstate2 tw \<and> (disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw))"
  hence "inv_nstate tw" "inv_nstate2 tw" and *: "(disjnt {STATE, INREADY, CTR_NEQ_0} (event_of tw))"
    by auto
  have eq0: "wline_of tw STATE (fst tw) = wline_of tw STATE (fst tw - 1)" and 
       eq1: "wline_of tw INREADY (fst tw) = wline_of tw INREADY (fst tw - 1)" and 
       eq2: "wline_of tw CTR_NEQ_0 (fst tw) = wline_of tw CTR_NEQ_0 (fst tw - 1)"
    using * unfolding event_of_alt_def by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
  have "wline_of tw NEXT_STATE (fst tw + 1) = wline_of tw NEXT_STATE (fst tw)"
    using `inv_nstate2 tw` * unfolding inv_nstate2_def  by (simp add: next_time_world_at_least) 
  also have "... = (case wline_of tw STATE (fst tw) of 
                      V_INIT \<Rightarrow> V_WAIT | 
                      V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw) then V_PRE else V_WAIT) |
                      V_PRE  \<Rightarrow> V_PROC  |
                      V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw) then V_PROC else V_POST) |
                      V_POST \<Rightarrow> V_WAIT |
                      _      \<Rightarrow> V_INIT)"
    using `inv_nstate tw` unfolding inv_nstate_def eq0 eq1 eq2 by auto
  finally show "inv_nstate (fst tw + 1, snd tw)"
    unfolding inv_nstate_def by auto  
qed

lemma inv_nstate2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_STATE, 1 :=\<^sub>2 v]"
  shows   "inv_nstate2 (fst tw' + 1, snd tw')"
  unfolding inv_nstate2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma inv_nstate_vinit:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_WAIT]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
  using assms unfolding inv_nstate_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nstate_vwait_true:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_WAIT"
  assumes " snd (snd tw) INREADY (get_time tw) = Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_PRE]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
  using assms unfolding inv_nstate_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma mysigsimp:
  "(x :: signames) \<noteq> y \<Longrightarrow> Sname x \<noteq> Sname y"
  by auto

lemma inv_nstate_vwait_false:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_WAIT"
  assumes " snd (snd tw) INREADY (get_time tw) \<noteq>  Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_WAIT]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have assms2: "snd (snd tw) INREADY (fst tw) = Bv False"
    using `wityping \<Gamma> (snd tw)` 
    by (smt assms(2) cosine_locale_axioms cosine_locale_def ty.distinct(1) type_of.elims val.inject(1) wityping_def wtyping_def)
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_WAIT"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_WAIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv fst_worldline_upd2 comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1) tw'_def)
  ultimately show ?thesis
    using assms2 snd_worldline_upd2[OF mysigsimp[OF signames.simps(118)]] unfolding inv_nstate_def tw'_def 
    by auto
qed

lemma inv_nstate_vpre:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_PROC]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
  using assms unfolding inv_nstate_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nstate_vproc_true:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_PROC"
  assumes " snd (snd tw) CTR_NEQ_0 (get_time tw) = Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_PROC]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
  using assms unfolding inv_nstate_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nstate_vproc_false:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_PROC"
  assumes " snd (snd tw) CTR_NEQ_0 (get_time tw) \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_POST]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
proof -
  have assms2: "snd (snd tw) CTR_NEQ_0 (fst tw) = Bv False"
    using `wityping \<Gamma> (snd tw)` 
    by (smt assms(2) cosine_locale_axioms cosine_locale_def ty.distinct(1) type_of.elims val.inject(1) wityping_def wtyping_def)
  have "wline_of tw' NEXT_STATE (fst tw + 1) = V_POST"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PROC"
    using assms(2) snd_worldline_upd2 unfolding fst_conv fst_worldline_upd2 comp_def snd_conv 
    by (simp add: snd_worldline_upd2 assms(1) tw'_def)
  ultimately show ?thesis
    using assms2 snd_worldline_upd2[OF mysigsimp[OF signames.simps(442)]] unfolding inv_nstate_def tw'_def  by auto
qed

lemma inv_nstate_vpost:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) = V_POST"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_WAIT]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
  using assms unfolding inv_nstate_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nstate_others:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_INIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_WAIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PRE"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PROC"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_POST"
  defines "tw' \<equiv> tw[ NEXT_STATE, 1 :=\<^sub>2 V_INIT]"
  shows   "inv_nstate (fst tw' + 1, snd tw')"
  using assms unfolding inv_nstate_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma correctness_nstate':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace> next_state \<lbrace>\<lambda>tw. inv_nstate (fst tw + 1, snd tw) \<and> inv_nstate2 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_state (\<lambda>tw. inv_nstate  (fst tw + 1, snd tw) \<and> 
                                                           inv_nstate2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_state, rule nonneg_delay_conc_next_state, rule cwt_ns, simp)
  unfolding next_state_def wp3_conc_single'[OF cwt_ns[unfolded next_state_def] nonneg_delay_conc_next_state[unfolded next_state_def]]
  wp3_fun.simps fst_worldline_upd2
  using inv_nstate2 inv_nstate2_preserved inv_nstate_others inv_nstate_preserved inv_nstate_vinit
  inv_nstate_vpost inv_nstate_vpre inv_nstate_vproc_false inv_nstate_vproc_true
  inv_nstate_vwait_false inv_nstate_vwait_true by force
 
lemma correctness_nstate:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace> next_state \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_nstate' by auto

section \<open>Functional specification of @{term "next_common"}\<close>

abbreviation bin_of_at :: "sig \<Rightarrow> nat \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> int" ("bin'_of (1_) at'_time (1_) on (1_)") where
  "bin_of_at sig t tw \<equiv> sbl_to_bin (lof_wline tw sig t)"

definition inv_ncommon :: "sig assn2" where
  "inv_ncommon tw = ((bin_of NEXT_COMMON at_time fst tw on tw) = 
                      (case wline_of tw STATE (fst tw - 1) of    
                       V_INIT \<Rightarrow> 0 |
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) 
                                  then (bin_of INPUT at_time fst tw - 1 on tw) 
                                  else (bin_of COMMON at_time (fst tw - 1) on tw)) | 
                       V_PRE  \<Rightarrow> sbintrunc 31 (- (sbl_to_bin (nths 
                                                             (lof_wline tw SQUARE_TEMP (fst tw - 1)) 
                                                             {1 .. 32})))  |
                       V_PROC \<Rightarrow> sbintrunc 31 (- bin_of COMMON at_time fst tw - 1 on tw) |
                       _      \<Rightarrow>   bin_of COMMON at_time fst tw - 1 on tw 
                    ))"

lemma inv_ncommon_alt_def:
  "inv_ncommon tw = 
    (if wline_of tw STATE (fst tw - 1) = V_INIT 
     then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (fst tw))) = 0 
     else if wline_of tw STATE (fst tw - 1) = V_WAIT 
          then if bval_of (wline_of tw INREADY (fst tw - 1)) 
               then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (fst tw))) = sbl_to_bin (lval_of (wline_of tw INPUT (fst tw - 1))) 
               else sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (fst tw))) = sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1)))
          else if wline_of tw STATE (fst tw - 1) = V_PRE
               then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (fst tw))) = sbintrunc 31 (- (sbl_to_bin (nths (lval_of (wline_of tw SQUARE_TEMP (fst tw - 1))) {1 .. 32})))
               else if wline_of tw STATE (fst tw - 1) = V_PROC 
                    then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (fst tw))) = sbintrunc 31 (- (sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1)))))
                    else sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (fst tw))) = sbl_to_bin (lval_of (wline_of tw COMMON (fst tw - 1))))"
  unfolding inv_ncommon_def
  by (simp split:val.splits signedness.splits list.splits bool.splits)

schematic_goal inc_ncommon_concrete:
  "inv_ncommon tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_ncommon_alt_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
          ("(if wline_of tw STATE (get_time tw - 1) = V_INIT then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (get_time tw))) = 0
     else if wline_of tw STATE (get_time tw - 1) = V_WAIT
          then if bval_of (wline_of tw INREADY (get_time tw - 1)) then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (get_time tw))) = sbl_to_bin (lval_of (wline_of tw INPUT (get_time tw - 1)))
               else sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (get_time tw))) = sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw - 1)))
          else if wline_of tw STATE (get_time tw - 1) = V_PRE then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (get_time tw))) = sbintrunc 31 (- sbl_to_bin (nths (lval_of (wline_of tw SQUARE_TEMP (get_time tw - 1))) {1..32}))
               else if wline_of tw STATE (get_time tw - 1) = V_PROC then sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (get_time tw))) = sbintrunc 31 (- sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw - 1))))
                    else sbl_to_bin (lval_of (wline_of tw NEXT_COMMON (get_time tw))) = sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw - 1))))"))
  by rule

definition inv_ncommon2 :: "sig assn2" where
  "inv_ncommon2 tw \<equiv> disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_COMMON i = wline_of tw NEXT_COMMON (fst tw))"

schematic_goal inv_ncommon2_concrete:
  "inv_ncommon2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_ncommon2_def
  apply (reify eval_simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps 
        ("(disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. wline_of tw NEXT_COMMON i = wline_of tw NEXT_COMMON (get_time tw)))"))
  by rule

lemma inv_ncommon_comb_alt_def:
  "inv_ncommon tw \<and> inv_ncommon2 tw \<longleftrightarrow> eval (Rsepand ((RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_INIT)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (IC 0))
       (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_WAIT))
         (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (NDec (NFst (Wvar 0)))))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NDec (NFst (Wvar 0))))))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))))
         (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PRE))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Isbintrunc (NC 31) (INeg (Islice (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (NC 1) (NC 32)))))
           (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PROC))
             (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Isbintrunc (NC 31) (INeg (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))
             (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))))) 
                                                      ((RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))))) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))) 
        [tw] [] [COMMON, NEXT_COMMON, STATE, SQUARE_TEMP, INPUT, INREADY, NEXT_COMMON, SQUARE_TEMP, INPUT, INREADY, COMMON, STATE] "
  unfolding inv_ncommon_alt_def inv_ncommon2_def by auto

definition 
  "inv_ncommon_comb \<equiv> (Rsepand ((RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_INIT)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (IC 0))
       (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_WAIT))
         (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (NDec (NFst (Wvar 0)))))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NDec (NFst (Wvar 0))))))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))))
         (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PRE))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Isbintrunc (NC 31) (INeg (Islice (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (NC 1) (NC 32)))))
           (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PROC))
             (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Isbintrunc (NC 31) (INeg (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))
             (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))))) 
                                                      ((RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc (Suc 0)))))) (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))))) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))))"

lemma [simp]: 
  "highest_idx_form_sig inv_ncommon_comb = 12"
  unfolding inv_ncommon_comb_def by auto

definition 
  "inv_ncommon_free_vars \<equiv> [COMMON, NEXT_COMMON, STATE, SQUARE_TEMP, INPUT, INREADY, NEXT_COMMON, SQUARE_TEMP, INPUT, INREADY, COMMON, STATE]"

lemma [simp]:
  "length inv_ncommon_free_vars = 12"
  unfolding inv_ncommon_free_vars_def by auto

lemma inv_ncommon_comb_alt_def':
  "inv_ncommon tw \<and> inv_ncommon2 tw \<longleftrightarrow> eval inv_ncommon_comb [tw] [] inv_ncommon_free_vars"
  unfolding inv_ncommon_comb_def inv_ncommon_free_vars_def inv_ncommon_comb_alt_def by auto

lemma inv_ncommon2_preserved:
  "\<And>tw. inv_ncommon2 tw \<and> (disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw)) \<Longrightarrow> inv_ncommon2 (fst tw + 1, snd tw)"
  unfolding inv_ncommon2_def by auto

lemma inv_ncommon_preserved:
  "\<And>tw. inv_ncommon tw \<and> inv_ncommon2 tw \<and>  (disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw)) \<Longrightarrow> inv_ncommon (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv_ncommon tw \<and> inv_ncommon2 tw \<and> (disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw))"
  hence "inv_ncommon tw" "inv_ncommon2 tw" and *: "(disjnt {STATE, COMMON, INREADY, INPUT, SQUARE_TEMP} (event_of tw))"
    by auto
  have eq0: "wline_of tw STATE (fst tw) = wline_of tw STATE (fst tw - 1)" and 
       eq1: "wline_of tw INREADY (fst tw) = wline_of tw INREADY (fst tw - 1)" and 
       eq2: "wline_of tw INPUT (fst tw) = wline_of tw INPUT (fst tw - 1)" and 
       eq3: "wline_of tw COMMON (fst tw) = wline_of tw COMMON (fst tw - 1)" and
       eq4: "wline_of tw SQUARE_TEMP (fst tw) = wline_of tw SQUARE_TEMP (fst tw - 1)"
    using * unfolding event_of_alt_def by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
  have "  bin_of NEXT_COMMON at_time fst tw + 1 on tw = bin_of NEXT_COMMON at_time fst tw on tw"
    using `inv_ncommon2 tw` * unfolding inv_ncommon2_def  by (simp add: next_time_world_at_least) 
  thus "inv_ncommon (fst tw + 1, snd tw)"
    unfolding inv_ncommon_alt_def fst_conv comp_def snd_conv 
    using eq0 eq1 eq2 eq3 eq4
    by (smt \<open>inv_ncommon tw\<close> add_diff_cancel_right' comp_apply inv_ncommon_alt_def)
qed

lemma inv_ncommon2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_COMMON, 1 :=\<^sub>2 v]"
  shows   "inv_ncommon2 (fst tw' + 1, snd tw')"
  unfolding inv_ncommon2_def tw'_def worldline_upd2_def worldline_upd_def by auto

abbreviation lval_of_at_on :: "sig \<Rightarrow> nat \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> val" ("value'_of (1_) at'_time (1_) on (1_)") where
  "lval_of_at_on sig t tw \<equiv> wline_of tw sig t"

abbreviation lval_of_at :: "sig \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> val" ("curr'_value'_of (1_) on (1_)") where
  "lval_of_at sig tw \<equiv> wline_of tw sig (fst tw)"

lemma inv_ncommon_vwait_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 curr_value_of INPUT on tw]"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
  using assms unfolding inv_ncommon_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_ncommon_vwait_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 curr_value_of COMMON on tw]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have assms2: "curr_value_of INREADY on tw = Bv False"
    using `wityping \<Gamma> (snd tw)` 
    by (smt assms(2) cosine_locale_axioms cosine_locale_def o_apply ty.distinct(1) type_of.elims wityping_def wtyping_def)
  have "bin_of NEXT_COMMON at_time (fst tw + 1) on tw' = bin_of COMMON at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_WAIT"
    using assms(2) snd_worldline_upd2 unfolding fst_conv fst_worldline_upd2 tw'_def comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 mysigsimp[OF signames.distinct(423)] tw'_def)
  ultimately show ?thesis
    using assms2 unfolding inv_ncommon_def fst_worldline_upd2  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma sbl_to_bin_to_bl:
  "sbl_to_bin (to_bl (w :: 'a :: len word)) = sint w"
  unfolding sbl_to_bin_alt_def to_bl_bin sint_uint
  by auto

lemma [simp]: "sint (1::32 word) = 1"
  by eval

lemma inv_ncommon_vpre:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 eval_world_raw2 tw (Badd (Bnot (Bslice SQUARE_TEMP 62 31)) ONE)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have sqty: "type_of (snd (snd tw) SQUARE_TEMP (get_time tw)) = Lty Sig 64"
    using `wityping \<Gamma> (snd tw)` cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence len: "length (lval_of (wline_of tw SQUARE_TEMP (get_time tw))) = 64"
    using `wityping \<Gamma> (snd tw)` 
    by (metis comp_apply ty.distinct(1) ty.inject type_of.elims val.sel(3))
  have len': "(length (nths (lval_of (curr_value_of SQUARE_TEMP on tw)) {Suc 0..32})) = 32"
    unfolding length_nths len using card_slice[of "62" "64" "31"] by auto
  have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = (sbl_to_bin o lval_of) (eval_world_raw2 tw (Badd (Bnot (Bslice SQUARE_TEMP 62 31)) ONE))"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... =  sbl_to_bin (bin_to_bl (max (length (nths (lval_of (curr_value_of SQUARE_TEMP on tw)) {Suc 0..32})) 32) 
                                              (sbl_to_bin (map Not (nths (lval_of (curr_value_of SQUARE_TEMP on tw)) {Suc 0..32})) + sbl_to_bin (to_bl (1::32 word))))"
    using sqty unfolding eval_world_raw.simps comp_def eval_arith.simps by (auto split:val.splits signedness.splits simp del: bin_to_bl_def)
  also have "... = sbl_to_bin (bin_to_bl 32 (sbl_to_bin (map Not (nths (lval_of (wline_of tw SQUARE_TEMP (get_time tw))) {Suc 0..32})) + 1))"
    unfolding len' sbl_to_bin_to_bl by auto
  also have "... =  sbl_to_bin (bin_to_bl 32 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32}))))"
    unfolding len' using  len'  by (simp add: uminus_alt)
  also have "... = sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32})))"
    using  sbin_bl_bin_sbintruc by auto
  finally have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = 
                sbintrunc 31 (- (sbl_to_bin (nths (lof_wline tw SQUARE_TEMP (fst tw)) {1 .. 32})))"
    by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PRE"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 mysigsimp[OF signames.distinct(423)] tw'_def)
  ultimately show ?thesis
    using assms(2) unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma inv_ncommon_vproc:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 eval_world_raw2 tw (Badd (Bnot (Bsig COMMON)) ONE)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
proof -
  have "fst tw' = fst tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have coty: "type_of (curr_value_of COMMON on tw) = Lty Sig 32"
    using `wityping \<Gamma> (snd tw)` cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence len: "length (lval_of (wline_of tw COMMON (get_time tw))) = 32"
    using `wityping \<Gamma> (snd tw)`
    by (metis comp_apply ty.distinct(1) ty.inject type_of.elims val.sel(3))
  have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = (sbl_to_bin o lval_of) (eval_world_raw2 tw (Badd (Bnot (Bsig COMMON)) ONE))"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... =  sbl_to_bin (bin_to_bl 32 (sbl_to_bin (map Not (lval_of curr_value_of COMMON on tw)) + sbl_to_bin (to_bl (1 :: 32 word))))"
    using coty unfolding eval_world_raw.simps comp_def eval_arith.simps by (auto split:val.splits signedness.splits simp del: bin_to_bl_def)
  also have "... =  sbl_to_bin (bin_to_bl 32 (sbl_to_bin (map Not (lval_of curr_value_of COMMON on tw)) + 1))"
    unfolding sbl_to_bin_to_bl by auto
  also have "... =  sbl_to_bin (bin_to_bl 32 ( - sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw)))))"
    using  len  uminus_alt[where bs="lval_of curr_value_of COMMON on tw"] by auto
  also have "... = sbintrunc 31 ( - sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw))))"
    using  sbin_bl_bin_sbintruc by auto
  finally have "(bin_of NEXT_COMMON at_time (fst tw + 1) on tw') = 
                sbintrunc 31 ( - sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw))))"
    by auto
  moreover have "wline_of (get_time tw' + 1, snd tw') STATE (get_time (get_time tw' + 1, snd tw') - 1) = V_PROC"
    using assms(2) snd_worldline_upd2 unfolding fst_conv `fst tw' = fst tw` comp_def snd_conv 
    by (metis assms(1) comp_eq_dest_lhs diff_add_inverse2 mysigsimp[OF signames.distinct(423)] tw'_def)
  ultimately show ?thesis
    using assms(2) unfolding inv_ncommon_def `fst tw' = fst tw`  
    by (auto simp add: tw'_def worldline_upd2_def worldline_upd_def)
qed

lemma inv_ncommon_vinit:
  fixes tw
  assumes " curr_value_of STATE on tw = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2 V_ZERO32]"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
  using assms unfolding inv_ncommon_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_ncommon_others:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_WAIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PRE"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PROC"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COMMON, 1 :=\<^sub>2  eval_world_raw2 tw (Bsig COMMON)]"
  shows   "inv_ncommon (fst tw' + 1, snd tw')"
  using assms unfolding inv_ncommon_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma correctness_ncommon':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace> next_common \<lbrace>\<lambda>tw. inv_ncommon (get_time tw + 1, snd tw) \<and> inv_ncommon2 (get_time tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_common 
                        (\<lambda>tw. inv_ncommon  (fst tw + 1, snd tw) \<and>  inv_ncommon2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_common, rule nonneg_delay_conc_next_common, 
         rule cwt_nc, simp)
  unfolding next_common_def wp3_conc_single'[OF cwt_nc[unfolded next_common_def] nonneg_delay_conc_next_common[unfolded next_common_def]]
  wp3_fun.simps fst_worldline_upd2
  using inv_ncommon2_preserved inv_ncommon_preserved inv_ncommon2 inv_ncommon_vwait_false inv_ncommon_vwait_true
  inv_ncommon_vpre inv_ncommon_vproc inv_ncommon_vinit inv_ncommon_others by force

lemma correctness_ncommon:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace> next_common \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_ncommon' by blast

lemma correctness_ncommon_semantic:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace> next_common \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace>"
  using conc_sim_soundness[OF correctness_ncommon] 
  using conc_stmt_wf_next_common cwt_nc nonneg_delay_conc_next_common by blast

lemma init_ensures_ncommon:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_common (\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw)"
  unfolding next_common_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_ncommon (fst tw + 1, snd tw) \<and> inv_ncommon2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_common[unfolded next_common_def conc_stmt.sel(4)] nonneg_delay_next_common[unfolded next_common_def conc_stmt.sel(4)]], simp)
  unfolding wp3_fun.simps fst_worldline_upd2
  using inv_ncommon2_preserved inv_ncommon_preserved inv_ncommon2 inv_ncommon_vwait_false inv_ncommon_vwait_true
  inv_ncommon_vpre inv_ncommon_vproc inv_ncommon_vinit inv_ncommon_others by force
  
lemma 
  assumes "sim_fin2 w (i + 1) next_common tw'" and "wityping \<Gamma> w"
  shows "inv_ncommon tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_common cwt_nc nonneg_delay_conc_next_common correctness_ncommon init_ensures_ncommon]
  by auto
    
section \<open>Functional specification of @{term "squaring"}\<close>

definition inv_sqr :: "sig assn2" where
  "inv_sqr tw = (bin_of SQUARE_TEMP at_time fst tw on tw = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw)\<^sup>2))"

schematic_goal inv_sqr_concrete: 
  "inv_sqr tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_sqr_def power2_eq_square
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(sbl_to_bin (lval_of (wline_of tw SQUARE_TEMP (get_time tw))) = 
            sbintrunc 63 (sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw - 1))) * sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw - 1)))))"))
  by rule

definition inv_sqr2 :: "sig assn2" where
  "inv_sqr2 tw \<equiv> disjnt {COMMON} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bin_of SQUARE_TEMP at_time i on tw = bin_of SQUARE_TEMP at_time fst tw on tw)"

schematic_goal inv_sqr2_concrete:
  "inv_sqr2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_sqr2_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(disjnt {COMMON} (event_of tw) \<longrightarrow> 
            (\<forall>i>get_time tw. sbl_to_bin (lval_of (wline_of tw SQUARE_TEMP i)) = sbl_to_bin (lval_of (wline_of tw SQUARE_TEMP (get_time tw)))))"))
  by rule

definition 
  "inv_sqr_comb \<equiv> (Rsepand 
                        (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Isbintrunc (NC 63) (IMult (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))
                        (RImp (RDisevt (LCons (Svar (Suc 0)) LEmpty) (Wvar 0)) (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NVar 0))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))
                   )"

lemma [simp]:
  "highest_idx_form_sig inv_sqr_comb = 4"
  unfolding inv_sqr_comb_def by auto

definition 
  "inv_sqr_FV \<equiv> [COMMON, SQUARE_TEMP, SQUARE_TEMP, COMMON]"

lemma [simp]:
  "length inv_sqr_FV = 4"
  unfolding inv_sqr_FV_def by auto

lemma inv_sqr_comb_alt_def: 
  "inv_sqr tw \<and> inv_sqr2 tw \<longleftrightarrow> eval inv_sqr_comb [tw] [] inv_sqr_FV"
  unfolding inv_sqr_comb_def inv_sqr_FV_def inv_sqr_def inv_sqr2_def power2_eq_square
  by auto

lemma inv_sqr2_preserved:
  "\<And>tw. inv_sqr2 tw \<and> (disjnt {COMMON} (event_of tw)) \<Longrightarrow> inv_sqr2 (fst tw + 1, snd tw)"
  unfolding inv_sqr2_def by auto

lemma inv_sqr_preserved:
  "\<And>tw. inv_sqr tw \<and> inv_sqr2 tw \<and>  (disjnt {COMMON} (event_of tw)) \<Longrightarrow> inv_sqr (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_sqr tw \<and> inv_sqr2 tw \<and>  (disjnt {COMMON} (event_of tw)) "
  hence "inv_sqr tw" and "inv_sqr2 tw" and "disjnt {COMMON} (event_of tw)"
    by auto
  hence "bin_of SQUARE_TEMP at_time fst tw + 1 on tw = bin_of SQUARE_TEMP at_time fst tw on tw"
    unfolding inv_sqr2_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw)\<^sup>2)"
    using `inv_sqr tw` unfolding inv_sqr_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw)\<^sup>2)"
    using `disjnt {COMMON} (event_of tw)` unfolding event_of_alt_def 
    by (smt disjnt_insert1 mem_Collect_eq minus_eq)
  finally show "inv_sqr (fst tw + 1, snd tw)"
    unfolding inv_sqr_def by auto
qed

lemma inv_sqr_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig COMMON))"
  defines "tw' \<equiv> tw[SQUARE_TEMP , 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_sqr (fst tw' + 1, snd tw')"
proof -
  have *: "type_of (snd (snd tw) COMMON (fst tw)) = Lty Sig 32"
    using cosine_locale_axioms `wityping \<Gamma> (snd tw)` 
    unfolding wityping_def wtyping_def cosine_locale_def by auto
  have "bin_of SQUARE_TEMP at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of SQUARE_TEMP at_time fst tw' + 1 on tw'"
    unfolding fst_conv comp_def tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bin_of SQUARE_TEMP at_time fst tw + 1 on tw'"
    unfolding tw'_def fst_worldline_upd2 by auto
  also have "... = sbl_to_bin (lval_of v)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sbl_to_bin (bin_to_bl 64 ((sbl_to_bin (lval_of (curr_value_of COMMON on tw)))\<^sup>2))"
    using * unfolding v_def eval_world_raw.simps eval_arith.simps Let_def power_def by (auto split: val.splits)
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw)\<^sup>2)"
    using sbin_bl_bin_sbintruc by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw' on (fst tw' + 1, snd tw'))\<^sup>2)"
    unfolding tw'_def fst_worldline_upd2 comp_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    unfolding inv_sqr_def by auto
qed

lemma inv_sqr2_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig COMMON))"
  defines "tw' \<equiv> tw[SQUARE_TEMP , 1 :=\<^sub>2 v]"
  shows   "inv_sqr2 (fst tw' + 1, snd tw')"
  using assms unfolding inv_sqr2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_sqr':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace> squaring \<lbrace>\<lambda>tw. inv_sqr (get_time tw + 1, snd tw) \<and> inv_sqr2 (get_time tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> squaring (\<lambda>tw. inv_sqr  (fst tw + 1, snd tw) \<and> 
                                                         inv_sqr2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp3_conc_is_pre, rule conc_stmt_wf_squaring, rule nonneg_delay_conc_squaring, rule cwts, simp)
  unfolding squaring_def wp3_conc_single'[OF cwts[unfolded squaring_def] nonneg_delay_conc_squaring[unfolded squaring_def]] wp3_fun.simps 
  fst_worldline_upd2 using inv_sqr_preserved inv_sqr2_preserved inv_sqr2_next_time inv_sqr_next_time by force

lemma correctness_sqr:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace> squaring \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_sqr' by auto

lemma correctness_sqr_semantic:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace> squaring \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace>"
  using conc_sim_soundness[OF correctness_sqr] 
  using conc_stmt_wf_squaring cwts nonneg_delay_conc_squaring by blast

lemma inv_sqr_imp_wp3_conc_next_common:
  " \<forall>w. wityping \<Gamma> (snd w) \<and> inv_sqr w \<and> inv_sqr2 w \<longrightarrow> wp3_conc \<Gamma> next_common (\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw) w"
  apply (rule, rule, unfold next_common_def)       
  unfolding wp3_conc_single'[OF cwt_nc[unfolded next_common_def] nonneg_delay_conc_next_common[unfolded next_common_def]] wp3_fun.simps
  inv_sqr_def inv_sqr2_def fst_worldline_upd2 by (simp add: event_of_worldline_upd2 snd_worldline_upd2)

lemma inv_sqr_comb_preserved_next_common_squaring:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace> next_common || squaring \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw", rotated])
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_common nonneg_delay_conc_next_common cwt_nc], simp)
  using inv_sqr_imp_wp3_conc_next_common correctness_sqr'
  by (auto simp add: conc_stmt_wf_def squaring_def next_common_def)

lemma inv_sqr_comb_preserved_next_common_squaring2:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace> next_common || squaring \<lbrace>\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw\<rbrace>"
  apply (auto intro!: conc_wt.intros conc_sim_soundness[OF inv_sqr_comb_preserved_next_common_squaring])
  by (auto simp add: conc_stmt_wf_def next_common_def  squaring_def)

lemma inv_ncommon_imp_wp3_conc_squaring:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_ncommon w \<and> inv_ncommon2 w \<longrightarrow> wp3_conc \<Gamma> squaring (\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw) w"
  apply (rule, rule, unfold squaring_def)
  unfolding wp3_conc_single'[OF cwts[unfolded squaring_def] nonneg_delay_conc_squaring[unfolded squaring_def]] wp3_fun.simps
proof -
  fix w
  assume "wityping \<Gamma> (snd w) \<and> inv_ncommon w \<and> inv_ncommon2 w"
  consider "disjnt {COMMON} (event_of w)" | "\<not> disjnt {COMMON} (event_of w)"
    by auto
  thus "if disjnt {COMMON} (event_of w) then (inv_ncommon w \<and> inv_ncommon2 w) \<and> wityping \<Gamma> (snd w)
         else wityping \<Gamma> (snd w) \<and> inv_ncommon w[ SQUARE_TEMP, 1 :=\<^sub>2 eval_world_raw2 w (Bmult (Bsig COMMON) (Bsig COMMON))] \<and> inv_ncommon2 w[ SQUARE_TEMP, 1 :=\<^sub>2 eval_world_raw2 w (Bmult (Bsig COMMON) (Bsig COMMON))]"
  proof (cases)
    case 2
    moreover have "inv_ncommon w[ SQUARE_TEMP, 1 :=\<^sub>2 eval_world_raw2 w (Bmult (Bsig COMMON) (Bsig COMMON))]"
      using `wityping \<Gamma> (snd w) \<and> inv_ncommon w \<and> inv_ncommon2 w` 
      unfolding inv_ncommon_alt_def fst_worldline_upd2 
      by (auto simp add: snd_worldline_upd2 snd_worldline_upd2' split:val.splits signedness.splits)
    moreover have "inv_ncommon2 w[ SQUARE_TEMP, 1 :=\<^sub>2 eval_world_raw2 w (Bmult (Bsig COMMON) (Bsig COMMON))]"
      using `wityping \<Gamma> (snd w) \<and> inv_ncommon w \<and> inv_ncommon2 w` 
      unfolding inv_ncommon2_def fst_worldline_upd2 
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2)                             
    ultimately show ?thesis 
      using `wityping \<Gamma> (snd w) \<and> inv_ncommon w \<and> inv_ncommon2 w` by auto
  qed (auto simp add: `wityping \<Gamma> (snd w) \<and> inv_ncommon w \<and> inv_ncommon2 w`)
qed

lemma inc_ncommon_comb_preserved_by_squaring_ncommon:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace> squaring || next_common \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw", rotated])
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_squaring nonneg_delay_conc_squaring cwts], simp)
  using inv_ncommon_imp_wp3_conc_squaring correctness_ncommon'
  by (auto simp add: conc_stmt_wf_def squaring_def next_common_def)

lemma inc_ncommon_comb_preserved_by_squaring_ncommon2:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace>  next_common || squaring \<lbrace>\<lambda>tw. inv_ncommon tw \<and> inv_ncommon2 tw\<rbrace>"
  apply (rule sim_hoare_valid_wt_parallel_commute[THEN cnf.cnftac_eq_imp])
  apply (auto intro!: sim_hoare_valid_wt_parallel_commute conc_sim_soundness[OF inc_ncommon_comb_preserved_by_squaring_ncommon] conc_wt.intros)
  by (auto simp add: conc_stmt_wf_def circuit_defs)
  
lemma inv_ncommon_inv_sqr_comb:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)\<rbrace> 
            next_common || squaring 
        \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)\<rbrace>"
    using inv_sqr_comb_preserved_next_common_squaring2 inc_ncommon_comb_preserved_by_squaring_ncommon2
    unfolding sim_hoare_valid_wt_def by blast

lemma init_ensures_nsqr:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) squaring (\<lambda>tw. inv_sqr tw \<and> inv_sqr2 tw)"
  unfolding squaring_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_sqr (fst tw + 1, snd tw) \<and> inv_sqr2 (fst tw + 1, snd tw)", rotated])
    apply (rule wp3_fun_is_pre[OF seq_wt_squaring[unfolded squaring_def conc_stmt.sel(4)] nonneg_delay_squaring[unfolded squaring_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_sqr2_next_time inv_sqr_next_time by blast

lemma 
  assumes "sim_fin2 w (i + 1) squaring tw'" and "wityping \<Gamma> w"
  shows "inv_sqr tw'"
  using grand_correctness[OF assms conc_stmt_wf_squaring cwts nonneg_delay_conc_squaring correctness_sqr init_ensures_nsqr]
  by auto

section \<open>Functional specfication for @{term "next_counter"}\<close>

abbreviation ubin_of_at :: "sig \<Rightarrow> nat \<Rightarrow> nat \<times> sig worldline_init \<Rightarrow> int" ("ubin'_of (1_) at'_time (1_) on (1_)") where
  "ubin_of_at sig t tw \<equiv> bl_to_bin (lof_wline tw sig t)"

definition inv_ncounter :: "sig assn2" where  
  "inv_ncounter tw = ((ubin_of NEXT_COUNTER at_time fst tw on tw) = 
                      (case wline_of tw STATE (fst tw - 1) of    
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then 4 else (ubin_of COUNTER at_time (fst tw - 1) on tw)) | 
                       V_PRE  \<Rightarrow> bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)  |
                       V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1) else (ubin_of COUNTER at_time (fst tw - 1) on tw)) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   ubin_of COUNTER at_time fst tw - 1 on tw 
                      ))"

lemma inv_ncounter_alt_def:
  "inv_ncounter tw = (if wline_of tw STATE (fst tw - 1) = V_WAIT  
                      then if bof_wline tw INREADY (fst tw - 1) 
                           then ubin_of NEXT_COUNTER at_time fst tw on tw = 4 
                           else ubin_of NEXT_COUNTER at_time fst tw on tw = ubin_of COUNTER at_time  (fst tw - 1) on tw
                      else if wline_of tw STATE (fst tw - 1) = V_PRE 
                           then ubin_of NEXT_COUNTER at_time fst tw on tw = bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)
                           else if wline_of tw STATE (fst tw - 1) = V_PROC
                                then if bof_wline tw CTR_NEQ_0 (fst tw - 1)
                                     then ubin_of NEXT_COUNTER at_time fst tw on tw = bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)
                                     else ubin_of NEXT_COUNTER at_time fst tw on tw = (ubin_of COUNTER at_time (fst tw - 1) on tw)
                                else if wline_of tw STATE (fst tw - 1) = V_INIT
                                     then ubin_of NEXT_COUNTER at_time fst tw on tw = 0
                                     else ubin_of NEXT_COUNTER at_time fst tw on tw = ubin_of COUNTER at_time fst tw - 1 on tw)"
  unfolding inv_ncounter_def
  by (simp split:val.splits signedness.splits list.splits bool.splits)

schematic_goal inv_ncounter_concrete:
  "inv_ncounter tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_ncounter_alt_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(if wline_of tw STATE (fst tw - 1) = V_WAIT  
                      then if bof_wline tw INREADY (fst tw - 1) 
                           then ubin_of NEXT_COUNTER at_time fst tw on tw = 4 
                           else ubin_of NEXT_COUNTER at_time fst tw on tw = ubin_of COUNTER at_time  (fst tw - 1) on tw
                      else if wline_of tw STATE (fst tw - 1) = V_PRE 
                           then ubin_of NEXT_COUNTER at_time fst tw on tw = bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)
                           else if wline_of tw STATE (fst tw - 1) = V_PROC
                                then if bof_wline tw CTR_NEQ_0 (fst tw - 1)
                                     then ubin_of NEXT_COUNTER at_time fst tw on tw = bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)
                                     else ubin_of NEXT_COUNTER at_time fst tw on tw = (ubin_of COUNTER at_time (fst tw - 1) on tw)
                                else if wline_of tw STATE (fst tw - 1) = V_INIT
                                     then ubin_of NEXT_COUNTER at_time fst tw on tw = 0
                                     else ubin_of NEXT_COUNTER at_time fst tw on tw = ubin_of COUNTER at_time fst tw - 1 on tw)"))
  by rule

definition inv_ncounter2 :: "sig assn2" where
  "inv_ncounter2 tw \<equiv> disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_COUNTER i = wline_of tw NEXT_COUNTER (fst tw))"

schematic_goal inv_ncounter2_concrete:
  "inv_ncounter2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_ncounter2_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
          (" (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. wline_of tw NEXT_COUNTER i = wline_of tw NEXT_COUNTER (get_time tw)))"))
  by rule

definition 
  "inv_ncounter_comb \<equiv> Rsepand 
                           (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_WAIT))
       (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NDec (NFst (Wvar 0))))) (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (IC 4))
         (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Iubin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))))
       (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PRE))
         (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibintrunc (NC 3) (ISub (Iubin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))) (IC 1))))
         (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PROC))
           (RIfte (RBval (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))))
             (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibintrunc (NC 3) (ISub (Iubin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))) (IC 1))))
             (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Iubin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))))
           (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_INIT)) (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (IC 0))
             (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Iubin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))))
   (RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty)))) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))"

lemma [simp]:
 "highest_idx_form_sig inv_ncounter_comb = 10"
  unfolding inv_ncounter_comb_def by auto

definition 
  "inv_ncounter_FV \<equiv> [COUNTER, NEXT_COUNTER, STATE, CTR_NEQ_0, INREADY, NEXT_COUNTER, COUNTER, CTR_NEQ_0, INREADY, STATE]"

lemma [simp]:
  "length inv_ncounter_FV = 10"
  unfolding inv_ncounter_FV_def by auto

lemma inv_ncounter_comb_alt_def:
  "inv_ncounter tw \<and> inv_ncounter2 tw \<longleftrightarrow> eval inv_ncounter_comb [tw] [] inv_ncounter_FV"
  unfolding inv_ncounter_alt_def inv_ncounter2_def inv_ncounter_comb_def inv_ncounter_FV_def
  by auto
  
lemma inv_ncounter2_preserved:
  "\<And>tw. inv_ncounter2 tw \<and> (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw)) \<Longrightarrow> inv_ncounter2 (fst tw + 1, snd tw)"
  unfolding inv_ncounter2_def by auto

lemma inv_ncounter_preserved:
  "\<And>tw. inv_ncounter tw \<and> inv_ncounter2 tw \<and>  (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw)) \<Longrightarrow> inv_ncounter (fst tw + 1, snd tw)"
proof -
  fix tw
  assume *: "inv_ncounter tw \<and> inv_ncounter2 tw \<and>  (disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw))"
  hence 0: "bof_wline tw INREADY (fst tw) = bof_wline tw INREADY (fst tw - 1)" and 
        1: "ubin_of COUNTER at_time (fst tw) on tw = ubin_of COUNTER at_time (fst tw - 1) on tw" and 
        2: "bof_wline tw CTR_NEQ_0 (fst tw) = bof_wline tw CTR_NEQ_0 (fst tw - 1)" and 
        3: "value_of STATE at_time (fst tw - 1) on tw = curr_value_of STATE on tw"
    unfolding event_of_alt_def 
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+

  have  "inv_ncounter tw" and "inv_ncounter2 tw" and "disjnt {STATE, INREADY, CTR_NEQ_0, COUNTER} (event_of tw)"
    using * by auto
  hence "ubin_of NEXT_COUNTER at_time fst tw + 1 on tw = ubin_of NEXT_COUNTER at_time fst tw on tw"
    unfolding inv_ncounter2_def by auto
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw - 1) then 4 else (ubin_of COUNTER at_time (fst tw - 1) on tw)) | 
                       V_PRE  \<Rightarrow> bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1)  |
                       V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw - 1) then bintrunc 3 ((ubin_of COUNTER at_time fst tw - 1 on tw) - 1) else (ubin_of COUNTER at_time (fst tw - 1) on tw)) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   ubin_of COUNTER at_time fst tw - 1 on tw 
                      )"
    using `inv_ncounter tw` unfolding inv_ncounter_def by auto
  also have "... = (case curr_value_of STATE on tw of    
                       V_WAIT \<Rightarrow> (if bof_wline tw INREADY (fst tw) then 4 else (ubin_of COUNTER at_time (fst tw) on tw)) | 
                       V_PRE  \<Rightarrow> bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1)  |
                       V_PROC \<Rightarrow> (if bof_wline tw CTR_NEQ_0 (fst tw) then bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1) else (ubin_of COUNTER at_time (fst tw) on tw)) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   ubin_of COUNTER at_time fst tw on tw 
                      )"
    unfolding 0 1 2 3 by auto
  finally show "inv_ncounter (fst tw + 1, snd tw)"
    unfolding inv_ncounter_def by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_ncounter_vwait_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 Lv Uns (to_bl (4 :: 3 word))]"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
  using assms unfolding inv_ncounter_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def, eval)

lemma inv_ncounter_vwait_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_WAIT"
  assumes " curr_value_of INREADY on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig COUNTER)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof - 
  have *: "curr_value_of STATE on tw' = V_WAIT"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "type_of ( snd (snd tw) INREADY (get_time tw)) = Bty"
    using assms(4) cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence "curr_value_of INREADY on tw = Bv False"
    using assms(2)  by (smt comp_apply ty.distinct(1) type_of.elims)
  hence **: "\<not> bof_wline tw' INREADY (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = ubin_of COUNTER at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    using * ** unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def 
    by auto
qed

lemma inv_ncounter_vpre:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 eval_world_raw2 tw (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 :: 3 word))))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -        
  have tyc: "type_of (snd (snd tw) COUNTER (get_time tw)) = Lty Uns 3"
    using assms(3) cosine_locale_axioms unfolding  wityping_def wtyping_def cosine_locale_def by auto
  have *: "curr_value_of STATE on tw' = V_PRE"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bl_to_bin (bin_to_bl 3 ((ubin_of COUNTER at_time fst tw on tw) - 1))"
    using tyc unfolding tw'_def worldline_upd2_def worldline_upd_def eval_world_raw.simps eval_arith.simps Let_def
    by (auto split: val.splits)
  also have "... = bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1)"
    unfolding bin_bl_bin by auto
  finally show ?thesis
    using * unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def
    by auto
qed

lemma inv_ncounter_vproc_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2  eval_world_raw2 tw (Bsub (Bsig COUNTER) (Bliteral Uns (to_bl (1 :: 3 word))))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -
  have tyc: "type_of (snd (snd tw) COUNTER (get_time tw)) = Lty Uns 3"
    using assms(4) cosine_locale_axioms unfolding  wityping_def wtyping_def cosine_locale_def by auto
  have *: "curr_value_of STATE on tw' = V_PROC"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have **: "bof_wline tw' CTR_NEQ_0 (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bl_to_bin (bin_to_bl 3 ((ubin_of COUNTER at_time fst tw on tw) - 1))"
    using tyc unfolding tw'_def worldline_upd2_def worldline_upd_def by (auto split: val.splits)
  also have "... = bintrunc 3 ((ubin_of COUNTER at_time fst tw on tw) - 1)"
    unfolding bin_bl_bin by auto
  finally show ?thesis
    using * ** unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def 
    by auto
qed

lemma inv_ncounter_vproc_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2  eval_world_raw2 tw (Bsig COUNTER)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
proof -
  have *: "curr_value_of STATE on tw' = V_PROC"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "type_of ( snd (snd tw) CTR_NEQ_0 (get_time tw)) = Bty"
    using assms(4) cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence "curr_value_of CTR_NEQ_0 on tw = Bv False"
    using assms(2)  by (smt comp_apply ty.distinct(1) type_of.elims)
  hence **: "\<not> bof_wline tw' CTR_NEQ_0 (fst tw')"
    using assms(2) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have "(ubin_of NEXT_COUNTER at_time fst tw' + 1 on (fst tw' + 1, snd tw')) =  (ubin_of NEXT_COUNTER at_time fst tw + 1 on tw')"  
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = ubin_of COUNTER at_time fst tw on tw"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    using * ** unfolding tw'_def inv_ncounter_def fst_conv comp_def snd_conv worldline_upd2_def worldline_upd_def 
    by auto
qed

lemma inv_ncounter_vinit:
  fixes tw
  assumes " curr_value_of STATE on tw = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2 Lv Uns (to_bl (0 :: 3 word))]"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
  using assms unfolding inv_ncounter_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_ncounter_others:
  fixes tw
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_WAIT"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PRE"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_PROC"
  assumes " snd (snd tw) STATE (fst tw) \<noteq> V_INIT"
  defines "tw' \<equiv> tw[ NEXT_COUNTER, 1 :=\<^sub>2  eval_world_raw2 tw (Bsig COUNTER)]"
  shows   "inv_ncounter (fst tw' + 1, snd tw')"
  using assms unfolding inv_ncounter_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_ncounter2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_COUNTER, 1 :=\<^sub>2 v]"
  shows   "inv_ncounter2 (fst tw' + 1, snd tw')"
  unfolding inv_ncounter2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_ncounter':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace> next_counter \<lbrace>\<lambda>tw. inv_ncounter (get_time tw + 1, snd tw) \<and> inv_ncounter2 (get_time tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_counter (\<lambda>tw. inv_ncounter  (fst tw + 1, snd tw) \<and> 
                                                             inv_ncounter2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_counter, rule nonneg_delay_conc_next_counter, rule cwt_ncnt, simp)
  unfolding next_counter_def wp3_conc_single'[OF cwt_ncnt[unfolded next_counter_def] nonneg_delay_conc_next_counter[unfolded next_counter_def]] wp3_fun.simps 
  fst_worldline_upd2 using inv_ncounter_preserved inv_ncounter2_preserved inv_ncounter2 inv_ncounter_vwait_true
  inv_ncounter_vwait_false inv_ncounter_vpre inv_ncounter_vproc_true inv_ncounter_vproc_false
  inv_ncounter_vinit inv_ncounter_others by force 

lemma correctness_ncounter:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace> next_counter \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_ncounter' by auto

lemma correctness_ncounter_semantic:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace> next_counter \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace>"
  using conc_sim_soundness[OF correctness_ncounter] conc_stmt_wf_next_counter cwt_ncnt nonneg_delay_conc_next_counter 
  by blast

lemma inv_ncommon_and_inv_sqr_comb:
  "eval (Rsepand inv_ncommon_comb inv_sqr_comb) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV) \<longleftrightarrow> 
   (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)"
  using inv_ncommon_comb_alt_def' inv_sqr_comb_alt_def by auto

lemma eval_inv_ncommon_sqr_ncounter_comb:
  "eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) inv_ncounter_comb) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV @ inv_ncounter_FV) \<longleftrightarrow> 
  ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)"
  using inv_ncommon_comb_alt_def'[symmetric] inv_sqr_comb_alt_def[symmetric] inv_ncounter_comb_alt_def[symmetric]
  by auto
  
lemma inv_ncommon_sqr_ncounter_comb:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)\<rbrace> 
          (next_common || squaring) || next_counter 
        \<lbrace>\<lambda>tw. ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand inv_ncommon_comb inv_sqr_comb) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV)\<rbrace> 
                (next_common || squaring) 
             \<lbrace>\<lambda>tw. eval (Rsepand inv_ncommon_comb inv_sqr_comb) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV)\<rbrace>"
    using inv_ncommon_inv_sqr_comb unfolding inv_ncommon_and_inv_sqr_comb by auto
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_ncounter_comb [tw] [] inv_ncounter_FV\<rbrace> next_counter \<lbrace>\<lambda>tw. eval inv_ncounter_comb [tw] [] inv_ncounter_FV\<rbrace>"
    using correctness_ncounter_semantic unfolding inv_ncounter_comb_alt_def by auto
  have 2: "set  (inv_ncommon_free_vars @ inv_sqr_FV) \<inter> set (signals_from next_counter) = {}"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def next_counter_def by auto
  have 3: "set (inv_ncounter_FV) \<inter> set (signals_from (next_common || squaring)) = {}"
    unfolding inv_ncounter_FV_def next_common_def squaring_def by auto
  have 4: "nonneg_delay_conc ((next_common || squaring) || next_counter)"
    by auto
  have 5: "conc_stmt_wf ((next_common || squaring) || next_counter)"
    unfolding conc_stmt_wf_def next_common_def squaring_def next_counter_def by auto
  have 6: "conc_wt \<Gamma> ((next_common || squaring) || next_counter)"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig inv_ncounter_comb (length inv_ncounter_FV) 0"
    unfolding inv_ncounter_comb_def inv_ncounter_FV_def by auto
  have 10: "wf_assertion (Abs inv_ncounter_comb) (length []) (length inv_ncounter_FV)"
    unfolding inv_ncounter_comb_def inv_ncounter_FV_def by auto
  have 9: "wf_form_sig (Rsepand inv_ncommon_comb inv_sqr_comb) (length (inv_ncommon_free_vars @ inv_sqr_FV)) 0"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def by auto
  have 8: "wf_assertion (Abs (Rsepand inv_ncommon_comb inv_sqr_comb)) (length []) (length (inv_ncommon_free_vars @ inv_sqr_FV))"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) inv_ncounter_comb) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV @ inv_ncounter_FV)\<rbrace> 
                  ((next_common || squaring) || next_counter) 
              \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) inv_ncounter_comb) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV @ inv_ncounter_FV)\<rbrace>"  
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] by auto
  thus ?thesis
    unfolding eval_inv_ncommon_sqr_ncounter_comb by auto
qed

lemma init_ensures_ncounter:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_counter (\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw)"
  unfolding next_counter_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_ncounter (fst tw + 1, snd tw) \<and> inv_ncounter2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_counter[unfolded next_counter_def conc_stmt.sel(4)] nonneg_delay_next_counter[unfolded next_counter_def conc_stmt.sel(4)]], simp)
  unfolding fst_worldline_upd2 using inv_ncounter_preserved inv_ncounter2_preserved inv_ncounter2 inv_ncounter_vwait_true
  inv_ncounter_vwait_false inv_ncounter_vpre inv_ncounter_vproc_true inv_ncounter_vproc_false
  inv_ncounter_vinit inv_ncounter_others by force 

lemma 
  assumes "sim_fin2 w (i + 1) next_counter tw'" and "wityping \<Gamma> w"
  shows "inv_ncounter tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_counter cwt_ncnt nonneg_delay_conc_next_counter correctness_ncounter init_ensures_ncounter]
  by auto    
  
section \<open>Functional specification for @{term "next_accum"}\<close>  
                                                   
definition inv_naccum :: "sig assn2" where
  "inv_naccum tw = (bin_of NEXT_ACCUM at_time fst tw on tw = 
                   (case wline_of tw STATE (fst tw - 1) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw - 1 on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw - 1)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      ))"

lemma inv_naccum_alt_def:
  "inv_naccum tw = (if wline_of tw STATE (fst tw - 1) = V_PRE 
                    then bin_of NEXT_ACCUM at_time fst tw on tw = 0 
                    else if wline_of tw STATE (fst tw - 1) = V_PROC 
                         then bin_of NEXT_ACCUM at_time fst tw on tw = sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw - 1 on tw)) + 
                                                                                    (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw - 1)) {1 .. 32}))   )
                         else if wline_of tw STATE (fst tw - 1) = V_INIT 
                              then bin_of NEXT_ACCUM at_time fst tw on tw = 0
                              else bin_of NEXT_ACCUM at_time fst tw on tw = bin_of ACCUM at_time fst tw - 1 on tw)"
  unfolding inv_naccum_def 
  by (simp split: val.splits signedness.splits list.splits bool.splits)

schematic_goal inv_naccum_concrete:
  "inv_naccum tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_naccum_alt_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(if wline_of tw STATE (get_time tw - 1) = V_PRE then sbl_to_bin (lval_of (wline_of tw NEXT_ACCUM (get_time tw))) = 0
     else if wline_of tw STATE (get_time tw - 1) = V_PROC
          then sbl_to_bin (lval_of (wline_of tw NEXT_ACCUM (get_time tw))) = sbintrunc 31 (sbl_to_bin (lval_of (wline_of tw FRAC (get_time tw - 1))) + sbl_to_bin (nths (lval_of (wline_of tw TERM1 (get_time tw - 1))) {1..32}))
          else if wline_of tw STATE (get_time tw - 1) = V_INIT then sbl_to_bin (lval_of (wline_of tw NEXT_ACCUM (get_time tw))) = 0
               else sbl_to_bin (lval_of (wline_of tw NEXT_ACCUM (get_time tw))) = sbl_to_bin (lval_of (wline_of tw ACCUM (get_time tw - 1))))"))
  by rule

definition inv_naccum2 :: "sig assn2" where
  "inv_naccum2 tw \<equiv> disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw) \<longrightarrow> 
                          (\<forall>i > fst tw. wline_of tw NEXT_ACCUM i = wline_of tw NEXT_ACCUM (fst tw))"

lemma inv_naccum2_preserved:
  "\<And>tw. inv_naccum2 tw \<and> (disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw)) \<Longrightarrow> inv_naccum2 (fst tw + 1, snd tw)"
  unfolding inv_naccum2_def by auto

schematic_goal inv_naccum2_concrete:
  "inv_naccum2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_naccum2_def 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. wline_of tw NEXT_ACCUM i = wline_of tw NEXT_ACCUM (get_time tw)))"))
  by rule

definition 
  "inv_naccum_comb = Rsepand (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PRE)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (IC 0))
       (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PROC))
         (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0))))
           (Isbintrunc (NC 31) (IAdd (Ibin_of (Vwline (Wvar 0) (Svar (Suc (Suc (Suc (Suc 0))))) (NDec (NFst (Wvar 0))))) (Islice (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))) (NC 1) (NC 32)))))
         (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_INIT)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (IC 0))
           (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))))))
 (RImp (RDisevt (LCons (Svar (Suc (Suc (Suc (Suc 0))))) (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty)))) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))"

lemma [simp]:
  "highest_idx_form_sig inv_naccum_comb = 10"
  unfolding inv_naccum_comb_def by auto

definition 
  "inv_naccum_FV = [ACCUM, NEXT_ACCUM, STATE, TERM1, FRAC, NEXT_ACCUM, TERM1, FRAC, ACCUM, STATE]"

lemma [simp]:
  "length inv_naccum_FV = 10"
  unfolding inv_naccum_FV_def by auto

lemma inv_naccum_com_alt_def: 
  "inv_naccum tw \<and> inv_naccum2 tw \<longleftrightarrow> eval inv_naccum_comb [tw] [] inv_naccum_FV"
  unfolding inv_naccum_alt_def inv_naccum2_def inv_naccum_comb_def inv_naccum_FV_def
  by simp

lemma inv_naccum_preserved:
  "\<And>tw. inv_naccum tw \<and> inv_naccum2 tw \<and>  (disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw)) \<Longrightarrow> inv_naccum (fst tw + 1, snd tw)"
proof -
  fix tw
  assume *: "inv_naccum tw \<and> inv_naccum2 tw \<and> (disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw))"
  hence 0: "value_of ACCUM at_time (fst tw - 1) on tw = curr_value_of ACCUM on tw" and
        1: "value_of TERM1 at_time (fst tw - 1) on tw = curr_value_of TERM1 on tw" and
        2: "value_of FRAC at_time (fst tw - 1) on tw = curr_value_of FRAC on tw" and
        3: "value_of STATE at_time (fst tw - 1) on tw = curr_value_of STATE on tw"
    unfolding event_of_alt_def
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+ 

  have  "inv_naccum tw" and "inv_naccum2 tw" and "(disjnt {STATE, ACCUM, FRAC, TERM1} (event_of tw))"
    using * by auto
  hence "bin_of NEXT_ACCUM at_time fst tw + 1 on tw = bin_of NEXT_ACCUM at_time fst tw on tw"
    unfolding inv_naccum2_def by auto
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw - 1 on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw - 1)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    using `inv_naccum tw` unfolding inv_naccum_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    unfolding 1 2 3 by auto
  finally show "inv_naccum (fst tw + 1, snd tw)"
    using 0 unfolding inv_naccum_def by (simp_all split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_naccum_vpre:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PRE"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 V_ZERO32]"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
  using assms unfolding inv_naccum_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_naccum_vproc:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 eval_world_raw2 tw (Badd (Bsig FRAC) (Bslice TERM1 62 31))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
proof -
  have *: "snd (snd tw') STATE (get_time tw') = V_PROC"
    using assms(1) unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have **: "snd (snd tw') FRAC (get_time tw') = snd (snd tw) FRAC (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have ***: "snd (snd tw') TERM1 (get_time tw') = snd (snd tw) TERM1 (get_time tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  have tyfrac: "type_of (snd (snd tw) FRAC (get_time tw)) = Lty Sig 32"
    using assms(3) cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def
    by auto
  have tyterm : "type_of (snd (snd tw) TERM1 (get_time tw)) = Lty Sig 64"
    using assms(3) cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def
    by auto
  hence len: "length (lval_of (wline_of tw TERM1 (get_time tw))) = 64"
    using `wityping \<Gamma> (snd tw)`  by (metis comp_apply ty.distinct(1) ty.inject type_of.elims val.sel(3))
  have len': "(length (nths (lval_of (curr_value_of TERM1 on tw)) {Suc 0..32})) = 32"
    unfolding length_nths len using card_slice[of "62" "64" "31"] by auto
  have "bin_of NEXT_ACCUM at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_ACCUM at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... =  sbl_to_bin (bin_to_bl 32  (bin_of FRAC at_time fst tw on tw
                                                  +
                                               sbl_to_bin (nths (lval_of (curr_value_of TERM1 on tw)) {Suc 0..32})))"
    using tyterm tyfrac len' unfolding tw'_def worldline_upd2_def worldline_upd_def
    by (auto split:val.splits signedness.splits simp del: bin_to_bl_def)
  also have "... = sbintrunc 31 (bin_of FRAC at_time fst tw on tw
                                                  +
                                 sbl_to_bin (nths (lval_of (curr_value_of TERM1 on tw)) {Suc 0..32}))"
    using sbin_bl_bin_sbintruc by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PRE  \<Rightarrow> 0  |
                       V_PROC \<Rightarrow> sbintrunc 31 (sbl_to_bin (lval_of (value_of FRAC at_time fst tw on tw)) + 
                                              (sbl_to_bin (nths (lof_wline tw TERM1 (fst tw)) {1 .. 32}))   ) |
                       V_INIT \<Rightarrow> 0 |
                       _      \<Rightarrow>   bin_of ACCUM at_time fst tw - 1 on tw 
                      )"
    using assms(1) unfolding comp_def by auto
  finally show ?thesis
    using * assms(1) ** ***
    unfolding inv_naccum_def fst_conv comp_def snd_conv by (simp_all split: val.splits)
qed

lemma inv_naccum_vinit:
  fixes tw
  assumes " curr_value_of STATE on tw = V_INIT"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 V_ZERO32]"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
  using assms unfolding inv_naccum_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_naccum_others:
  fixes tw
  assumes " curr_value_of STATE on tw \<noteq> V_PRE"
  assumes " curr_value_of STATE on tw \<noteq> V_PROC"
  assumes " curr_value_of STATE on tw \<noteq> V_INIT"
  defines "tw' \<equiv> tw[ NEXT_ACCUM, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig ACCUM)]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_naccum (fst tw' + 1, snd tw')"
  using assms unfolding inv_naccum_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_naccum2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_ACCUM, 1 :=\<^sub>2 v]"
  shows   "inv_naccum2 (fst tw' + 1, snd tw')"
  unfolding inv_naccum2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_naccum':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace> next_accum \<lbrace>\<lambda>tw. inv_naccum (fst tw + 1, snd tw) \<and> inv_naccum2 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_accum (\<lambda>tw. inv_naccum  (fst tw + 1, snd tw) \<and> 
                                                           inv_naccum2 (fst tw + 1, snd tw))", rotated])  
    apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_accum, rule nonneg_delay_conc_next_accum, rule cwt_na, simp)
  unfolding next_accum_def wp3_conc_single'[OF cwt_na[unfolded next_accum_def] nonneg_delay_conc_next_accum[unfolded next_accum_def]] wp3_fun.simps 
  fst_worldline_upd2 using inv_naccum_preserved inv_naccum2_preserved inv_naccum2 inv_naccum_vpre
  inv_naccum_vproc inv_naccum_vinit inv_naccum_others by force

lemma correctness_naccum:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace> next_accum \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_naccum' by auto

lemma helper: "Lv Sig (to_bl (0 :: 32 word)) = V_ZERO32"
  by eval

lemma init_ensures_naccum:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_accum (\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw)"
  unfolding next_accum_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_naccum (fst tw + 1, snd tw) \<and> inv_naccum2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_next_accum[unfolded next_accum_def conc_stmt.sel(4)] nonneg_delay_next_accum[unfolded next_accum_def conc_stmt.sel(4)]], simp)
  unfolding next_accum_def wp3_conc_single'[OF cwt_na[unfolded next_accum_def] nonneg_delay_conc_next_accum[unfolded next_accum_def]] wp3_fun.simps 
  fst_worldline_upd2 using inv_naccum_preserved inv_naccum2_preserved inv_naccum2 inv_naccum_vpre
  inv_naccum_vproc inv_naccum_vinit inv_naccum_others by force

lemma 
  assumes "sim_fin2 w (i + 1) next_accum tw'" and "wityping \<Gamma> w"
  shows "inv_naccum tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_accum cwt_na nonneg_delay_conc_next_accum correctness_naccum init_ensures_naccum]
  by auto    

section \<open>Functional specification of @{term "term1"}\<close>

definition inv_term1 :: "sig assn2" where
  "inv_term1 tw = (bin_of TERM1 at_time fst tw on tw = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw) * (bin_of ACCUM at_time fst tw - 1 on tw)))"

schematic_goal inv_term1_concrete:
  "inv_term1 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_term1_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(sbl_to_bin (lval_of (wline_of tw TERM1 (get_time tw))) = sbintrunc 63 (sbl_to_bin (lval_of (wline_of tw COMMON (get_time tw - 1))) * sbl_to_bin (lval_of (wline_of tw ACCUM (get_time tw - 1)))))"))
  by rule

definition inv_term12 :: "sig assn2" where
  "inv_term12 tw \<equiv> disjnt {COMMON, ACCUM} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bin_of TERM1 at_time i on tw = bin_of TERM1 at_time fst tw on tw)"

schematic_goal inv_term12_concrete:
  "inv_term12 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_term12_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(disjnt {COMMON, ACCUM} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. sbl_to_bin (lval_of (wline_of tw TERM1 i)) = sbl_to_bin (lval_of (wline_of tw TERM1 (get_time tw)))))"))
  by rule

definition 
  "inv_term1_comb \<equiv> Rsepand 
 (RIEq (Ibin_of (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NFst (Wvar 0)))) (Isbintrunc (NC 63) (IMult (Ibin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0))))))))
(RImp (RDisevt (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty)) (Wvar 0)) (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NVar 0))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))
 "

lemma [simp]:
  "highest_idx_form_sig inv_term1_comb = 6"
  unfolding inv_term1_comb_def by auto

definition 
  "inv_term1_FV = [ACCUM, COMMON, TERM1, TERM1, ACCUM, COMMON]"

lemma [simp]:
  "length inv_term1_FV = 6"
  unfolding inv_term1_FV_def by auto

lemma inv_term1_comb_alt_def:
  "inv_term1 tw \<and> inv_term12 tw \<longleftrightarrow> eval inv_term1_comb [tw] [] inv_term1_FV"
  unfolding inv_term1_def inv_term12_def inv_term1_comb_def inv_term1_FV_def
  by simp

lemma inv_term12_preserved:
  "\<And>tw. inv_term12 tw \<and> (disjnt {COMMON, ACCUM} (event_of tw)) \<Longrightarrow> inv_term12 (fst tw + 1, snd tw)"
  unfolding inv_term12_def by auto

lemma inv_term1_preserved:
  "\<And>tw. inv_term1 tw \<and> inv_term12 tw \<and>  (disjnt {COMMON, ACCUM} (event_of tw)) \<Longrightarrow> inv_term1 (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_term1 tw \<and> inv_term12 tw \<and>  (disjnt {COMMON, ACCUM} (event_of tw)) "
  hence "inv_term1 tw" and "inv_term12 tw" and "disjnt {COMMON, ACCUM} (event_of tw)"
    by auto
  hence "bin_of TERM1 at_time fst tw + 1 on tw = bin_of TERM1 at_time fst tw on tw"
    unfolding inv_term12_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw - 1 on tw) * (bin_of ACCUM at_time fst tw - 1 on tw))"
    using `inv_term1 tw` unfolding inv_term1_def by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw) * (bin_of ACCUM at_time fst tw on tw))"
    using `disjnt {COMMON, ACCUM} (event_of tw)` unfolding event_of_alt_def 
    by (smt disjnt_insert1 mem_Collect_eq minus_eq)
  finally show "inv_term1 (fst tw + 1, snd tw)"
    unfolding inv_term1_def by auto
qed

lemma inv_term1_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig ACCUM))"
  defines "tw' \<equiv> tw[TERM1 , 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_term1 (fst tw' + 1, snd tw')"
proof -
  have *: "type_of (snd (snd tw) COMMON (fst tw)) = Lty Sig 32"
    using cosine_locale_axioms `wityping \<Gamma> (snd tw)` 
    unfolding wityping_def wtyping_def cosine_locale_def by auto
  have **: "type_of (snd (snd tw) ACCUM (fst tw)) = Lty Sig 32"
    using cosine_locale_axioms `wityping \<Gamma> (snd tw)` 
    unfolding wityping_def wtyping_def cosine_locale_def by auto
  have "bin_of TERM1 at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of TERM1 at_time fst tw' + 1 on tw'"
    unfolding fst_conv comp_def tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bin_of TERM1 at_time fst tw + 1 on tw'"
    unfolding tw'_def fst_worldline_upd2 by auto
  also have "... = sbl_to_bin (lval_of v)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sbl_to_bin (bin_to_bl 64 ((sbl_to_bin (lval_of (curr_value_of COMMON on tw))) * (sbl_to_bin (lval_of (curr_value_of ACCUM on tw)))))"
    using * ** unfolding v_def eval_world_raw.simps eval_arith.simps Let_def power_def by (auto split: val.splits)
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw on tw) * (bin_of ACCUM at_time fst tw on tw))"
    using sbin_bl_bin_sbintruc by auto
  also have "... = sbintrunc 63 ((bin_of COMMON at_time fst tw' on (fst tw' + 1, snd tw')) * (bin_of ACCUM at_time fst tw' on (fst tw' + 1, snd tw')))"
    unfolding tw'_def fst_worldline_upd2 comp_def worldline_upd2_def worldline_upd_def by auto
  finally show ?thesis
    unfolding inv_term1_def by auto
qed

lemma inv_term12_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bmult (Bsig COMMON) (Bsig ACCUM))"
  defines "tw' \<equiv> tw[TERM1 , 1 :=\<^sub>2 v]"
  shows   "inv_term12 (fst tw' + 1, snd tw')"
  using assms unfolding inv_term12_def tw'_def worldline_upd2_def worldline_upd_def by auto 

lemma correctness_term1': 
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace> term1 \<lbrace>\<lambda>tw. inv_term1 (fst tw + 1, snd tw) \<and> inv_term12 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> term1 (\<lambda>tw. inv_term1  (fst tw + 1, snd tw) \<and> 
                                                           inv_term12 (fst tw + 1, snd tw))", rotated])  
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_term1, rule nonneg_delay_conc_term1, rule cwt_t1, simp)
  unfolding term1_def wp3_conc_single'[OF cwt_t1[unfolded term1_def] nonneg_delay_conc_term1[unfolded term1_def]] wp3_fun.simps 
  fst_worldline_upd2 using inv_term1_preserved inv_term12_preserved inv_term1_next_time inv_term12_next_time
  by force
   
lemma correctness_term1:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace> term1 \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace>"
  apply (rule While_Suc) using correctness_term1' by auto

lemma correctness_term1_semantic:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace> term1 \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace>"
  using conc_sim_soundness[OF correctness_term1] conc_stmt_wf_term1 cwt_t1 nonneg_delay_conc_term1 
  by blast

lemma inv_term1_imp_wp3_conc_next_accum:
  " \<forall>w. wityping \<Gamma> (snd w) \<and> inv_term1 w \<and> inv_term12 w \<longrightarrow> wp3_conc \<Gamma> next_accum (\<lambda>tw. inv_term1 tw \<and> inv_term12 tw) w"
  apply (rule, rule, unfold next_accum_def)
  unfolding wp3_conc_single'[OF cwt_na[unfolded next_accum_def] nonneg_delay_conc_next_accum[unfolded next_accum_def]]
  wp3_fun.simps inv_term1_def inv_term12_def fst_worldline_upd2
  by (simp add: event_of_worldline_upd2 snd_worldline_upd2)

lemma inv_term_comb_preserved_next_accum_term1:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace> next_accum || term1 \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_term1 tw \<and> inv_term12 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_term1 tw \<and> inv_term12 tw", rotated])
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_accum nonneg_delay_conc_next_accum cwt_na], simp)
  using inv_term1_imp_wp3_conc_next_accum correctness_term1'
  by (auto simp add: conc_stmt_wf_def next_accum_def term1_def)

lemma inv_naccum_comb_imp_wp_conc_term1:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_naccum w \<and> inv_naccum2 w \<longrightarrow> wp3_conc \<Gamma> term1 (\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw) w"
  unfolding term1_def wp3_conc_single'[OF cwt_t1[unfolded term1_def] nonneg_delay_conc_term1[unfolded term1_def]]
  wp3_fun.simps inv_naccum_alt_def inv_naccum2_def fst_worldline_upd2
  by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2' split : val.splits)

lemma inv_naccum_comb_preserved_next_accum_term1:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace> term1 || next_accum \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw", rotated])
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_term1 nonneg_delay_conc_term1 cwt_t1], simp)
  using inv_naccum_comb_imp_wp_conc_term1 correctness_naccum'
  by (auto simp add: term1_def next_accum_def conc_stmt_wf_def)

lemma inv_naccum_term1_comb:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw)\<rbrace> 
              next_accum || term1 
        \<lbrace>\<lambda>tw. (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw)\<rbrace>"
proof -
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace> term1 || next_accum \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace>"
    apply (intro conc_sim_soundness[OF inv_naccum_comb_preserved_next_accum_term1])
    unfolding conc_stmt_wf_def term1_def next_accum_def apply auto
    using conc_wt.intros(2) next_accum_def term1_def by force
  moreover have "conc_stmt_wf (term1 || next_accum)"
    unfolding conc_stmt_wf_def term1_def next_accum_def by auto
  ultimately have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace> next_accum || term1 \<lbrace>\<lambda>tw. inv_naccum tw \<and> inv_naccum2 tw\<rbrace>"
    using sim_hoare_valid_wt_parallel_commute  by blast
  moreover have " \<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace> next_accum || term1 \<lbrace>\<lambda>tw. inv_term1 tw \<and> inv_term12 tw\<rbrace>"
    apply (intro conc_sim_soundness[OF inv_term_comb_preserved_next_accum_term1])
    unfolding conc_stmt_wf_def term1_def next_accum_def apply auto
    using conc_wt.intros(2) next_accum_def term1_def by force
  ultimately show ?thesis
    unfolding sim_hoare_valid_wt_def  by blast
qed

lemma inv_naccum_term1_alt_def:
  "(inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<longleftrightarrow> 
   eval (Rsepand inv_naccum_comb inv_term1_comb) [tw] [] (inv_naccum_FV @ inv_term1_FV)"
proof -
  have 0: "highest_idx_form_sig inv_naccum_comb = 10" and 1: "take 10 inv_naccum_FV = inv_naccum_FV" and 2: "length inv_naccum_FV = 10"
    and 3: "drop 10 inv_naccum_FV = []"
    unfolding inv_naccum_comb_def inv_naccum_FV_def by auto
  have "eval (Rsepand inv_naccum_comb inv_term1_comb) [tw] [] (inv_naccum_FV @ inv_term1_FV) \<longleftrightarrow>
        eval inv_naccum_comb [tw] [] (inv_naccum_FV) \<and> eval inv_term1_comb [tw] [] inv_term1_FV"
    using 0 1 2 3 by auto
  thus ?thesis
    unfolding inv_naccum_com_alt_def inv_term1_comb_alt_def by auto
qed

lemma inv_ncommon_sqr_ncounter_naccum_term1_comb:
  " eval (Rsepand ((Rsepand inv_ncommon_comb inv_sqr_comb)) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] []
                ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) \<longleftrightarrow> 
  ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))"
proof -
  have 0: "highest_idx_form_sig inv_ncommon_comb = 12" and 1: "highest_idx_form_sig inv_sqr_comb = 4" and 2: "highest_idx_form_sig inv_ncounter_comb = 10"
    and 3: "length inv_ncommon_free_vars = 12" and 4: "length inv_sqr_FV = 4" and 5: "length inv_ncounter_FV = 10" and 6: "length inv_naccum_FV = 10"
    and 7: "highest_idx_form_sig inv_naccum_comb = 10"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncounter_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def
              inv_naccum_FV_def inv_naccum_comb_def
    by auto
  have "eval (Rsepand ((Rsepand inv_ncommon_comb inv_sqr_comb)) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] []
                ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) \<longleftrightarrow> 
      eval inv_ncommon_comb [tw] [] (inv_ncommon_free_vars) \<and> eval inv_sqr_comb [tw] [] (inv_sqr_FV) \<and>
     eval inv_naccum_comb [tw] [] (inv_naccum_FV) \<and> eval inv_term1_comb [tw] [] (inv_term1_FV)"
    using 0 1 2 3 4 5 6 7 by auto
  thus ?thesis
    unfolding inv_ncommon_comb_alt_def'[symmetric] inv_sqr_comb_alt_def[symmetric]
    inv_ncounter_comb_alt_def[symmetric] inv_naccum_com_alt_def[symmetric] inv_term1_comb_alt_def[symmetric]
    by argo
qed

lemma comb_prop_next_common_squaring_next_accum_term1:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))\<rbrace>
          ((next_common || squaring)) || (next_accum || term1)
        \<lbrace>\<lambda>tw. ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval ((Rsepand inv_ncommon_comb inv_sqr_comb)) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV)\<rbrace> 
                  ((next_common || squaring)) 
              \<lbrace>\<lambda>tw. eval ((Rsepand inv_ncommon_comb inv_sqr_comb)) [tw] [] (inv_ncommon_free_vars @ inv_sqr_FV)\<rbrace>"  
    using inv_ncommon_inv_sqr_comb unfolding inv_ncommon_and_inv_sqr_comb by auto
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand inv_naccum_comb inv_term1_comb) [tw] [] (inv_naccum_FV @ inv_term1_FV) \<rbrace> 
                  next_accum || term1 
                \<lbrace>\<lambda>tw. eval (Rsepand inv_naccum_comb inv_term1_comb) [tw] [] (inv_naccum_FV @ inv_term1_FV)\<rbrace>"
    using inv_naccum_term1_comb unfolding inv_naccum_term1_alt_def by auto
  have 2: "set (inv_ncommon_free_vars @ inv_sqr_FV) \<inter> set (signals_from (next_accum || term1)) = {}"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def next_accum_def term1_def
    by auto
  have 3: "set (inv_naccum_FV @ inv_term1_FV) \<inter> set (signals_from ((next_common || squaring))) = {}"
    unfolding inv_naccum_FV_def inv_term1_FV_def next_common_def squaring_def next_counter_def by auto
  have 4: "nonneg_delay_conc (((next_common || squaring)) || (next_accum || term1)) "
    by auto
  have 5: "conc_stmt_wf (((next_common || squaring)) || (next_accum || term1))"
    unfolding conc_stmt_wf_def next_common_def squaring_def next_counter_def next_accum_def term1_def
    by auto
  have 6: "conc_wt \<Gamma> (((next_common || squaring)) || (next_accum || term1))"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig  (Rsepand inv_naccum_comb inv_term1_comb) (length (inv_naccum_FV @ inv_term1_FV)) 0"
    unfolding inv_naccum_comb_def inv_term1_comb_def inv_naccum_FV_def inv_term1_FV_def
    by auto
  have 8: "wf_assertion (Abs ((Rsepand inv_ncommon_comb inv_sqr_comb))) (length []) (length (inv_ncommon_free_vars @ inv_sqr_FV))"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncounter_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def
    by auto
  have 9: "wf_form_sig (((Rsepand inv_ncommon_comb inv_sqr_comb))) (length (inv_ncommon_free_vars @ inv_sqr_FV)) 0"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncounter_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def
    by auto
  have 10: "wf_assertion (Abs (Rsepand inv_naccum_comb inv_term1_comb)) (length []) (length (inv_naccum_FV @ inv_term1_FV))"
    unfolding inv_naccum_comb_def inv_term1_comb_def inv_naccum_FV_def inv_term1_FV_def
    by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] ([]) ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)\<rbrace>
  (next_common || squaring) || next_accum || term1
  \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] ([]) ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)\<rbrace>"
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] 
    by (metis append_Nil)
  thus ?thesis
    unfolding inv_ncommon_sqr_ncounter_naccum_term1_comb  by auto
qed

lemma init_ensures_term1:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) term1 (\<lambda>tw. inv_term1 tw \<and> inv_term12 tw)"
  unfolding term1_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_term1 (fst tw + 1, snd tw) \<and> inv_term12 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_term1[unfolded term1_def conc_stmt.sel(4)] nonneg_delay_term1[unfolded term1_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_term1_next_time inv_term12_next_time by blast

section \<open>Functional specification of @{term "next_frac"}\<close>

definition inv_nfrac :: "sig assn2" where
  "inv_nfrac tw \<equiv> ((bin_of NEXT_FRAC at_time fst tw on tw) = 
                      (case nat ubin_of COUNTER at_time fst tw - 1 on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | 
                          _ \<Rightarrow> 0))"

lemma inv_nfrac_alt_def:
  "inv_nfrac tw = (if ubin_of COUNTER at_time fst tw - 1 on tw = 0
                   then bin_of NEXT_FRAC at_time fst tw on tw = approx_one
                   else if ubin_of COUNTER at_time fst tw - 1 on tw = 1 
                        then bin_of NEXT_FRAC at_time fst tw on tw = approx_half
                        else if ubin_of COUNTER at_time fst tw - 1 on tw = 2
                             then bin_of NEXT_FRAC at_time fst tw on tw = approx_fourth
                             else if ubin_of COUNTER at_time fst tw - 1 on tw = 3 
                                  then bin_of NEXT_FRAC at_time fst tw on tw = approx_sixth
                                  else if ubin_of COUNTER at_time fst tw - 1 on tw = 4 
                                       then bin_of NEXT_FRAC at_time fst tw on tw = approx_eighth
                                       else bin_of NEXT_FRAC at_time fst tw on tw = 0)"
  unfolding inv_nfrac_def using bl_to_bin_ge0 antisym 
  by (auto split: nat.splits)

schematic_goal inv_nfrac_concrete:
  "inv_nfrac tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_nfrac_alt_def approx_one_def approx_half_def approx_fourth_def approx_eighth_def approx_sixth_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(if bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw - 1))) = 0 then sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw))) = 2147483647
     else if bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw - 1))) = 1 then sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw))) = 1073741824
          else if bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw - 1))) = 2 then sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw))) = 89478484
               else if bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw - 1))) = 3 then sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw))) = 2982616
                    else if bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw - 1))) = 4 then sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw))) = 53261
                         else sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw))) = 0)"))
  by rule
  
definition inv_nfrac2 :: "sig assn2" where
  "inv_nfrac2 tw \<equiv> disjnt {COUNTER} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bin_of NEXT_FRAC at_time i on tw = bin_of NEXT_FRAC at_time fst tw on tw)"

schematic_goal inv_nfrac2_concrete:
  "inv_nfrac2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_nfrac2_def 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(disjnt {COUNTER} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. sbl_to_bin (lval_of (wline_of tw NEXT_FRAC i)) = sbl_to_bin (lval_of (wline_of tw NEXT_FRAC (get_time tw)))))"))
  by rule

definition 
  "inv_nfrac_comb \<equiv> RAnd  (RIfte (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))) (IC 0)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (IC 2147483647))
       (RIfte (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))) (IC 1)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (IC 1073741824))
         (RIfte (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))) (IC 2)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (IC 89478484))
           (RIfte (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))) (IC 3)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (IC 2982616))
             (RIfte (RIEq (Iubin_of (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0))))) (IC 4)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (IC 53261))
               (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (IC 0)))))))
(RImp (RDisevt (LCons (Svar (Suc 0)) LEmpty) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RIEq (Ibin_of (Vwline (Wvar 0) (Svar 0) (NVar 0))) (Ibin_of (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))"

definition 
  "inv_nfrac_FV \<equiv> [NEXT_FRAC, COUNTER]"

lemma inv_nfrac_comb_alt_def:
  "inv_nfrac tw \<and> inv_nfrac2 tw \<longleftrightarrow> eval inv_nfrac_comb [tw] [] inv_nfrac_FV "
  unfolding inv_nfrac_alt_def inv_nfrac2_def inv_nfrac_comb_def inv_nfrac_FV_def
  approx_one_def approx_half_def approx_fourth_def approx_eighth_def approx_sixth_def
  by auto

lemma inv_nfrac2_preserved:
  "\<And>tw. inv_nfrac2 tw \<and> (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_nfrac2 (fst tw + 1, snd tw)"
  unfolding inv_nfrac2_def by auto

lemma inv_nfrac_preserved:
  "\<And>tw. inv_nfrac tw \<and> inv_nfrac2 tw \<and>  (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_nfrac (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_nfrac tw \<and> inv_nfrac2 tw \<and>  (disjnt {COUNTER} (event_of tw)) "
  hence "inv_nfrac tw" and "inv_nfrac2 tw" and "disjnt {COUNTER} (event_of tw)"
    by auto
  hence "bin_of NEXT_FRAC at_time fst tw + 1 on tw = bin_of NEXT_FRAC at_time fst tw on tw"
    unfolding inv_nfrac2_def by auto
  also have "... = (case nat ubin_of COUNTER at_time fst tw - 1 on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using `inv_nfrac tw` unfolding inv_nfrac_def by auto
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using `disjnt {COUNTER} (event_of tw)` unfolding event_of_alt_def 
    by (smt disjnt_insert1 mem_Collect_eq minus_eq)
  finally show "inv_nfrac (fst tw + 1, snd tw)"
    unfolding inv_nfrac_def by auto
qed

lemma eval_helper: "nat (bl_to_bin [True, False, False]) = 4"
          "nat (bl_to_bin [False, True, True]) = 3"
          "nat (bl_to_bin [False, True, False]) = 2"
          "nat (bl_to_bin [False, False, True]) = 1"
          "nat (bl_to_bin [False, False, False]) = 0"
    by eval+


lemma inv_nfrac_4:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_4"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_eighth :: 32 word))]"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
  using assms eval_helper unfolding inv_nfrac_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def, eval)


lemma inv_nfrac_3:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_3"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_sixth :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
  using assms eval_helper unfolding inv_nfrac_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def, eval)

lemma inv_nfrac_2:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_2"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_fourth :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
  using assms eval_helper unfolding inv_nfrac_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def, eval)

lemma inv_nfrac_1:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_1"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_half :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
  using assms eval_helper unfolding inv_nfrac_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def, eval)

lemma inv_nfrac_0:
  fixes tw
  assumes " curr_value_of COUNTER on tw = V_0"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (approx_one :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
  using assms eval_helper unfolding inv_nfrac_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def, eval)

lemma inv_nfrac_others:
  fixes tw
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (0 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (1 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (2 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (3 :: 3 word))"
  assumes " curr_value_of COUNTER on tw \<noteq> Lv Uns (to_bl (4 :: 3 word))"
  defines "tw' \<equiv> tw[ NEXT_FRAC, 1 :=\<^sub>2  Lv Sig (to_bl (0 :: 32 word))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nfrac (fst tw' + 1, snd tw')"
proof -
  have "type_of (snd (snd tw) COUNTER (fst tw)) = Lty Uns 3"
    using `wityping \<Gamma> (snd tw)` cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  then obtain bs where counter_is: " snd (snd tw) COUNTER (fst tw) = Lv Uns bs" and "length bs = 3"
    by (metis ty.distinct(1) ty.inject type_of.elims)
  have 0: "nat (bl_to_bin bs) \<noteq>  0"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq>  0" hence "nat (bl_to_bin bs) = 0"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 0"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 0"
      using `length bs = 3` by auto
    also have "... = [False, False, False]"
      by eval
    finally have "bs = [False, False, False]"
      unfolding bl_bin_bl by auto
    with assms(1) show False
      using counter_is unfolding comp_def by auto
  qed
  have 1: "nat (bl_to_bin bs) \<noteq> Suc 0"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc 0" hence "nat (bl_to_bin bs) = Suc 0"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 1"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 1"
      using `length bs = 3` by auto
    also have "... = [False, False, True]"
      by eval
    finally have "bs = [False, False, True]"
      unfolding bl_bin_bl by auto
    moreover have "to_bl (1 :: 3 word) = [False, False, True]"
      by eval
    ultimately show False
      using assms(2) counter_is unfolding comp_def by auto
  qed
  have 2: "nat (bl_to_bin bs) \<noteq> Suc (Suc 0)"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc (Suc 0)" hence "nat (bl_to_bin bs) = Suc (Suc 0)"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 2"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 2"
      using `length bs = 3` by auto
    also have "... = [False, True, False]"
      by eval
    finally have "bs = [False, True, False]"
      unfolding bl_bin_bl by auto
    with assms(3) show False
      using counter_is unfolding comp_def by auto
  qed
  have 3: "nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc 0))"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc 0))" hence "nat (bl_to_bin bs) = Suc (Suc (Suc 0))"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 3"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 3"
      using `length bs = 3` by auto
    also have "... = [False, True, True]"
      by eval
    finally have "bs = [False, True, True]"
      unfolding bl_bin_bl by auto
    with assms(4) show False
      using counter_is unfolding comp_def by auto
  qed
  have 4: "nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc (Suc 0)))"
  proof (rule ccontr)
    assume "\<not> nat (bl_to_bin bs) \<noteq> Suc (Suc (Suc (Suc 0)))" hence "nat (bl_to_bin bs) = Suc (Suc (Suc (Suc 0)))"
      by auto
    moreover have "nat (bl_to_bin bs) = bl_to_bin bs"
      using bl_to_bin_ge0 by auto
    ultimately have "bl_to_bin bs = 4"
      by auto
    hence "bin_to_bl (length bs) (bl_to_bin bs) = bin_to_bl 3 4"
      using `length bs = 3` by auto
    also have "... = [True, False, False]"
      by eval
    finally have "bs = [True, False, False]"
      unfolding bl_bin_bl by auto
    with assms(5) show False
      using counter_is unfolding comp_def by auto
  qed
  have "bin_of NEXT_FRAC at_time fst tw' + 1 on (fst tw' + 1, snd tw') = bin_of NEXT_FRAC at_time fst tw + 1 on tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = sint (0 :: 32 word)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def using sbl_to_bin_to_bl
    by auto
  also have "... = (0 :: int)"
    by eval
  also have "... = (case nat ubin_of COUNTER at_time fst tw on tw of 
                          0 \<Rightarrow> approx_one |
                          Suc 0 \<Rightarrow> approx_half |
                          Suc (Suc 0) \<Rightarrow> approx_fourth |
                          Suc (Suc (Suc 0)) \<Rightarrow> approx_sixth |
                          Suc (Suc (Suc (Suc 0))) \<Rightarrow> approx_eighth | _ \<Rightarrow> 0)"
    using 0 1 2 3 4 counter_is by (auto split: nat.splits)
  finally show ?thesis
    unfolding inv_nfrac_def fst_conv comp_def snd_conv tw'_def
    worldline_upd2_def worldline_upd_def by (auto)
qed

lemma inv_nfrac2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_FRAC, 1 :=\<^sub>2 v]"
  shows   "inv_nfrac2 (fst tw' + 1, snd tw')"
  unfolding inv_nfrac2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_nfrac':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace> next_frac \<lbrace>\<lambda>tw. inv_nfrac (fst tw + 1, snd tw) \<and> inv_nfrac2 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_frac (\<lambda>tw. inv_nfrac  (fst tw + 1, snd tw) \<and> 
                                                          inv_nfrac2 (fst tw + 1, snd tw))", rotated])  
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_frac, rule nonneg_delay_conc_next_frac, rule cwt_nf, simp)
  unfolding next_frac_def wp3_conc_single'[OF cwt_nf[unfolded next_frac_def] nonneg_delay_conc_next_frac[unfolded next_frac_def]] wp3_fun.simps 
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  apply (rule_tac[2] impI | rule_tac[2] conjI)+  apply (rule_tac[4] impI | rule_tac[4] conjI)+
  apply (rule_tac[6] impI | rule_tac[6] conjI)+  apply (rule_tac[8] impI | rule_tac[8] conjI)+
  apply (rule_tac[10] impI | rule_tac[10] conjI)+   
  subgoal using inv_nfrac_preserved inv_nfrac2_preserved by auto subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_4 by auto subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_3 by auto subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_2 by auto subgoal by auto
  subgoal 
  proof -
    fix tw
    assume *: "wityping \<Gamma> (snd tw) \<and> inv_nfrac tw \<and> inv_nfrac2 tw"
    assume "eval_world_raw2 tw (Bsig COUNTER) = eval_world_raw2 tw (Bliteral Uns (to_bl (1 :: 3 word)))"
    hence "snd (snd tw) COUNTER (get_time tw) = Lv Uns (to_bl (1 :: 3 word))"
      by auto
    also have "... = Lv Uns [False, False, True]"
      by eval
    finally have **: "curr_value_of COUNTER on tw = V_1"
      by auto
    hence "inv_nfrac
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))])"
      using inv_nfrac_1 * by auto
    moreover have "inv_nfrac2
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))])"
      using inv_nfrac2 by auto
    ultimately show " inv_nfrac
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))]) \<and>
    inv_nfrac2
     (get_time tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))] + 1, snd tw[ NEXT_FRAC, 1 :=\<^sub>2 eval_world_raw2 tw (Bliteral Sig (to_bl (approx_half :: 32 word)))])"
      by auto
  qed
  subgoal by auto
  subgoal using inv_nfrac2 inv_nfrac_0 by auto 
  subgoal using inv_nfrac_others inv_nfrac2 by auto
  done

lemma correctness_nfrac:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace> next_frac \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_nfrac' by auto

lemma eval_inv_ncommon_sqr_ncounter_naccum_term1_nfrac:
  " eval (Rsepand (Rsepand ((Rsepand inv_ncommon_comb inv_sqr_comb)) (Rsepand inv_naccum_comb inv_term1_comb)) inv_nfrac_comb) [tw] ([] @ [])
                (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_nfrac_FV) \<longleftrightarrow> 
    (((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) 
              \<and> (inv_nfrac tw \<and> inv_nfrac2 tw)"
  using inv_ncommon_comb_alt_def'[symmetric] inv_sqr_comb_alt_def[symmetric] inv_ncounter_comb_alt_def[symmetric] inv_naccum_com_alt_def[symmetric]
    inv_term1_comb_alt_def[symmetric] inv_nfrac_comb_alt_def[symmetric]  by auto

lemma comb_inv_ncommon_sqr_ncounter_naccum_term1_nfrac:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) 
              \<and> (inv_nfrac tw \<and> inv_nfrac2 tw)\<rbrace>
          (((next_common || squaring)) || (next_accum || term1)) || next_frac
        \<lbrace>\<lambda>tw. (((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw)))
              \<and> (inv_nfrac tw \<and> inv_nfrac2 tw)\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] ([]) ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)\<rbrace>
  (next_common || squaring) || next_accum || term1
  \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] ([]) ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)\<rbrace>"
    using comb_prop_next_common_squaring_next_accum_term1 unfolding inv_ncommon_sqr_ncounter_naccum_term1_comb
    by auto
  have  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace> next_frac \<lbrace>\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw\<rbrace>"
    apply (intro conc_sim_soundness[OF correctness_nfrac])
    unfolding next_frac_def conc_stmt_wf_def apply auto
    using next_frac_def by auto
  hence 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_nfrac_comb [tw] [] inv_nfrac_FV\<rbrace> next_frac \<lbrace>\<lambda>tw. eval inv_nfrac_comb [tw] [] inv_nfrac_FV\<rbrace>"
    unfolding inv_nfrac_comb_alt_def by auto
  have 2: "set ((inv_ncommon_free_vars @ inv_sqr_FV) @ ((inv_naccum_FV @ inv_term1_FV))) \<inter> set (signals_from next_frac) = {}"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def inv_naccum_FV_def inv_term1_FV_def next_frac_def
    by auto
  have 3: "set (inv_nfrac_FV) \<inter> set (signals_from (((next_common || squaring)) || (next_accum || term1))) = {}"
    unfolding inv_nfrac_FV_def next_common_def squaring_def next_counter_def next_accum_def term1_def by auto
  have 4: "nonneg_delay_conc ((((next_common || squaring)) || (next_accum || term1)) || next_frac)"
    by auto
  have 5: "conc_stmt_wf ((((next_common || squaring)) || (next_accum || term1)) || next_frac)"
    unfolding conc_stmt_wf_def next_common_def squaring_def next_counter_def next_accum_def term1_def next_frac_def
    by auto
  have 6: "conc_wt \<Gamma> ((((next_common || squaring)) || (next_accum || term1)) || next_frac)"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig inv_nfrac_comb (length inv_nfrac_FV) 0"
    unfolding inv_nfrac_comb_def inv_nfrac_FV_def by auto
  have 8: "wf_assertion (Abs (Rsepand ((Rsepand inv_ncommon_comb inv_sqr_comb)) (Rsepand inv_naccum_comb inv_term1_comb))) (length []) 
              (length ((inv_ncommon_free_vars @ inv_sqr_FV) @ ((inv_naccum_FV @ inv_term1_FV))))"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncounter_comb_def inv_naccum_comb_def inv_term1_comb_def
    inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def inv_naccum_FV_def inv_term1_FV_def
    by auto
  have 9: "wf_form_sig (Rsepand ((Rsepand inv_ncommon_comb inv_sqr_comb)) (Rsepand inv_naccum_comb inv_term1_comb)) 
            (length ((inv_ncommon_free_vars @ inv_sqr_FV) @ ((inv_naccum_FV @ inv_term1_FV)))) 0" (is "wf_form_sig ?comb (length ?list) _")
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_ncounter_comb_def inv_naccum_comb_def inv_term1_comb_def
    inv_ncommon_free_vars_def inv_sqr_FV_def inv_ncounter_FV_def inv_naccum_FV_def inv_term1_FV_def
    by auto
  have 10: "wf_assertion (Abs inv_nfrac_comb) (length []) (length inv_nfrac_FV)"
    unfolding inv_nfrac_comb_def inv_nfrac_FV_def by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand ?comb inv_nfrac_comb) [tw] ([] @ []) (?list @ inv_nfrac_FV)\<rbrace> 
          (((next_common || squaring)) || (next_accum || term1)) || next_frac
              \<lbrace>\<lambda>tw. eval (Rsepand ?comb inv_nfrac_comb) [tw] ([] @ []) (?list @ inv_nfrac_FV)\<rbrace>"
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] by satx
  thus ?thesis
    unfolding eval_inv_ncommon_sqr_ncounter_naccum_term1_nfrac by blast
qed

lemma helper2: "Lv Uns (to_bl (4 :: 3 word)) = V_4"
  by eval

lemma helper3: "Lv Uns (to_bl (3 :: 3 word)) = V_3"
  by eval

lemma helper4: "Lv Uns (to_bl (2 :: 3 word)) = V_2"
  by eval

lemma helper5: "Lv Uns (to_bl (1 :: 3 word)) = V_1"
  by eval

lemma helper6: "Lv Uns (to_bl (0 :: 3 word)) = V_0"
  by eval

lemma init_ensures_nfrac:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_frac (\<lambda>tw. inv_nfrac tw \<and> inv_nfrac2 tw)"
  unfolding next_frac_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_nfrac (fst tw + 1, snd tw) \<and> inv_nfrac2 (fst tw + 1, snd tw)", rotated])
    apply (rule wp3_fun_is_pre[OF seq_wt_next_frac[unfolded next_frac_def conc_stmt.sel(4)] nonneg_delay_next_frac[unfolded next_frac_def conc_stmt.sel(4)]], simp)
  unfolding wp3_fun.simps fst_worldline_upd2 using helper2 helper3 helper4 helper5 helper6
  inv_nfrac2 inv_nfrac_0 inv_nfrac_1 inv_nfrac_2 inv_nfrac_3 inv_nfrac_4 inv_nfrac_others by force
    
lemma 
  assumes "sim_fin2 w (i + 1) next_frac tw'" and "wityping \<Gamma> w"
  shows "inv_nfrac tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_frac cwt_nf nonneg_delay_conc_next_frac correctness_nfrac init_ensures_nfrac]
  by auto  
                                           
section \<open>Functional specification of @{term "next_outready_reg"}\<close>

definition inv_nout :: "sig assn2" where
  "inv_nout tw = (bval_of (curr_value_of NEXT_OUTREADYREG on tw) = 
                  (case wline_of tw STATE (fst tw - 1) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw - 1 on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw - 1 on tw) |
                       _      \<Rightarrow>   False))"

lemma inv_nout_alt_def:
  "inv_nout tw \<longleftrightarrow> (if wline_of tw STATE (fst tw - 1) = V_PROC 
                    then bval_of (curr_value_of NEXT_OUTREADYREG on tw) \<longleftrightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw - 1 on tw) 
                    else if wline_of tw STATE (fst tw - 1) = V_POST 
                         then bval_of (curr_value_of NEXT_OUTREADYREG on tw) \<longleftrightarrow> bval_of (value_of OUTREADY_REG at_time fst tw - 1 on tw) 
                         else \<not> bval_of (curr_value_of NEXT_OUTREADYREG on tw))"
  unfolding inv_nout_def 
  by (simp split:val.splits signedness.splits list.splits bool.splits)

schematic_goal inv_nout_concrete:
  "inv_nout tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_nout_alt_def 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         (" (if wline_of tw STATE (get_time tw - 1) = V_PROC then bval_of (wline_of tw NEXT_OUTREADYREG (get_time tw)) = (\<not> bval_of (wline_of tw CTR_NEQ_0 (get_time tw - 1)))
     else if wline_of tw STATE (get_time tw - 1) = V_POST then bval_of (wline_of tw NEXT_OUTREADYREG (get_time tw)) = bval_of (wline_of tw OUTREADY_REG (get_time tw - 1))
          else \<not> bval_of (wline_of tw NEXT_OUTREADYREG (get_time tw)))"))
  by rule

definition inv_nout2 :: "sig assn2" where
  "inv_nout2 tw \<equiv> disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. bval_of (value_of NEXT_OUTREADYREG at_time i on tw) = bval_of (value_of NEXT_OUTREADYREG at_time fst tw on tw))"

schematic_goal inv_nout2_concrete:
  "inv_nout2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_nout2_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. bval_of (wline_of tw NEXT_OUTREADYREG i) = bval_of (wline_of tw NEXT_OUTREADYREG (get_time tw))))"))
  by rule

definition 
  "inv_nout_comb \<equiv> Rsepand (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_PROC))
       (RBImp (RBval (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (Rnot (RBval (Vwline (Wvar 0) (Svar (Suc (Suc (Suc 0)))) (NDec (NFst (Wvar 0)))))))
       (RIfte (RVEq (Vwline (Wvar 0) (Svar (Suc (Suc 0))) (NDec (NFst (Wvar 0)))) (VC V_POST))
         (RBImp (RBval (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))) (RBval (Vwline (Wvar 0) (Svar (Suc 0)) (NDec (NFst (Wvar 0)))))) (Rnot (RBval (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))
(RImp (RDisevt (LCons (Svar (Suc (Suc (Suc 0)))) (LCons (Svar (Suc (Suc 0))) (LCons (Svar (Suc 0)) LEmpty))) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RBImp (RBval (Vwline (Wvar 0) (Svar 0) (NVar 0))) (RBval (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))"

lemma [simp]:
  "highest_idx_form_sig inv_nout_comb = 8"
  unfolding inv_nout_comb_def by auto

definition 
  "inv_nout_FV = [NEXT_OUTREADYREG, OUTREADY_REG, STATE, CTR_NEQ_0, NEXT_OUTREADYREG, OUTREADY_REG, CTR_NEQ_0, STATE]"

lemma [simp]:
  "length inv_nout_FV = 8"
  unfolding inv_nout_FV_def by auto

lemma inv_nout_comb_alt_def:
  "inv_nout tw \<and> inv_nout2 tw \<longleftrightarrow> eval inv_nout_comb [tw] [] inv_nout_FV"
  unfolding inv_nout_alt_def inv_nout2_def inv_nout_comb_def inv_nout_FV_def
  by auto

lemma inv_nout2_preserved:
  "\<And>tw. inv_nout2 tw \<and> (disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_nout2 (fst tw + 1, snd tw)"
  unfolding inv_nout2_def by auto

lemma inv_nout_preserved:
  "\<And>tw. inv_nout tw \<and> inv_nout2 tw \<and>  (disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_nout (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_nout tw \<and> inv_nout2 tw \<and>  (disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)) "
  hence "inv_nout tw" and *: "inv_nout2 tw" and **: "disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)"
    by auto
  hence 0: "wline_of tw STATE (fst tw - 1) = wline_of tw STATE (fst tw)" and 
        1: "value_of CTR_NEQ_0 at_time (fst tw - 1) on tw = curr_value_of CTR_NEQ_0 on tw" and 
        2: "value_of OUTREADY_REG at_time (fst tw - 1) on tw = curr_value_of OUTREADY_REG on tw"
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have "bval_of (value_of NEXT_OUTREADYREG at_time fst tw + 1 on tw) = bval_of (value_of NEXT_OUTREADYREG at_time fst tw on tw)"
    using * ** unfolding inv_nout2_def by auto
  also have "... = (case wline_of tw STATE (fst tw - 1) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw - 1 on tw) |
                       V_POST \<Rightarrow> bval_of (value_of OUTREADY_REG at_time fst tw - 1 on tw) |
                       _      \<Rightarrow>   False)"
    using `inv_nout tw` unfolding inv_nout_def by auto
  also have "... = (case wline_of tw STATE (fst tw) of    
                       V_PROC \<Rightarrow> \<not> bval_of (value_of CTR_NEQ_0 at_time fst tw  on tw) |
                       V_POST \<Rightarrow>   bval_of (value_of OUTREADY_REG at_time fst tw  on tw) |
                       _      \<Rightarrow>   False)"
    using `disjnt {STATE, CTR_NEQ_0, OUTREADY_REG} (event_of tw)` unfolding 0 1 2
    by auto
  finally show "inv_nout (fst tw + 1, snd tw)"
    unfolding inv_nout_def comp_def snd_conv fst_conv 
    by (auto split: val.splits signedness.splits list.splits bool.splits)
qed

lemma inv_nout_vproc_true:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw = Bv True"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 Bv False]"
  shows   "inv_nout (fst tw' + 1, snd tw')"
  using assms unfolding inv_nout_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nout_vproc_false:
  fixes tw
  assumes " curr_value_of STATE on tw = V_PROC"
  assumes " curr_value_of CTR_NEQ_0 on tw \<noteq> Bv True"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 Bv True]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_nout (fst tw' + 1, snd tw')"
proof -
  have "type_of (snd (snd tw) CTR_NEQ_0 (get_time tw)) = Bty"
    using assms(4) cosine_locale_axioms unfolding cosine_locale_def wityping_def wtyping_def
    by auto
  hence *: "snd (snd tw) CTR_NEQ_0 (fst tw) = Bv False"
    using assms(2) by (smt comp_apply ty.distinct(1) type_of.elims)
  thus ?thesis
    using assms unfolding inv_nout_alt_def fst_worldline_upd2
    by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)
qed

lemma inv_nout_vpost:
  fixes tw
  assumes " curr_value_of STATE on tw = V_POST"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig OUTREADY_REG)]"
  shows   "inv_nout (fst tw' + 1, snd tw')"
  using assms unfolding inv_nout_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nout_others:
  fixes tw
  assumes " curr_value_of STATE on tw \<noteq> V_PROC"
  assumes " curr_value_of STATE on tw \<noteq> V_POST"
  defines "tw' \<equiv> tw[ NEXT_OUTREADYREG, 1 :=\<^sub>2 Bv False]"
  shows   "inv_nout (fst tw' + 1, snd tw')"
  using assms unfolding inv_nout_alt_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_nout2: 
  fixes tw v
  defines "tw' \<equiv> tw[NEXT_OUTREADYREG, 1 :=\<^sub>2 v]"
  shows   "inv_nout2 (fst tw' + 1, snd tw')"
  unfolding inv_nout2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_nout':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace> next_outready_reg \<lbrace>\<lambda>tw. inv_nout (fst tw + 1, snd tw) \<and> inv_nout2 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> next_outready_reg (\<lambda>tw. inv_nout  (fst tw + 1, snd tw) \<and> 
                                                                  inv_nout2 (fst tw + 1, snd tw))", rotated])  
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_next_outready_reg, rule nonneg_delay_conc_next_outready_reg, rule cwt_no, simp)
  unfolding next_outready_reg_def wp3_conc_single'[OF cwt_no[unfolded next_outready_reg_def] nonneg_delay_conc_next_outready_reg[unfolded next_outready_reg_def]] wp3_fun.simps
  fst_worldline_upd2 using inv_nout_preserved inv_nout2_preserved inv_nout2 inv_nout_vproc_true
  inv_nout_vproc_false inv_nout_vpost inv_nout_others by force
  
lemma correctness_nout:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace> next_outready_reg \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_nout' by auto

lemma init_ensures_nout:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) next_outready_reg (\<lambda>tw. inv_nout tw \<and> inv_nout2 tw)"
  unfolding next_outready_reg_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_nout (fst tw + 1, snd tw) \<and> inv_nout2 (fst tw + 1, snd tw)", rotated])
    apply (rule wp3_fun_is_pre[OF seq_wt_next_outready_reg[unfolded next_outready_reg_def conc_stmt.sel(4)] nonneg_delay_next_outready_reg[unfolded next_outready_reg_def conc_stmt.sel(4)]], simp)
  unfolding wp3_fun.simps fst_worldline_upd2 using inv_nout2 inv_nout_vproc_true inv_nout_vproc_false
  inv_nout_vpost inv_nout_others by force

lemma 
  assumes "sim_fin2 w (i + 1) next_outready_reg tw'" and "wityping \<Gamma> w"
  shows "inv_nout tw'"
  using grand_correctness[OF assms conc_stmt_wf_next_outready_reg cwt_no nonneg_delay_conc_next_outready_reg correctness_nout init_ensures_nout]
  by auto  

section \<open>Functional specification for @{term "ctr_neq_0"}\<close>

definition inv_n0 :: "sig assn2" where
  "inv_n0 tw = (bval_of (curr_value_of CTR_NEQ_0 on tw) \<longleftrightarrow> 0 < ubin_of COUNTER at_time fst tw - 1 on tw)"

schematic_goal inv_n0_concrete:
  "inv_n0 tw \<equiv> eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_n0_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         (" bval_of (wline_of tw CTR_NEQ_0 (get_time tw)) = (0 < bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw - 1))))"))
  by presburger

definition inv_n02 :: "sig assn2" where
  "inv_n02 tw \<equiv> disjnt {COUNTER} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. bval_of (value_of CTR_NEQ_0 at_time i on tw) = bval_of (value_of CTR_NEQ_0 at_time fst tw on tw))"

schematic_goal inv_n02_concrete:
  "inv_n02 tw \<equiv> eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_n02_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         (" disjnt {COUNTER} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. bval_of (wline_of tw CTR_NEQ_0 i) = bval_of (wline_of tw CTR_NEQ_0 (get_time tw)))"))
  by presburger

definition 
  "inv_n0_comb \<equiv> Rsepand 
(RBImp (RBval (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0)))) (RILT (IC 0) (Iubin_of (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))))
(RImp (RDisevt (LCons (Svar (Suc 0)) LEmpty) (Wvar 0))
       (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RBImp (RBval (Vwline (Wvar 0) (Svar 0) (NVar 0))) (RBval (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0))))))))
"

definition 
  "inv_n0_FV = [COUNTER, CTR_NEQ_0, CTR_NEQ_0, COUNTER]"

lemma inv_n0_comb_alt_def:
  "inv_n0 tw \<and> inv_n02 tw \<longleftrightarrow> eval inv_n0_comb [tw] [] inv_n0_FV"
  unfolding inv_n0_def inv_n02_def inv_n0_comb_def inv_n0_FV_def
  by simp
 
lemma inv_n02_preserved:
  "\<And>tw. inv_n02 tw \<and> (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_n02 (fst tw + 1, snd tw)"
  unfolding inv_n02_def by auto

lemma inv_n0_preserved:
  "\<And>tw. inv_n0 tw \<and> inv_n02 tw \<and>  (disjnt {COUNTER} (event_of tw)) \<Longrightarrow> inv_n0 (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_n0 tw \<and> inv_n02 tw \<and>  (disjnt  {COUNTER} (event_of tw)) "
  hence "inv_n0 tw" and *: "inv_n02 tw" and **: "disjnt  {COUNTER} (event_of tw)"
    by auto
  hence 0: "wline_of tw COUNTER (fst tw - 1) = wline_of tw COUNTER (fst tw)" 
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have "bval_of (value_of CTR_NEQ_0 at_time fst tw + 1 on tw) = bval_of (curr_value_of CTR_NEQ_0 on tw)"
    using ** * unfolding inv_n02_def by auto
  also have "...  \<longleftrightarrow> (0 < ubin_of COUNTER at_time fst tw - 1 on tw)"
    using `inv_n0 tw` unfolding inv_n0_def by auto
  also have "... \<longleftrightarrow> (0 < ubin_of COUNTER at_time fst tw on tw)"
    using 0 by auto
  finally show "inv_n0 (fst tw + 1, snd tw)"
    unfolding inv_n0_def by auto
qed

lemma inv_n0:
  fixes tw
  defines "tw' \<equiv> tw[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 tw (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv_n0 (fst tw' + 1, snd tw')"
proof -
  have *: "type_of (snd (snd tw) COUNTER (get_time tw)) = Lty Uns 3"
    using assms(2) cosine_locale_axioms unfolding wityping_def wtyping_def cosine_locale_def
    by auto
  hence len: "length (lval_of (wline_of tw COUNTER (get_time tw))) = 3"
    by (metis comp_def ty.inject ty.simps(3) type_of.elims val.sel(3))
  have "bval_of (value_of CTR_NEQ_0 at_time fst tw' + 1 on (fst tw' + 1, snd tw')) = 
        bval_of (value_of CTR_NEQ_0 at_time fst tw + 1 on tw')"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (lval_of (curr_value_of COUNTER on tw) ! 2 \<or> lval_of (curr_value_of COUNTER on tw) ! 1 \<or> lval_of (curr_value_of COUNTER on tw) ! 0)"
    using * unfolding tw'_def worldline_upd2_def worldline_upd_def
    by (auto split: val.splits)
  also have "... \<longleftrightarrow> (0 < ubin_of COUNTER at_time fst tw on tw)"
  proof 
    assume asm: "lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 0"
    show "0 < ubin_of COUNTER at_time fst tw on tw "
    proof (rule ccontr)
      assume "\<not> 0 < ubin_of COUNTER at_time fst tw on tw"
      hence "ubin_of COUNTER at_time fst tw on tw \<le> 0"
        by auto
      hence "ubin_of COUNTER at_time fst tw on tw = 0"
        using bl_to_bin_ge0 by smt
      hence "bin_to_bl 3 (ubin_of COUNTER at_time fst tw on tw) = bin_to_bl 3 0"
        by auto
      also have "... = [False, False, False]"
        by auto
      finally have "bin_to_bl 3 (ubin_of COUNTER at_time fst tw on tw) = [False, False, False]"
        by auto
      hence "lval_of (wline_of tw COUNTER (get_time tw)) = [False, False, False]"
        using bl_bin_bl[of "lval_of (wline_of tw COUNTER (fst tw))"] len by auto 
      with asm show False 
        by auto
    qed
  next
    assume "0 < bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw)))"
    thus   "lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 0"
    proof (rule contrapos_pp)
      have cases: "\<And> i ::nat. i < 3 \<Longrightarrow> i = 0 \<or> i = 1 \<or> i = 2"
        by auto
      assume "\<not> (lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<or> lval_of (wline_of tw COUNTER (get_time tw)) ! 0)"
      hence " (\<not> lval_of (wline_of tw COUNTER (get_time tw)) ! 2 \<and> \<not> lval_of (wline_of tw COUNTER (get_time tw)) ! 1 \<and> \<not> lval_of (wline_of tw COUNTER (get_time tw)) ! 0)"
        by auto
      hence 2: "lval_of (curr_value_of COUNTER on tw) ! 2 = False" and 
            1: "lval_of (curr_value_of COUNTER on tw) ! 1 = False" and
            0: "lval_of (curr_value_of COUNTER on tw) ! 0 = False"
        by auto
      have "(\<forall>i<3. lval_of (wline_of tw COUNTER (get_time tw)) ! i = U_ZERO3 ! i)"
      proof (rule, rule)
        fix i  :: nat
        assume "i < 3"
        then consider "i = 0" | "i = 1" | "i = 2"
          by linarith
        thus "lval_of (wline_of tw COUNTER (get_time tw)) ! i = U_ZERO3 ! i "
          using 0 1 2 by cases auto
      qed
      hence "lval_of (curr_value_of COUNTER on tw) = [False, False, False]"
        using len unfolding list_eq_iff_nth_eq by auto
      hence "bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw))) = 0"
        by auto
      thus "\<not> 0 < bl_to_bin (lval_of (wline_of tw COUNTER (get_time tw)))"
        by auto
    qed
  qed
  finally show ?thesis
    unfolding inv_n0_def fst_conv  comp_def snd_conv tw'_def worldline_upd2_def worldline_upd_def
    by auto
qed

lemma inv_n02: 
  fixes tw v
  defines "tw' \<equiv> tw[CTR_NEQ_0, 1 :=\<^sub>2 v]"
  shows   "inv_n02 (fst tw' + 1, snd tw')"
  unfolding inv_n02_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_n0':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace> ctr_neq_0 \<lbrace>\<lambda>tw. inv_n0 (fst tw + 1, snd tw) \<and> inv_n02 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> ctr_neq_0 (\<lambda>tw. inv_n0  (fst tw + 1, snd tw) \<and> 
                                                          inv_n02 (fst tw + 1, snd tw))", rotated]) 
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_ctr_neq_0, rule nonneg_delay_conc_ctr_neq_0, rule cwt_n0, simp)
  unfolding ctr_neq_0_def wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_n0_preserved inv_n02_preserved by auto
  subgoal using inv_n02 inv_n0 by auto
  done
  
lemma correctness_n0:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace> ctr_neq_0 \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
  apply (rule While_Suc) using correctness_n0' by auto

lemma inv_n0_comb_imp_wp3_conc_next_outready_reg:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_n0 w \<and> inv_n02 w \<longrightarrow> wp3_conc \<Gamma> next_outready_reg (\<lambda>tw. inv_n0 tw \<and> inv_n02 tw) w"
  apply (rule, rule, unfold next_outready_reg_def)
  unfolding wp3_conc_single'[OF cwt_no[unfolded next_outready_reg_def] nonneg_delay_conc_next_outready_reg[unfolded next_outready_reg_def]]
  wp3_fun.simps inv_n0_def inv_n02_def fst_worldline_upd2
  by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  
lemma inv_n0_comb_preserved_outready_reg_ctr_neq_0:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace> next_outready_reg || ctr_neq_0 \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw", rotated])  
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_outready_reg nonneg_delay_conc_next_outready_reg cwt_no], simp)
  using inv_n0_comb_imp_wp3_conc_next_outready_reg correctness_n0'
  unfolding conc_stmt_wf_def next_outready_reg_def ctr_neq_0_def by auto

lemma inv_nout_comb_imp_wp3_conc_ctr_neq_0:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_nout w \<and> inv_nout2 w \<longrightarrow> wp3_conc \<Gamma> ctr_neq_0 (\<lambda>tw. inv_nout tw \<and> inv_nout2 tw) w"
  apply (rule, rule, unfold ctr_neq_0_def)
  unfolding wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]]
  wp3_fun.simps inv_nout_alt_def inv_nout2_def fst_worldline_upd2
  by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')

lemma inv_nout_comb_preserved_ctr_neq0_outready_reg:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>  ctr_neq_0 || next_outready_reg \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_nout tw \<and> inv_nout2 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_nout tw \<and> inv_nout2 tw", rotated])  
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_ctr_neq_0 nonneg_delay_conc_ctr_neq_0 cwt_n0], simp)
  using inv_nout_comb_imp_wp3_conc_ctr_neq_0 correctness_nout'
  unfolding conc_stmt_wf_def ctr_neq_0_def next_outready_reg_def by auto

definition 
  "inv_nout_n0_comb \<equiv> Rsepand inv_nout_comb inv_n0_comb"

lemma inv_nout_n0_comb_alt_def:
  "(inv_nout tw \<and> inv_nout2 tw) \<and> inv_n0 tw \<and> inv_n02 tw \<longleftrightarrow> eval inv_nout_n0_comb [tw] [] (inv_nout_FV @ inv_n0_FV)"
  unfolding inv_nout_alt_def inv_nout2_def inv_n0_def inv_n02_def inv_nout_n0_comb_def inv_nout_FV_def inv_n0_FV_def
  inv_nout_comb_def inv_n0_comb_def by auto

lemma inv_nout_n0_comb:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv_nout tw \<and> inv_nout2 tw) \<and> inv_n0 tw \<and> inv_n02 tw\<rbrace> 
              next_outready_reg || ctr_neq_0 
        \<lbrace>\<lambda>tw. (inv_nout tw \<and> inv_nout2 tw) \<and> inv_n0 tw \<and> inv_n02 tw\<rbrace>"
proof -
  have *: "conc_stmt_wf ( ctr_neq_0 || next_outready_reg)"
    unfolding conc_stmt_wf_def ctr_neq_0_def next_outready_reg_def by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>  ctr_neq_0 || next_outready_reg \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>"
    apply (intro conc_sim_soundness[OF inv_nout_comb_preserved_ctr_neq0_outready_reg])
    unfolding conc_stmt_wf_def next_outready_reg_def ctr_neq_0_def  apply auto
    using conc_wt.simps ctr_neq_0_def next_outready_reg_def by fastforce
  hence "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>  next_outready_reg || ctr_neq_0  \<lbrace>\<lambda>tw. inv_nout tw \<and> inv_nout2 tw\<rbrace>"
    using sim_hoare_valid_wt_parallel_commute[OF *] by auto 
  moreover have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace> next_outready_reg || ctr_neq_0 \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
    apply (intro conc_sim_soundness[OF inv_n0_comb_preserved_outready_reg_ctr_neq_0])
    unfolding conc_stmt_wf_def next_outready_reg_def ctr_neq_0_def  apply auto
    using conc_wt.simps ctr_neq_0_def next_outready_reg_def by fastforce
  ultimately show ?thesis
    unfolding sim_hoare_valid_wt_def by blast
qed

lemma inv_ncounter_comb_imp_wp3_conc_ctr_neq_0:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_ncounter w \<and> inv_ncounter2 w \<longrightarrow> wp3_conc \<Gamma> ctr_neq_0 (\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw) w"
  apply (rule, rule, unfold ctr_neq_0_def)
  unfolding wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]]
  wp3_fun.simps 
proof -
  fix w
  assume "wityping \<Gamma> (snd w) \<and> inv_ncounter w \<and> inv_ncounter2 w "
  hence "inv_ncounter w" and "inv_ncounter2 w"
    by auto
  have "disjnt {COUNTER} (event_of w) \<or> \<not> disjnt {COUNTER} (event_of w)"
    by auto
  moreover
  { assume "disjnt {COUNTER} (event_of w)"
    hence " if disjnt {COUNTER} (event_of w) then (inv_ncounter w \<and> inv_ncounter2 w) \<and> wityping \<Gamma> (snd w)
         else wityping \<Gamma> (snd w) \<and>
              inv_ncounter w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))] \<and>
              inv_ncounter2 w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]"
      using `wityping \<Gamma> (snd w) \<and> inv_ncounter w \<and> inv_ncounter2 w` by auto }
  moreover
  { assume "\<not> disjnt {COUNTER} (event_of w)"
    have "inv_ncounter w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]"
      using `inv_ncounter w` snd_worldline_upd2 snd_worldline_upd2' unfolding inv_ncounter_alt_def fst_worldline_upd2
      apply (auto simp del: eval_world_raw.simps)
      by (smt One_nat_def comp_eq_dest_lhs diff_le_self le_refl less_numeral_extra(1) list.inject snd_worldline_upd2' val.inject(2))+ 
    moreover have "inv_ncounter2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_ncounter2 w` unfolding inv_ncounter2_def fst_worldline_upd2 
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 del: eval_world_raw.simps split:val.splits)
    ultimately have " if disjnt {COUNTER} (event_of w) then (inv_ncounter w \<and> inv_ncounter2 w) \<and> wityping \<Gamma> (snd w)
         else wityping \<Gamma> (snd w) \<and>
              inv_ncounter w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))] \<and>
              inv_ncounter2 w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]"
      using `wityping \<Gamma> (snd w) \<and> inv_ncounter w \<and> inv_ncounter2 w` by auto }
  ultimately show " if disjnt {COUNTER} (event_of w) then (inv_ncounter w \<and> inv_ncounter2 w) \<and> wityping \<Gamma> (snd w)
       else wityping \<Gamma> (snd w) \<and>
              inv_ncounter w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))] \<and>
              inv_ncounter2 w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]"
      using `wityping \<Gamma> (snd w) \<and> inv_ncounter w \<and> inv_ncounter2 w` by auto 
qed

lemma inv_ncounter_comb_preserved_ctr_neq_0_next_counter:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace>  ctr_neq_0 || next_counter \<lbrace>\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_ncounter tw \<and> inv_ncounter2 tw", rotated])  
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_ctr_neq_0 nonneg_delay_conc_ctr_neq_0 cwt_n0], simp)
  using inv_ncounter_comb_imp_wp3_conc_ctr_neq_0 correctness_ncounter'
  unfolding conc_stmt_wf_def ctr_neq_0_def next_counter_def by auto

lemma inv_n0_comb_imp_wp3_conc_next_counter:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_n0 w \<and> inv_n02 w \<longrightarrow> wp3_conc \<Gamma> next_counter (\<lambda>tw. inv_n0 tw \<and> inv_n02 tw) w"
  apply (rule, rule, unfold next_counter_def)
  unfolding wp3_conc_single'[OF cwt_ncnt[unfolded next_counter_def] nonneg_delay_conc_next_counter[unfolded next_counter_def]]
  wp3_fun.simps inv_n0_def inv_n02_def fst_worldline_upd2
  by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')

lemma inv_n0_comb_preserved_next_counter_ctr_neq_0':
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace> next_counter || ctr_neq_0 \<lbrace>\<lambda>tw. inv_n0 (get_time tw + 1, snd tw) \<and> inv_n02 (get_time tw + 1, snd tw)\<rbrace>"
  apply (rule Parallel[where R="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw", rotated])    
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_counter nonneg_delay_conc_next_counter cwt_ncnt], simp)
  using inv_n0_comb_imp_wp3_conc_next_counter correctness_n0'
  unfolding conc_stmt_wf_def next_counter_def ctr_neq_0_def by auto

lemma inv_n0_comb_preserved_next_counter_ctr_neq_0:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>  next_counter || ctr_neq_0  \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
  apply (rule While_Suc) using inv_n0_comb_preserved_next_counter_ctr_neq_0' by auto

lemma inv_n0_comb_imp_wp3_conc_next_state:
  " \<forall>w. wityping \<Gamma> (snd w) \<and> inv_n0 w \<and> inv_n02 w \<longrightarrow> wp3_conc \<Gamma> local.next_state (\<lambda>tw. inv_n0 tw \<and> inv_n02 tw) w"
  apply (rule, rule, unfold next_state_def)
  unfolding wp3_conc_single'[OF cwt_ns[unfolded next_state_def] nonneg_delay_conc_next_state[unfolded next_state_def]]
  wp3_fun.simps inv_n0_def inv_n02_def fst_worldline_upd2
  by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')

lemma inv_n0_comb_preserved_next_state_ctr_neq_0:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>  next_state || ctr_neq_0  \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw", rotated])    
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_state nonneg_delay_conc_next_state cwt_ns], simp)
  using inv_n0_comb_imp_wp3_conc_next_state correctness_n0'
  unfolding conc_stmt_wf_def next_state_def ctr_neq_0_def
  by auto

lemma inv_nstate_imp_wp3_conc_ctr_neq_0:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> inv_nstate w \<and> inv_nstate2 w \<longrightarrow> wp3_conc \<Gamma> ctr_neq_0 (\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw) w"
  apply (rule, rule, unfold ctr_neq_0_def)
  unfolding wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]]
  wp3_fun.simps inv_nstate_def inv_nstate2_def fst_worldline_upd2
  by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')

lemma inv_nstate_comb_preserved_ctr_neq_0_next_state:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace>  ctr_neq_0 || next_state \<lbrace>\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Parallel[where R="\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw"])
    apply (rule Conseq'[where Q="\<lambda>tw. inv_nstate tw \<and> inv_nstate2 tw", rotated])    
      apply (rule wp3_conc_is_pre[OF conc_stmt_wf_ctr_neq_0 nonneg_delay_conc_ctr_neq_0 cwt_n0], simp)
  using inv_nstate_imp_wp3_conc_ctr_neq_0 correctness_nstate'
  unfolding conc_stmt_wf_def next_state_def ctr_neq_0_def by auto

lemma eval_inv_nout_nstate:
  "eval (Rsepand inv_nout_comb inv_nstate_comb) [tw] ([] @ []) (inv_nout_FV @ inv_nstate_FV) \<longleftrightarrow> 
    ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw))"
  using inv_nout_comb_alt_def inv_nstate_comb_alt_def  by auto

lemma inv_nout_nstate_preserved:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw))\<rbrace> 
              (next_outready_reg || next_state)
        \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw))\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_nout_comb [tw] [] inv_nout_FV\<rbrace> next_outready_reg \<lbrace>\<lambda>tw. eval inv_nout_comb [tw] [] inv_nout_FV\<rbrace>"
    apply (rule conc_sim_soundness [OF correctness_nout, unfolded inv_nout_comb_alt_def])
    by (auto)(simp add: conc_stmt_wf_def next_outready_reg_def)
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_nstate_comb [tw] [] inv_nstate_FV\<rbrace> next_state \<lbrace>\<lambda>tw. eval inv_nstate_comb [tw] [] inv_nstate_FV\<rbrace>"
    using conc_sim_soundness[OF correctness_nstate] unfolding inv_nstate_comb_alt_def
    using conc_stmt_wf_next_state cwt_ns nonneg_delay_conc_next_state by blast
  have 2: "set inv_nout_FV \<inter> set (signals_from next_state) = {}"
    unfolding inv_nout_FV_def next_state_def by auto
  have 3: "set inv_nstate_FV \<inter> set (signals_from next_outready_reg) = {}"
    unfolding inv_nstate_FV_def next_outready_reg_def by auto
  have 4: "nonneg_delay_conc (next_outready_reg || next_state)"
    by auto
  have 5: "conc_stmt_wf (next_outready_reg || next_state)"
    unfolding conc_stmt_wf_def next_outready_reg_def next_state_def by auto
  have 6: "conc_wt \<Gamma> (next_outready_reg || next_state)"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig inv_nstate_comb (length inv_nstate_FV) 0"
    unfolding inv_nstate_comb_def inv_nstate_FV_def by auto
  have 8: "wf_assertion (Abs inv_nout_comb) (length []) (length inv_nout_FV)"
    unfolding inv_nout_comb_def inv_nout_FV_def by auto
  have 9: "wf_form_sig inv_nout_comb (length inv_nout_FV) 0"
    unfolding inv_nout_comb_def inv_nout_FV_def by auto
  have 10: "wf_assertion (Abs inv_nstate_comb) (length []) (length inv_nstate_FV)"
    unfolding inv_nstate_comb_def inv_nstate_FV_def by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand inv_nout_comb inv_nstate_comb) [tw] ([] @ []) (inv_nout_FV @ inv_nstate_FV)\<rbrace> next_outready_reg || local.next_state \<lbrace>\<lambda>tw. eval (Rsepand inv_nout_comb inv_nstate_comb) [tw] ([] @ []) (inv_nout_FV @ inv_nstate_FV)\<rbrace>"
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] by auto
  thus ?thesis
    unfolding eval_inv_nout_nstate by auto
qed

lemma eval_inv_nout_ncounter_nstate_comb:
  "eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) inv_ncounter_comb) [tw] (([] @ []) @ []) ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV)  \<longleftrightarrow> 
((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)"
  using inv_nout_comb_alt_def inv_nstate_comb_alt_def inv_ncounter_comb_alt_def by auto

lemma inv_nout_nstate_ncounter_preserved:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)\<rbrace> 
              (next_outready_reg || next_state) || next_counter
        \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand inv_nout_comb inv_nstate_comb) [tw] ([] @ []) (inv_nout_FV @ inv_nstate_FV)\<rbrace> next_outready_reg || local.next_state \<lbrace>\<lambda>tw. eval (Rsepand inv_nout_comb inv_nstate_comb) [tw] ([] @ []) (inv_nout_FV @ inv_nstate_FV)\<rbrace>"
    using inv_nout_nstate_preserved unfolding eval_inv_nout_nstate by auto
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_ncounter_comb [tw] [] inv_ncounter_FV\<rbrace> next_counter \<lbrace>\<lambda>tw. eval inv_ncounter_comb [tw] [] inv_ncounter_FV\<rbrace>"
    using correctness_ncounter_semantic unfolding inv_ncounter_comb_alt_def by auto
  have 2: "set (inv_nout_FV @ inv_nstate_FV) \<inter> set (signals_from next_counter) = {}"
    unfolding inv_nout_FV_def inv_nstate_FV_def next_counter_def by auto
  have 3: "set inv_ncounter_FV \<inter> set (signals_from (next_outready_reg || next_state)) = {}"
    unfolding inv_ncounter_FV_def next_outready_reg_def next_state_def by auto
  have 4: "nonneg_delay_conc (              (next_outready_reg || next_state) || next_counter)"
    by auto
  have 5: "conc_stmt_wf (              (next_outready_reg || next_state) || next_counter)"
    unfolding next_outready_reg_def next_state_def next_counter_def conc_stmt_wf_def by auto
  have 6: "conc_wt \<Gamma> (              (next_outready_reg || next_state) || next_counter)"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig inv_ncounter_comb (length inv_ncounter_FV) 0"
    unfolding inv_ncounter_comb_def inv_ncounter_FV_def by auto
  have 8: "wf_assertion (Abs (Rsepand inv_nout_comb inv_nstate_comb)) (length ([] @ [])) (length (inv_nout_FV @ inv_nstate_FV))"
    unfolding inv_nout_comb_def inv_nstate_comb_def inv_nout_FV_def inv_nstate_FV_def by auto
  have 9: "wf_form_sig (Rsepand inv_nout_comb inv_nstate_comb) (length (inv_nout_FV @ inv_nstate_FV)) 0"
    unfolding inv_nout_comb_def inv_nstate_comb_def inv_nout_FV_def inv_nstate_FV_def by auto
  have 10: "wf_assertion (Abs inv_ncounter_comb) (length []) (length inv_ncounter_FV)"
    unfolding inv_ncounter_comb_def inv_ncounter_FV_def by auto
  have " \<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) inv_ncounter_comb) [tw] (([] @ []) @ []) ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV)\<rbrace>
                  (next_outready_reg || local.next_state) || next_counter
               \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) inv_ncounter_comb) [tw] (([] @ []) @ []) ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV)\<rbrace>"
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] by auto
  thus ?thesis
    unfolding eval_inv_nout_ncounter_nstate_comb by auto
qed

lemma inv_nout_nstate_ncounter_inc_time:
  "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> inv_nstate tw \<and> inv_nstate2 tw) \<and> inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace> 
          (next_outready_reg || local.next_state) || next_counter
       \<lbrace>\<lambda>tw. ((inv_nout (get_time tw + 1, snd tw) \<and> inv_nout2 (get_time tw + 1, snd tw)) \<and> inv_nstate (get_time tw + 1, snd tw) \<and> inv_nstate2 (get_time tw + 1, snd tw)) \<and>
               inv_ncounter (get_time tw + 1, snd tw) \<and> inv_ncounter2 (get_time tw + 1, snd tw)\<rbrace>"
proof -
  have 0: "nonneg_delay_conc ((next_outready_reg || local.next_state) || next_counter)"
    by auto
  have 1: "conc_stmt_wf ((next_outready_reg || local.next_state) || next_counter)"
    unfolding conc_stmt_wf_def next_outready_reg_def next_state_def next_counter_def
    by auto
  have 2: "conc_wt \<Gamma> ((next_outready_reg || local.next_state) || next_counter)"
    by (simp add: conc_wt.intros(2))
  show "\<Gamma> \<Turnstile> \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> inv_nstate tw \<and> inv_nstate2 tw) \<and> inv_ncounter tw \<and> inv_ncounter2 tw\<rbrace> 
                  (next_outready_reg || local.next_state) || next_counter
             \<lbrace>\<lambda>tw. ((inv_nout (get_time tw + 1, snd tw) \<and> inv_nout2 (get_time tw + 1, snd tw)) \<and> inv_nstate (get_time tw + 1, snd tw) \<and> inv_nstate2 (get_time tw + 1, snd tw)) \<and>
      inv_ncounter (get_time tw + 1, snd tw) \<and> inv_ncounter2 (get_time tw + 1, snd tw)\<rbrace>"
    using simulation_semi_complete[OF inv_nout_nstate_ncounter_preserved 0 1 2] by auto
qed
    
lemma inv_nout_nstate_ncounter_comb_imp_wp3_conc_ctr_neq_0:
  "\<forall>w. wityping \<Gamma> (snd w) \<and> ((inv_nout w \<and> inv_nout2 w) \<and> inv_nstate w \<and> inv_nstate2 w) \<and> inv_ncounter w \<and> inv_ncounter2 w \<longrightarrow>
        wp3_conc \<Gamma> ctr_neq_0 (\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> inv_nstate tw \<and> inv_nstate2 tw) \<and> inv_ncounter tw \<and> inv_ncounter2 tw) w"
  apply (rule, rule, unfold ctr_neq_0_def)
  unfolding wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]] wp3_fun.simps  
proof -
  fix w
  assume "wityping \<Gamma> (snd w) \<and> ((inv_nout w \<and> inv_nout2 w) \<and> inv_nstate w \<and> inv_nstate2 w) \<and> inv_ncounter w \<and> inv_ncounter2 w"
  hence "wityping \<Gamma> (snd w)" and "inv_nout w \<and> inv_nout2 w" and "inv_nstate w \<and> inv_nstate2 w" and "inv_ncounter w \<and> inv_ncounter2 w"
    by auto
  consider "disjnt {COUNTER} (event_of w)" | "\<not> disjnt {COUNTER} (event_of w)"
    by auto
  thus "if disjnt {COUNTER} (event_of w) then (((inv_nout w \<and> inv_nout2 w) \<and> inv_nstate w \<and> inv_nstate2 w) \<and> inv_ncounter w \<and> inv_ncounter2 w) \<and> wityping \<Gamma> (snd w)
         else wityping \<Gamma> (snd w) \<and>
              ((inv_nout (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]) \<and>
                inv_nout2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])) \<and>
               inv_nstate (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]) \<and>
               inv_nstate2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])) \<and>
              inv_ncounter (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]) \<and>
              inv_ncounter2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))]) "
  proof (cases)
    case 1
    then show ?thesis 
      by (simp add: \<open>inv_ncounter w \<and> inv_ncounter2 w\<close> \<open>inv_nout w \<and> inv_nout2 w\<close> \<open>inv_nstate w \<and> inv_nstate2 w\<close> \<open>wityping \<Gamma> (snd w)\<close>)
  next
    case 2
    hence a: "inv_nout (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_nout w \<and> inv_nout2 w` unfolding inv_nout_alt_def fst_worldline_upd2
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
    hence b: "inv_nout2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_nout w \<and> inv_nout2 w` unfolding inv_nout2_def fst_worldline_upd2
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
    have c: "inv_ncounter (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_ncounter w \<and> inv_ncounter2 w` unfolding inv_ncounter_alt_def  fst_worldline_upd2
      apply (auto simp add:  snd_worldline_upd2 snd_worldline_upd2')
      by (metis One_nat_def comp_apply)+
    have d: "inv_ncounter2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_ncounter w \<and> inv_ncounter2 w` unfolding inv_ncounter2_def fst_worldline_upd2
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
    have e: "inv_nstate (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_nstate w \<and> inv_nstate2 w` unfolding inv_nstate_alt_def fst_worldline_upd2
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
    have f: "inv_nstate2 (w[ CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w (Bor (Bindex COUNTER 2) (Bor (Bindex COUNTER 1) (Bindex COUNTER 0)))])"
      using `inv_nstate w \<and> inv_nstate2 w` unfolding inv_nstate2_def fst_worldline_upd2
      by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
    then show ?thesis 
      using 2 a b c d e f  by (simp add: \<open>wityping \<Gamma> (snd w)\<close>) 
  qed
qed

lemma csw_ctr_neq_0_next_outready_reg_next_state_next_counter:
  "conc_stmt_wf (ctr_neq_0 || ((next_outready_reg || next_state) || next_counter))"
  "conc_stmt_wf (((next_outready_reg || next_state) || next_counter) || ctr_neq_0)"
  unfolding conc_stmt_wf_def ctr_neq_0_def next_outready_reg_def next_state_def next_counter_def
  by auto

lemma inv_nout_nstate_ncounter_preserved2:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw))\<rbrace> 
              ctr_neq_0 || ((next_outready_reg || next_state) || next_counter)
        \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)\<rbrace>"
  apply (rule While_Suc')
  apply simp
  apply (simp add: conc_stmt_wf_def circuit_defs)
  apply (simp add: conc_wt.intros(2))
  apply (rule parallel_valid[where R="\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> inv_nstate tw \<and> inv_nstate2 tw) \<and> inv_ncounter tw \<and> inv_ncounter2 tw"])
  apply (rule conseq_valid[where Q="\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> inv_nstate tw \<and> inv_nstate2 tw) \<and> inv_ncounter tw \<and> inv_ncounter2 tw", rotated])
  apply (rule wp3_conc_is_pre_valid[OF conc_stmt_wf_ctr_neq_0 nonneg_delay_conc_ctr_neq_0 cwt_n0], simp)
  using inv_nout_nstate_ncounter_comb_imp_wp3_conc_ctr_neq_0 apply simp
  using inv_nout_nstate_ncounter_inc_time apply simp
  apply (simp add: conc_stmt_wf_def circuit_defs)
  apply simp
  by (simp add: conc_wt.intros(2))

lemma inv_nout_nstate_ncounter_preserved3:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw))\<rbrace> 
              (next_outready_reg || next_state) || (next_counter || ctr_neq_0)
        \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw)\<rbrace>"
  using inv_nout_nstate_ncounter_preserved2 
  unfolding sim_hoare_valid_wt_parallel_commute[OF csw_ctr_neq_0_next_outready_reg_next_state_next_counter(1)]
  using sim_hoare_valid_wt_parallel_associative[OF csw_ctr_neq_0_next_outready_reg_next_state_next_counter(2)]
  by auto

lemma inv_n0_preserved2:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>  (next_outready_reg || next_state) || (next_counter || ctr_neq_0)  \<lbrace>\<lambda>tw. inv_n0 tw \<and> inv_n02 tw\<rbrace>"
  apply (rule While_Suc')
     apply (simp)
    apply (simp add: conc_stmt_wf_def circuit_defs)
   apply (simp add: conc_wt.intros(2))
  apply (rule parallel_valid[where R="\<lambda>tw. inv_n0 tw \<and> inv_n02 tw"])
  subgoal 
  proof -
    have 0: "set (signals_from (next_outready_reg || local.next_state)) \<inter> set (inv_n0_FV) = {}"
      unfolding next_outready_reg_def next_state_def inv_n0_FV_def by auto
    have 1: "conc_stmt_wf (next_outready_reg || local.next_state)"
      by (simp add: conc_stmt_wf_def next_outready_reg_def next_state_def next_counter_def ctr_neq_0_def)
    have 2: "nonneg_delay_conc (next_outready_reg || local.next_state)"
      by auto
    have 3: "conc_wt \<Gamma> ((next_outready_reg || local.next_state))"
      by (simp add: conc_wt.intros(2))
    have 4: "wf_form_sig (inv_n0_comb) (length inv_n0_FV) 0"
      unfolding inv_n0_comb_def inv_n0_FV_def by auto
    have 5: "highest_idx_form_rwline inv_n0_comb \<le> 1"
      unfolding inv_n0_comb_def by auto
    have "interp_hoare_conc (Hoare (Abs inv_n0_comb) (Abs inv_n0_comb)) [] inv_n0_FV [] inv_n0_FV \<Gamma> (next_outready_reg || local.next_state)"
      using interp_hoare_conc_free_vars[OF 0 1 2 3 4 5] by auto
    thus ?thesis
      by (auto simp add: inv_n0_comb_alt_def)
  qed
     apply (rule soundness_conc_hoare[OF inv_n0_comb_preserved_next_counter_ctr_neq_0'])
       apply (simp add: conc_wt.intros(2))
      apply (simp add: conc_stmt_wf_def circuit_defs)
     apply simp
    apply (simp add: conc_stmt_wf_def circuit_defs)
  apply simp
  apply (simp add: conc_wt.intros(2))
  done

lemma inv_nout_nstate_ncounter_n0_preserved:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace> 
              (next_outready_reg || next_state) || (next_counter || ctr_neq_0)
        \<lbrace>\<lambda>tw. ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>"
  using inv_nout_nstate_ncounter_preserved3 inv_n0_preserved2 
  unfolding sim_hoare_valid_wt_def by fast

lemma eval_inv_nout_nstate_ncounter_nout:
  "eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)) [tw] [] ((inv_nout_FV @ inv_nstate_FV) @ (inv_ncounter_FV @ inv_n0_FV)) \<longleftrightarrow> 
   ((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)"
  using inv_nout_comb_alt_def inv_nstate_comb_alt_def inv_ncounter_comb_alt_def inv_n0_comb_alt_def
  by auto

lemma inv_nout_nstate_ncounter_n0_preserved2:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)) [tw] [] ((inv_nout_FV @ inv_nstate_FV) @ (inv_ncounter_FV @ inv_n0_FV))\<rbrace> 
                  (next_outready_reg || next_state) || (next_counter || ctr_neq_0)
        \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)) [tw] [] ((inv_nout_FV @ inv_nstate_FV) @ (inv_ncounter_FV @ inv_n0_FV))\<rbrace>"
  using inv_nout_nstate_ncounter_n0_preserved unfolding eval_inv_nout_nstate_ncounter_nout by auto

lemma init_ensures_n0:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) ctr_neq_0 (\<lambda>tw. inv_n0 tw \<and> inv_n02 tw)"
  unfolding ctr_neq_0_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_n0 (fst tw + 1, snd tw) \<and> inv_n02 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_ctr_neq_0[unfolded ctr_neq_0_def conc_stmt.sel(4)] nonneg_delay_ctr_neq_0[unfolded ctr_neq_0_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_n02 inv_n0 by blast

lemma 
  assumes "sim_fin2 w (i + 1) ctr_neq_0 tw'" and "wityping \<Gamma> w"
  shows "inv_n0 tw'"
  using grand_correctness[OF assms conc_stmt_wf_ctr_neq_0 cwt_n0 nonneg_delay_conc_ctr_neq_0 correctness_n0 init_ensures_n0]
  by auto  

section \<open>Functional specification for @{term "output"}\<close>

definition inv_output :: "sig assn2" where
  "inv_output tw = (curr_value_of OUTPUT on tw = value_of ACCUM at_time fst tw - 1 on tw)"

schematic_goal inv_output_concrete:
  "inv_output tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_output_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
         ("(wline_of tw OUTPUT (get_time tw) = wline_of tw ACCUM (get_time tw - 1))"))
  by rule

definition inv_output2 :: "sig assn2" where
  "inv_output2 tw \<equiv> disjnt {ACCUM} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. (value_of OUTPUT at_time i on tw) = (value_of OUTPUT at_time fst tw on tw))"

schematic_goal inv_output2_concrete:
  "inv_output2 tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_output2_def
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(disjnt {ACCUM} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. wline_of tw OUTPUT i = wline_of tw OUTPUT (get_time tw)))"))
  by rule

definition 
  "inv_output_comb = Rsepand 
(RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))
(RImp (RDisevt (LCons (Svar (Suc 0)) LEmpty) (Wvar 0)) (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))"

lemma [simp]:
  "highest_idx_form_sig inv_output_comb = 4"
  unfolding inv_output_comb_def by auto

definition 
  "inv_output_FV = [ACCUM, OUTPUT, OUTPUT, ACCUM]"

lemma [simp]:
  "length inv_output_FV = 4"
  unfolding inv_output_FV_def by auto

lemma inv_output_comb_alt_def:
  "inv_output tw \<and> inv_output2 tw \<longleftrightarrow> eval inv_output_comb [tw] [] inv_output_FV"
  unfolding inv_output_def inv_output2_def inv_output_comb_def inv_output_FV_def 
  by simp

lemma inv_output2_preserved:
  "\<And>tw. inv_output2 tw \<and> (disjnt {ACCUM} (event_of tw)) \<Longrightarrow> inv_output2 (fst tw + 1, snd tw)"
  unfolding inv_output2_def by auto

lemma inv_output_preserved:
  "\<And>tw. inv_output tw \<and> inv_output2 tw \<and>  (disjnt {ACCUM} (event_of tw)) \<Longrightarrow> inv_output (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_output tw \<and> inv_output2 tw \<and>  (disjnt  {ACCUM} (event_of tw)) "
  hence "inv_output tw" and *: "inv_output2 tw" and **: "disjnt  {ACCUM} (event_of tw)"
    by auto
  hence 0: "wline_of tw ACCUM (fst tw - 1) = wline_of tw ACCUM (fst tw)" 
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have " (value_of OUTPUT at_time fst tw + 1 on tw) = (curr_value_of OUTPUT on tw)"
    using ** * unfolding inv_output2_def by auto
  also have "... = value_of ACCUM at_time fst tw - 1 on tw"
    using `inv_output tw` unfolding inv_output_def by auto
  also have "... = value_of ACCUM at_time fst tw on tw"
    using 0 by auto
  finally show "inv_output (fst tw + 1, snd tw)"
    unfolding inv_output_def by auto
qed

lemma inv_output:
  fixes tw
  defines "tw' \<equiv> tw[ OUTPUT, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig ACCUM)]"
  shows   "inv_output (fst tw' + 1, snd tw')"
  using assms unfolding inv_output_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_output2: 
  fixes tw v
  defines "tw' \<equiv> tw[OUTPUT, 1 :=\<^sub>2 v]"
  shows   "inv_output2 (fst tw' + 1, snd tw')"
  unfolding inv_output2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_output':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_output tw \<and> inv_output2 tw\<rbrace> output \<lbrace>\<lambda>tw. inv_output (fst tw + 1, snd tw) \<and> inv_output2 (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> output (\<lambda>tw. inv_output  (fst tw + 1, snd tw) \<and> 
                                                          inv_output2 (fst tw + 1, snd tw))", rotated]) 
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_output, rule nonneg_delay_conc_output, rule cwt_output, simp)
  unfolding output_def wp3_conc_single'[OF cwt_output[unfolded output_def] nonneg_delay_conc_output[unfolded output_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_output_preserved inv_output2_preserved by auto
  subgoal using inv_output inv_output2 by auto
  done

lemma correctness_output:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_output tw \<and> inv_output2 tw\<rbrace> output \<lbrace>\<lambda>tw. inv_output tw \<and> inv_output2 tw\<rbrace>"
  apply (rule While_Suc) using correctness_output' by auto

lemma eval_ncommon_sqr_naccum_term1_output:
  "eval (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) [tw] ([] @ []) (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) \<longleftrightarrow>
  (((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw)"
  using inv_ncommon_comb_alt_def'[symmetric] inv_sqr_comb_alt_def[symmetric] inv_naccum_com_alt_def[symmetric]
    inv_term1_comb_alt_def[symmetric] inv_output_comb_alt_def[symmetric] by auto

lemma comb_ncommon_sqr_naccum_term1_output:
  "\<Gamma> \<Turnstile>\<^sub>s\<lbrace>\<lambda>tw. (((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw)\<rbrace>
          (((next_common || squaring)) || (next_accum || term1)) || output
        \<lbrace>\<lambda>tw. (((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw)\<rbrace>"  
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] ([]) ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)\<rbrace>
                    (next_common || squaring) || next_accum || term1
                 \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) [tw] ([]) ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)\<rbrace>"
    using comb_prop_next_common_squaring_next_accum_term1 unfolding inv_ncommon_sqr_ncounter_naccum_term1_comb by auto
  have  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_output_comb [tw] [] inv_output_FV\<rbrace> output \<lbrace>\<lambda>tw. eval inv_output_comb [tw] [] inv_output_FV\<rbrace>"
    using correctness_output unfolding inv_output_comb_alt_def by auto
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_output_comb [tw] [] inv_output_FV\<rbrace> output \<lbrace>\<lambda>tw. eval inv_output_comb [tw] [] inv_output_FV\<rbrace>"
    apply (intro conc_sim_soundness[OF correctness_output, unfolded inv_output_comb_alt_def])
    apply (auto simp add: conc_stmt_wf_def output_def)
    using cwt_output  by (simp add: output_def)
  have 2: "set ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) \<inter> set (signals_from output) = {}"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def output_def by auto
  have 3: "set (inv_output_FV) \<inter> set (signals_from ((next_common || squaring) || next_accum || term1)) = {}"
    unfolding inv_output_FV_def next_common_def squaring_def next_accum_def term1_def by auto
  have 4: "nonneg_delay_conc ((((next_common || squaring)) || (next_accum || term1)) || output)"
    by auto
  have 5: "conc_stmt_wf ((((next_common || squaring)) || (next_accum || term1)) || output)"
    unfolding conc_stmt_wf_def next_common_def squaring_def next_accum_def term1_def output_def
    by auto
  have 6: "conc_wt \<Gamma> ((((next_common || squaring)) || (next_accum || term1)) || output)"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig inv_output_comb (length inv_output_FV) 0"
    unfolding inv_output_comb_def inv_output_FV_def by auto
  have 8: "wf_assertion (Abs (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb))) (length []) (length ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV))"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_naccum_comb_def inv_term1_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_def inv_term1_FV_def
    by auto
  have 9: "wf_assertion (Abs inv_output_comb) (length []) (length inv_output_FV)"
    unfolding inv_output_comb_def inv_output_FV_def by auto
  have 10: "wf_form_sig (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) (length ((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV)) 0"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_naccum_comb_def inv_term1_comb_def inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def 
    by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) [tw] ([] @ []) (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV)\<rbrace>
  ((next_common || squaring) || next_accum || term1) || output
  \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) [tw] ([] @ []) (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV)\<rbrace>"
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 10 9] by satx
  thus ?thesis
    unfolding eval_ncommon_sqr_naccum_term1_output by auto
qed

lemma init_ensures_output:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) output (\<lambda>tw. inv_output tw \<and> inv_output2 tw)"
  unfolding output_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_output (fst tw + 1, snd tw) \<and> inv_output2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_output[unfolded output_def conc_stmt.sel(4)] nonneg_delay_output[unfolded output_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_output inv_output2 by blast

lemma 
  assumes "sim_fin2 w (i + 1) output tw'" and "wityping \<Gamma> w"
  shows "inv_output tw'"
  using grand_correctness[OF assms conc_stmt_wf_output cwt_output nonneg_delay_conc_output correctness_output init_ensures_output]
  by auto  

section \<open>Functional specification for @{term "output_ready"}\<close>

definition inv_output_ready :: "sig assn2" where
  "inv_output_ready tw = (curr_value_of OUTREADY on tw = value_of OUTREADY_REG at_time fst tw - 1 on tw)"

schematic_goal inv_output_ready_concrete:
  "inv_output_ready tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_output_ready_def 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(wline_of tw OUTREADY (get_time tw) = wline_of tw OUTREADY_REG (get_time tw - 1))"))
  by rule

definition inv_output2_ready :: "sig assn2" where
  "inv_output2_ready tw \<equiv> disjnt {OUTREADY_REG} (event_of tw) \<longrightarrow> 
          (\<forall>i > fst tw. (value_of OUTREADY at_time i on tw) = (value_of OUTREADY at_time fst tw on tw))"

schematic_goal inv_output2_ready_concrete:
  "inv_output2_ready tw = eval ?Q ?ws ?ns (?ss :: sig list)"
  unfolding inv_output2_ready_def 
  apply (reify eval.simps Irwline.simps Irnat_simps Irsig_simps Irval_simps Irset.simps Irint_simps
        ("(disjnt {OUTREADY_REG} (event_of tw) \<longrightarrow> (\<forall>i>get_time tw. wline_of tw OUTREADY i = wline_of tw OUTREADY (get_time tw)))"))
  by rule

definition 
  "inv_output_ready_comb \<equiv> Rsepand 
  (RVEq (Vwline (Wvar 0) (Svar (Suc 0)) (NFst (Wvar 0))) (Vwline (Wvar 0) (Svar 0) (NDec (NFst (Wvar 0)))))
(RImp (RDisevt (LCons (Svar (Suc 0)) LEmpty) (Wvar 0)) (RNall (RImp (RNLT (NFst (Wvar 0)) (NVar 0)) (RVEq (Vwline (Wvar 0) (Svar 0) (NVar 0)) (Vwline (Wvar 0) (Svar 0) (NFst (Wvar 0)))))))"

lemma [simp]:
  "highest_idx_form_sig inv_output_ready_comb = 4"
  unfolding inv_output_ready_comb_def by auto

definition
  "inv_output_ready_FV = [OUTREADY_REG, OUTREADY, OUTREADY, OUTREADY_REG]"

lemma [simp]:
  "length inv_output_ready_FV = 4"
  unfolding inv_output_ready_FV_def by auto

lemma inv_output_ready_comb_alt_def:
  "inv_output_ready tw \<and> inv_output2_ready tw \<longleftrightarrow> eval inv_output_ready_comb [tw] [] inv_output_ready_FV"
  unfolding inv_output_ready_def inv_output2_ready_def inv_output_ready_comb_def inv_output_ready_FV_def
  by auto

lemma inv_output2_preserved_ready:
  "\<And>tw. inv_output2_ready tw \<and> (disjnt {OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_output2_ready (fst tw + 1, snd tw)"
  unfolding inv_output2_ready_def by auto

lemma inv_output_preserved_ready:
  "\<And>tw. inv_output_ready tw \<and> inv_output2_ready tw \<and>  (disjnt {OUTREADY_REG} (event_of tw)) \<Longrightarrow> inv_output_ready (fst tw + 1, snd tw)"
proof -
  fix tw 
  assume "inv_output_ready tw \<and> inv_output2_ready tw \<and>  (disjnt  {OUTREADY_REG} (event_of tw)) "
  hence "inv_output_ready tw" and *: "inv_output2_ready tw" and **: "disjnt  {OUTREADY_REG} (event_of tw)"
    by auto
  hence 0: "wline_of tw OUTREADY_REG (fst tw - 1) = wline_of tw OUTREADY_REG (fst tw)" 
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq)+
  have " (value_of OUTREADY at_time fst tw + 1 on tw) = (curr_value_of OUTREADY on tw)"
    using ** * unfolding inv_output2_ready_def by auto
  also have "... = value_of OUTREADY_REG at_time fst tw - 1 on tw"
    using `inv_output_ready tw` unfolding inv_output_ready_def by auto
  also have "... = value_of OUTREADY_REG at_time fst tw on tw"
    using 0 by auto
  finally show "inv_output_ready (fst tw + 1, snd tw)"
    unfolding inv_output_ready_def by auto
qed

lemma inv_output_ready:
  fixes tw
  defines "tw' \<equiv> tw[ OUTREADY, 1 :=\<^sub>2 eval_world_raw2 tw (Bsig OUTREADY_REG)]"
  shows   "inv_output_ready (fst tw' + 1, snd tw')"
  using assms unfolding inv_output_ready_def fst_worldline_upd2
  by (auto simp add: snd_worldline_upd2)(auto simp add: worldline_upd2_def worldline_upd_def)

lemma inv_output2_ready: 
  fixes tw v
  defines "tw' \<equiv> tw[OUTREADY, 1 :=\<^sub>2 v]"
  shows   "inv_output2_ready (fst tw' + 1, snd tw')"
  unfolding inv_output2_ready_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma correctness_output_ready':
  "\<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw\<rbrace> output_ready \<lbrace>\<lambda>tw. inv_output_ready (fst tw + 1, snd tw) \<and> inv_output2_ready (fst tw + 1, snd tw)\<rbrace>"
  apply (rule Conseq'[where P="wp3_conc \<Gamma> output_ready (\<lambda>tw. inv_output_ready  (fst tw + 1, snd tw) \<and> 
                                                          inv_output2_ready (fst tw + 1, snd tw))", rotated]) 
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_output_ready, rule nonneg_delay_conc_output_ready, rule cwt_outready, simp)
  unfolding output_ready_def wp3_conc_single'[OF cwt_outready[unfolded output_ready_def] nonneg_delay_conc_output_ready[unfolded output_ready_def]] wp3_fun.simps
  apply (rule, rule, unfold if_bool_eq_conj, rule, rule, rule_tac[2] impI) 
  subgoal using inv_output_preserved_ready inv_output2_preserved_ready by auto
  subgoal using inv_output_ready inv_output2_ready by auto
  done

lemma correctness_output_ready:                          
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw\<rbrace> output_ready \<lbrace>\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw\<rbrace>"
  apply (rule While_Suc) using correctness_output_ready' by auto

section \<open>Combining everything\<close>

lemma eval_inv_ncommon_naccum_term1_output_ready:
  " eval (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb) [tw] (([] @ []) @ [])
                ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV) \<longleftrightarrow>
  ((((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw) 
                \<and> inv_output_ready tw \<and> inv_output2_ready tw)"
  using inv_ncommon_comb_alt_def'[symmetric] inv_sqr_comb_alt_def[symmetric] inv_naccum_com_alt_def[symmetric]
    inv_term1_comb_alt_def[symmetric] inv_output_comb_alt_def[symmetric] inv_output_ready_comb_alt_def[symmetric] by auto

lemma inv_ncommon_sqr_naccum_term1_output_preserved:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw) 
                \<and> inv_output_ready tw \<and> inv_output2_ready tw)\<rbrace>
            (((next_common || squaring) || next_accum || term1) || output) || output_ready
        \<lbrace>\<lambda>tw. ((((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw) 
                \<and> inv_output_ready tw \<and> inv_output2_ready tw)\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) [tw] ([] @ []) (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV)\<rbrace>
  ((next_common || squaring) || next_accum || term1) || output
  \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) [tw] ([] @ []) (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV)\<rbrace>"
    using comb_ncommon_sqr_naccum_term1_output unfolding eval_ncommon_sqr_naccum_term1_output[symmetric] by blast
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval inv_output_ready_comb [tw] [] inv_output_ready_FV\<rbrace> output_ready \<lbrace>\<lambda>tw. eval inv_output_ready_comb [tw] [] inv_output_ready_FV\<rbrace>"
    apply (intro conc_sim_soundness[OF correctness_output_ready, unfolded inv_output_ready_comb_alt_def])
    apply (auto) unfolding conc_stmt_wf_def output_ready_def by auto
  have 2: "set (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) \<inter> set (signals_from output_ready) = {}"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def inv_output_FV_def output_ready_def by  auto
  have 3: "set inv_output_ready_FV \<inter> set (signals_from (((next_common || squaring) || next_accum || term1) || output)) = {}"
    unfolding inv_output_ready_FV_def next_common_def squaring_def next_accum_def term1_def output_def by auto
  have 4: "nonneg_delay_conc  ((((next_common || squaring) || next_accum || term1) || output) || output_ready) "
    by auto
  have 5: "conc_stmt_wf ((((next_common || squaring) || next_accum || term1) || output) || output_ready)"
    unfolding inv_output_ready_FV_def next_common_def squaring_def next_accum_def term1_def output_def output_ready_def 
    by (auto simp add: conc_stmt_wf_def)
  have 6: "conc_wt \<Gamma> ((((next_common || squaring) || next_accum || term1) || output) || output_ready)"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig inv_output_ready_comb (length inv_output_ready_FV) 0"
    unfolding inv_output_ready_comb_def inv_output_ready_FV_def by auto
  have 8: "wf_assertion (Abs (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb)) 
                        (length ([] @ [])) (length (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV))"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_naccum_comb_def inv_term1_comb_def inv_output_comb_def
    inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def inv_output_FV_def
    by auto
  have 9: "wf_form_sig (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb)
                       (length (((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV)) 0"
    unfolding inv_ncommon_comb_def inv_sqr_comb_def inv_naccum_comb_def inv_term1_comb_def inv_output_comb_def
    inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def inv_output_FV_def
    by auto
  have 10: "wf_assertion (Abs inv_output_ready_comb) (length []) (length inv_output_ready_FV)"
    unfolding inv_output_ready_comb_def inv_output_ready_FV_def by auto
  have "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb) [tw] (([] @ []) @ [])
                ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV)\<rbrace>
  (((next_common || squaring) || next_accum || term1) || output) || output_ready
  \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb) [tw] (([] @ []) @ [])
         ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV)\<rbrace>"
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] by presburger
  thus ?thesis
    unfolding eval_inv_ncommon_naccum_term1_output_ready by auto
qed

lemma init_ensures_output_ready:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) output_ready (\<lambda>tw. inv_output_ready tw \<and> inv_output2_ready tw)"
  unfolding output_ready_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv_output_ready (fst tw + 1, snd tw) \<and> inv_output2_ready (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_output_ready[unfolded output_ready_def conc_stmt.sel(4)] nonneg_delay_output_ready[unfolded output_ready_def conc_stmt.sel(4)]], simp)
  apply (rule, rule, unfold wp3_fun.simps)
  using inv_output_ready inv_output2_ready by blast

lemma 
  assumes "sim_fin2 w (i + 1) output_ready tw'" and "wityping \<Gamma> w"
  shows "inv_output_ready tw'"
  using grand_correctness[OF assms conc_stmt_wf_output_ready cwt_outready nonneg_delay_conc_output_ready correctness_output_ready init_ensures_output_ready]
  by auto

lemma eval_all_except_registers:
  "eval (Rsepand (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb)
                      (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)))
                [tw] ((([] @ []) @ []) @ [])
                (((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV) @ (inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV @ inv_n0_FV)
   \<longleftrightarrow> (((((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw)) \<and> ((inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw))) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> inv_output_ready tw \<and> inv_output2_ready tw))
            \<and> (((inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw)) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw))
  "
  using inv_ncommon_comb_alt_def' inv_sqr_comb_alt_def inv_naccum_com_alt_def
    inv_term1_comb_alt_def inv_output_comb_alt_def inv_output_ready_comb_alt_def
    inv_nout_comb_alt_def inv_nstate_comb_alt_def inv_ncounter_comb_alt_def inv_n0_comb_alt_def by auto

lemma inv_all_except_reg_preserved:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>
              ((((next_common || squaring) || next_accum || term1) || output) || output_ready)  ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))
        \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>"
proof -
  have 0: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb) [tw] (([] @ []) @ [])
                  ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV)\<rbrace>
                      (((next_common || squaring) || next_accum || term1) || output) || output_ready
                \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb) [tw] (([] @ []) @ [])
                  ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV)\<rbrace>"
    using inv_ncommon_sqr_naccum_term1_output_preserved unfolding eval_inv_ncommon_naccum_term1_output_ready by auto
  have 1: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)) [tw] [] ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV @ inv_n0_FV)\<rbrace>
                    (next_outready_reg || local.next_state) || next_counter || ctr_neq_0
                 \<lbrace>\<lambda>tw. eval (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)) [tw] [] ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV @ inv_n0_FV)\<rbrace>"
    using inv_nout_nstate_ncounter_n0_preserved2 by blast
  have 2: "set ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV) \<inter> set (signals_from ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))) = {}"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def inv_output_FV_def inv_output_ready_FV_def next_outready_reg_def next_state_def next_counter_def ctr_neq_0_def
    by auto
  have 3: "set  ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV @ inv_n0_FV) \<inter> set (signals_from ((((next_common || squaring) || next_accum || term1) || output) || output_ready)) = {}"
    unfolding inv_nout_FV_def  inv_nstate_FV_def  inv_ncounter_FV_def inv_n0_FV_def next_common_def squaring_def next_accum_def term1_def output_def output_ready_def
    by auto
  have 4: "nonneg_delay_conc (((((next_common || squaring) || next_accum || term1) || output) || output_ready) 
          ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0)))"
    by auto
  have 5: "conc_stmt_wf (((((next_common || squaring) || next_accum || term1) || output) || output_ready) 
          ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0)))"
    unfolding next_common_def squaring_def next_accum_def term1_def output_def output_ready_def 
    next_outready_reg_def next_state_def next_counter_def ctr_neq_0_def by (auto simp add: conc_stmt_wf_def)
  have 6: " conc_wt \<Gamma> (((((next_common || squaring) || next_accum || term1) || output) || output_ready) 
          ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0)))"
    by (simp add: conc_wt.intros(2))
  have 7: "wf_form_sig (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb)) (length  ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV @ inv_n0_FV)) 0"
    unfolding inv_nout_FV_def  inv_nstate_FV_def  inv_ncounter_FV_def inv_n0_FV_def inv_nout_comb_def inv_nstate_comb_def inv_ncounter_comb_def inv_n0_comb_def
    by auto
  have 8: "wf_assertion (Abs (Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb)) 
                         (length (([] @ []) @ [])) (length ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV))"
    unfolding inv_ncommon_free_vars_def inv_sqr_FV_def inv_naccum_FV_def inv_term1_FV_def inv_output_FV_def inv_output_ready_FV_def
              inv_ncommon_comb_def inv_sqr_comb_def inv_naccum_comb_def inv_term1_comb_def inv_output_comb_def inv_output_ready_comb_def
    by auto
  have 9: "wf_form_sig ((Rsepand (Rsepand (Rsepand (Rsepand inv_ncommon_comb inv_sqr_comb) (Rsepand inv_naccum_comb inv_term1_comb)) inv_output_comb) inv_output_ready_comb)) 
                       (length ((((inv_ncommon_free_vars @ inv_sqr_FV) @ inv_naccum_FV @ inv_term1_FV) @ inv_output_FV) @ inv_output_ready_FV)) 0"
    unfolding inv_ncommon_free_vars_def  inv_sqr_FV_def  inv_naccum_FV_def inv_term1_FV_def inv_output_FV_def inv_output_ready_FV_def 
    inv_ncommon_comb_def inv_sqr_comb_def inv_naccum_comb_def inv_term1_comb_def inv_output_comb_def  inv_output_ready_comb_def  
    by auto
  have 10: "wf_assertion (Abs (Rsepand (Rsepand inv_nout_comb inv_nstate_comb) (Rsepand inv_ncounter_comb inv_n0_comb))) (length []) (length ((inv_nout_FV @ inv_nstate_FV) @ inv_ncounter_FV @ inv_n0_FV))"
    unfolding inv_nout_FV_def  inv_nstate_FV_def  inv_ncounter_FV_def inv_n0_FV_def inv_nout_comb_def inv_nstate_comb_def inv_ncounter_comb_def inv_n0_comb_def
    by auto
  show ?thesis
    using interp_hgoare_sim_parallel[OF 0 1 2 3 4 5 6 7 8 9 10] unfolding eval_all_except_registers
    by auto
qed

lemma inv_all_imp_wp3_conc_registers:
  "\<forall>w. wityping \<Gamma> (snd w) \<and>
        (inv_ncommon w \<and> inv_ncommon2 w) \<and>
        (inv_sqr w \<and> inv_sqr2 w) \<and>
        (inv_naccum w \<and> inv_naccum2 w) \<and>
        (inv_term1 w \<and> inv_term12 w) \<and> (inv_output w \<and> inv_output2 w) \<and> (inv_output_ready w \<and> inv_output2_ready w) \<and> (inv_nout w \<and> inv_nout2 w) \<and> (inv_nstate w \<and> inv_nstate2 w) \<and> (inv_ncounter w \<and> inv_ncounter2 w) \<and> inv_n0 w \<and> inv_n02 w \<longrightarrow>
        wp3_conc \<Gamma> registers
         (\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and>
               (inv_sqr tw \<and> inv_sqr2 tw) \<and>
               (inv_naccum tw \<and> inv_naccum2 tw) \<and>
               (inv_term1 tw \<and> inv_term12 tw) \<and>
               (inv_output tw \<and> inv_output2 tw) \<and> (inv_output_ready tw \<and> inv_output2_ready tw) \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> inv_n0 tw \<and> inv_n02 tw)
         w"
  apply (rule, rule, unfold registers_def)
  unfolding wp3_conc_single'[OF cwt_reg[unfolded registers_def] nonneg_delay_conc_registers[unfolded registers_def]] wp3_fun.simps(7)
proof -
  fix w
  assume *: "wityping \<Gamma> (snd w) \<and>
         (inv_ncommon w \<and> inv_ncommon2 w) \<and>
         (inv_sqr w \<and> inv_sqr2 w) \<and>
         (inv_naccum w \<and> inv_naccum2 w) \<and>
         (inv_term1 w \<and> inv_term12 w) \<and> (inv_output w \<and> inv_output2 w) \<and> (inv_output_ready w \<and> inv_output2_ready w) \<and> (inv_nout w \<and> inv_nout2 w) \<and> (inv_nstate w \<and> inv_nstate2 w) \<and> (inv_ncounter w \<and> inv_ncounter2 w) \<and> inv_n0 w \<and> inv_n02 w"
  hence "wityping \<Gamma> (snd w)"
    by auto
  consider "disjnt {CLK} (event_of w)" | "\<not> disjnt {CLK} (event_of w) \<and> (eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) = Bv True) \<and> eval_world_raw2 w (Bsig RST) = Bv True" 
    | "\<not> disjnt {CLK} (event_of w) \<and> (eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) = Bv True) \<and> eval_world_raw2 w (Bsig RST) \<noteq> Bv True"
    | "\<not> disjnt {CLK} (event_of w) \<and> eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) \<noteq> Bv True"
    by auto
  thus "if disjnt {CLK} (event_of w)
         then ((inv_ncommon w \<and> inv_ncommon2 w) \<and>
               (inv_sqr w \<and> inv_sqr2 w) \<and>
               (inv_naccum w \<and> inv_naccum2 w) \<and>
               (inv_term1 w \<and> inv_term12 w) \<and>
               (inv_output w \<and> inv_output2 w) \<and> (inv_output_ready w \<and> inv_output2_ready w) \<and> (inv_nout w \<and> inv_nout2 w) \<and> (inv_nstate w \<and> inv_nstate2 w) \<and> (inv_ncounter w \<and> inv_ncounter2 w) \<and> inv_n0 w \<and> inv_n02 w) \<and>
              wityping \<Gamma> (snd w)
         else if eval_world_raw2 w (Band (Bsig CLK) (Bsig_event CLK)) = Bv True
              then if eval_world_raw2 w (Bsig RST) = Bv True
                   then wp3_fun \<Gamma>
                         (Bcomp (Bassign_trans ACCUM (Bliteral Sig U_ZERO32) 1)
                           (Bcomp (Bassign_trans COUNTER (Bliteral Uns U_ZERO3) 1)
                             (Bcomp (Bassign_trans FRAC (Bliteral Sig U_ZERO32) 1) (Bcomp (Bassign_trans COMMON (Bliteral Sig U_ZERO32) 1) (Bcomp (Bassign_trans STATE S_INIT 1) (Bassign_trans OUTREADY_REG Bfalse 1))))))
                         (\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and>
                               (inv_sqr tw \<and> inv_sqr2 tw) \<and>
                               (inv_naccum tw \<and> inv_naccum2 tw) \<and>
                               (inv_term1 tw \<and> inv_term12 tw) \<and>
                               (inv_output tw \<and> inv_output2 tw) \<and> (inv_output_ready tw \<and> inv_output2_ready tw) \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> inv_n0 tw \<and> inv_n02 tw)
                         w
                   else wp3_fun \<Gamma>
                         (Bcomp (Bassign_trans ACCUM (Bsig NEXT_ACCUM) 1)
                           (Bcomp (Bassign_trans COUNTER (Bsig NEXT_COUNTER) 1)
                             (Bcomp (Bassign_trans FRAC (Bsig NEXT_FRAC) 1) (Bcomp (Bassign_trans COMMON (Bsig NEXT_COMMON) 1) (Bcomp (Bassign_trans STATE (Bsig NEXT_STATE) 1) (Bassign_trans OUTREADY_REG (Bsig NEXT_OUTREADYREG) 1))))))
                         (\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and>
                               (inv_sqr tw \<and> inv_sqr2 tw) \<and>
                               (inv_naccum tw \<and> inv_naccum2 tw) \<and>
                               (inv_term1 tw \<and> inv_term12 tw) \<and>
                               (inv_output tw \<and> inv_output2 tw) \<and> (inv_output_ready tw \<and> inv_output2_ready tw) \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> inv_n0 tw \<and> inv_n02 tw)
                         w
              else wp3_fun \<Gamma> Bnull
                    (\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and>
                          (inv_sqr tw \<and> inv_sqr2 tw) \<and>
                          (inv_naccum tw \<and> inv_naccum2 tw) \<and>
                          (inv_term1 tw \<and> inv_term12 tw) \<and>
                          (inv_output tw \<and> inv_output2 tw) \<and> (inv_output_ready tw \<and> inv_output2_ready tw) \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> inv_n0 tw \<and> inv_n02 tw)
                    w"
  proof (cases)
    case 1
    then show ?thesis 
      using * by auto
  next
    case 2
    have a: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)])"
    and  b: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)])"
    and  c: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)])"
    and  d: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bliteral Sig U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)])"
    and  e: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bliteral Sig
                                             U_ZERO32)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w
                                                                          (Bliteral Uns
                                                                            U_ZERO3)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)][ STATE, 1 :=\<^sub>2 eval_world_raw2 w S_INIT])"
      using cosine_locale_axioms * unfolding cosine_locale_def
      unfolding eval_world_raw2_suc
      by (auto intro!: worldline_upd_eval_world_raw_preserve_wityping2 )
   let ?w = "w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)]
                      [ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Uns U_ZERO3)]
                      [ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)]
                      [ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bliteral Sig U_ZERO32)]
                      [ STATE, 1 :=\<^sub>2 eval_world_raw2 w S_INIT]
                      [ OUTREADY_REG, 1 :=\<^sub>2 eval_world_raw2 w Bfalse]"
   have f: "(inv_ncommon ?w)" 
      using * unfolding inv_ncommon_alt_def fst_worldline_upd2
      by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have g: "(inv_ncommon2 ?w)"
     using * unfolding inv_ncommon2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have h: "(inv_sqr ?w)"
     using * unfolding inv_sqr_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have i: "(inv_sqr2 ?w)"
     using * unfolding inv_sqr2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have l: "(inv_naccum ?w)"
     using * unfolding inv_naccum_alt_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have m: "(inv_naccum2 ?w)"
     using * unfolding inv_naccum2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have n: "(inv_term1 ?w)"
     using * unfolding inv_term1_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have o: "(inv_term12 ?w)"
     using * unfolding inv_term12_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have p: "(inv_output ?w)"
     using * unfolding inv_output_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have q: "(inv_output2 ?w)"
     using * unfolding inv_output2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have r: "(inv_output_ready ?w)"
     using * unfolding inv_output_ready_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have s: "(inv_output2_ready ?w)"
     using * unfolding inv_output2_ready_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have t: "(inv_nout ?w)"
     using * unfolding inv_nout_alt_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have u: "(inv_nout2 ?w)"
     using * unfolding inv_nout2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have v: "(inv_nstate ?w)"
     using * unfolding inv_nstate_alt_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have w: "(inv_nstate2 ?w)"
     using * unfolding inv_nstate2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have x: "(inv_ncounter ?w)"
     using * unfolding inv_ncounter_alt_def fst_worldline_upd2
     apply (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
     apply (metis One_nat_def comp_apply)
     by (metis One_nat_def comp_apply)
   have y: "(inv_ncounter2 ?w)"
     using * unfolding inv_ncounter2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have z: "(inv_n0 ?w)"
     using * unfolding inv_n0_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have "(inv_n02 ?w)"
     using * unfolding inv_n02_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   then show ?thesis 
     unfolding wp3_fun.simps eval_world_raw2_suc      
     using a b c d e f g h i l m n o p q r s t u v w x y z 2
     using \<open>wityping \<Gamma> (snd w)\<close> by presburger
  next
    case 3
    have a: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)])"
      apply  (intro worldline_upd_eval_world_raw_preserve_wityping)
      using cosine_locale_axioms unfolding cosine_locale_def  
      by (auto simp add: bexp_wt.intros(3) \<open>wityping \<Gamma> (snd w)\<close>)
    hence b: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)])"
      apply (intro worldline_upd_eval_world_raw_preserve_wityping[where tw="w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)]", unfolded eval_world_raw2_suc])
      using cosine_locale_axioms unfolding cosine_locale_def  by (auto simp add: bexp_wt.intros(3) \<open>wityping \<Gamma> (snd w)\<close>)
    hence c: "wityping \<Gamma> (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)])"
      apply (intro worldline_upd_eval_world_raw_preserve_wityping[where tw="w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)]", unfolded eval_world_raw2_suc])
      using cosine_locale_axioms unfolding cosine_locale_def  by (auto simp add: bexp_wt.intros(3) \<open>wityping \<Gamma> (snd w)\<close>)
    hence d: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COMMON)])"
      apply (intro worldline_upd_eval_world_raw_preserve_wityping[where tw="w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w
                                           (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)]", unfolded eval_world_raw2_suc])
      using cosine_locale_axioms unfolding cosine_locale_def  by (auto simp add: bexp_wt.intros(3) \<open>wityping \<Gamma> (snd w)\<close>)
    hence e: " wityping \<Gamma>
                    (snd w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)]
                          [ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COMMON)][ STATE, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_STATE)])"
      apply (intro worldline_upd_eval_world_raw_preserve_wityping[where tw="w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)][ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)][ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)][ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COMMON)]", unfolded eval_world_raw2_suc])
      using cosine_locale_axioms unfolding cosine_locale_def  by (auto simp add: bexp_wt.intros(3) \<open>wityping \<Gamma> (snd w)\<close>)      
    let ?w = "w[ ACCUM, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_ACCUM)]
                      [ COUNTER, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COUNTER)]
                      [ FRAC, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_FRAC)]
                      [ COMMON, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_COMMON)]
                      [ STATE, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_STATE)]
                      [ OUTREADY_REG, 1 :=\<^sub>2 eval_world_raw2 w (Bsig NEXT_OUTREADYREG)]"      
   have f: "(inv_ncommon ?w)"
      using * unfolding inv_ncommon_alt_def fst_worldline_upd2
      by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have g: "(inv_ncommon2 ?w)"
     using * unfolding inv_ncommon2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have h: "(inv_sqr ?w)"
     using * unfolding inv_sqr_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have i: "(inv_sqr2 ?w)"
     using * unfolding inv_sqr2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have l: "(inv_naccum ?w)"
     using * unfolding inv_naccum_alt_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have m: "(inv_naccum2 ?w)"
     using * unfolding inv_naccum2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have n: "(inv_term1 ?w)"
     using * unfolding inv_term1_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have o: "(inv_term12 ?w)"
     using * unfolding inv_term12_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have p: "(inv_output ?w)"
     using * unfolding inv_output_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have q: "(inv_output2 ?w)"
     using * unfolding inv_output2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have r: "(inv_output_ready ?w)"
     using * unfolding inv_output_ready_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have s: "(inv_output2_ready ?w)"
     using * unfolding inv_output2_ready_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have t: "(inv_nout ?w)"
     using * unfolding inv_nout_alt_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have u: "(inv_nout2 ?w)"
     using * unfolding inv_nout2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have v: "(inv_nstate ?w)"
     using * unfolding inv_nstate_alt_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have w: "(inv_nstate2 ?w)"
     using * unfolding inv_nstate2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have x: "(inv_ncounter ?w)"
     using * unfolding inv_ncounter_alt_def fst_worldline_upd2
     apply (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
     apply (metis One_nat_def comp_apply)
     by (metis One_nat_def comp_apply)
   have y: "(inv_ncounter2 ?w)"
     using * unfolding inv_ncounter2_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
   have z: "(inv_n0 ?w)"
     using * unfolding inv_n0_def fst_worldline_upd2
     by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')
   have "(inv_n02 ?w)"
     using * unfolding inv_n02_def fst_worldline_upd2
     by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show ?thesis  
     unfolding wp3_fun.simps eval_world_raw2_suc      
     using a b c d e f g h i l m n o p q r s t u v w x y z 3
     using \<open>wityping \<Gamma> (snd w)\<close> by presburger
  next
    case 4
    then show ?thesis 
      unfolding wp3_fun.simps eval_world_raw2_suc using "*" by presburger
  qed
qed

lemma inv_all_except_reg_preserved2:
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>
              registers || ((((next_common || squaring) || next_accum || term1) || output) || output_ready)  ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))
        \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>"
  apply (rule  While_Suc')
     apply simp
    apply (simp add: conc_stmt_wf_def registers_def next_common_def squaring_def next_accum_def term1_def output_def output_ready_def next_outready_reg_def next_state_def next_counter_def ctr_neq_0_def)
   apply (simp add: conc_wt.intros(2))
  apply (rule parallel_valid[where R="\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)"])
  apply (rule conseq_valid[where Q="\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)", rotated])
  apply (rule wp3_conc_is_pre_valid[OF conc_stmt_wf_registers nonneg_delay_conc_registers cwt_reg], simp)
  using inv_all_imp_wp3_conc_registers apply (simp)
  apply (rule simulation_semi_complete)
  apply (rule inv_all_except_reg_preserved)
       apply simp
    apply (simp add: conc_stmt_wf_def registers_def next_common_def squaring_def next_accum_def term1_def output_def output_ready_def next_outready_reg_def next_state_def next_counter_def ctr_neq_0_def)
     apply (simp add: conc_wt.intros(2))
    apply (simp add: conc_stmt_wf_def registers_def next_common_def squaring_def next_accum_def term1_def output_def output_ready_def next_outready_reg_def next_state_def next_counter_def ctr_neq_0_def)
   apply simp
  apply (simp add: conc_wt.intros(2))
  done

lemma inv_reg_helper: 
  "\<And>s expr. inv_reg (w[s, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg w"
    unfolding inv_reg_alt_def fst_worldline_upd2
    by (auto simp add: snd_worldline_upd2 snd_worldline_upd2')

lemma inv_reg_comb_preserved_by_next_common:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> next_common \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_common nonneg_delay_conc_next_common cwt_nc], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[NEXT_COMMON, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> next_common (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding next_common_def
    wp3_conc_single'[OF cwt_nc[unfolded next_common_def] nonneg_delay_conc_next_common[unfolded next_common_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_squaring:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> squaring \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_squaring nonneg_delay_conc_squaring cwts], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[SQUARE_TEMP, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> squaring (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding squaring_def
    wp3_conc_single'[OF cwts[unfolded squaring_def] nonneg_delay_conc_squaring[unfolded squaring_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_next_accum:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> next_accum \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_accum nonneg_delay_conc_next_accum cwt_na], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[NEXT_ACCUM, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> next_accum (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding next_accum_def
    wp3_conc_single'[OF cwt_na[unfolded next_accum_def] nonneg_delay_conc_next_accum[unfolded next_accum_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_term1:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> term1 \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_term1 nonneg_delay_conc_term1 cwt_t1], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[TERM1, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> term1 (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w"
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding term1_def
    wp3_conc_single'[OF cwt_t1[unfolded term1_def] nonneg_delay_conc_term1[unfolded term1_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_output:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> output \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_output nonneg_delay_conc_output cwt_output], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[OUTPUT, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> output (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding output_def
    wp3_conc_single'[OF cwt_output[unfolded output_def] nonneg_delay_conc_output[unfolded output_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_output_ready:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> output_ready \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_output_ready nonneg_delay_conc_output_ready cwt_outready], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[OUTREADY, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> output_ready (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w"
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding output_ready_def
    wp3_conc_single'[OF cwt_outready[unfolded output_ready_def] nonneg_delay_conc_output_ready[unfolded output_ready_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_next_outready_reg:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> next_outready_reg \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_outready_reg nonneg_delay_conc_next_outready_reg cwt_no], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[NEXT_OUTREADYREG, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> next_outready_reg (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding next_outready_reg_def
    wp3_conc_single'[OF cwt_no[unfolded next_outready_reg_def] nonneg_delay_conc_next_outready_reg[unfolded next_outready_reg_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_next_state:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> next_state \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_state nonneg_delay_conc_next_state cwt_ns], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[NEXT_STATE, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> local.next_state (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding next_state_def
    wp3_conc_single'[OF cwt_ns[unfolded next_state_def] nonneg_delay_conc_next_state[unfolded next_state_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_next_counter:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> next_counter \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_next_counter nonneg_delay_conc_next_counter cwt_ncnt], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[NEXT_COUNTER, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> local.next_counter (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding next_counter_def
    wp3_conc_single'[OF cwt_ncnt[unfolded next_counter_def] nonneg_delay_conc_next_counter[unfolded next_counter_def]]
    wp3_fun.simps by presburger
qed

lemma inv_reg_comb_preserved_by_ctr_neq_0:
  " \<Gamma> \<turnstile> \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> ctr_neq_0 \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule Conseq'[where Q="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_ctr_neq_0 nonneg_delay_conc_ctr_neq_0 cwt_n0], simp)
proof (rule, rule)
  fix w
  assume " wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w"
  have **: "\<And>expr. inv_reg2 (w[CTR_NEQ_0, 1 :=\<^sub>2 eval_world_raw2 w expr]) \<longleftrightarrow> inv_reg2 w"
    unfolding inv_reg2_def fst_worldline_upd2
    by (auto simp add: event_of_worldline_upd2 snd_worldline_upd2 snd_worldline_upd2')
  then show "wp3_conc \<Gamma> local.ctr_neq_0 (\<lambda>tw. inv_reg tw \<and> inv_reg2 tw) w" 
    using inv_reg_helper ** ` wityping \<Gamma> (snd w) \<and> inv_reg w \<and> inv_reg2 w` 
    unfolding ctr_neq_0_def
    wp3_conc_single'[OF cwt_n0[unfolded ctr_neq_0_def] nonneg_delay_conc_ctr_neq_0[unfolded ctr_neq_0_def]]
    wp3_fun.simps by presburger
qed

lemmas collection = inv_reg_comb_preserved_by_next_common inv_reg_comb_preserved_by_squaring
inv_reg_comb_preserved_by_next_accum inv_reg_comb_preserved_by_term1 inv_reg_comb_preserved_by_output
inv_reg_comb_preserved_by_output_ready inv_reg_comb_preserved_by_next_outready_reg
inv_reg_comb_preserved_by_next_state inv_reg_comb_preserved_by_next_counter inv_reg_comb_preserved_by_ctr_neq_0
correctness_registers'

lemma inv_reg_preserved_by_all:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> 
         (((((next_common || squaring) || next_accum || term1) || output) || output_ready)  ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))) || registers
        \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
  apply (rule While_Suc)
  by (auto intro!: Parallel[where R="\<lambda>tw. inv_reg tw \<and> inv_reg2 tw"] simp add: collection)
     (auto simp add: conc_stmt_wf_def circuit_defs)

theorem
  "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)) \<and> (inv_reg tw \<and> inv_reg2 tw)\<rbrace>
          architecture
        \<lbrace>\<lambda>tw. ((inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)) \<and> (inv_reg tw \<and> inv_reg2 tw)\<rbrace>"
proof -
  have *: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace> 
         (((((next_common || squaring) || next_accum || term1) || output) || output_ready)  ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))) || registers
        \<lbrace>\<lambda>tw. inv_reg tw \<and> inv_reg2 tw\<rbrace>"
    apply (intro conc_sim_soundness[OF inv_reg_preserved_by_all])
    by (auto intro!: conc_wt.intros)(auto simp add: conc_stmt_wf_def circuit_defs)
  have **: "conc_stmt_wf ((((((next_common || squaring) || next_accum || term1) || output) || output_ready)  ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))) || registers)"
    unfolding conc_stmt_wf_def circuit_defs by auto
  have ***: "\<Gamma> \<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>
              (((((next_common || squaring) || next_accum || term1) || output) || output_ready)  ||  ((next_outready_reg || next_state) || (next_counter || ctr_neq_0))) || registers
        \<lbrace>\<lambda>tw. (inv_ncommon tw \<and> inv_ncommon2 tw) \<and> (inv_sqr tw \<and> inv_sqr2 tw) \<and> (inv_naccum tw \<and> inv_naccum2 tw) \<and> (inv_term1 tw \<and> inv_term12 tw) \<and> (inv_output tw \<and> inv_output2 tw)  \<and> (inv_output_ready tw \<and> inv_output2_ready tw)
            \<and> (inv_nout tw \<and> inv_nout2 tw) \<and> (inv_nstate tw \<and> inv_nstate2 tw) \<and> (inv_ncounter tw \<and> inv_ncounter2 tw) \<and> (inv_n0 tw \<and> inv_n02 tw)\<rbrace>"
    using inv_all_except_reg_preserved2  unfolding sim_hoare_valid_wt_parallel_commute[OF **, symmetric]
    by auto
  show ?thesis
    using comb_sim_hoare_valid_wt[OF *** *]  unfolding architecture_def by auto
qed

end

end
 