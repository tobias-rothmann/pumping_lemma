theory Original
  imports Defs 
begin

section \<open>Defs and preleminaries/auxillary lemmas\<close>
subsection \<open>local defs\<close>
text \<open>since the definition of the language (lang dfa) uses states and not only words, we also need to argue about 
states, which we therefore track by extending our word definition.\<close>
inductive word_rec_states :: "state list \<Rightarrow> state \<Rightarrow> DFA \<Rightarrow> word \<Rightarrow> bool" where
empty:  "q \<in> (Q dfa) \<Longrightarrow> word_rec_states [] q dfa ''''" |
step: "\<lbrakk>word_rec_states qs q' dfa w ;c \<in> (\<Sigma> dfa); p \<in> (Q dfa); (\<delta> dfa) q' c = p\<rbrakk> \<Longrightarrow>  word_rec_states (qs@[q']) p dfa (w@[c])" |
back_step: "\<lbrakk>word_rec_states qs q' dfa w ;c \<in> (\<Sigma> dfa); p \<in> (Q dfa); (\<delta> dfa) p c = hd (qs@[q'])\<rbrakk> \<Longrightarrow>  word_rec_states (p#qs) q' dfa (c#w)"

fun repeat :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  0: "repeat v 0 = []" | 
  i: "repeat v i = repeat v (i-1) @ v"

subsection \<open>auxiliary lemmas\<close>
lemma wordl_eq_statesl: "word_rec_states qs p dfa w \<Longrightarrow> length qs = length w"
proof (induction rule: word_rec_states.induct)
  case (empty q dfa)
  then show ?case by simp
next
  case (step qs q' dfa w c p)
  then show ?case by simp
next
  case (back_step qs q' dfa w c p)
  then show ?case by simp
qed

text \<open>show that word implies word_rec_states and vice versa\<close>
lemma word_imp_rec:  "word q p dfa w \<Longrightarrow> \<exists>qs. word_rec_states (qs) p dfa w \<and> hd (qs@[p]) = q" 
proof (induction rule: word.induct)
  case (empty q dfa)
  then show ?case using word_rec_states.empty by fastforce
next
  case (step q q' dfa w c p)
  then show ?case using word_rec_states.step using hd_append2 by blast
next
  case (back_step q q' dfa w c p)
  then show ?case using word_rec_states.back_step
    by (metis hd_append2 list.distinct(1) list.sel(1))
qed

lemma rec_imp_word:  "word_rec_states (qs) p dfa w \<Longrightarrow>word (hd (qs@[p])) p dfa w" 
proof (induction rule: word_rec_states.induct)
  case (empty q dfa)
  then show ?case using word.empty by simp
next
  case (step qs q' dfa w c p)
  then show ?case using word.step 
    by (metis hd_append2 snoc_eq_iff_butlast)
next
  case (back_step qs q' dfa w c p)
  then show ?case by (simp add: word.back_step)
qed

text \<open>show that all states referred to in the state list (qs) and final state (p) of word_rec_states
are indeed states of the dfa (\<in> (Q dfa))\<close>
lemma state_of_Q: "\<lbrakk>word_rec_states qs p dfa w\<rbrakk> \<Longrightarrow> \<forall>q \<in> (set qs) \<union> {p} . q \<in> (Q dfa)"
proof (induction rule: word_rec_states.induct)
  case (empty q dfa)
  then show ?case by simp
next
  case (step qs q' dfa w c p)
  then show ?case
    by (metis Un_iff empty_set list.simps(15) set_append singletonD)
next
  case (back_step qs q' dfa w c p)
  then show ?case by simp
qed

lemma hd_drop: "i < length l \<Longrightarrow> hd (drop i l) = nth l i"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case using hd_drop_conv_nth by blast
qed

text \<open>aux lemma for the next one\<close>
lemma not_distinct: "\<lbrakk>finite M; (set l) \<subseteq> M ; length l > card M\<rbrakk> \<Longrightarrow> \<not> distinct l"
proof 
  assume 0: "finite M"
  assume 1: "(set l) \<subseteq> M"
  assume 2: "length l > card M"
  assume 3: "distinct l"
  have "card M \<ge> card (set l)" using "0" "1" card_mono by blast
  also have "card (set l) = length l" using distinct_card using "3" by blast
  also have "length l > card M" using 2 by blast
  then show "False" using calculation leD by blast
qed

text \<open>for the purpose of showing that if qs is longer than the cardianlity of Q, there must be two equal states in qs\<close>
corollary i_j: "\<lbrakk>finite M; (set l) \<subseteq> M ; length l > card M\<rbrakk> \<Longrightarrow> \<exists>i j. i\<ge>0 \<and> i<j \<and> j<length l \<and> l ! i = l!j"
  by (metis distinct_conv_nth not_distinct not_less_iff_gr_or_eq zero_le)

text \<open>show that sub paths in a path/word are still valid paths in the dfa\<close>
lemma take_word_rec_states: "\<lbrakk>word_rec_states sts s dfa w; i\<le>length w\<rbrakk> \<Longrightarrow> word_rec_states (take i (sts@[s])) ((sts@[s]) ! i) dfa (take i w)"
proof (induction arbitrary: i rule: word_rec_states.induct)
  case (empty q dfa)
  then show ?case using word_rec_states.empty by auto
next
  case (step qs q' dfa w c p)
  then show ?case
  proof (cases "i>length w")
    let ?qs = "((qs @ [q']) @ [p])"
    case True
    then show ?thesis
      by (metis (no_types, lifting) Suc_leI antisym butlast_snoc le_imp_less_Suc length_append_singleton nth_append_length step.hyps(1) step.hyps(2) step.hyps(3) step.hyps(4) step.prems take_all_iff take_butlast word_rec_states.step wordl_eq_statesl)
  next
    case False 
    then show ?thesis
      by (metis (no_types, lifting) butlast_snoc length_append_singleton less_Suc_eq_le not_less_eq nth_append step.IH step.hyps(1) step.prems take_butlast wordl_eq_statesl)
  qed
next
  case (back_step qs q' dfa w c p)
  then show ?case
  proof (cases "i<1")
    case True
    then show ?thesis by (simp add: back_step.hyps(3) word_rec_states.empty)
  next
    case False
    have take: "take i ((p # qs) @ [q']) = [p] @ take (i-1) (qs@[q'])" 
      by (metis Cons_eq_appendI False add_diff_inverse_nat append_Nil plus_1_eq_Suc take_Suc_Cons)
    have bang:"((p # qs) @ [q']) ! i = (qs@[q']) ! (i-1)" using False by auto 
    have c:"take i (c # w) = c#(take (i-1) w)" by (metis False less_one take_Cons')
    have i: "(i-1)\<le>length w" using back_step.prems by auto
    then have w_im1: "word_rec_states (take (i-1) (qs @ [q'])) ((qs @ [q']) ! (i-1)) dfa (take (i-1) w)"
      using take bang c back_step.IH by blast
    let ?qstake =  "(take (i-1) (qs @ [q']))"
    let ?qsi = "((qs @ [q']) ! (i-1))"
    let ?wtake = "(take (i-1) w)"
    have "hd ((take (i - 1) (qs @ [q'])) @ [(qs @ [q']) ! (i - 1)]) = hd (qs @ [q'])"
      by (metis append_Nil hd_append2 hd_conv_nth hd_take list.sel(1) neq0_conv snoc_eq_iff_butlast take_eq_Nil2)
    then have "\<delta> dfa p c = hd ((take (i - 1) (qs @ [q'])) @ [(qs @ [q']) ! (i - 1)])" 
      using back_step.hyps(4) by presburger
    then have "word_rec_states (p#?qstake) ?qsi dfa (c#?wtake)"
      using back_step.hyps(2) back_step.hyps(3) w_im1 word_rec_states.back_step by blast
    then show ?thesis
      by (metis Cons_eq_appendI append_Nil bang c take)
 qed
qed


lemma drop_word_rec_states: "\<lbrakk>word_rec_states sts s dfa w; i\<le>length w\<rbrakk> \<Longrightarrow> word_rec_states (butlast (drop i (sts@[s]))) (last (sts@[s])) dfa (drop i w)"
proof (induction arbitrary: i rule: word_rec_states.induct)
  case (empty q dfa)
  then show ?case by (simp add: word_rec_states.empty)
next
  case (step qs q' dfa w c p)
  then show ?case 
  proof (cases "i\<le>length w")
    case True
    have "word_rec_states (butlast (drop i ((qs @ [q']) @ [p]))) (last ((qs @ [q']) @ [p])) dfa (drop i (w @ [c]))
    = word_rec_states (drop i (qs) @ [q']) p dfa (drop i (w) @ [c])"
      by (metis (no_types, lifting) True butlast_snoc diff_is_0_eq' drop0 drop_append drop_butlast last_snoc step.hyps(1) wordl_eq_statesl)
    also have "word_rec_states (drop i (qs) @ [q']) p dfa (drop i (w) @ [c])"
      using word_rec_states.step
      by (metis True butlast_snoc drop_butlast last_snoc step.IH step.hyps(2) step.hyps(3) step.hyps(4))
    then show ?thesis using calculation by blast
  next
    case False
    have "i>length w" using False step.prems by auto
    then show ?thesis 
      using not_less_eq step.hyps(1) step.hyps(3) step.prems word_rec_states.empty wordl_eq_statesl by fastforce
 qed
next
  case (back_step qs q' dfa w c p)
  then show ?case
  proof (cases "i>1")
    show ?thesis
      by (metis Cons_eq_appendI back_step.hyps(1) back_step.hyps(2) back_step.hyps(3) back_step.hyps(4) back_step.prems butlast_snoc diff_diff_left diff_is_0_eq drop_Cons' last_snoc length_Cons local.back_step(5) plus_1_eq_Suc word_rec_states.back_step) 
  next
    case False
    then show ?thesis
      by (metis Cons_eq_appendI One_nat_def back_step.hyps(1) back_step.hyps(2) back_step.hyps(3) back_step.hyps(4) butlast_snoc diff_Suc_1 drop0 drop_Cons' last_snoc less_one not_less_iff_gr_or_eq word_rec_states.back_step)
  qed
qed


text \<open>show append property of paths/subwords\<close>
lemma append_word_rec_states: "\<lbrakk>word_rec_states qs q dfa w; word_rec_states (q#ps) p dfa w'\<rbrakk> \<Longrightarrow> (word_rec_states (qs@(q#ps)) p dfa (w@w'))"
proof (induction arbitrary: ps p w' rule: word_rec_states.induct)
  case (empty q dfa)
  then show ?case by simp
next
  case (step qs q dfa w c p')
  have rule: "word_rec_states (q # p' # ps) p dfa (c#w') \<Longrightarrow> word_rec_states (qs @ q # p' # ps) p dfa (w @ c#w')" 
    using step.IH by simp
  have "q \<in> Q dfa" using state_of_Q step.hyps(1) by auto
  have " \<delta> dfa q c = hd (p' # ps)" by (simp add: step.hyps(4))
  then have "word_rec_states (q # (p' # ps)) p dfa (c#w')"
    by (simp add: \<open>q \<in> Q dfa\<close> step.hyps(2) word_rec_states.back_step step.prems)
  then show ?case using rule by simp
next
  case (back_step qs q' dfa w c p')
  then show ?case
    by (metis (no_types, lifting) append_Cons append_is_Nil_conv hd_append2 list.sel(1) self_append_conv2 word_rec_states.back_step)
qed


text \<open>extend append property to allquantor in the case that the path starts with the same state it 
ended with, to at some point show that uv^iw is a valid word for all i.\<close>
lemma loop_states: "\<lbrakk>length qs > 0;word_rec_states qs q dfa w; hd qs = q; i \<ge> 0\<rbrakk> \<Longrightarrow> word_rec_states (repeat qs i) q dfa (repeat w i)"
proof (induction i)
  case 0
  then show ?case using state_of_Q word_rec_states.empty by simp
next
  case (Suc i)
  have wrs_repeat: "word_rec_states (repeat qs i) q dfa (repeat w i)" 
    using Suc.IH Suc.prems by blast
  from \<open>hd qs = q\<close> obtain qs' where qs':"qs= (q#qs')"
    by (metis Cons_nth_drop_Suc Suc.prems(1) drop0 hd_conv_nth length_greater_0_conv) 
  then have wrs_qs': "word_rec_states (q#qs') q dfa w" using Suc.prems(2) by blast
  have eq: "word_rec_states (repeat qs (Suc i)) q dfa (repeat w (Suc i)) = 
       word_rec_states  ((repeat qs i)@(q#qs')) q dfa ((repeat w i)@w)" using qs' by simp
  have "word_rec_states  ((repeat qs i)@(q#qs')) q dfa ((repeat w i)@w)"
    using append_word_rec_states wrs_qs' wrs_repeat by simp
  then show ?case using eq by blast
qed 

text \<open>repeat for prepending instead of appending\<close>
lemma repeat_rev: "i>0 \<Longrightarrow>repeat v i = v @ repeat v (i-1)"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case
    by (metis append.assoc append.right_neutral append_self_conv2 bot_nat_0.not_eq_extremum diff_Suc_1 nat.discI repeat.elims)
qed


section \<open>pumping lemma\<close>
text \<open>pumping lemma based on
https://teaching.model.in.tum.de/2022ss/theo/handout.pdf theorem 3.32 pumping lemma for regular 
langauges\<close>
theorem pumping_lemma:
  assumes  "Q_\<Sigma>_finite (dfa::DFA)" 
      and "\<delta>_total_on_Q_\<Sigma> dfa"
      and "q\<^sub>0_in_Q dfa"
      and "F_sub_Q dfa"
    shows "\<exists>n::nat>0. \<forall>z \<in> (lang dfa). length z \<ge> n \<longrightarrow> (
        \<exists> u v w. z = u@v@w \<and>
        v \<noteq> '''' \<and>
        length (u@v) \<le> n \<and>
        (\<forall>i::nat. (u@(repeat v i)@w) \<in> (lang dfa))
)" 
proof -
  text \<open> pick n such that n = cardinality of Q and therefore first show that card Q > 0\<close>
  from assms(3) have "card (Q dfa) > 0"
    using Q_\<Sigma>_finite_def assms(1) card_gt_0_iff q\<^sub>0_in_Q_def by auto
  then obtain n where n: "card (Q dfa) = n \<and> n > 0" by blast
  text \<open>show the implication with our picked n for arbitrary but fixed z \<close>
  have z: "(\<forall>z. z\<in>lang dfa \<and> n \<le> length z \<longrightarrow> (\<exists>u v w. z = u @ v @ w \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<and> (\<forall>i. u @ repeat v i @ w \<in> lang dfa)))"
  proof (intro allI)
    fix z
    show "z\<in>lang dfa \<and> n \<le> length z \<longrightarrow> (\<exists>u v w. z = u @ v @ w \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<and> (\<forall>i. u @ repeat v i @ w \<in> lang dfa))" 
    proof (cases "z\<in>lang dfa \<and> n \<le> length z")
      case True
      text \<open>proof that u v w = z exist and fulfill the requirements if the precondition is True\<close>
      then obtain m where m: "length z = m \<and> m\<ge>n" by blast
      have "(\<exists>u v w. z = u @ v @ w \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<and> (\<forall>i. u @ repeat v i @ w \<in> lang dfa))"
      proof -
        text \<open>reconstruct the state path from z\<close>
        obtain qs q where qs_q: "word_rec_states qs q dfa z \<and> hd (qs@[q]) = q\<^sub>0 dfa \<and> q \<in> F dfa" using word_imp_rec True by fastforce
        let ?qs = "(qs@[q])"
        have qs_q_length: "length ?qs = m+1" using wordl_eq_statesl qs_q m by fastforce
        then have qs_q_l_n: "n\<le>length z" using m by simp
        subsubsection \<open>cut n+1 states in of ?qs to guarantee |uv| \<le> n\<close>
        text \<open>cut off qs@[q] at n+1 for |uv| \<le> n (to get a word with length \<le> n).
        We split into qs'@[q'] and gw, where gw stands for guarantied w, which means these states
        only compute the tail of w and qs'@[q'] could compute u v and the head (front part) of w \<close>
        then obtain qs' q' Wqs'q' where qs'_q'_Wqs'q':"qs'=take n ?qs \<and> q' = ?qs ! n \<and> Wqs'q' = take n z \<and> word_rec_states qs' q' dfa Wqs'q'" 
          using qs_q take_word_rec_states by simp
        let ?qs' = "(qs'@[q'])"
        have "length ?qs' = n+1" using qs_q_length m
          by (metis Suc_eq_plus1 add_diff_cancel_right' append_take_drop_id diff_diff_cancel length_append length_append_singleton length_drop qs'_q'_Wqs'q' wordl_eq_statesl)
        then obtain gwqs gwq gw where gwqs_gwq_Wgwqsgwq: "gwqs = butlast (drop n ?qs) \<and> gwq = last ?qs \<and> gw = drop n z \<and>  word_rec_states gwqs gwq dfa gw"
          using drop_word_rec_states qs_q qs_q_l_n by presburger
        then have "Wqs'q'@gw=z" using append_take_drop_id qs'_q'_Wqs'q' by blast 
        from qs'_q'_Wqs'q' qs_q_length m have "length ?qs' = n+1" by simp
        then have qs'q'_length: "length ?qs' > card (Q dfa)" using n by simp 
        also have qs'q'_sub_Q: "set ?qs' \<subseteq> Q dfa" using qs'_q'_Wqs'q' state_of_Q by auto
        text \<open>Now ?qs' is exactly one longer than the cardinality of Q and we therefore can
        find equal states Pi and Pj to loop over and obtain u and v after wards, such that |uv| \<le> n\<close>
        obtain i j where i_j: "0\<le>i \<and> i<j \<and> j < length ?qs' \<and> ?qs' ! i = ?qs' ! j" 
          using i_j assms qs'q'_sub_Q qs'q'_length Q_\<Sigma>_finite_def by metis
        subsubsection \<open>Cut into u v w\<close>
        text \<open> We cut ?qs' accordingly int u v w, where v is a loop that can be used l times, where l\<ge>0 and
          uv^lw \<in> (lang dfa). To make correct use of our append_word_rec_states lemma we therefore 
          need to make ?qs'[i] the last state of u and the first of v and ?qs'[j] the last state of v and the first 
          of fw where fw is the possible first part of w that could still be in ?qs'\<close>
        then obtain uqs uq u where u:"uqs=take i ?qs' \<and> uq = ?qs' ! i \<and> u = take i Wqs'q' \<and> word_rec_states uqs uq dfa u"
          by (metis length_append_singleton less_Suc_eq_le order_less_trans qs'_q'_Wqs'q' take_word_rec_states wordl_eq_statesl)
        obtain vfwqs vfwq vfw where vfw: "vfwqs= butlast (drop i ?qs') \<and> vfwq = last ?qs' \<and> vfw = drop i Wqs'q' \<and> word_rec_states vfwqs vfwq dfa vfw"
          by (metis (no_types, lifting) drop_word_rec_states length_append_singleton less_Suc_eq_le local.i_j order_less_trans qs'_q'_Wqs'q' wordl_eq_statesl)
        let ?vfwqs = "vfwqs@[vfwq]"
        have "u@vfw@gw=z" by (metis \<open>Wqs'q' @ gw = z\<close> u append.assoc append_take_drop_id vfw)
        let ?j="(j-i)"
        have j:"?j < length ?vfwqs" using last_drop local.i_j vfw by auto
        then obtain vqs vq v where v: "vqs= take ?j ?vfwqs \<and> vq = ?vfwqs ! ?j \<and> v = take ?j vfw \<and> word_rec_states vqs vq dfa v"
          by (metis length_append_singleton less_Suc_eq_le take_word_rec_states vfw wordl_eq_statesl)
        text \<open>as a corollary we can show now the condition v\<noteq>'''' because i and j are not equal, 
        and therefore |vqs@[vq]|\<ge>2/|vqs|\<ge>1 and hence v cannot be empty by wordl_eq_statesl\<close>
        then have "v\<noteq>''''"
          by (metis j diff_is_0_eq leD length_append_singleton list.size(3) local.i_j not_less_eq take_eq_Nil vfw wordl_eq_statesl zero_less_diff)
        have hd_eq_last_v: "hd vqs = vq"
        proof -
          have "?vfwqs = drop i ?qs'" using local.i_j vfw by auto
          then have "?vfwqs ! ?j = ?qs' ! j "
            by (metis (full_types) le_add_diff_inverse less_or_eq_imp_le local.i_j nth_drop order_less_trans) 
          also have "hd ?vfwqs = ?qs' ! i"
            by (metis \<open>vfwqs @ [vfwq] = drop i (qs' @ [q'])\<close> hd_drop local.i_j order_less_trans)
          then show ?thesis
            by (metis calculation hd_take local.i_j v zero_less_diff)
        qed
        obtain fwqs fwq fw where fw: "fwqs = butlast (drop ?j ?vfwqs) \<and> fwq = last ?vfwqs \<and> fw = drop ?j vfw \<and> word_rec_states fwqs fwq dfa fw"
          by (metis drop_word_rec_states j length_append_singleton less_Suc_eq_le vfw wordl_eq_statesl)
        text \<open>put together the front part and the tail part of w\<close>
        let ?w = "(fw@gw)"
        let ?wqs = "fwqs@gwqs"
        let ?wq = "gwq"
        have w: "word_rec_states ?wqs ?wq dfa ?w"
        proof (cases gwqs)
          case Nil
          then show ?thesis
            by (metis add.right_neutral append.right_neutral drop_eq_Nil fw gwqs_gwq_Wgwqsgwq last_snoc le_add_diff_inverse length_drop list.size(3) nth_append_length qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl m)
        next
          case (Cons a list)
          then show ?thesis 
            by (metis append_butlast_last_id append_word_rec_states drop_eq_Nil fw gwqs_gwq_Wgwqsgwq hd_append2 hd_drop last_snoc le_imp_less_Suc length_append_singleton list.distinct(1) list.sel(1) not_less_eq_eq qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl m)
        qed
        text \<open>after we cut u v and ?w and its states check that u v and ?w form still z and are 
        correct obtained\<close>
        have "u@v@?w=z" by (metis \<open>u @ vfw @ gw = z\<close> append.assoc append_take_drop_id v fw)
        have hd_fwqsfwq: "hd (fwqs@[fwq]) = vq" by (metis append_butlast_last_id drop_eq_Nil fw hd_drop j last_drop linorder_not_le v)
        text \<open>finally for the split we can conclude that |uv|\<le>n\<close>
        have length_uv_n: "length (u@v) \<le> n"
        proof -
          have l_u_vfw: "length (u@vfw) < length ?qs'" 
            by (metis append_take_drop_id length_append_singleton lessI qs'_q'_Wqs'q' u vfw wordl_eq_statesl)
          have "length (u@v) < length ?qs'" using v l_u_vfw by auto 
          then show ?thesis using \<open>length (qs' @ [q']) = n + 1\<close> by presburger
        qed
        subsubsection \<open>show u@(repeat l v)@w \<in> (lang dfa)\<close>
        text \<open>the next big step is showing u@(repeat l v)@w is valid and in (lang dfa)
        We start by showing v^l is a valid sub-path of the dfa for all l\<close>
        from hd_eq_last_v have v_l: "\<forall>l. l\<ge>0 \<longrightarrow>  word_rec_states (repeat vqs l) vq dfa (repeat v l)"
          by (metis \<open>v \<noteq> []\<close> bot_nat_0.extremum length_greater_0_conv loop_states v wordl_eq_statesl)
        text \<open>next we want to prepend u to v^l
        Therefore  we show that they are appendable because they have the same ending state on u 
        and starting state on v\<close>
        have "uq= hd ?vfwqs"
        proof -
          have "?vfwqs = drop i ?qs'" using local.i_j vfw by auto
          then have "hd ?vfwqs = ?qs' ! i"
            by (metis hd_drop local.i_j order_less_trans)
          then show ?thesis using u by argo
        qed
        then have uq_hd_vqs: "uq = hd vqs" by (metis hd_take local.i_j v zero_less_diff)
        text \<open>first the base appendiation for l=1, that we'll use in the l step\<close>
        have base_uv: "word_rec_states (uqs@vqs) vq dfa (u@v)" 
        proof -
          obtain vqs' where "vqs=(uq#vqs')"
            using uq_hd_vqs by (metis \<open>v \<noteq> []\<close> list.collapse list.discI rotate1.simps(2) rotate1_is_Nil_conv take_eq_Nil v)
          then have "word_rec_states (uqs @ (uq#vqs')) vq dfa (u @ v)" using append_word_rec_states u v by blast
          then show ?thesis by (simp add: \<open>vqs = uq # vqs'\<close>)
        qed
        text \<open>and now using the base case we can proof u@v^l for all l\<close>
        then have urv: "\<forall>l. l\<ge>0\<longrightarrow>word_rec_states (uqs@(repeat vqs l)) vq dfa (u@(repeat v l))" 
        proof (intro allI)
          fix l
          show "l\<ge>0 \<longrightarrow> word_rec_states (uqs@(repeat vqs l)) vq dfa (u@(repeat v l))" 
           proof (cases "l\<le>1")
             case True
             then show ?thesis
             proof (cases "l=1")
               case True
               then show ?thesis using base_uv by simp
             next
               case False
               have "l=0" using False True by linarith
               then show ?thesis
                 using hd_eq_last_v u uq_hd_vqs by auto
           qed
           next
             case False
             have "uq= hd ?vfwqs" using \<open>uq = hd (vfwqs @ [vfwq])\<close> by blast
             then have "uq = hd vqs" using uq_hd_vqs by blast
             then obtain vqs' where "vqs=(uq#vqs')"
               by (metis Nil_is_append_conv diff_is_0_eq leD list.collapse local.i_j not_Cons_self2 take_eq_Nil v)
             then have r:"l\<ge>1\<Longrightarrow>repeat vqs l = (uq#vqs')@(repeat vqs (l-1))" 
             proof (induction l)
               case 0
               then show ?case by simp
             next
               case (Suc l)
               then show ?case using repeat_rev by blast 
             qed
             then show ?thesis
               by (metis False append_Cons append_word_rec_states nat_le_linear u v_l)
           qed
         qed
         text \<open>now append ?w to uv^l
        We start with the base case l=0 and append ?w to u\<close>
        have uw: "word_rec_states (uqs@?wqs) ?wq dfa (u@?w)" 
        proof (cases ?wqs)
          case Nil
          then show ?thesis
            by (metis Nil_is_append_conv add.right_neutral append.right_neutral append_self_conv2 butlast_snoc drop_butlast drop_eq_Nil fw gwqs_gwq_Wgwqsgwq hd_eq_last_v hd_fwqsfwq last_snoc le_add_diff_inverse length_drop list.sel(1) list.size(3) nth_append_length qs'_q'_Wqs'q' qs_q u uq_hd_vqs vfw wordl_eq_statesl m)
        next
          case (Cons a list)
          then show ?thesis
            by (metis (no_types, lifting) \<open>word_rec_states (fwqs @ gwqs) gwq dfa (fw @ gw)\<close> append_butlast_last_id append_self_conv2 append_word_rec_states drop_eq_Nil fw gwqs_gwq_Wgwqsgwq hd_append2 hd_drop hd_eq_last_v hd_fwqsfwq last_snoc leD le_imp_less_Suc length_append_singleton list.distinct(1) list.sel(1) qs'_q'_Wqs'q' qs_q u uq_hd_vqs vfw wordl_eq_statesl m)
        qed
        text \<open>then we go in the induction on l\<close>
        have u_repeat_v_l_w: "\<forall>l. l\<ge>0 \<longrightarrow> word_rec_states (uqs@(repeat vqs l)@?wqs) ?wq dfa (u@(repeat v l)@?w)"
        proof (intro allI)
          fix l
          show "l\<ge>0 \<longrightarrow> word_rec_states (uqs@(repeat vqs l)@?wqs) ?wq dfa (u@(repeat v l)@?w)"
          proof (cases"l=0")
            case True
            then show ?thesis by (simp add: uw)
          next
            case False
            let ?l = "(l-1)"
            have "word_rec_states (vqs@?wqs) ?wq dfa (v@?w)" 
            proof (cases ?wqs)
              case Nil
              then have "vq = ?wq"
                by (metis Nil_is_append_conv True add.right_neutral append_self_conv2 fw gwqs_gwq_Wgwqsgwq hd_fwqsfwq last_snoc le_add_diff_inverse length_drop list.sel(1) list.size(3) nth_append_length qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl)
              then show ?thesis 
                by (metis append.right_neutral length_0_conv local.Nil v w wordl_eq_statesl)
            next
              case (Cons a list)
              then obtain hdw wqs where "(hdw# wqs) = ?wqs" by simp
              then have "hdw = vq"
                by (metis (no_types, lifting) True append_butlast_last_id append_self_conv2 drop_eq_Nil fw gwqs_gwq_Wgwqsgwq hd_append hd_drop hd_fwqsfwq last_snoc le_imp_less_Suc length_append_singleton list.distinct(1) list.sel(1) not_less_eq_eq qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl)
              then show ?thesis
                by (metis \<open>hdw # wqs = fwqs @ gwqs\<close> append_word_rec_states v w)
            qed
            text \<open>we divide uvw into a frontpart uv^(l-1) and a backpart vw to bring the multiple 
            appendiations into a form where we can apply our append_word_rec_states lemma, because 
            we know uv^l holds for arbitrary l and vw also holds.\<close>
            have eq:"?thesis = word_rec_states (uqs@(repeat vqs ?l)@(vqs@?wqs)) ?wq dfa (u@(repeat v ?l)@(v@?w))"
              by (metis False append.assoc bot_nat_0.extremum repeat.elims)
            obtain vqs' where vqs': "vqs=(vq#vqs')" by (metis \<open>v \<noteq> []\<close> hd_eq_last_v length_0_conv list.collapse v wordl_eq_statesl)
            from eq have "?thesis =  word_rec_states (uqs@(repeat vqs ?l)@((vq#vqs')@?wqs)) ?wq dfa (u@(repeat v ?l)@(v@?w))"
              using vqs' by simp
            let ?frontpart = "(uqs@(repeat vqs ?l))"
            let ?frontword= "(u@(repeat v ?l))"
            obtain backpart backword where b: "backpart=vqs'@?wqs \<and> backword=(v@?w)" by simp
            have "word_rec_states (uqs@(repeat vqs ?l)@(vq#vqs'@?wqs)) ?wq dfa (u@(repeat v ?l)@(v@?w))
              = word_rec_states (?frontpart @ (vq#backpart)) ?wq dfa (?frontword@backword)"
              by (simp add: b )
            have uvw: "word_rec_states (?frontpart @ (vq#backpart)) ?wq dfa (?frontword@backword)"
            proof (rule append_word_rec_states)
              show "word_rec_states ?frontpart vq dfa ?frontword" using urv by simp
              show "word_rec_states (vq # backpart) gwq dfa backword"
                using vqs' \<open>word_rec_states (vqs @ fwqs @ gwqs) gwq dfa (v @ fw @ gw)\<close> b by simp
            qed
            then show ?thesis
              using vqs' b eq by auto
          qed  
        qed
        text \<open>After we now showed that uv^lw is a valid path in the dfa, we now show that for all l
         uv^lw is also in the langauage of the dfa. Therefore we need to show for all l that the head is  
         q0 and the last state is in (F dfa)\<close>
        have u_repeat_v_l_w_lang: "\<forall>l. l\<ge>0 \<longrightarrow> (u@(repeat v l)@?w) \<in> lang dfa"
        proof (intro allI)
          fix l
          text \<open>we know per construction that ?wq is always the last state in uv^lw and therefore
           only need to show that ?wq \<in> (F dfa)\<close>
          have wq_f: "?wq \<in> F dfa" by (simp add: gwqs_gwq_Wgwqsgwq qs_q)
          text \<open>now the head of uv^lw's states must be shown to be q0 for all l\<close>
          show "0 \<le> l \<longrightarrow> u @ repeat v l @ ?w \<in> lang dfa"
          proof (cases "l=0")
            case True
            have "word (hd (uqs@vqs@?wqs@[?wq])) ?wq dfa (u@v@?w)"
            proof -
              have uvw: "word_rec_states (uqs@vqs@?wqs) ?wq dfa (u@v@?w)" 
              proof (cases ?wqs)
                case Nil
                then have "word_rec_states (uqs@vqs@?wqs) ?wq dfa (u@v@?w) = word_rec_states (uqs@vqs) ?wq dfa (u@v)" using wordl_eq_statesl
                  by (metis Nil_is_append_conv append.right_neutral fw gwqs_gwq_Wgwqsgwq length_0_conv)
                also have "word_rec_states (uqs@vqs) ?wq dfa (u@v)" 
                proof -
                  from Nil have "vq = ?wq"
                    by (metis Nil_is_append_conv add.right_neutral append_self_conv2 fw gwqs_gwq_Wgwqsgwq hd_fwqsfwq last_snoc le_add_diff_inverse length_drop list.sel(1) list.size(3) m nth_append_length qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl)
                  then show ?thesis using base_uv by blast
                qed
                then show ?thesis using calculation by blast
              next
                case (Cons a list)
                then obtain hdw wqs where "(hdw# wqs) = ?wqs" by simp
                then have "hdw = vq"
                   by (metis append_self_conv2 butlast_snoc drop_butlast drop_eq_Nil fw gwqs_gwq_Wgwqsgwq hd_append hd_drop hd_fwqsfwq last_snoc le_eq_less_or_eq list.distinct(1) list.sel(1) m nth_append qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl)
                then show ?thesis 
                  by (metis \<open>hdw # wqs = fwqs @ gwqs\<close> append.assoc append_word_rec_states base_uv w)
              qed
              then show ?thesis using rec_imp_word  uvw \<open>u @ v @ ?w = z\<close> by force
            qed
            then have "hd (uqs@vqs@?wqs@[?wq]) = q\<^sub>0 dfa" using True
              by (metis Nil_is_append_conv append_self_conv2 diff_is_0_eq hd_append2 hd_conv_nth hd_take leD le_eq_less_or_eq local.i_j n not_Cons_self2 qs'_q'_Wqs'q' qs_q take_eq_Nil2 u uq_hd_vqs v)
            also have "hd (uqs@vqs@?wqs@[?wq]) = hd (uqs@vqs)"
              by (metis Nil_is_append_conv diff_is_0_eq hd_append leD local.i_j not_Cons_self2 take_eq_Nil2 v)
            then have "hd (uqs@vqs) = q\<^sub>0 dfa" using calculation by presburger
            let ?wrs = "word_rec_states (uqs@(repeat vqs l)@?wqs) ?wq dfa (u@(repeat v l)@?w)"
            have ?wrs using u_repeat_v_l_w by simp
            have "?wrs = word_rec_states (uqs@?wqs) ?wq dfa (u@?w)" using u_repeat_v_l_w uw by blast
            have "hd ((uqs@?wqs)@[?wq]) = q\<^sub>0 dfa"
            proof (cases "uqs=[]")
              case True
              then have "vq = q\<^sub>0 dfa"
                using \<open>hd (uqs @ vqs) = q\<^sub>0 dfa\<close>  hd_eq_last_v by auto
              also have "hd (?wqs@[?wq]) = vq" 
              proof (cases ?wqs)
                case Nil
                then show ?thesis
                  by (metis Nil_is_append_conv add.right_neutral fw gwqs_gwq_Wgwqsgwq hd_fwqsfwq last_snoc le_add_diff_inverse length_drop list.size(3) m nth_append_length qs'_q'_Wqs'q' qs_q vfw wordl_eq_statesl)
              next
                case (Cons a list)
                then show ?thesis
                proof (cases fwqs)
                  case Nil  
                  then show ?thesis 
                  proof (cases gwqs)
                    case Nil
                    then show ?thesis 
                      using hd_fwqsfwq local.Cons by force
                  next
                    case (Cons a list)
                    then obtain hdgwq gwq' where "(hdgwq#gwq') = gwqs" by simp
                    then have "hdgwq = vq" 
                      by (metis add.commute append_butlast_last_id drop_eq_Nil2 fw gwqs_gwq_Wgwqsgwq hd_append hd_drop_conv_nth hd_fwqsfwq last_ConsL last_appendR less_Suc_eq_le list.sel(1) list.simps(3) local.Nil m not_less_eq_eq plus_1_eq_Suc qs'_q'_Wqs'q' qs_q_length vfw)
                    then show ?thesis
                      using \<open>hdgwq # gwq' = gwqs\<close> local.Nil by force
                  qed
                next
                  case (Cons a list)
                  then show ?thesis 
                    using hd_fwqsfwq by auto
                qed
              qed
              then show ?thesis  by (simp add: True calculation)
            next
              case False
              then show ?thesis using calculation by fastforce
            qed
            then show ?thesis using rec_imp_word uw wq_f using True by force
          next
            case False
            let ?l = "(l-1)" 
            let ?ulvw=  "word_rec_states (uqs@(repeat vqs l)@?wqs) ?wq dfa (u@(repeat v l)@?w)"
            have ulvw: ?ulvw using u_repeat_v_l_w by blast
            then have eq:"?ulvw = word_rec_states (uqs@vqs@(repeat vqs ?l)@?wqs) ?wq dfa (u@v@(repeat v ?l)@?w)"
              by (metis False append.assoc bot_nat_0.extremum le_eq_less_or_eq repeat_rev)
            then have "hd (uqs@(repeat vqs l)@?wqs@[?wq]) = hd (uqs@vqs)"
              by (metis False Nil_is_append_conv bot_nat_0.extremum diff_is_0_eq hd_append leD le_eq_less_or_eq local.i_j not_Cons_self2 repeat_rev take_eq_Nil2 v)
            then have "hd (uqs@(repeat vqs l)@?wqs@[?wq]) = q\<^sub>0 dfa"
              by (metis (no_types, lifting) antisym_conv3 gr_implies_not_zero hd_append hd_conv_nth hd_take n qs'_q'_Wqs'q' qs_q snoc_eq_iff_butlast take_eq_Nil u uq_hd_vqs)
            then show ?thesis using rec_imp_word ulvw wq_f by fastforce
          qed
        qed
        text \<open>Now we simply put everything together\<close>
        then show ?thesis
          using \<open>length (u @ v) \<le> n\<close> \<open>u @ v @ ?w = z\<close> \<open>v \<noteq> []\<close> by blast
      qed
      then show ?thesis
        by blast
    next
      case False
      then show ?thesis by blast
    qed
  qed
  show ?thesis using n z by blast
qed

end