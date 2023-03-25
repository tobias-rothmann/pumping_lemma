theory Example
  imports Original
begin

text \<open>As an example we prove that a^nb^n is not regular using the PL\<close>

subsection \<open>aux lemmas\<close>

lemma repeat_length: "\<lbrakk>length w = x; n\<ge>0\<rbrakk> \<Longrightarrow> length (repeat w n) = n*x"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma take_at: "\<lbrakk>i\<le>n; length x = 1\<rbrakk> \<Longrightarrow> take i (repeat x n @ repeat y m) = take i (repeat x n)"
proof (induction i arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case 
  proof (cases "(repeat x n @ repeat y m)")
    case Nil
    then show ?thesis by auto 
  next
    case (Cons a list)
    then show ?thesis
      by (metis Suc.prems(1) Suc.prems(2) append.right_neutral bot_nat_0.extremum diff_is_0_eq' mult.right_neutral repeat_length take_0 take_append)
  qed
qed

lemma drop_at: "\<lbrakk>i\<le>n; length x = 1\<rbrakk> \<Longrightarrow> drop i (repeat x n @ repeat y m) = drop i (repeat x n) @ repeat y m"
proof (induction i arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case 
    proof (cases "(repeat x n @ repeat y m)")
      case Nil
      then show ?thesis by simp
    next
      case (Cons a list)
      then show ?thesis
        by (metis Suc.prems(1) Suc.prems(2) bot_nat_0.extremum diff_is_0_eq' drop0 drop_append mult.right_neutral repeat_length)
    qed
qed

lemma drop_1_repeat: "length x = 1 \<Longrightarrow> drop 1 (repeat x n) = repeat x (n-1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (metis append_eq_conv_conj repeat_rev zero_less_Suc)
qed

lemma drop_repeat: "\<lbrakk>i\<le>n; length x = 1\<rbrakk> \<Longrightarrow> drop i (repeat x n) = repeat x (n-i)"
proof (induction i arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc i)
  have "drop (Suc i) (repeat x n) = drop 1 (drop i (repeat x n))" by simp
  then have "drop (Suc i) (repeat x n) = drop 1 (repeat x (n - i))"
    using Suc.IH Suc.prems(1) Suc.prems(2) Suc_leD by presburger
  then have "drop (Suc i) (repeat x n) = repeat x (n-i-1)"
    by (metis Suc.prems(2) drop_1_repeat)
  then show ?case by simp
qed

lemma take_repeat: "\<lbrakk>i\<le>n; length x = 1\<rbrakk> \<Longrightarrow> take i (repeat x n) = repeat x i"
proof (induction i arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case 
    by (metis Suc_le_D Suc_le_mono bot_nat_0.extremum diff_Suc_1 le_refl mult.right_neutral repeat_length repeat_rev take_all_iff take_append zero_less_Suc)
qed

lemma repeat_concat: "repeat x i @ repeat x j = repeat x (i+j)"
proof (induction i arbitrary: j)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case
    by (metis Original.i add_Suc_shift append.assoc diff_Suc_1 repeat_rev zero_less_Suc)
qed

lemma set_repeat: "set (repeat a n) \<subseteq> set a"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

subsection\<open>Example proof a^nb^n\<close>
text \<open>Showing that a^nb^n is indeed not a regular language using the pumping lemma definition
from Orginal.thy We assume that the language of the dfa is a^nb^n and the properties of a DFA 
(finite and determinstic etc.) then we show that the pumping lemma doesn't hold.\<close>
theorem anbn: 
  assumes dfa_lang: "lang dfa = {w. \<exists>n\<ge>0. w=repeat ''a'' n @ (repeat ''b'' n)}"
      and "Q_\<Sigma>_finite (dfa::DFA)" 
      and "\<delta>_total_on_Q_\<Sigma> dfa"
      and "q\<^sub>0_in_Q dfa"
      and "F_sub_Q dfa"
    shows "\<not>(\<exists>n::nat>0. \<forall>z \<in> (lang dfa). length z \<ge> n \<longrightarrow> (
        \<exists> u v w. z = u@v@w \<and>
        v \<noteq> '''' \<and>
        length (u@v) \<le> n \<and>
        (\<forall>i::nat. (u@(repeat v i)@w) \<in> (lang dfa))
))"
proof 
  text \<open>simply an abbreviation for the PL\<close>
  let ?PL = "(\<exists>n::nat>0. \<forall>z \<in> (lang dfa). length z \<ge> n \<longrightarrow> (
          \<exists> u v w. z = u@v@w \<and>
          v \<noteq> '''' \<and>
          length (u@v) \<le> n \<and>
          (\<forall>i::nat. (u@(repeat v i)@w) \<in> (lang dfa))
  ))"
  text \<open>This is what we want to show and which does falsify the PL, therefore FPL\<close>
  let ?FPL = "\<forall>n>0. \<exists>z\<in>lang dfa. n\<le>length z \<and> (\<forall>u v w. u@v@w=z \<and> v\<noteq> [] \<and> length (u@v) \<le> n \<longrightarrow> (\<exists>i. u @ repeat v i @ w \<notin> lang dfa))"
  show "?PL \<Longrightarrow> False" 
  proof - 
    let ?a = "''a''"
    let ?b = "''b''"
    have length_a: "length ?a = 1" by simp
    have length_b: "length ?b = 1" by simp
    have uneq_ab: "?a\<noteq>?b" by simp
    have falsify_pl: "?FPL \<Longrightarrow> \<not>?PL"
    proof 
      assume asm1: "\<forall>n>0. \<exists>z\<in>lang dfa. n \<le> length z \<and> (\<forall>u v w. u @ v @ w = z \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<longrightarrow> (\<exists>i. u @ repeat v i @ w \<notin> lang dfa))"
      assume asm2: ?PL
      then show False using asm1 by metis
    qed
    text \<open>have the PL hold for contradiction\<close>
    have ?PL using assms pumping_lemma by fast
    text \<open>Now show that the PL actually doesn't hold via our FPL\<close>
    also have ?FPL
    proof (intro allI)
      fix n
      show "0 < n \<longrightarrow>
         (\<exists>z\<in>lang dfa. n \<le> length z \<and> (\<forall>u v w. u @ v @ w = z \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<longrightarrow> (\<exists>i. u @ repeat v i @ w \<notin> lang dfa))) "
      proof
        assume "0 < n"
        show "\<exists>z\<in>lang dfa. n \<le> length z \<and> (\<forall>u v w. u @ v @ w = z \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<longrightarrow> (\<exists>i. u @ repeat v i @ w \<notin> lang dfa)) "
        proof -
          obtain z where z: "z=repeat ?a n @ (repeat ?b n)"
            by simp
          then have z_in_lang: "z \<in> lang dfa"
            using assms(1) using \<open>0 < n\<close> by blast
          have "n \<le> length z " by (simp add: repeat_length z)
          also have "(\<forall>u v w. u @ v @ w = z \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<longrightarrow> (\<exists>i. u @ repeat v i @ w \<notin> lang dfa))"
          proof (intro allI)
            fix u v w
            show "u @ v @ w = z \<and> v \<noteq> [] \<and> length (u @ v) \<le> n \<longrightarrow> (\<exists>i. u @ repeat v i @ w \<notin> lang dfa)"
            proof
              assume asm_uvw: "u @ v @ w = z \<and> v \<noteq> [] \<and> length (u @ v) \<le> n"
              text \<open>Until this point we were just instantiating the predicates, now we want show 
              that u=a^j and v = a^k and therefore if we cut v or multiply it, the amount of as will
              no longer equal the amount of bs\<close>
              then obtain m where m: "u@v = repeat ?a m \<and> m\<le>n" unfolding z using append.assoc append_eq_conv_conj length_a take_at take_repeat by metis
              then have take_m: "take m z = repeat ?a m" unfolding z using length_a take_at take_repeat by metis
              then have w: "w=drop m z" by (metis asm_uvw append.assoc append_take_drop_id m same_append_eq)
              then obtain l where w_l:"w=repeat ?a l @ repeat ?b n \<and> l=(n-m)" unfolding z
                by (metis drop_at drop_repeat length_a m)
              have "repeat ?a m @ repeat ?a l @ repeat ?b n = z" using asm_uvw m w_l by force
              obtain j where j: "u=take j (u@v) \<and> v=drop j (u@v)" using append_eq_conv_conj by blast
              then have u_repeat: "u=repeat ?a j"
                by (metis \<open>\<And>thesis. (\<And>m. u @ v = repeat ''a'' m \<and> m \<le> n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> asm_uvw bot_nat_0.extremum drop_all length_a linorder_not_less mult.right_neutral order_less_le repeat_length take_repeat)
              obtain k where v_repeat: "v=repeat ?a k \<and> k=(m-j)"
                by (metis asm_uvw bot_nat_0.extremum drop_repeat drop_take j length_a m order_less_le take0 take_m zero_less_diff)
              have "repeat ?a j @ repeat ?a k @ repeat ?a l @ repeat ?b n = z"
                using asm_uvw u_repeat v_repeat w_l by blast
              then have "j+k+l=n"
                by (metis "Original.0" add.commute add_diff_inverse_nat asm_uvw diff_is_0_eq le_add_diff_inverse2 m order_less_le v_repeat w_l)
              have u_v0_w: "u@repeat v 0@w = repeat ?a j @ repeat ?a l @ repeat ?b n" 
                using u_repeat w_l using "Original.0" by blast
              then have u_v0_w: "u@repeat v 0@w = repeat ?a (j+l) @ repeat ?b n"
                by (simp add: repeat_concat)
              text \<open>After obtaining uv and w accordingly we show that if we cut v, which is not 
              empty, the word u@w is no longer in the language because the number of as and bs is 
              unequal. We show this by contradiction and assume u@w is in lang dfa to show that 
              they are actually not.\<close>
              have "u@ repeat v 0 @w \<notin> lang dfa"
              proof 
                 text \<open>As an auxillary lemma we prove that for every word, if it is in the language 
                 of the dfa, then the amount of as and bs must be equal. Because we now j+l<n and
                 this lemma will later indicate that they are equal, which leads to the contradiction.\<close>
                 have in_lang: "\<forall>i j. repeat ?a i @ repeat ?b j \<in> lang dfa \<longrightarrow> i=j"
                 proof (intro allI)
                  fix i j
                  show "repeat ?a i @ repeat ?b j \<in> lang dfa \<longrightarrow> i = j"
                  proof 
                    assume "repeat ?a i @ repeat ?b j \<in> lang dfa"
                    then have pre: "\<exists>n\<ge>0. repeat ?a i @ repeat ?b j = repeat ?a n @ (repeat ?b n)"
                      using dfa_lang by blast
                    have "\<exists>n\<ge>0. repeat ?a i @ repeat ?b j = repeat ?a n @ (repeat ?b n) \<Longrightarrow> i=j"
                    proof -
                      assume "\<exists>n\<ge>0. repeat ?a i @ repeat ?b j = repeat ?a n @ repeat ?b n"
                      then obtain n where "n\<ge>0 \<and> repeat ?a i @ repeat ?b j = repeat ?a n @ repeat ?b n" by fast
                      then have eq: "repeat ?a i @ repeat ?b j = repeat ?a n @ repeat ?b n" by simp
                      show ?thesis 
                      proof -   
                        text \<open>Now the quantors are all unfolded and the proof can be done by induction. 
                        To do the proof by induction on n we fold i=j into i=n \<and>j=n\<close>
                        have imp_same: "repeat ?a n @ repeat ?b n = repeat ?a i @ repeat ?b j \<Longrightarrow> i=n \<and> j=n"
                        proof (induction n arbitrary: i j)
                          case 0
                          then show ?case
                            by (metis "Original.0" Nil_is_append_conv list.discI repeat.elims)
                        next
                          case (Suc n)
                          text \<open>simply unfold the repeat function until the IH can be satisfied to 
                          then obtain i-1=n and j-1=n, which obviously indicates the case (i=Suc n \<and> j=Suc n)\<close>
                          have "repeat ?a (Suc n) @ repeat ?b (Suc n) = ?a @ repeat ?a (Suc n -1) @ repeat ?b (n) @ ?b"
                            using append.assoc repeat_rev zero_less_Suc by (metis Original.i diff_Suc_1)
                          then have n_extend_ab: "repeat ?a (Suc n) @ repeat ?b (Suc n) = ?a @ repeat ?a n @ repeat ?b n @ ?b" by simp
                          have ijg0: "i>0\<and>j>0"
                          proof 
                            have a_sub: "\<forall>x. set (repeat ?a x) \<subseteq> set ?a "
                            proof 
                              fix x
                              show "set (repeat ?a x) \<subseteq> set ?a"
                              proof (induction x)
                                case 0
                                then show ?case by simp
                              next
                                case (Suc x)
                                then show ?case by simp
                              qed
                            qed
                            have b_sub:"\<forall>x. set (repeat ?b x) \<subseteq> set ?b "
                            proof 
                              fix x
                              show "set (repeat ?b x) \<subseteq> set ?b"
                              proof (induction x)
                                case 0
                                then show ?case by simp
                              next
                                case (Suc x)
                                then show ?case by simp
                              qed
                            qed
                            show i0: "i>0"
                            proof -            
                              have "(CHR ''a'') \<in> set (repeat ''a'' (Suc n) @ repeat ''b'' (Suc n))" by simp
                              also have "(CHR ''a'') \<notin> set (repeat ''b'' j)" using b_sub by auto
                              then have "(CHR ''a'') \<in> set (repeat ''a'' i)"
                                using Suc.prems calculation by fastforce
                              then have "length (repeat ''a'' i) > 0" by force
                              then show ?thesis using gr0I by force
                            qed
                            show j0: "j>0" 
                            proof -            
                              have "(CHR ''b'') \<in> set (repeat ''a'' (Suc n) @ repeat ''b'' (Suc n))" by simp
                              also have "(CHR ''b'') \<notin> set (repeat ''a'' i)" using a_sub by auto
                              then have "(CHR ''b'') \<in> set (repeat ''b'' j)"
                                using Suc.prems calculation by fastforce
                              then have "length (repeat ''b'' j) > 0" by force
                              then show ?thesis using gr0I by force
                            qed
                          qed
                          then have ij_extend_a: "repeat ?a (i) @ repeat ?b (j) = ?a @ repeat ?a (i -1) @ repeat ?b (j)"
                            by (simp add: repeat_rev)
                          then have ij_extend_ab: "repeat ?a (i) @ repeat ?b (j) = ?a @ repeat ?a (i -1) @ repeat ?b (j-1) @ ?b"
                            by (metis Original.i Suc_pred' ijg0)
                          have "repeat ?a n @ repeat ?b n = repeat ?a (i -1) @ repeat ?b (j-1)"
                            using Suc.prems ij_extend_ab n_extend_ab by auto
                          then have " i-1 = n \<and> j-1 = n" using Suc.IH by blast
                          then show ?case by (metis Suc_pred' ijg0)
                        qed 
                        show ?thesis using eq imp_same by presburger
                      qed
                    qed
                    then show "i = j" using pre by blast
                  qed
                qed
                text \<open>After the aux lemma, we can now contradict using our assumptions.\<close>
                assume asm2: "u @ repeat v 0 @ w \<in> lang dfa"
                then have jl_eq_n: "(j+l) = n" using in_lang u_v0_w by force
                also have jl_less_n: "j+l<n"
                proof -  
                  have "k>0" by (metis "Original.0" asm_uvw v_repeat zero_less_iff_neq_zero)
                  then show ?thesis using \<open>j + k + l = n\<close> by fastforce
                qed
                show False using jl_eq_n jl_less_n by blast
              qed
              then show "\<exists>i. u @ repeat v i @ w \<notin> lang dfa" by blast
            qed
          qed
          then show ?thesis using calculation z_in_lang by blast
      qed
    qed
  qed
    then show ?thesis by (metis calculation)
  qed
qed
end