theory Homework3_template
  imports "HOL-IMP.Hoare_Examples"
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
  refl:  "star r x x"
| step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

(* Problem 1 *)



inductive palindrome :: "'a list \<Rightarrow> bool" where
  pal0: "palindrome []" | 
  palaxsa: "palindrome xs \<Longrightarrow>  palindrome (s # xs @ [s]) "  (* complete definition *)


lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct )
  by auto  (* replace with proof *)


(* Problem 2 *)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x"
| step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"



lemma star_one: "r a b \<Longrightarrow> star r a b"
  (* After applying rule step, ?y appears because Isabelle does
     not know what to instantiate for y in theorem step. *)
  apply (rule step)
  (* apply assumption means looking for an assumption that matches
     the goal. Isabelle will see that r a ?y matches r a b with ?y = b. *)
   apply assumption
  (* The remaining goal is just refl rule. *)
  apply (rule refl)
  done



lemma star_step2_detailed: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  (* Induction on proof trees begin with induction rule followed
     by the name of the induction theorem. Isabelle will figure out
     what need to be proved for induction. Here we show detailed
     application of introduction rules. *)
  apply (induction rule: star.induct)
   apply (rule step)
    apply assumption
   apply (rule refl)
  subgoal for x y z'
    apply (rule step[where y=y])
     apply assumption
    by auto
  done



lemma  "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule:star'.induct) 
  apply (rule refl)
  apply (rule star_step2_detailed)
   apply assumption
  apply assumption
  

lemma[simp]: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  by(auto intro: refl' step')

lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  by (auto simp: refl')
  
   (* replace with proof *)


(* Problem 3 *)

lemma
  "\<turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x}
     WHILE Less (N 0) (V ''x'') DO (
       ''x'' ::= Plus (V ''x'') (N (-1));;
       ''y'' ::= Plus (V ''y'') (N (-1))
     )
     {\<lambda>t. t ''y'' = y - x}"
apply (rule strengthen_pre)
  prefer 2
  apply (rule While'[where P="\<lambda>s. s ''y'' = y - x + s ''x'' \<and>   0 \<le> s ''x''"])
 prefer 2
   apply simp
  apply (rule Seq)
  prefer 2
  apply (rule Assign)
  apply simp
   apply (rule Assign')
  apply simp
  by auto   (* replace with proof *)


(* Problem 4 *)

(* Hint: use algebra_simps and power2_eq_square *)
thm algebra_simps
thm power2_eq_square

lemma
  "\<turnstile> { \<lambda>s. s ''x'' = i \<and> 0 \<le> i}                  \<comment> \<open>x = i \<and> 0 \<le> i\<close>
     ''r'' ::= N 0;; ''r2'' ::= N 1;;             \<comment> \<open>r := 0; r2 := 1;\<close>
     WHILE (Not (Less (V ''x'') (V ''r2'')))      \<comment> \<open>while (!x < r2)) {\<close>
     DO (''r'' ::= Plus (V ''r'') (N 1);;         \<comment> \<open>   r := r + 1\<close>
         ''r2'' ::= Plus (V ''r2'')               \<comment> \<open>   r2 := r2 + (r + r + 1)\<close>
            (Plus (Plus (V ''r'') (V ''r'')) (N 1)))
     {\<lambda>s. (s ''r'')^2 \<le> i \<and> i < (s ''r'' + 1)^2}"  \<comment> \<open>r ^ 2 \<le> i \<and> i < (r+1) ^ 2\<close>
   (* replace with proof *)
  apply (rule strengthen_pre)
  prefer 2
  apply (rule Seq)
  prefer 2
    apply (rule While'[where P="\<lambda>s. s ''x'' = i \<and> (s ''r'')^2 \<le> i \<and> s ''r2'' = (s ''r''+1)^2"])
     apply (rule Seq)
      apply simp
      prefer 2
      apply (rule Assign)
  apply simp
     apply (rule Assign')
     apply simp
  apply auto
   by (auto simp add: algebra_simps  power2_eq_square)
