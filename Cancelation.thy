header {* Cancelation of words of generators and their inverses *}

theory Cancelation
imports
   "~~/src/HOL/Algebra/Group"
   List
   "~~/src/HOL/Lambda/Commutation"
begin

text {*
This theory defines cancelation via relations. The one-step relation @{term
"cancels_to_1 a b"} describes that @{term b} is obtained from @{term a} by removing
exactly one pair of generators, while @{term cancels_to} is the reflexive
transitive hull of that relation. Due to confluence, this relation has a normal
form, allowing for the definition of @{term normalize}.
*}


subsection {* Auxillary results about relations *}

text {*
These were helpfully provided by Andreas Lochbihler.
*}

theorem lconfluent_confluent:
  "\<lbrakk> wfP (R^--1); \<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d  \<rbrakk> \<Longrightarrow> confluent R"
by(auto simp add: diamond_def commute_def square_def intro: newman)

lemma confluentD:
  "\<lbrakk> confluent R; R^** a b; R^** a c  \<rbrakk> \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d"
by(auto simp add: commute_def diamond_def square_def)

lemma tranclp_DomainP: "R^++ a b \<Longrightarrow> DomainP R a"
by(auto elim: converse_tranclpE)

lemma confluent_unique_normal_form:
  "\<lbrakk> confluent R; R^** a b; R^** a c; \<not> DomainP R b; \<not> DomainP R c  \<rbrakk> \<Longrightarrow> b = c"
-- "AL: komprimierter Beweis"
by(fastsimp dest!: confluentD[of R a b c] dest: tranclp_DomainP rtranclpD[where a=b] rtranclpD[where a=c])

subsection {* Definition of the @{term "canceling"} relation *}

types 'a "g_i" = "(bool \<times> 'a)" (* A generator or its inverse *)
types 'a "word_g_i" = "'a g_i list" (* A word in the generators or their inverses *)

text {*
These type aliases encode the notion of a ``generator or its inverse''
(@{typ "'a g_i"}) and the notion of a ``word in generators and their inverse''
(@{typ "'a word_g_i"}), which form the building blocks of Free Groups.
*}
(* Too bad I cannot use antiquotations _before_ the definition, it would make
the text easier to read. *)

definition canceling :: "'a g_i \<Rightarrow> 'a g_i \<Rightarrow> bool"
 where "canceling a b = ((snd a = snd b) \<and> (fst a \<noteq> fst b))"

text {*
A generators cancels with its inverse, either way.
*}

subsubsection {* Simple results about canceling *}

lemma cancel_cancel: "\<lbrakk> canceling a b; canceling b c \<rbrakk> \<Longrightarrow> a = c"
by (auto intro: prod_eqI simp add:canceling_def)

lemma cancel_sym: "canceling a b \<Longrightarrow> canceling b a"
by (simp add:canceling_def)

lemma cancel_sym_neg: "\<not>canceling a b \<Longrightarrow> \<not>canceling b a"
by (rule classical, simp add:canceling_def)

subsection {* Definition of the @{term "cancels_to"} relation *}

text {*
First, we define the function that removes the @{term i}th and @{text "(i+1)"}st
element from a word of generators, together with basic properties.
*}

definition cancel_at :: "nat \<Rightarrow> 'a word_g_i \<Rightarrow> 'a word_g_i"
where "cancel_at i l = take i l @ drop (2+i) l"

lemma cancel_at_length[simp]:
  "1+i < length l \<Longrightarrow> length (cancel_at i l) = length l - 2"
by(auto simp add: cancel_at_def)

lemma cancel_at_nth1[simp]:
  "\<lbrakk> n < i; 1+i < length l  \<rbrakk> \<Longrightarrow> (cancel_at i l) ! n = l ! n"
by(auto simp add: cancel_at_def nth_append)


lemma cancel_at_nth2[simp]:
  assumes "n \<ge> i" and "n < length l - 2"
  shows "(cancel_at i l) ! n = l ! (n + 2)"
proof-
  from `n \<ge> i` and `n < length l - 2`
  have "i = min (length l) i"
    by auto
  with `n \<ge> i` and `n < length l - 2`
  show "(cancel_at i l) ! n = l ! (n + 2)" 
    by(auto simp add: cancel_at_def nth_append nth_via_drop)
qed

text {*
Then we can define the relation @{term "cancels_to_1_at i a b"} which specifies
that @{term b} can be obtained by @{term a} by canceling the @{term i}th and
@{text "(i+1)"}st position.

Base on that, we existentially quantify over the position @{text i} to obtain
the relation @{text "cancels_to_1"}, of wich @{text "cancels_to"} is the
transitive hull.

A word is @{text "canceled"} if it can not be canceled any futher.
*}

definition cancels_to_1_at ::  "nat \<Rightarrow> 'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> bool"
where  "cancels_to_1_at i l1 l2 = (0\<le>i \<and> (1+i) < length l1
                              \<and> canceling (l1 ! i) (l1 ! (1+i))
                              \<and> (l2 = cancel_at i l1))"

definition cancels_to_1 :: "'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> bool"
where "cancels_to_1 l1 l2 = (\<exists>i. cancels_to_1_at i l1 l2)"

definition cancels_to  :: "'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> bool"
where "cancels_to = cancels_to_1^**"

-- "AL: [trans] deklariert Transitivitaetsregeln, die man mit also verwenden kann"
lemma cancels_to_trans [trans]: "\<lbrakk> cancels_to a b; cancels_to b c \<rbrakk> \<Longrightarrow> cancels_to a c"
by (auto simp add:cancels_to_def)

definition canceled :: "'a word_g_i \<Rightarrow> bool"
 where "canceled l = (\<not> DomainP cancels_to_1 l)"

(*
lemma "cancels_to_1 [(True,(1::nat)),(False,1)] []"
  by (auto simp add:cancels_to_1_def canceling_def cancel_at_def cancels_to_1_at_def)
lemma "cancels_to [(True,(1::nat)),(False,1)] []"
  by (auto simp add:cancels_to_1_def canceling_def cancel_at_def cancels_to_1_at_def)
*)

subsubsection {* Existence of the normal form *}

text {*
One of two steps to show that we have a normal form is the following lemma,
quaranteeing that by canceling, we always end up at a fully canceled word.
*}

(*
I turned this proof into the next, structured proof. But is this really an improvement?
lemma canceling_terminates: "wfP (cancels_to_1^--1)"
apply(simp add:wfP_def)
apply (rule_tac r = "measure size" in wf_subset)
apply(auto simp add: cancels_to_1_def cancel_at_def cancels_to_1_at_def)
done
*)
lemma canceling_terminates: "wfP (cancels_to_1^--1)"
proof-
  have "wf (measure length)" by auto
  -- "AL" 
  moreover
  have "{(x, y). cancels_to_1 y x} \<subseteq> measure length"
    by (auto simp add: cancels_to_1_def cancel_at_def cancels_to_1_at_def)
  ultimately -- "AL" (* with `wf (measure length)` *)
  have "wf {(x, y). cancels_to_1 y x}"
    by(rule wf_subset)
  -- "AL: ersetzt:"
  (*by(rule_tac r = "measure size" in wf_subset)*)
  thus ?thesis by (simp add:wfP_def)
qed

text {*
The next two lemmas prepare for the proof of confluence. It does not matter in
which order we cancel, we can obtain the same result.
*}

lemma canceling_neighbor:
  assumes "cancels_to_1_at i l a" and "cancels_to_1_at (Suc i) l b"
  shows "a = b"
proof-
  from `cancels_to_1_at i l a`
    have "canceling (l ! i) (l ! Suc i)" and "i < length l"
    by (auto simp add: cancels_to_1_at_def)
  
  from `cancels_to_1_at (Suc i) l b`
    have "canceling (l ! Suc i) (l ! Suc (Suc i))" and "Suc (Suc i) < length l"
    by (auto simp add: cancels_to_1_at_def)

  from `canceling (l ! i) (l ! Suc i)` and `canceling (l ! Suc i) (l ! Suc (Suc i))`
    have "l ! i = l ! Suc (Suc i)" by (rule cancel_cancel)

  from `cancels_to_1_at (Suc i) l b`
    have "b = take (Suc i) l @ drop (Suc (Suc (Suc i))) l"
    by (simp add: cancels_to_1_at_def cancel_at_def)
  also from `i < length l`
  have "\<dots> = take i l @ [l ! i] @ drop (Suc (Suc (Suc i))) l"
    by(auto simp add: take_Suc_conv_app_nth)
  also from `l ! i = l ! Suc (Suc i)`
  have "\<dots> = take i l @ [l ! Suc (Suc i)] @ drop (Suc (Suc (Suc i))) l"
    by simp
  also from `Suc (Suc i) < length l`
  have "\<dots> = take i l @ drop (Suc (Suc i)) l"
    by (simp add: drop_Suc_conv_tl)
  also from `cancels_to_1_at i l a` have "\<dots> = a"
    by (simp add: cancels_to_1_at_def cancel_at_def)
  finally show "a = b" by(rule sym)
qed

lemma canceling_indep:
  assumes "cancels_to_1_at i l a" and "cancels_to_1_at j l b" and "j > Suc i"
  obtains c where "cancels_to_1_at (j - 2) a c" and "cancels_to_1_at i b c"
proof(atomize_elim)
  from `cancels_to_1_at i l a`
    have "Suc i < length l"
     and "canceling (l ! i) (l ! Suc i)"
     and "a = cancel_at i l"
     and "length a = length l - 2"
     and "min (length l) i = i"
    by (auto simp add:cancels_to_1_at_def)
  from `cancels_to_1_at j l b`
    have "Suc j < length l"
     and "canceling (l ! j) (l ! Suc j)"
     and "b = cancel_at j l"
     and "length b = length l - 2"
    by (auto simp add:cancels_to_1_at_def)

  let ?c = "cancel_at (j - 2) a"
  from `j > Suc i`
  have "Suc (Suc (j - 2)) = j"
    and "Suc (Suc (Suc j - 2)) = Suc j"
    by auto
  with `min (length l) i = i` and `j > Suc i` and `Suc j < length l`
  have "(l ! j) = (cancel_at i l ! (j - 2))"
    and "(l ! (Suc j)) = (cancel_at i l ! Suc (j - 2))"
    by(auto simp add:cancel_at_def simp add:nth_append)
  
  with `cancels_to_1_at i l a`
    and `cancels_to_1_at j l b`
  have "canceling (a ! (j - 2)) (a ! Suc (j - 2))"
    by(auto simp add:cancels_to_1_at_def)
  
  with `j > Suc i` and `Suc j < length l` and `length a = length l - 2`
  have "cancels_to_1_at (j - 2) a ?c" by (auto simp add: cancels_to_1_at_def)

  from `length b = length l - 2` and `j > Suc i` and `Suc j < length l`
  have "Suc i < length b" by auto
  
  moreover from `b = cancel_at j l` and `j > Suc i` and `Suc i < length l`
  have "(b ! i) = (l ! i)" and "(b ! Suc i) = (l ! Suc i)"
    by (auto simp add:cancel_at_def nth_append)
  with `canceling (l ! i) (l ! Suc i)`
  have "canceling (b ! i) (b ! Suc i)" by simp
  
  moreover from `j > Suc i` and `Suc j < length l`
  have "min i j = i"
    and "min (j - 2) i = i"
    and "min (length l) j = j"
    and "min (length l) i = i"
    and "Suc (Suc (j - 2)) = j"
    by auto
  with `a = cancel_at i l` and `b = cancel_at j l` and `Suc (Suc (j - 2)) = j`
  have "cancel_at (j - 2) a = cancel_at i b"
    by (auto simp add:cancel_at_def take_drop)
  
  ultimately have "cancels_to_1_at i b (cancel_at (j - 2) a)"
    by (auto simp add:cancels_to_1_at_def)

  with `cancels_to_1_at (j - 2) a ?c`
  show "\<exists>c. cancels_to_1_at (j - 2) a c \<and> cancels_to_1_at i b c" by blast
qed

text {* This is the confluence lemma *}
-- "AL: Besserer Name? z.B. confluent_cancels_to_1"
lemma lconf: "confluent cancels_to_1"
proof(rule lconfluent_confluent)
  show "wfP cancels_to_1\<inverse>\<inverse>" by (rule canceling_terminates)
next
  fix a b c
  assume "cancels_to_1 a b"
  then obtain i where "cancels_to_1_at i a b"
    by(simp add: cancels_to_1_def)(erule exE)
    -- "AL: ersetzt by -(simp add: cancels_to_1_def, erule exE)"
  assume "cancels_to_1 a c"
  then obtain j where "cancels_to_1_at j a c"
    by(simp add: cancels_to_1_def)(erule exE)
    -- "AL: ersetzt by -(simp add: cancels_to_1_def, erule exE)"

  show "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d"
  proof (cases "i=j")
    assume "i=j"
    from `cancels_to_1_at i a b`
      have "b = cancel_at i a" by (simp add:cancels_to_1_at_def)
    moreover from `i=j`
      have "\<dots> = cancel_at j a" by (clarify)
    moreover from `cancels_to_1_at j a c`
      have "\<dots> = c" by (simp add:cancels_to_1_at_def)
    ultimately have "b = c" by (simp)
    hence "cancels_to_1\<^sup>*\<^sup>* b b"
      and "cancels_to_1\<^sup>*\<^sup>* c b" by auto
    thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by blast
  next 
    assume "i \<noteq> j"
    show ?thesis
    proof (cases "j = Suc i")
      assume "j = Suc i"
        with `cancels_to_1_at i a b` and `cancels_to_1_at j a c`
        have "b = c" by (auto elim: canceling_neighbor)
      hence "cancels_to_1\<^sup>*\<^sup>* b b"
        and "cancels_to_1\<^sup>*\<^sup>* c b" by auto
      thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by blast
    next
      assume "j \<noteq> Suc i"
      show ?thesis
      proof (cases "i = Suc j")
        assume "i = Suc j"
          with `cancels_to_1_at i a b` and `cancels_to_1_at j a c`
          have "c = b" by (auto elim: canceling_neighbor)
        hence "cancels_to_1\<^sup>*\<^sup>* b b"
          and "cancels_to_1\<^sup>*\<^sup>* c b" by auto
        thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by blast
      next
        assume "i \<noteq> Suc j"
        show ?thesis
        proof (cases "i < j")
          assume "i < j"
            with `j \<noteq> Suc i` have "Suc i < j" by auto
          with `cancels_to_1_at i a b` and `cancels_to_1_at j a c`
          obtain d where "cancels_to_1_at (j - 2) b d" and "cancels_to_1_at i c d"
            by(erule canceling_indep)
          hence "cancels_to_1 b d" and "cancels_to_1 c d" 
            by (auto simp add:cancels_to_1_def)
          (* ersetzt
              have "\<exists>d. cancels_to_1_at (j - 2) b d \<and> cancels_to_1_at i c d" by (auto elim: canceling_indep)
              then obtain d where "cancels_to_1_at (j - 2) b d \<and> cancels_to_1_at i c d" by (erule exE)
              hence "cancels_to_1 b d \<and> cancels_to_1 c d" by (auto simp add:cancels_to_1_def)*)
          thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by (auto)
        next
          assume "\<not> i < j"
          with `j \<noteq> Suc i` and `i \<noteq> j` and `i \<noteq> Suc j` have "Suc j < i" by auto
          with `cancels_to_1_at i a b` and `cancels_to_1_at j a c`
          obtain d where "cancels_to_1_at (i - 2) c d" and "cancels_to_1_at j b d"
            by -(erule canceling_indep)
          hence "cancels_to_1 b d" and "cancels_to_1 c d" 
            by (auto simp add:cancels_to_1_def)
              (* ersetzt
              have "\<exists>d. cancels_to_1_at (i - 2) c d \<and> cancels_to_1_at j b d" by (auto elim: canceling_indep)
              then obtain d where "cancels_to_1_at (i - 2) c d \<and> cancels_to_1_at j b d" by (erule exE)
              hence "cancels_to_1 b d \<and> cancels_to_1 c d" by (auto simp add:cancels_to_1_def)*)
          thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by (auto)
        qed
      qed
    qed
  qed
qed

text {*
And finally, we show that there exists a unique normal form for each word.
*}

lemma inv_rtrcl: "R^**^--1 = R^--1^**" (* Did I overlook this in the standard libs? *)
by (auto simp add:expand_fun_eq intro: dest:rtranclp_converseD intro:rtranclp_converseI)


lemma norm_form_uniq:
  assumes "cancels_to a b"
      and "cancels_to a c"
      and "canceled b"
      and "canceled c"
  shows "b = c"
proof-
  have "confluent cancels_to_1" by (rule lconf)
  moreover 
  from `cancels_to a b` have "cancels_to_1^** a b" by (simp add: cancels_to_def)
  moreover
  from `cancels_to a c` have "cancels_to_1^** a c" by (simp add: cancels_to_def)
  moreover
  from `canceled b` have "\<not> DomainP cancels_to_1 b" by (simp add: canceled_def)
  moreover
  from `canceled c` have "\<not> DomainP cancels_to_1 c" by (simp add: canceled_def)
  ultimately
  show "b = c"
    by (rule confluent_unique_normal_form)
qed

subsubsection {* Some properties on cancelation *}

text {*
Distributivity rules of cancelation and @{text append}.
*}

lemma cancel_to_1_append:
  assumes "cancels_to_1 a b"
  shows "cancels_to_1 (l@a@l') (l@b@l')"
proof-
  from `cancels_to_1 a b` obtain i where "cancels_to_1_at i a b"
    -- "AL ersetzt: by -(simp add: cancels_to_1_def, erule exE)"
    by(simp add: cancels_to_1_def)(erule exE)
  hence "cancels_to_1_at (length l + i) (l@a@l') (l@b@l')"
    by (auto simp add:cancels_to_1_at_def nth_append cancel_at_def)
  thus "cancels_to_1 (l@a@l') (l@b@l')"
    by (auto simp add: cancels_to_1_def)
qed

lemma cancel_to_append:
  assumes "cancels_to a b"
  shows "cancels_to (l@a@l') (l@b@l')"
proof-
  from `cancels_to a b`
  have "cancels_to_1^** a b" by (simp add:cancels_to_def)
  thus ?thesis
  proof(induct)
    case base show ?case by (simp add:cancels_to_def)
  next
    case (step b c)
    from `cancels_to_1 b c`
    have "cancels_to_1 (l @ b @ l') (l @ c @ l')" by (rule cancel_to_1_append)
    with `cancels_to (l @ a @ l') (l @ b @ l')` show ?case
      by (auto simp add:cancels_to_def)
  qed

  (* AL ersetzt:
  proof(induct rule:rtranclp.induct)
    fix a
    show "cancels_to (l @ a @ l') (l @ a @ l')" by (simp add:cancels_to_def)
  next
    fix a b c
    assume "cancels_to (l @ a @ l') (l @ b @ l')"
    assume "cancels_to_1 b c"
    hence "cancels_to_1 (l @ b @ l') (l @ c @ l')" by (rule cancel_to_1_append)
    with `cancels_to (l @ a @ l') (l @ b @ l')`
    show "cancels_to (l @ a @ l') (l @ c @ l')" by (auto simp add:cancels_to_def)
  qed *)
qed

lemma cancels_to_append2:
  assumes "cancels_to a a'"
      and "cancels_to b b'"
  shows "cancels_to (a@b) (a'@b')"
proof-
  from `cancels_to a a'`
  have "cancels_to_1^** a a'" by (simp add:cancels_to_def)
  thus ?thesis
  proof induct
    case base
    from `cancels_to b b'` have "cancels_to (a@b@[]) (a@b'@[])" by (rule cancel_to_append)
    thus ?case by simp
  next
    case (step ba c)
    from `cancels_to_1 ba c` have "cancels_to_1 ([]@ba@b') ([]@c@b')"
      by(rule cancel_to_1_append)
    with `cancels_to (a @ b) (ba @ b')` show ?case by (simp add:cancels_to_def)
  qed
  (* AL: ersetzt
  proof(induct rule:rtranclp.induct)
   fix a
   from `cancels_to b b'`
   have "cancels_to (a@b@[]) (a@b'@[])" by (rule cancel_to_append)
   thus "cancels_to (a@b) (a@b')" by simp
  next
   fix a ba c
   assume "cancels_to_1 (ba :: (bool \<times> 'a) list) c"
      -- "Why do I have to fix the type here?"
      -- "AL: because Isabelle first tries to type-check your terms and infers the most general types. Only at the show command it tries to match the assumtions and fixes with the actual goals."
      
   hence "cancels_to_1 ([]@ba@b') ([]@c@b')" by (rule cancel_to_1_append)
   hence "cancels_to_1 (ba@b') (c@b')" by simp
   moreover
   assume "cancels_to (a @ b) (ba @ b')"
   ultimately
   show "cancels_to (a @ b) (c @ b')" by (simp add:cancels_to_def)
  qed *)
qed

text {*
The empty list is cancelled.
*}

lemma empty_canceled[simp]: "canceled []"
by(auto simp:add canceled_def cancels_to_1_def cancels_to_1_at_def)

lemma cancels_to_self[simp]: "cancels_to l l"
by (simp add:cancels_to_def)

subsection {* Definition of normalization *}

text {*
Using the THE construct, we can define the normalization function
@{text normalize} as the unique fully cancled word that the argument cancels
to.
*}

definition normalize :: "'a word_g_i \<Rightarrow> 'a word_g_i"
where "normalize l = (THE l'. cancels_to l l' \<and> canceled l')"

text {*
Some obvious properties of the normalize function, and other useful lemmas.
*}

lemma
  shows normalized_canceled[simp]: "canceled (normalize l)"
  and   normalized_cancels_to[simp]: "cancels_to l (normalize l)"
proof-
  thm canceling_terminates
  let ?Q = "{l'. cancels_to_1^** l l'}"
  have "l \<in> ?Q" by (auto) hence "\<exists>x. x \<in> ?Q" by (rule exI)

  have "wfP cancels_to_1^--1"
    by (rule canceling_terminates)
  hence "\<forall>Q. (\<exists>x. x \<in> Q) \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. cancels_to_1 z y \<longrightarrow> y \<notin> Q)"
    by (simp add:wfP_eq_minimal)
  hence "(\<exists>x. x \<in> ?Q) \<longrightarrow> (\<exists>z\<in>?Q. \<forall>y. cancels_to_1 z y \<longrightarrow> y \<notin> ?Q)"
    by (erule_tac x="?Q" in allE)
  then obtain l' where "l' \<in> ?Q" and minimal: "\<And>y. cancels_to_1 l' y \<Longrightarrow> y \<notin> ?Q"
    (* AL ersetzt: "(\<forall>y. cancels_to_1 l' y \<longrightarrow> y \<notin> ?Q)" *) by auto
  
  from `l' \<in> ?Q` have "cancels_to l l'" by (auto simp add: cancels_to_def)

  have "canceled l'"
  proof(rule ccontr)
    assume "\<not> canceled l'" hence "DomainP cancels_to_1 l'" by (simp add: canceled_def)
    then obtain y where "cancels_to_1 l' y" by auto
    with `cancels_to l l'` have "cancels_to l y" by (auto simp add: cancels_to_def)
    from `cancels_to_1 l' y` have "y \<notin> ?Q" by(rule minimal)
    (* AL: ersetzt
      from `\<forall>y. cancels_to_1 l' y \<longrightarrow> y \<notin> ?Q`
      have "cancels_to_1 l' y \<longrightarrow> y \<notin> ?Q" by auto
      with `cancels_to_1 l' y` have "y \<notin> ?Q" by -(rule mp) *)
    hence "\<not> cancels_to_1^** l y" by auto
    hence "\<not> cancels_to l y" by (simp add: cancels_to_def)
    with `cancels_to l y` show False by contradiction
  qed

  from `cancels_to l l'` and `canceled l'`
  have "cancels_to l l' \<and> canceled l'" by simp 
  hence "cancels_to l (normalize l) \<and> canceled (normalize l)"
    unfolding normalize_def
  proof ((*simp add:normalize_def, *)rule theI)
    fix l'a
    assume "cancels_to l l'a \<and> canceled l'a"
    thus "l'a = l'" using `cancels_to l l' \<and> canceled l'` by (auto elim:norm_form_uniq)
  qed
  thus "canceled (normalize l)" and "cancels_to l (normalize l)" by auto
qed

lemma normalize_discover:
  assumes "canceled l'"
      and "cancels_to l l'"
  shows "normalize l = l'"
proof-
  from `canceled l'` and `cancels_to l l'`
  have "cancels_to l l' \<and> canceled l'" by auto
  thus ?thesis by (auto simp add:normalize_def elim:norm_form_uniq)
qed

text {* Words, related by cancelation, have the same normal form *}

lemma normalize_canceled[simp]:
  assumes "cancels_to l l'"
  shows   "normalize l = normalize l'"
proof(rule normalize_discover)
  show "canceled (normalize l')" by (rule normalized_canceled)
next
  have "cancels_to l' (normalize l')" by (rule normalized_cancels_to)
  with `cancels_to l l'`
  show "cancels_to l (normalize l')" by (rule cancels_to_trans)
qed

text {* Normalization is idempotent *}

lemma normalize_idemp[simp]:
  assumes "canceled l"
  shows "normalize l = l"
using assms
by(rule normalize_discover)(rule cancels_to_self)

(* AL ersetzt:
proof(rule normalize_discover)
  from `canceled l` show "canceled l".
next
  show "cancels_to l l" by (rule cancels_to_self)
qed
*)

text {*
This lemma lifts the distributivity results from above to the normalize
function.
*}

lemma normalize_append_cancel_to:
  assumes "cancels_to l1 l1'"
  and     "cancels_to l2 l2'"
  shows "normalize (l1 @ l2) = normalize (l1' @ l2')"
proof(rule normalize_discover)
  show "canceled (normalize (l1' @ l2'))" by (rule normalized_canceled)
next
  from `cancels_to l1 l1'` and `cancels_to l2 l2'`
  have "cancels_to (l1 @ l2) (l1' @ l2')" by (rule cancels_to_append2)
  also -- "AL ersetzt:  moreover"
  have "cancels_to (l1' @ l2') (normalize (l1' @ l2'))" by (rule normalized_cancels_to)
  finally -- "AL ersetzt: ultimately"
  show "cancels_to (l1 @ l2) (normalize (l1' @ l2'))" . -- "AL ersetzt  by (rule cancels_to_trans)"
qed

end