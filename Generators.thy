header {* Generators *}

theory "Generators"
imports
   "~~/src/HOL/Algebra/Group"
   "~~/src/HOL/Algebra/Lattice"
begin

text {* This theory is not specific to Free Groups and could be moved to a more 
general place. It defines the subgroup generated by a set of generators and
that homomorphisms agree on the generated subgroup if they agree on the
generators. *}

notation subgroup (infix "\<le>" 80)

subsection {* The subgroup generated by a set *}

text {* The span of a set of subgroup generators, i.e. the generated subgroup, can
be defined inductively or as the intersection of all subgroups containing the
generators. Here, we define it inductively and proof the equivalence *}

inductive_set gen_span :: "('a,'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set" ("\<guillemotleft>_\<guillemotright>\<index>")
  for G and gens
where gen_one [intro!, simp]: "\<one>\<^bsub>G\<^esub> \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"
    | gen_gens: "x \<in> gens \<Longrightarrow> x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"
    | gen_inv: "x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<Longrightarrow> inv\<^bsub>G\<^esub> x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"
    | gen_mult: "\<lbrakk> x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>; y \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<rbrakk> \<Longrightarrow>  x \<otimes>\<^bsub>G\<^esub> y \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"

lemma (in group) gen_span_closed:
  assumes "gens \<subseteq> carrier G"
  shows "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> carrier G"
proof (* How can I do this in one "by" line? *)
  fix x
  from assms show "x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<Longrightarrow> x \<in> carrier G"
    by -(induct rule:gen_span.induct, auto)
qed

lemma (in group) gen_subgroup_is_subgroup: 
      "gens \<subseteq> carrier G \<Longrightarrow> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<le> G"
by(rule subgroupI)(auto intro:gen_span.intros simp add:gen_span_closed)

lemma (in group) gen_subgroup_is_smallest_containing:
  assumes "gens \<subseteq> carrier G"
    shows "\<Inter>{H. H \<le> G \<and> gens \<subseteq> H} = \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"
proof
  show "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> \<Inter>{H. H \<le> G \<and> gens \<subseteq> H}"
  proof(rule Inf_greatest)
    fix H
    assume "H \<in> {H. H \<le> G \<and> gens \<subseteq> H}"
    hence "H \<le> G" and "gens \<subseteq> H" by auto
    show "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> H"
    proof
      fix x
      from `H \<le> G` and `gens \<subseteq> H`
      show "x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<Longrightarrow> x \<in> H"
       unfolding subgroup_def
       by -(induct rule:gen_span.induct, auto)
    qed
  qed
next
  from `gens \<subseteq> carrier G`
  have "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<le> G" by (rule gen_subgroup_is_subgroup)
  moreover
  have "gens \<subseteq> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>" by (auto intro:gen_span.intros)
  ultimately
  show "\<Inter>{H. H \<le> G \<and> gens \<subseteq> H} \<subseteq> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"
    by(auto intro:Inter_lower)
qed

subsection {* Generators and homomorphisms *}

text {* Two homorphisms agreeing on some elements agree on the span of those elements.*}

lemma hom_unique_on_span:
  assumes "group G"
      and "group H"
      and "gens \<subseteq> carrier G"
      and "h \<in> hom G H"
      and "h' \<in> hom G H"
      and "\<forall>g \<in> gens. h g = h' g"
  shows "\<forall>x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>. h x = h' x"
proof
  interpret G: group G by fact
  interpret H: group H by fact
  interpret h: group_hom G H h by unfold_locales fact
  interpret h': group_hom G H h' by unfold_locales fact

  fix x
  from `gens \<subseteq> carrier G` have "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> carrier G" by (rule G.gen_span_closed)
  with assms show "x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<Longrightarrow> h x = h' x" apply -
  proof(induct rule:gen_span.induct)
    case (gen_mult x y)
      hence x: "x \<in> carrier G" and y: "y \<in> carrier G" and
            hx: "h x = h' x" and hy: "h y = h' y" by auto
      thus "h (x \<otimes>\<^bsub>G\<^esub> y) = h' (x \<otimes>\<^bsub>G\<^esub> y)" by simp
  qed auto
qed

subsection {* Sets of generators *}

text {* There is no definition for @{text gens} is a generating set of
@{text G}. This is easily expressed by @{text "\<guillemotleft>gens\<guillemotright> = carrier G"}. *}

text {* The following is application of @{text hom_unique_on_span} on a generating
  set of the whole group. *}

lemma (in group) hom_unique_by_gens:
  assumes "group H"
      and gens: "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> = carrier G"
      and "h \<in> hom G H"
      and "h' \<in> hom G H"
      and "\<forall>g \<in> gens. h g = h' g"
  shows "\<forall>x \<in> carrier G. h x = h' x"
proof
  fix x

  from gens have "gens \<subseteq> carrier G" by (auto intro:gen_span.gen_gens)
  with assms and group_axioms have r: "\<forall>x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>. h x = h' x"
    by -(erule hom_unique_on_span, auto)
  with gens show "x \<in> carrier G \<Longrightarrow> h x = h' x" by auto
qed

lemma (in group_hom) hom_span:
  assumes "gens \<subseteq> carrier G"
  shows "h ` (\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>) = \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub>"
proof(rule set_ext, rule iffI)
  from `gens \<subseteq> carrier G`
  have "\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> carrier G" by (rule G.gen_span_closed)

  fix y
  assume "y \<in> h ` \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>"
  then obtain x where "x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>" and "y = h x" by auto
  from `x \<in> \<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub>`
  have "h x \<in> \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub>"
  proof(induct x)
    print_cases
    case (gen_inv x)
    hence "x \<in> carrier G" and "h x \<in> \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub>"
      using `\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> carrier G`
      by auto
    thus ?case by (auto intro:gen_span.intros)
  next
    case (gen_mult x y)
    hence "x \<in> carrier G" and "h x \<in> \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub>"
    and   "y \<in> carrier G" and "h y \<in> \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub>"
      using `\<guillemotleft>gens\<guillemotright>\<^bsub>G\<^esub> \<subseteq> carrier G`
      by auto
    thus ?case by (auto intro:gen_span.intros)
  qed(auto intro: gen_span.intros)
  with `y = h x`
  show "y \<in> \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub>" by simp
next
  fix x
  show "x \<in> \<guillemotleft>h ` gens\<guillemotright>\<^bsub>H\<^esub> \<Longrightarrow> x \<in> h ` \<guillemotleft>gens\<guillemotright>"
  proof(induct x rule:gen_span.induct)
  print_cases
    case (gen_inv y)
      then  obtain x where "y = h x" and "x \<in> \<guillemotleft>gens\<guillemotright>" by auto
      moreover
      hence "x \<in> carrier G"  using `gens \<subseteq> carrier G` 
        by (auto dest:G.gen_span_closed)
      ultimately show ?case 
        by (auto intro:hom_inv[THEN sym] rev_image_eqI gen_span.gen_inv simp del:group_hom.hom_inv hom_inv)
  next
   case (gen_mult y y')
      then  obtain x and x'
        where "y = h x" and "x \<in> \<guillemotleft>gens\<guillemotright>"
        and "y' = h x'" and "x' \<in> \<guillemotleft>gens\<guillemotright>" by auto
      moreover
      hence "x \<in> carrier G" and "x' \<in> carrier G" using `gens \<subseteq> carrier G` 
        by (auto dest:G.gen_span_closed)
      ultimately show ?case
        by (auto intro:hom_mult[THEN sym] rev_image_eqI gen_span.gen_mult simp del:group_hom.hom_mult hom_mult)
  qed(auto intro:rev_image_eqI intro:gen_span.intros)
qed


subsection {* Product of a list of group elements *}

text {* Not strictly related to generators of groups, this is still a general
group concept and not related to FreeGroups. *}

abbreviation (in monoid) m_concat
  where "m_concat \<equiv> foldl (op \<otimes>) \<one>"

lemma (in monoid) m_concat_closed[simp]:
 "set l \<subseteq> carrier G \<Longrightarrow> m_concat l \<in> carrier G"
  by (induct l rule:rev_induct, auto)

lemma (in monoid) m_concat_append[simp]:
  assumes "set a \<subseteq> carrier G"
      and "set b \<subseteq> carrier G"
  shows "m_concat (a@b) = m_concat a \<otimes> m_concat b"
using assms
by(induct b rule:rev_induct)(auto simp add: m_assoc)

lemma (in monoid) m_concat_cons[simp]:
  "\<lbrakk> x \<in> carrier G ; set xs \<subseteq> carrier G \<rbrakk> \<Longrightarrow> m_concat (x#xs) = x \<otimes> m_concat xs"
by(induct xs rule:rev_induct)(auto simp add: m_assoc)

subsection {* Isomorphisms *}

text {* Nicer way of proving that something is a group homomorphism or isomorphism *}

lemma group_homI[intro]:
  assumes range: "h ` (carrier g1) \<subseteq> carrier g2"
      and hom: "\<forall>x\<in>carrier g1. \<forall>y\<in>carrier g1. h (x \<otimes>\<^bsub>g1\<^esub> y) = h x \<otimes>\<^bsub>g2\<^esub> h y"
  shows "h \<in> hom g1 g2"
proof-
  have "h \<in> carrier g1 \<rightarrow> carrier g2" using range  by auto
  thus "h \<in> hom g1 g2" using hom unfolding hom_def by auto
qed

lemma group_isoI[intro]:
  assumes inj: "inj_on h (carrier g1)"
      and surj: "h ` (carrier g1) = carrier g2"
      and hom: "\<forall>x\<in>carrier g1. \<forall>y\<in>carrier g1. h (x \<otimes>\<^bsub>g1\<^esub> y) = h x \<otimes>\<^bsub>g2\<^esub> h y"
  shows "h \<in> g1 \<cong> g2"
proof-
  from inj and surj
  have bij: "bij_betw h (carrier g1) (carrier g2)"
    unfolding bij_betw_def by (rule conjI)
  hence "h \<in> carrier g1 \<rightarrow> carrier g2"
    by (rule bij_betw_imp_funcset)
  with hom have "h \<in> hom g1 g2"
    unfolding hom_def by auto
  with bij show "h \<in> g1 \<cong> g2"
    unfolding iso_def by auto
qed


end

