theory hw2
imports Main
begin

fun add :: "nat \<Rightarrow> nat" where
  "add x = x + 1"

value "add 3"


fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0"
| "count x (y # xs) = (if x = y then add (count x xs)  else count x xs) " 

value "length [1::nat,3,5,3]"
value "count (3::nat) [1,3,5,3]"

theorem[simp]: "count a xs <= length xs"
  apply (induction xs)
  by auto

 (*define tree*)
datatype 'a tree = Tip | Node " 'a tree" 'a " 'a tree" | leave 'a

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r ) = Node (mirror r ) a (mirror l)"
| "mirror (leave a) = leave a"

datatype 'a list = Nil | Cons 'a " 'a list"

thm list.induct

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"


lemma app_nil [simp]: "app xs Nil = xs"
  apply (induction xs)
  by auto

lemma app_assoc [simp]: "app xs (app ys zs) = app (app xs ys) zs"
  apply (induction xs)
  by auto

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev(Cons True (Cons False Nil))"
value "app (Cons a (Cons b Nil)) (Cons a (Cons c Nil))"

fun preorder :: "'a tree \<Rightarrow> 'a list" where
"preorder Tip = Nil" 
| "preorder (Node l a r) = (app (app (Cons a Nil) (preorder l)) (preorder r))"
| "preorder (leave a)  = (Cons a Nil)"

value "preorder (Node (Node Tip f Tip) a Tip)"

fun postorder :: "'a tree \<Rightarrow> 'a list" where
"postorder Tip = Nil" 
| "postorder (Node l a r) = (app (app (postorder l) (postorder r)) (Cons a Nil))"
| "postorder (leave a) = (Cons a Nil)"


value "rev (postorder (Node (Node Tip f Tip) a (Node (Node Tip a_1 Tip) a_2 (leave a_3))))"
value "preorder (mirror (Node (Node Tip f Tip) a (Node (Node Tip a_1 Tip) a_2 (leave a_3))))"

theorem Tip_lema1:
 "preorder (mirror Tip) = rev (postorder Tip)"
  apply (induction Tip)
  by auto

theorem leave_lema[simp]: 
 "\<And>x. preorder (mirror (leave x)) = hw2.rev (postorder (leave x))"
  apply (induction)
  by auto

lemma rev_append [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  by auto

theorem final : "preorder (mirror t) = rev (postorder t)"
  apply (induction t)
  by auto

end