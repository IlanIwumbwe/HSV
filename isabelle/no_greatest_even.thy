theory no_greatest_even imports Complex_Main 
begin

(*
  doing proof that there's no greatest even number myself
  
  clarify: move  statement to different level of abstraction, better for proof library
  have: this fact is true, inregardless of any other statement
  can also use `moreover`, `ultimately` idiom to make this cleaner (remove need for using part in show)
*)

theorem "\<forall>n :: int. even n \<longrightarrow> (\<exists>m :: int. even m \<and> m > n)"
proof clarify
  fix n :: int
  assume "even n"
  hence * : "even (n+2)" by simp
  have ** : "n < n+2" by simp
  show "\<exists>m. even m \<and> n < m" using * and ** by blast
qed
end
